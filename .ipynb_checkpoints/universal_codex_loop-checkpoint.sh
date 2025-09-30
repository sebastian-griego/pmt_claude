#!/usr/bin/env bash
set -euo pipefail

# ---------------- Config ----------------
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
FRONTIER="${REPO_ROOT}/blueprint/frontier.jsonl"
PROMPT_PREAMBLE="${REPO_ROOT}/prompts/task_preamble.txt"

LOG_DIR="${REPO_ROOT}/logs"
BUILD_LOG="${LOG_DIR}/lean_build.log"
CODEX_LOG="${LOG_DIR}/codex_run.log"

CODEX_BIN="${CODEX_BIN:-codex}"     # path to Codex CLI

mkdir -p "${LOG_DIR}"

# ------------- Helpers (no jq) -------------
first_line() { head -n 1 "${FRONTIER}" 2>/dev/null || true; }

extract_json_str() {
  local key="$1"
  local line="$2"
  echo "${line}" | sed -n "s/.*\"${key}\"[[:space:]]*:[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p"
}

gather_context() {
  local file="$1"
  echo "----- TARGET FILE -----"
  echo "${file:-"(none specified)"}"
  if [[ -n "${file}" && -f "${REPO_ROOT}/${file}" ]]; then
    echo "----- HEAD (first 80 lines) -----"
    sed -n '1,80p' "${REPO_ROOT}/${file}"
    echo "----- NEARBY CODE (last 200 of first 300) -----"
    sed -n '1,300p' "${REPO_ROOT}/${file}" | tail -n 200
  else
    echo "File does not exist yet; create it if appropriate."
  fi
}

build_once() {
  echo "==> lake build"
  (cd "${REPO_ROOT}" && lake build) &> "${BUILD_LOG}" || true
  if grep -q "error:" "${BUILD_LOG}"; then
    echo "FAIL"
  else
    echo "OK"
  fi
}

# --------------- Main ---------------------
ITER="${1:-1}"

for ((i=1;i<=ITER;i++)); do
  echo "============= CODEX iteration ${i} ============="
  STATUS="$(build_once)"
  ERR_SNIP="$(sed -n '1,200p' "${BUILD_LOG}" 2>/dev/null || true)"

  LINE="$(first_line)"
  GOAL="$(extract_json_str goal "${LINE}")"
  FILE_TARGET="$(extract_json_str file "${LINE}")"
  NOTES="$(extract_json_str notes "${LINE}")"

  CONTEXT="$(gather_context "${FILE_TARGET}")"

  # Compose a single prompt for codex exec
  PROMPT="$(mktemp)"
  {
    cat "${PROMPT_PREAMBLE}"
    echo
    echo "== BUILD STATUS =="
    echo "${STATUS}"
    if [[ "${STATUS}" == "FAIL" ]]; then
      echo
      echo "== BUILD ERROR (first 200 lines) =="
      echo "${ERR_SNIP}"
    fi
    echo
    echo "== FRONTIER GOAL =="
    echo "${GOAL:-"(unspecified)"}"
    echo
    echo "== FRONTIER FILE =="
    echo "${FILE_TARGET:-"(unspecified)"}"
    [[ -n "${NOTES}" ]] && { echo; echo "== NOTES =="; echo "${NOTES}"; }
    echo
    echo "== CONTEXT =="
    echo "${CONTEXT}"
    echo
    echo "Please proceed autonomously: make edits, run shell, and build until success; then implement the frontier task."
  } > "${PROMPT}"

  # Run Codex non-interactively.
  # Official docs: `codex exec "..."` runs without the TUI.
  # Default approval mode is `auto` which allows edits/commands inside the current workspace w/o prompts.
  # Keep the working dir at repo root so Codex has full access to this project.
  (cd "${REPO_ROOT}" && "${CODEX_BIN}" exec "$(cat "${PROMPT}")") | tee -a "${CODEX_LOG}"

  # Rebuild after the agent’s run to capture final logs
  build_once >/dev/null
done
