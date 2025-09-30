#!/usr/bin/env bash
set -euo pipefail

# ---------------- Config ----------------
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
FRONTIER="${REPO_ROOT}/blueprint/frontier.jsonl"
PROMPT_PREAMBLE="${REPO_ROOT}/prompts/task_preamble.txt"

LOG_DIR="${REPO_ROOT}/logs"
BUILD_LOG="${LOG_DIR}/lean_build.log"
CLAUDE_LOG="${LOG_DIR}/claude_run.log"

CLAUDE_BIN="${CLAUDE_BIN:-claude}"                       # path to Claude Code CLI
CLAUDE_MODEL="${CLAUDE_MODEL:-claude-sonnet-4-5-20250929}"        # pick your favorite
MAX_TURNS="${CLAUDE_MAX_TURNS:-8}"                       # headless multi-turn cap

mkdir -p "${LOG_DIR}"

# ------------- Helpers (no jq) -------------
first_line() { head -n 1 "${FRONTIER}" 2>/dev/null || true; }

extract_json_str() {
  # Very simple JSON string extractor (first occurrence): key -> value
  # Handles: ..."key":"value"...  (no escaped quotes)
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
  echo "============= CLAUDE iteration ${i} ============="
  STATUS="$(build_once)"
  ERR_SNIP="$(sed -n '1,200p' "${BUILD_LOG}" 2>/dev/null || true)"

  LINE="$(first_line)"
  GOAL="$(extract_json_str goal "${LINE}")"
  FILE_TARGET="$(extract_json_str file "${LINE}")"
  NOTES="$(extract_json_str notes "${LINE}")"

  CONTEXT="$(gather_context "${FILE_TARGET}")"

  # Assemble the user prompt
  USER_PROMPT="$(mktemp)"
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
  } > "${USER_PROMPT}"

  # Run Claude Code headless, bypassing permissions so it can edit/run
  # Flags come from Anthropic’s docs: headless (-p), permission mode, and "dangerously skip permissions".
  # We also cap turns so it doesn’t run forever.
  "${CLAUDE_BIN}" -p \
    --model "${CLAUDE_MODEL}" \
    --max-turns "${MAX_TURNS}" \
    --output-format text \
    --permission-mode acceptEdits \
    --dangerously-skip-permissions \
    --verbose \
    < "${USER_PROMPT}" | tee -a "${CLAUDE_LOG}"

  # Rebuild after the agent’s run to capture final logs
  build_once >/dev/null
done
