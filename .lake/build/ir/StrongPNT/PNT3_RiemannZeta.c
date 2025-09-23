// Lean compiler output
// Module: StrongPNT.PNT3_RiemannZeta
// Imports: Init Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Topology.Basic Mathlib.Analysis.Calculus.Deriv.Basic Mathlib.NumberTheory.ArithmeticFunction Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Topology.Algebra.InfiniteSum.Field
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_ArithmeticFunction_moebius___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_PNT3__RiemannZeta_mu(lean_object*);
LEAN_EXPORT lean_object* l_PNT3__RiemannZeta_mu(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ArithmeticFunction_moebius___lam__0(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_CauchyIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_ArithmeticFunction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_InfiniteSum_Field(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_StrongPNT_PNT3__RiemannZeta(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_CauchyIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_ArithmeticFunction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_InfiniteSum_Field(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
