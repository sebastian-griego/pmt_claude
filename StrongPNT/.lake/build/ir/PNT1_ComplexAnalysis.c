// Lean compiler output
// Module: PNT1_ComplexAnalysis
// Imports: Init Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Complex.Norm Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Pow.Complex Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex Mathlib.Analysis.Complex.Exponential Mathlib.Data.Complex.Basic Mathlib.Analysis.Analytic.Basic Mathlib.Analysis.Analytic.Constructions Mathlib.Analysis.Calculus.Deriv.Basic Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Analysis.Calculus.Deriv.Comp Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.Topology.MetricSpace.Basic Mathlib.Analysis.Complex.Liouville Mathlib.Analysis.Complex.Schwarz Mathlib.Analysis.Complex.AbsMax Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Data.Set.Function Mathlib.Analysis.Normed.Module.RCLike.Real
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Exponential(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Constructions(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Mul(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Comp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Liouville(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Schwarz(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_AbsMax(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_CauchyIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Set_Function(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Normed_Module_RCLike_Real(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PNT1__ComplexAnalysis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Exponential(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Constructions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Mul(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Comp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Liouville(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Schwarz(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_AbsMax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_CauchyIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Set_Function(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Normed_Module_RCLike_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
