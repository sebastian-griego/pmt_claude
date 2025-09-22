// Lean compiler output
// Module: PNT4_ZeroFreeRegion
// Imports: Init Mathlib.Analysis.Complex.Basic Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.Analysis.Complex.Exponential Mathlib.Data.Finset.Basic Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.NumberTheory.ArithmeticFunction Mathlib.NumberTheory.VonMangoldt Mathlib.Data.Complex.BigOperators Mathlib.Data.Complex.Basic
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
static lean_object* l_N__zeros___closed__0;
static lean_object* l_N__T___closed__1;
static lean_object* l_N__zeros___closed__14;
static lean_object* l_N__T___closed__10;
LEAN_EXPORT lean_object* l_N__zeros(lean_object*);
static lean_object* l_N__zeros___closed__1;
static lean_object* l_N__T___closed__3;
static lean_object* l_N__zeros___closed__9;
static lean_object* l_N__T___closed__9;
static lean_object* l_N__zeros___closed__2;
LEAN_EXPORT lean_object* l_N__T(lean_object*);
static lean_object* l_N__T___closed__2;
static lean_object* l_N__T___closed__5;
static lean_object* l_N__zeros___closed__13;
static lean_object* l_N__T___closed__6;
static lean_object* l_N__zeros___closed__8;
static lean_object* l_N__T___closed__4;
LEAN_EXPORT lean_object* l_N__T___boxed(lean_object*);
static lean_object* l_N__zeros___closed__12;
lean_object* lean_sorry(uint8_t);
static lean_object* l_N__zeros___closed__15;
static lean_object* l_N__zeros___closed__16;
static lean_object* l_N__T___closed__0;
static lean_object* l_N__zeros___closed__10;
static lean_object* l_N__T___closed__8;
static lean_object* l_N__zeros___closed__11;
static lean_object* l_N__zeros___closed__7;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_N__zeros___closed__17;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_N__zeros___closed__4;
static lean_object* l_N__zeros___closed__6;
LEAN_EXPORT lean_object* l_N__zeros___boxed(lean_object*);
static lean_object* l_N__zeros___closed__3;
static lean_object* l_N__T___closed__11;
static lean_object* l_N__T___closed__12;
static lean_object* l_N__zeros___closed__5;
static lean_object* l_N__zeros___closed__18;
static lean_object* l_N__T___closed__7;
static lean_object* _init_l_N__zeros___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PNT4_ZeroFreeRegion", 19, 19);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(508u);
x_2 = l_N__zeros___closed__1;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__zeros___closed__2;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(508u);
x_2 = l_N__zeros___closed__3;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_N__zeros___closed__4;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__zeros___closed__5;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_N__zeros___closed__6;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_sorry", 6, 6);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__8;
x_2 = l_N__zeros___closed__7;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__10;
x_2 = l_N__zeros___closed__9;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__0;
x_2 = l_N__zeros___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(460825290u);
x_2 = l_N__zeros___closed__12;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__14;
x_2 = l_N__zeros___closed__13;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__16;
x_2 = l_N__zeros___closed__15;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_N__zeros___closed__17;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_N__zeros(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_N__zeros___closed__18;
x_4 = lean_sorry(x_2);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_N__zeros___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_N__zeros(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_N__T___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(512u);
x_2 = l_N__zeros___closed__1;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__T___closed__0;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(512u);
x_2 = l_N__T___closed__1;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_N__T___closed__2;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__T___closed__3;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_N__T___closed__4;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__8;
x_2 = l_N__T___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__10;
x_2 = l_N__T___closed__6;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__0;
x_2 = l_N__T___closed__7;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1630772416u);
x_2 = l_N__T___closed__8;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__14;
x_2 = l_N__T___closed__9;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__16;
x_2 = l_N__T___closed__10;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_N__T___closed__11;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_N__T(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_N__T___closed__12;
x_4 = lean_sorry(x_2);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_N__T___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_N__T(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_Nonvanishing(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Exponential(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_ArithmeticFunction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_VonMangoldt(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_BigOperators(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PNT4__ZeroFreeRegion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_Nonvanishing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Exponential(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_ArithmeticFunction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_VonMangoldt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_BigOperators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_N__zeros___closed__0 = _init_l_N__zeros___closed__0();
lean_mark_persistent(l_N__zeros___closed__0);
l_N__zeros___closed__1 = _init_l_N__zeros___closed__1();
lean_mark_persistent(l_N__zeros___closed__1);
l_N__zeros___closed__2 = _init_l_N__zeros___closed__2();
lean_mark_persistent(l_N__zeros___closed__2);
l_N__zeros___closed__3 = _init_l_N__zeros___closed__3();
lean_mark_persistent(l_N__zeros___closed__3);
l_N__zeros___closed__4 = _init_l_N__zeros___closed__4();
lean_mark_persistent(l_N__zeros___closed__4);
l_N__zeros___closed__5 = _init_l_N__zeros___closed__5();
lean_mark_persistent(l_N__zeros___closed__5);
l_N__zeros___closed__6 = _init_l_N__zeros___closed__6();
lean_mark_persistent(l_N__zeros___closed__6);
l_N__zeros___closed__7 = _init_l_N__zeros___closed__7();
lean_mark_persistent(l_N__zeros___closed__7);
l_N__zeros___closed__8 = _init_l_N__zeros___closed__8();
lean_mark_persistent(l_N__zeros___closed__8);
l_N__zeros___closed__9 = _init_l_N__zeros___closed__9();
lean_mark_persistent(l_N__zeros___closed__9);
l_N__zeros___closed__10 = _init_l_N__zeros___closed__10();
lean_mark_persistent(l_N__zeros___closed__10);
l_N__zeros___closed__11 = _init_l_N__zeros___closed__11();
lean_mark_persistent(l_N__zeros___closed__11);
l_N__zeros___closed__12 = _init_l_N__zeros___closed__12();
lean_mark_persistent(l_N__zeros___closed__12);
l_N__zeros___closed__13 = _init_l_N__zeros___closed__13();
lean_mark_persistent(l_N__zeros___closed__13);
l_N__zeros___closed__14 = _init_l_N__zeros___closed__14();
lean_mark_persistent(l_N__zeros___closed__14);
l_N__zeros___closed__15 = _init_l_N__zeros___closed__15();
lean_mark_persistent(l_N__zeros___closed__15);
l_N__zeros___closed__16 = _init_l_N__zeros___closed__16();
lean_mark_persistent(l_N__zeros___closed__16);
l_N__zeros___closed__17 = _init_l_N__zeros___closed__17();
lean_mark_persistent(l_N__zeros___closed__17);
l_N__zeros___closed__18 = _init_l_N__zeros___closed__18();
lean_mark_persistent(l_N__zeros___closed__18);
l_N__T___closed__0 = _init_l_N__T___closed__0();
lean_mark_persistent(l_N__T___closed__0);
l_N__T___closed__1 = _init_l_N__T___closed__1();
lean_mark_persistent(l_N__T___closed__1);
l_N__T___closed__2 = _init_l_N__T___closed__2();
lean_mark_persistent(l_N__T___closed__2);
l_N__T___closed__3 = _init_l_N__T___closed__3();
lean_mark_persistent(l_N__T___closed__3);
l_N__T___closed__4 = _init_l_N__T___closed__4();
lean_mark_persistent(l_N__T___closed__4);
l_N__T___closed__5 = _init_l_N__T___closed__5();
lean_mark_persistent(l_N__T___closed__5);
l_N__T___closed__6 = _init_l_N__T___closed__6();
lean_mark_persistent(l_N__T___closed__6);
l_N__T___closed__7 = _init_l_N__T___closed__7();
lean_mark_persistent(l_N__T___closed__7);
l_N__T___closed__8 = _init_l_N__T___closed__8();
lean_mark_persistent(l_N__T___closed__8);
l_N__T___closed__9 = _init_l_N__T___closed__9();
lean_mark_persistent(l_N__T___closed__9);
l_N__T___closed__10 = _init_l_N__T___closed__10();
lean_mark_persistent(l_N__T___closed__10);
l_N__T___closed__11 = _init_l_N__T___closed__11();
lean_mark_persistent(l_N__T___closed__11);
l_N__T___closed__12 = _init_l_N__T___closed__12();
lean_mark_persistent(l_N__T___closed__12);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
