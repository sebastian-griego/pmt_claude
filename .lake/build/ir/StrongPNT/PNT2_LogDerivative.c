// Lean compiler output
// Module: StrongPNT.PNT2_LogDerivative
// Imports: Init Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Analytic.Basic Mathlib.Analysis.Analytic.Composition Mathlib.Analysis.Analytic.CPolynomial Mathlib.Analysis.Calculus.Deriv.Basic Mathlib.Topology.MetricSpace.Basic Mathlib.Topology.MetricSpace.ProperSpace Mathlib.Topology.CompactOpen Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Exp Mathlib.Analysis.Complex.ExponentialBounds Mathlib.Topology.Instances.Complex Mathlib.Analysis.Normed.Module.RCLike.Real StrongPNT.PNT1_ComplexAnalysis
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
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10;
static lean_object* l_PNT2__LogDerivative_termD___closed__1;
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0;
uint8_t l_Lean_Syntax_matchesLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative_termD___closed__2;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6;
static lean_object* l_PNT2__LogDerivative_termD___closed__5;
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__zerosetKfR__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1;
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f;
static lean_object* l_PNT2__LogDerivative_termD___closed__0;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative_termD___closed__3;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3;
LEAN_EXPORT lean_object* l_PNT2__LogDerivative_termD;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3;
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5;
static lean_object* l_PNT2__LogDerivative_termD___closed__4;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0;
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__zerosetKfR__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9;
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2;
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12;
static lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1;
static lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3;
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PNT2_LogDerivative", 18, 18);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termD", 5, 5);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PNT2__LogDerivative_termD___closed__1;
x_2 = l_PNT2__LogDerivative_termD___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("D", 1, 1);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative_termD___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_PNT2__LogDerivative_termD___closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_PNT2__LogDerivative_termD___closed__2;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_PNT2__LogDerivative_termD() {
_start:
{
lean_object* x_1; 
x_1 = l_PNT2__LogDerivative_termD___closed__5;
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3;
x_2 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2;
x_3 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1;
x_4 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("openDisk", 8, 8);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5;
x_2 = l_PNT2__LogDerivative_termD___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_PNT2__LogDerivative_termD___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4;
x_14 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6;
x_15 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7;
x_16 = l_Lean_addMacroScope(x_8, x_15, x_9);
x_17 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10;
lean_inc(x_12);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12;
x_20 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14;
x_21 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15;
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node1(x_12, x_20, x_22);
lean_inc(x_12);
x_24 = l_Lean_Syntax_node1(x_12, x_19, x_23);
x_25 = l_Lean_Syntax_node2(x_12, x_13, x_18, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
lean_inc(x_15);
x_16 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Syntax_getArg(x_15, x_8);
lean_dec(x_15);
x_20 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14;
x_21 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15;
x_22 = l_Lean_Syntax_matchesLit(x_19, x_20, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_26 = 0;
x_27 = l_Lean_SourceInfo_fromRef(x_25, x_26);
lean_dec(x_25);
x_28 = l_PNT2__LogDerivative_termD___closed__2;
x_29 = l_PNT2__LogDerivative_termD___closed__3;
lean_inc(x_27);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Syntax_node1(x_27, x_28, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("StrongPNT", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2;
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PNT2__LogDerivative_termD___closed__0;
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PNT2__LogDerivative_termD___closed__0;
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termK_f", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7;
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("K_f", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f() {
_start:
{
lean_object* x_1; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11;
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zerosetKfR", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0;
x_2 = l_PNT2__LogDerivative_termD___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1;
x_14 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2;
x_15 = l_Lean_addMacroScope(x_8, x_14, x_9);
x_16 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5;
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__zerosetKfR__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_replaceRef(x_1, x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8;
x_12 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9;
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Syntax_node1(x_10, x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__zerosetKfR__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__zerosetKfR__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Composition(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_CPolynomial(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_ProperSpace(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_CompactOpen(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Exp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_ExponentialBounds(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Normed_Module_RCLike_Real(uint8_t builtin, lean_object*);
lean_object* initialize_StrongPNT_PNT1__ComplexAnalysis(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_StrongPNT_PNT2__LogDerivative(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Composition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_CPolynomial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_ProperSpace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_CompactOpen(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Exp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_ExponentialBounds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Normed_Module_RCLike_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_StrongPNT_PNT1__ComplexAnalysis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PNT2__LogDerivative_termD___closed__0 = _init_l_PNT2__LogDerivative_termD___closed__0();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__0);
l_PNT2__LogDerivative_termD___closed__1 = _init_l_PNT2__LogDerivative_termD___closed__1();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__1);
l_PNT2__LogDerivative_termD___closed__2 = _init_l_PNT2__LogDerivative_termD___closed__2();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__2);
l_PNT2__LogDerivative_termD___closed__3 = _init_l_PNT2__LogDerivative_termD___closed__3();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__3);
l_PNT2__LogDerivative_termD___closed__4 = _init_l_PNT2__LogDerivative_termD___closed__4();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__4);
l_PNT2__LogDerivative_termD___closed__5 = _init_l_PNT2__LogDerivative_termD___closed__5();
lean_mark_persistent(l_PNT2__LogDerivative_termD___closed__5);
l_PNT2__LogDerivative_termD = _init_l_PNT2__LogDerivative_termD();
lean_mark_persistent(l_PNT2__LogDerivative_termD);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__0);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__1);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__2);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__3);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__4);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__5);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__6);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__7);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__8);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__9);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__10);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__11);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__12);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__13);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__14);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules__PNT2__LogDerivative__termD__1___closed__15);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__0);
l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1 = _init_l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1();
lean_mark_persistent(l_PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______unexpand__PNT2__LogDerivative__openDisk__1___closed__1);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__0);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__1);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__2);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__3);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__4);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__5);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__6);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__7);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__8);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__9);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__10);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f___closed__11);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative_termK__f);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__0);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__1);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__2);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__3);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__4);
l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5 = _init_l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5();
lean_mark_persistent(l___private_StrongPNT_PNT2__LogDerivative_0__PNT2__LogDerivative___aux__StrongPNT__PNT2__LogDerivative______macroRules____private__StrongPNT__PNT2__LogDerivative__0__PNT2__LogDerivative__termK__f__1___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
