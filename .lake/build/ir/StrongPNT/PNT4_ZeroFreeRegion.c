// Lean compiler output
// Module: StrongPNT.PNT4_ZeroFreeRegion
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
static lean_object* l_N__T___closed__13;
static lean_object* l_term_U0001d4b5___closed__1;
static lean_object* l_N__zeros___closed__1;
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0;
static lean_object* l_N__T___closed__3;
static lean_object* l_N__zeros___closed__9;
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1;
static lean_object* l_N__zeros___closed__21;
static lean_object* l_N__T___closed__9;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_N__zeros___closed__2;
LEAN_EXPORT lean_object* l_N__T(lean_object*);
static lean_object* l_N__T___closed__2;
static lean_object* l_N__T___closed__5;
static lean_object* l_N__zeros___closed__13;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_N__T___closed__6;
static lean_object* l_N__zeros___closed__8;
static lean_object* l_N__T___closed__4;
LEAN_EXPORT lean_object* l_N__T___boxed(lean_object*);
static lean_object* l_N__zeros___closed__12;
static lean_object* l_term_U0001d4b5___closed__2;
lean_object* lean_sorry(uint8_t);
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1;
static lean_object* l_N__zeros___closed__15;
static lean_object* l_N__zeros___closed__16;
static lean_object* l_N__T___closed__0;
static lean_object* l_N__zeros___closed__10;
static lean_object* l_N__zeros___closed__19;
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_N__T___closed__8;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_N__zeros___closed__11;
static lean_object* l_N__zeros___closed__7;
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_N__zeros___closed__17;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_term_U0001d4b5___closed__0;
static lean_object* l_N__zeros___closed__4;
static lean_object* l_N__zeros___closed__6;
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0;
LEAN_EXPORT lean_object* l_N__zeros___boxed(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_N__zeros___closed__3;
static lean_object* l_N__T___closed__11;
static lean_object* l_N__zeros___closed__20;
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_term_U0001d4b5___closed__3;
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_N__T___closed__12;
static lean_object* l_N__zeros___closed__5;
static lean_object* l_N__zeros___closed__18;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3;
static lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2;
static lean_object* l_term_U0001d4b5___closed__4;
LEAN_EXPORT lean_object* l_term_U0001d4b5;
static lean_object* l_N__T___closed__7;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_term_U0001d4b5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term𝒵", 8, 5);
return x_1;
}
}
static lean_object* _init_l_term_U0001d4b5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_U0001d4b5___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_term_U0001d4b5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("𝒵", 4, 1);
return x_1;
}
}
static lean_object* _init_l_term_U0001d4b5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_U0001d4b5___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_U0001d4b5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_U0001d4b5___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_term_U0001d4b5___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_term_U0001d4b5() {
_start:
{
lean_object* x_1; 
x_1 = l_term_U0001d4b5___closed__4;
return x_1;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zeroZ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_term_U0001d4b5___closed__1;
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
x_13 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1;
x_14 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2;
x_15 = l_Lean_addMacroScope(x_8, x_14, x_9);
x_16 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4;
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
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1;
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
x_11 = l_term_U0001d4b5___closed__1;
x_12 = l_term_U0001d4b5___closed__2;
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
LEAN_EXPORT lean_object* l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_N__zeros___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("StrongPNT", 9, 9);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PNT4_ZeroFreeRegion", 19, 19);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__2;
x_2 = l_N__zeros___closed__1;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(578u);
x_2 = l_N__zeros___closed__3;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__zeros___closed__4;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(578u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_N__zeros___closed__7;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_N__zeros___closed__8;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_sorry", 6, 6);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__12;
x_2 = l_N__zeros___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__0;
x_2 = l_N__zeros___closed__13;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__2;
x_2 = l_N__zeros___closed__14;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(460825290u);
x_2 = l_N__zeros___closed__15;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__17;
x_2 = l_N__zeros___closed__16;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_N__zeros___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__19;
x_2 = l_N__zeros___closed__18;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__zeros___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_N__zeros___closed__20;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_N__zeros(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_N__zeros___closed__21;
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
x_1 = lean_unsigned_to_nat(582u);
x_2 = l_N__zeros___closed__3;
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
x_1 = lean_unsigned_to_nat(582u);
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
x_1 = l_N__zeros___closed__10;
x_2 = l_N__T___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__12;
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
x_1 = l_N__zeros___closed__2;
x_2 = l_N__T___closed__8;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1630772416u);
x_2 = l_N__T___closed__9;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__17;
x_2 = l_N__T___closed__10;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_N__zeros___closed__19;
x_2 = l_N__T___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_N__T___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_N__T___closed__12;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_N__T(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_N__T___closed__13;
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
LEAN_EXPORT lean_object* initialize_StrongPNT_PNT4__ZeroFreeRegion(uint8_t builtin, lean_object* w) {
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
l_term_U0001d4b5___closed__0 = _init_l_term_U0001d4b5___closed__0();
lean_mark_persistent(l_term_U0001d4b5___closed__0);
l_term_U0001d4b5___closed__1 = _init_l_term_U0001d4b5___closed__1();
lean_mark_persistent(l_term_U0001d4b5___closed__1);
l_term_U0001d4b5___closed__2 = _init_l_term_U0001d4b5___closed__2();
lean_mark_persistent(l_term_U0001d4b5___closed__2);
l_term_U0001d4b5___closed__3 = _init_l_term_U0001d4b5___closed__3();
lean_mark_persistent(l_term_U0001d4b5___closed__3);
l_term_U0001d4b5___closed__4 = _init_l_term_U0001d4b5___closed__4();
lean_mark_persistent(l_term_U0001d4b5___closed__4);
l_term_U0001d4b5 = _init_l_term_U0001d4b5();
lean_mark_persistent(l_term_U0001d4b5);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__0);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__1);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__2);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__3);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______macroRules__term_U0001d4b5__1___closed__4);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__0);
l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1 = _init_l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1();
lean_mark_persistent(l___aux__StrongPNT__PNT4__ZeroFreeRegion______unexpand__zeroZ__1___closed__1);
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
l_N__zeros___closed__19 = _init_l_N__zeros___closed__19();
lean_mark_persistent(l_N__zeros___closed__19);
l_N__zeros___closed__20 = _init_l_N__zeros___closed__20();
lean_mark_persistent(l_N__zeros___closed__20);
l_N__zeros___closed__21 = _init_l_N__zeros___closed__21();
lean_mark_persistent(l_N__zeros___closed__21);
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
l_N__T___closed__13 = _init_l_N__T___closed__13();
lean_mark_persistent(l_N__T___closed__13);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
