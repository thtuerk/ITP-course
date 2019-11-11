open HolKernel Parse boolLib bossLib;

open rich_listTheory arithmeticTheory
val _ = new_theory "e3";


``!l. APPEND l [] = l``

Induct >| [
  REWRITE_TAC [APPEND],
  ASM_REWRITE_TAC [APPEN]
])



open listTheory


val``!l1 l2. REV l1 l2 = REVERSE l1 ++ l2``

Induct >| [
  REWRITE_TAC [REV_DEF, REVERSE, APPEND],
  ASM_REWRITE_TAC [REVERSE, REV_DEF, APPEND_SNOC1]
])

``!l. REVERSE l = REV l []``

Induct >| [
  REWRITE_TAC [REV_DEF, REVERSE],
  ASM_REWRITE_TAC [REVERSE, REV_DEF]
])


``!l1 l2. LENGTH (DROP (LENGTH l2) (l1 ++ l2)) = LENGTH l1``

Induct >| [
  REWRITE_TAC[LENGTH, APPEND, DROP_LENGTH_NIL],

  Cases_on `l2` |> [
    REWRITE_TAC[APPEND_NIL, LENGTH, DROP],

    ASM_REWRITE_TAC[APPEND, LENGTH, DROP]


``!l1 l2. LENGTH (DROP (LENGTH l2) (l1 ++ l2)) = LENGTH l1``

REPEAT GEN_TAC >>
SPEC_TAC (``l1:'a list``, ``l1:'a list``) THEN
Induct_on `l2` >| [
  REWRITE_TAC[LENGTH, DROP, APPEND_NIL],

  Cases_on `l1` >| [
    REWRITE_TAC[LENGTH, DROP, APPEND, DROP_LENGTH_NIL],

    REPEAT GEN_TAC >>
    REWRITE_TAC[LENGTH, DROP, APPEND] THEN
    `t ++ h' :: l2 = (t ++ [h']) ++ l2` by REWRITE_TAC[APPEND, GSYM APPEND_ASSOC] >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[LENGTH_APPEND, LENGTH, ADD_CLAUSES]
  ]
])


val MAKE_CHANGE_def = Define `
  (MAKE_CHANGE [] a = if (a = 0) then [[]] else []) /\
  (MAKE_CHANGE (c::cs) a = (
     (if (c <= a /\ 0 < a) then
       (MAP (\l. c::l) (MAKE_CHANGE cs (a - c)))
     else []) ++ (MAKE_CHANGE cs a)))`


val MAKE_CHANGE_PROP = prove(``!cs. MAKE_CHANGE cs 0 = [[]]``,

Induct >| [
  REWRITE_TAC[MAKE_CHANGE_def],
  ASM_REWRITE_TAC[MAKE_CHANGE_def, prim_recTheory.LESS_REFL, APPEND]
])

val MAKE_CHANGE_PROP1 = prove (``!cs a l.
  MEM l (MAKE_CHANGE cs a) ==> (SUM l = a)``,

Induct >| [
  REPEAT GEN_TAC >>
  REWRITE_TAC[MAKE_CHANGE_def] >> 
  Cases_on `a = 0` >> (
    ASM_REWRITE_TAC[MEM] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUM]
  ),

  REPEAT GEN_TAC >>
  ASM_REWRITE_TAC [MAKE_CHANGE_def, MEM_APPEND, DISJ_IMP_THM] >>
  Cases_on `h <= a /\ 0 < a` >| [
    ASM_REWRITE_TAC[MEM_MAP] THEN
    BETA_TAC THEN
    REPEAT STRIP_TAC THEN
    `SUM y = (a - h)` by METIS_TAC[] >>
    ASM_REWRITE_TAC [SUM] >>
    DECIDE_TAC,

    ASM_REWRITE_TAC[MEM]
  ]
]);


val _ = export_theory();

