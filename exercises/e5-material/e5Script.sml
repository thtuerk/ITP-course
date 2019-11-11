open HolKernel Parse boolLib bossLib;

val _ = new_theory "e5";

open listTheory rich_listTheory arithmeticTheory

(**************)
(* Question 1 *)
(**************)

(*--- 1.1 --- *)

(* TODO: Fill in a proper definition *)
val IS_WEAK_SUBLIST_REC_def = Define `IS_WEAK_SUBLIST_REC (l1 : 'a list) (l2 : 'a list) = T`


(* Some tests *)
val test1 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6]``;
val test2 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;6;5]``;
val test3 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6;8]``;

(* TODO: at least 2 sanity check lemmata *)


(*--- 1.2 --- *)

(* TODO: fill in Definition *)
val IS_WEAK_SUBLIST_FILTER_def = Define `IS_WEAK_SUBLIST_FILTER (l1 : 'a list) (l2 : 'a list) = T`

(* TODO: at least 2 sanity check lemmata *)


(*--- 1.3 --- *)

(* TODO: Prove of auxiliary lemmata *)

val IS_WEAK_SUBLIST_EQUIV = store_thm ("IS_WEAK_SUBLIST_EQUIV",
  ``IS_WEAK_SUBLIST_REC = IS_WEAK_SUBLIST_FILTER``,

REWRITE_TAC[FUN_EQ_THM] >>
CONV_TAC (RENAME_VARS_CONV ["l1", "l2"]) >>
cheat)


(*--- 1.4 --- *)

(* TODO: Prove of auxiliary lemmata and perhaps reorder lemmata below *)

val IS_WEAK_SUBLIST_REC_APPEND_EXTEND_LEFT = store_thm ("IS_WEAK_SUBLIST_REC_APPEND_EXTEND_LEFT",
  ``!l1a l1 l1b l2. IS_WEAK_SUBLIST_REC l1 l2 ==> IS_WEAK_SUBLIST_REC (l1a ++ l1 ++ l1b) l2``,
cheat);

val IS_WEAK_SUBLIST_REC_APPEND = store_thm ("IS_WEAK_SUBLIST_REC_APPEND_EXTEND_LEFT",
  ``!l1a l1b l2a l2b. IS_WEAK_SUBLIST_REC l1a l2a ==>
                      IS_WEAK_SUBLIST_REC l1b l2b ==>
                      IS_WEAK_SUBLIST_REC (l1a ++ l1b) (l2a ++ l2b)``,
cheat);


val IS_WEAK_SUBLIST_REC_REFL = store_thm ("IS_WEAK_SUBLIST_REC_REFL",
  ``!l. IS_WEAK_SUBLIST_REC l l``,
cheat);


val IS_WEAK_SUBLIST_REC_TRANS = store_thm ("IS_WEAK_SUBLIST_REC_TRANS",
  ``!l1 l2 l3. IS_WEAK_SUBLIST_REC l1 l2 ==>
               IS_WEAK_SUBLIST_REC l2 l3 ==>
               IS_WEAK_SUBLIST_REC l1 l3``,
cheat);


val IS_WEAK_SUBLIST_REC_ANTISYM = store_thm ("IS_WEAK_SUBLIST_REC_ANTISYM",
  ``!l1 l2. IS_WEAK_SUBLIST_REC l1 l2 ==>
            IS_WEAK_SUBLIST_REC l2 l1 ==>
            (l1 = l2)``,
cheat);


val IS_WEAK_SUBLIST_FILTER_APPEND_EXTEND_LEFT = store_thm ("IS_WEAK_SUBLIST_FILTER_APPEND_EXTEND_LEFT",
  ``!l1a l1 l1b l2. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (l1a ++ l1 ++ l1b) l2``,
cheat);

val IS_WEAK_SUBLIST_FILTER_APPEND = store_thm ("IS_WEAK_SUBLIST_FILTER_APPEND_EXTEND_LEFT",
  ``!l1a l1b l2a l2b. IS_WEAK_SUBLIST_FILTER l1a l2a ==>
                      IS_WEAK_SUBLIST_FILTER l1b l2b ==>
                      IS_WEAK_SUBLIST_FILTER (l1a ++ l1b) (l2a ++ l2b)``,
cheat);


val IS_WEAK_SUBLIST_FILTER_REFL = store_thm ("IS_WEAK_SUBLIST_FILTER_REFL",
  ``!l. IS_WEAK_SUBLIST_FILTER l l``,
cheat);


val IS_WEAK_SUBLIST_FILTER_TRANS = store_thm ("IS_WEAK_SUBLIST_FILTER_TRANS",
  ``!l1 l2 l3. IS_WEAK_SUBLIST_FILTER l1 l2 ==>
               IS_WEAK_SUBLIST_FILTER l2 l3 ==>
               IS_WEAK_SUBLIST_FILTER l1 l3``,
cheat);


val IS_WEAK_SUBLIST_FILTER_ANTISYM = store_thm ("IS_WEAK_SUBLIST_FILTER_ANTISYM",
  ``!l1 l2. IS_WEAK_SUBLIST_FILTER l1 l2 ==>
            IS_WEAK_SUBLIST_FILTER l2 l1 ==>
            (l1 = l2)``,
cheat);






(**************)
(* Question 2 *)
(**************)

val sh_true_def    = Define `sh_true = T`;
val sh_var_def     = Define `sh_var (v:bool) = v`;
val sh_not_def     = Define `sh_not b = ~b`;
val sh_and_def     = Define `sh_and b1 b2 = (b1 /\ b2)`;
val sh_or_def      = Define `sh_or b1 b2 = (b1 \/ b2)`;
val sh_implies_def = Define `sh_implies b1 b2 = (b1 ==> b2)`;


val _ = Datatype `bvar = BVar num`
val _ = Datatype `prop = d_true | d_var bvar | d_not prop
                       | d_and prop prop | d_or prop prop
                       | d_implies prop prop`;

val _ = Datatype `var_assignment = BAssign (bvar -> bool)`
val VAR_VALUE_def = Define `VAR_VALUE (BAssign a) v = (a v)`

val PROP_SEM_def = Define `
  (PROP_SEM a d_true = T) /\
  (PROP_SEM a (d_var v) = VAR_VALUE a v) /\
  (PROP_SEM a (d_not p) = ~(PROP_SEM a p)) /\
  (PROP_SEM a (d_and p1 p2) = (PROP_SEM a p1 /\ PROP_SEM a p2)) /\
  (PROP_SEM a (d_or p1 p2) = (PROP_SEM a p1 \/ PROP_SEM a p2)) /\
  (PROP_SEM a (d_implies p1 p2) = (PROP_SEM a p1 ==> PROP_SEM a p2))`


(* TODO Work on question 2 *)




(**************)
(* Question 3 *)
(**************)

val expunge_def =
 Define
    `(expunge x []     = [])
 /\  (expunge x (h::t) = if x=h then expunge x t else h::expunge x t)`;

val min_def =
 Define
    `(min [] m = m)
 /\  (min (h::t) m = if m <= h then min t m else min t h)`;

val minsort_defn =
 Hol_defn "minsort"
    `(minsort [] = [])
 /\  (minsort (h::t) =
       let m = min t h
       in
         m::minsort (expunge m (h::t)))`;



(* TODO: prove some auxiliary lemmata and fill in termination proof *)

(* For interactive use

Defn.tgoal minsort_defn

*)

val (minsort_def, minsort_ind) = Defn.tprove (minsort_defn,
  WF_REL_TAC `TODO` >>
  cheat);



val _ = export_theory();
