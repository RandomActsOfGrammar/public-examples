Require Import List.
Require Import Coq.Arith.Arith.
From Coq Require Import Strings.String.
Open Scope string_scope.
Require Export Strings.String.


Inductive ty : Type :=
| Bool : ty
| Arrow : ty -> ty -> ty
| Monad : ty -> ty
| NT : string -> ty.


(*We treat multiple-argument functions as taking single arguments--the end
  effect is the same, but the implementation here is easier.*)
Inductive tm : Type :=
| tt : tm
| ff : tm
  (*should include and because of short circuitng's effects*)
| and : tm -> tm -> tm
| var : string -> tm
| lam : string -> ty -> tm -> tm
| app : tm -> tm -> tm
| ifthenelse : tm -> tm -> tm -> tm
| mreturn : tm -> tm
| mfail : string -> tm (*use a string as a "generic" argument*)
| mbind : tm -> tm -> tm
| mzero : tm
| mplus : tm -> tm -> tm
| letexpr : string -> ty -> tm -> tm -> tm
| caseexpr : tm -> clauses -> tm
| mcase : tm -> clauses -> tm

with clauses : Type :=
| singleclause : patt -> tm -> clauses
| addclause : patt -> tm -> clauses -> clauses

(*It's fine to ignore pattern-matching bindings because they don't add
  anything interesting to monadification.  Any name bound by matching
  will have a set type under our scheme.  If it is a monad type, it
  may be used monadically within the particular clause, and the
  binding may be treated in the same manner as a let.*)
with patt : Type :=
| allpatt : patt
| otherpatt : ty -> patt.


(*For identifying trees in evaluation*)
Definition tree_identifier : Type := nat.


Inductive value : Type :=
| v_tt : value
| v_ff : value
| v_closure : evalctx -> string -> ty -> tm -> value
| v_return : value -> value
| v_fail : value
(*Evaluation contexts holding results for other names.  If we want, we
  can pretend we are working in an AG that pushes all attributes down
  and pulls all attributes up as you go, and that attribute accesses
  can only be done directly, so they can be treated as vars (e.g. var
  "t.a"), in which case this also holds the results for other
  attributes.*)
with evalctx : Type :=
| emptyeval : evalctx
| addeval : string -> value -> evalctx -> evalctx.


(*Look up a value in an evaluation context.*)
Inductive lookup : evalctx -> string -> value -> Prop :=
| LKP_Here : forall x v rest,
    lookup (addeval x v rest) x v
| LKP_Later : forall y v rest x vx,
    lookup rest x vx -> x <> y ->
    lookup (addeval y v rest) x vx.
Theorem lookup_unique : forall G x v1 v2,
    lookup G x v1 -> lookup G x v2 -> v1 = v2.
Proof.
  intros G x v1 v2 lkp1. induction lkp1; intros lkp2; inversion lkp2.
  - auto.
  - contradiction.
  - symmetry in H0. contradiction.
  - auto.
Qed.


(*Whether a value matches a pattern.*)
Inductive matchpatt : patt -> value -> Prop := .


Inductive basic_eval : evalctx -> tm -> value -> Prop :=
| BE_TT : forall G, basic_eval G tt v_tt
| BE_FF : forall G, basic_eval G ff v_ff
| BE_And_TT : forall G t1 t2,
    basic_eval G t1 v_tt -> basic_eval G t2 v_tt ->
    basic_eval G (and t1 t2) v_tt
| BE_And_FF1 : forall G t1 t2,
    basic_eval G t1 v_ff -> basic_eval G (and t1 t2) v_ff
| BE_And_FF2 : forall G t1 t2,
    basic_eval G t1 v_tt -> basic_eval G t2 v_ff ->
    basic_eval G (and t1 t2) v_ff
| BE_Var : forall G x v,
    lookup G x v -> basic_eval G (var x) v
| BE_Lam : forall G x ty t,
    basic_eval G (lam x ty t) (v_closure G x ty t)
| BE_App : forall G t1 t2 cG x ty t v2 v,
    basic_eval G t1 (v_closure cG x ty t) ->
    basic_eval G t2 v2 ->
    basic_eval (addeval x v2 cG) t v ->
    basic_eval G (app t1 t2) v
| BE_IfThenElse_TT : forall G c t1 t2 v,
    basic_eval G c v_tt -> basic_eval G t1 v ->
    basic_eval G (ifthenelse c t1 t2) v
| BE_IfThenElse_FF : forall G c t1 t2 v,
    basic_eval G c v_ff -> basic_eval G t2 v ->
    basic_eval G (ifthenelse c t1 t2) v
| BE_Return : forall G t v,
    basic_eval G t v ->
    basic_eval G (mreturn t) (v_return v)
| BE_Fail : forall G s,
    basic_eval G (mfail s) v_fail
| BE_Bind_Return : forall G t1 t2 v cG x ty t vfinal,
    basic_eval G t1 (v_return v) ->
    basic_eval G t2 (v_closure cG x ty t) ->
    basic_eval (addeval x v cG) t vfinal ->
    basic_eval G (mbind t1 t2) vfinal
| BE_Bind_Fail : forall G t1 t2,
    basic_eval G t1 v_fail ->
    basic_eval G (mbind t1 t2) v_fail
| BE_MZero : forall G, basic_eval G mzero v_fail
| BE_MPlus_Return : forall G t1 t2 v,
    basic_eval G t1 (v_return v) ->
    basic_eval G (mplus t1 t2) (v_return v)
| BE_MPlus_Fail : forall G t1 t2 v2,
    basic_eval G t1 v_fail -> basic_eval G t2 v2 ->
    basic_eval G (mplus t1 t2) v2
| BE_Let : forall G x ty t1 t2 v1 v2,
    basic_eval G t1 v1 ->
    basic_eval (addeval x v1 G) t2 v2 ->
    basic_eval G (letexpr x ty t1 t2) v2
| BE_Case : forall G t cs vt v,
    basic_eval G t vt -> basic_eval_cs G cs vt v ->
    basic_eval G (caseexpr t cs) v

with basic_eval_cs : evalctx -> clauses -> value -> value -> Prop :=
| BE_CS_Single_Match : forall G p t vm v,
    matchpatt p vm -> basic_eval G t v ->
    basic_eval_cs G (singleclause p t) vm v
| BE_CS_Add_NoMatch : forall G p t cs vm v,
    ~(matchpatt p vm) -> basic_eval_cs G cs vm v ->
    basic_eval_cs G (addclause p t cs) vm v
| BE_CS_Add_Match : forall G p t cs vm v,
    matchpatt p vm -> basic_eval G t v ->
    basic_eval_cs G (addclause p t cs) vm v.


Theorem basic_eval_unique : forall G t v1 v2,
    basic_eval G t v1 -> basic_eval G t v2 -> v1 = v2
with basic_eval_cs_unique : forall G cs vm v1 v2,
    basic_eval_cs G cs vm v1 ->
    basic_eval_cs G cs vm v2 -> v1 = v2.
Proof.
{
  intros G t ve1 ve2 be1 be2. generalize dependent ve2.
  induction be1; intros ve2 be2; inversion be2.
  (*true*)
  - reflexivity.
  (*false*)
  - reflexivity.
  (*and*)
  - reflexivity.
  - apply IHbe1_1 in H3. discriminate H3.
  - apply IHbe1_2 in H4. discriminate H4.
  - apply IHbe1 in H2. discriminate H2.
  - reflexivity.
  - reflexivity.
  - apply IHbe1_2 in H4. discriminate H4.
  - reflexivity.
  - reflexivity.
  (*var*)
  - apply lookup_unique with G x; auto.
  (*abs*)
  - reflexivity.
  (*app*)
  - apply IHbe1_1 in H1. inversion H1.
    apply IHbe1_2 in H3. inversion H3.
    apply IHbe1_3. rewrite H8, H6, H7, H10. apply H5.
  (*if-then-else*)
  - apply IHbe1_2. assumption.
  - apply IHbe1_1 in H4. inversion H4.
  - apply IHbe1_1 in H4. inversion H4.
  - apply IHbe1_2. assumption.
  (*return*)
  - apply IHbe1 in H1. rewrite H1. reflexivity.
  (*fail*)
  - reflexivity.
  (*bind*)
  - apply IHbe1_1 in H1. inversion H1.
    apply IHbe1_2 in H3. inversion H3.
    apply IHbe1_3. rewrite H9, H7, H8, H11. apply H5.
  - apply IHbe1_1 in H3. inversion H3.
  - apply IHbe1 in H1. inversion H1.
  - reflexivity.
  (*mzero*)
  - reflexivity.
  (*mplus*)
  - apply IHbe1. assumption.
  - apply IHbe1 in H2. inversion H2.
  - apply IHbe1_1 in H3. inversion H3.
  - apply IHbe1_2. assumption.
  (*let*)
  - apply IHbe1_1 in H5. rewrite <- H5 in H6. apply IHbe1_2; auto.
  (*case*)
  - apply IHbe1 in H3.
    apply basic_eval_cs_unique with G cs vt; auto.
    rewrite H3. apply H5.
}
{
  intros G cs vm v1 v2 be1 be2. generalize dependent v2.
  induction be1; intros v2 be2; inversion be2.
  - apply basic_eval_unique with G t; auto.
  - apply IHbe1; auto.
  - exfalso. apply H. assumption.
  - exfalso. apply H7. assumption.
  - apply basic_eval_unique with G t; auto.
}
Qed.

