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
| attraccess : tm -> string -> tm (*tm and attr name*)
| tt : tm
| ff : tm
  (*should include and because of short circuitng's effects*)
| and : tm -> tm -> tm
| var : string -> tm
| lam : string -> ty -> tm -> tm
| app : tm -> tm -> tm
| ifthenelse : tm -> tm -> tm -> tm
| ifthen : tm -> tm -> tm
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


Inductive equation : Type :=
(*tree reference -> attr name -> equation body*)
| basic_equ : string -> string -> tm -> equation
(*tree reference -> attr name*)
| empty_equ : string -> string -> equation.


(*For identifying trees in evaluation*)
Definition tree_identifier : Type := nat.

Definition trid_eq (n1 n2 : nat) : bool := beq_nat n1 n2.


Inductive value : Type :=
| v_tt : value
| v_ff : value
| v_closure : evalctx -> string -> ty -> tm -> value
| v_return : value -> value
| v_fail : value
| v_tree : tree_identifier -> value
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


Inductive inhsyn : Type :=
| inh : inhsyn
| syn : inhsyn.


Inductive decl : Type :=
(*production name -> top name and type -> child names and types ->
  list of equations*)
| prod : string -> (string * ty) -> list (string * ty) ->
         list equation -> decl
(*attribute name -> attribute type -> inherited or synthesized*)
| attrdecl : string -> ty -> inhsyn -> decl
(*attribute name -> nonterminal name it occurs on*)
| occurson : string -> string -> decl
(*nonterminal name*)
| ntdecl : string -> decl.

Definition grammar : Type := list decl.

(*A context holding the information about things in the grammar.*)
Definition grammarctx : Type := grammar.


(*A context for the nodes in the tree the evaluation is over.*)
Definition treectx : Type :=
  (*this tree, production building it, children, parent of this tree*)
  list (tree_identifier * string * list value * tree_identifier).


Fixpoint build_evalctx (sig : list (string * ty))
         (children : list value) : evalctx :=
  match sig, children with
  | nil, _ => emptyeval
  | _, nil => emptyeval
  | (name, ty)::sig', tid::children' =>
    addeval name tid (build_evalctx sig' children')
  end.

Fixpoint find_eq (eqs : list equation) (tree : string)
         (attr : string) : option equation :=
  match eqs with
  | nil => None
  | (basic_equ tr a tm)::eqs' =>
    if string_dec tr tree
    then if string_dec a attr
         then Some (basic_equ tr a tm)
         else find_eq eqs' tree attr
    else find_eq eqs' tree attr
  | (empty_equ tr a)::eqs' =>
    if string_dec tr tree
    then if string_dec a attr
         then Some (empty_equ tr a)
         else find_eq eqs' tree attr
    else find_eq eqs' tree attr
  end.

Fixpoint find_prod (GC : grammarctx) (pname : string) :
         (*(top, top ty), child names and types, equations*)
  option ((string * ty) * list (string * ty) * list equation) :=
  match GC with
  | nil => None
  | (prod name top children eqs)::GC' =>
    if string_dec name pname
    then Some (top, children, eqs)
    else find_prod GC' pname
  | d::GC' => find_prod GC' pname
  end.

(*Find the production that built a tree and its children's identifiers*)
Fixpoint find_tree (tc : treectx) (tr : tree_identifier) :
  option (string * list value * tree_identifier) :=
  match tc with
  | nil => None
  | (tid, p, c, pid)::tc' => if trid_eq tid tr
                             then Some (p, c, pid)
                             else find_tree tc' tr
  end.

Fixpoint attr_ty (GC : grammarctx) (a : string) :
  option (ty * inhsyn) :=
  match GC with
  | nil => None
  | (attrdecl aname t inh_or_not)::GC' =>
    if string_dec aname a
    then Some (t, inh_or_not)
    else attr_ty GC' a
  | d::GC' => attr_ty GC' a
  end.

Fixpoint find_id_name (sig : list (string * ty))
         (children : list value) (id : tree_identifier) :
  option string :=
  match sig, children with
  | nil, _ => None
  | _, nil => None
  | (name, ty)::sig', (v_tree tid)::children' =>
    if trid_eq tid id
    then Some name
    else find_id_name sig' children' id
  | (name, ty)::sig', v::children' =>
    find_id_name sig' children' id
  end.


Inductive basic_eval :
  treectx -> grammarctx -> evalctx -> tm -> value -> Prop :=
| BE_SynAttr :
    forall TC GC G t a aty trid prod chil parentid top ty
           ch eqs e G' v,
      basic_eval TC GC G t (v_tree trid) ->
      (*look up attribute to find inherited or synthesized*)
      attr_ty GC a = Some (aty, syn) ->
      (*look up tree to get prod name and child ID's*)
      find_tree TC trid = Some (prod, chil, parentid) ->
      (*look up prod to get equations and production signature*)
      find_prod GC prod = Some ((top, ty), ch, eqs) ->
      (*get the equation*)
      find_eq eqs top a = Some e ->
      (*build a ctx based on the production*)
      build_evalctx ((top, ty)::ch) ((v_tree trid)::chil) = G' ->
      (*evaluate the equation*)
      basic_eval_equation TC GC G' e v ->
      basic_eval TC GC G (attraccess t a) v
| BE_InhAttr :
    forall TC GC G t a trid cprod cchil parentid prod chil pparentid
           top ty ch eqs e aty trname G' v,
      basic_eval TC GC G t (v_tree trid) ->
      (*look up attribute to find inherited or synthesized*)
      attr_ty GC a = Some (aty, inh) ->
      (*look up tree to get parent*)
      find_tree TC trid = Some (cprod, cchil, parentid) ->
      (*look up parent to get prod and child ID's*)
      find_tree TC parentid = Some (prod, chil, pparentid) ->
      (*look up prod to get equations and production signature*)
      find_prod GC prod = Some ((top, ty), ch, eqs) ->
      (*look up the name for the current tree in this production*)
      find_id_name ch chil trid = Some trname ->
      (*get the equation*)
      find_eq eqs trname a = Some e ->
      (*build a ctx based on the production*)
      build_evalctx ((top, ty)::ch) ((v_tree parentid)::chil) = G' ->
      (*evaluate the equation*)
      basic_eval_equation TC GC G' e v ->
      basic_eval TC GC G (attraccess t a) v
| BE_TT : forall TC GC G, basic_eval TC GC G tt v_tt
| BE_FF : forall TC GC G, basic_eval TC GC G ff v_ff
| BE_And_TT : forall TC GC G t1 t2,
    basic_eval TC GC G t1 v_tt -> basic_eval TC GC G t2 v_tt ->
    basic_eval TC GC G (and t1 t2) v_tt
| BE_And_FF1 : forall TC GC G t1 t2,
    basic_eval TC GC G t1 v_ff -> basic_eval TC GC G (and t1 t2) v_ff
| BE_And_FF2 : forall TC GC G t1 t2,
    basic_eval TC GC G t1 v_tt -> basic_eval TC GC G t2 v_ff ->
    basic_eval TC GC G (and t1 t2) v_ff
| BE_Var : forall TC GC G x v,
    lookup G x v -> basic_eval TC GC G (var x) v
| BE_Lam : forall TC GC G x ty t,
    basic_eval TC GC G (lam x ty t) (v_closure G x ty t)
| BE_App : forall TC GC G t1 t2 cG x ty t v2 v,
    basic_eval TC GC G t1 (v_closure cG x ty t) ->
    basic_eval TC GC G t2 v2 ->
    basic_eval TC GC (addeval x v2 cG) t v ->
    basic_eval TC GC G (app t1 t2) v
| BE_IfThenElse_TT : forall TC GC G c t1 t2 v,
    basic_eval TC GC G c v_tt -> basic_eval TC GC G t1 v ->
    basic_eval TC GC G (ifthenelse c t1 t2) v
| BE_IfThenElse_FF : forall TC GC G c t1 t2 v,
    basic_eval TC GC G c v_ff -> basic_eval TC GC G t2 v ->
    basic_eval TC GC G (ifthenelse c t1 t2) v
| BE_Return : forall TC GC G t v,
    basic_eval TC GC G t v ->
    basic_eval TC GC G (mreturn t) (v_return v)
| BE_Fail : forall TC GC G s,
    basic_eval TC GC G (mfail s) v_fail
| BE_Bind_Return : forall TC GC G t1 t2 v cG x ty t vfinal,
    basic_eval TC GC G t1 (v_return v) ->
    basic_eval TC GC G t2 (v_closure cG x ty t) ->
    basic_eval TC GC (addeval x v cG) t vfinal ->
    basic_eval TC GC G (mbind t1 t2) vfinal
| BE_Bind_Fail : forall TC GC G t1 t2,
    basic_eval TC GC G t1 v_fail ->
    basic_eval TC GC G (mbind t1 t2) v_fail
| BE_MZero : forall TC GC G, basic_eval TC GC G mzero v_fail
| BE_MPlus_Return : forall TC GC G t1 t2 v,
    basic_eval TC GC G t1 (v_return v) ->
    basic_eval TC GC G (mplus t1 t2) (v_return v)
| BE_MPlus_Fail : forall TC GC G t1 t2 v2,
    basic_eval TC GC G t1 v_fail -> basic_eval TC GC G t2 v2 ->
    basic_eval TC GC G (mplus t1 t2) v2
| BE_Let : forall TC GC G x ty t1 t2 v1 v2,
    basic_eval TC GC G t1 v1 ->
    basic_eval TC GC (addeval x v1 G) t2 v2 ->
    basic_eval TC GC G (letexpr x ty t1 t2) v2
| BE_Case : forall TC GC G t cs vt v,
    basic_eval TC GC G t vt -> basic_eval_cs TC GC G cs vt v ->
    basic_eval TC GC G (caseexpr t cs) v

with basic_eval_cs : treectx -> grammarctx -> evalctx -> clauses ->
                     value -> value -> Prop :=
| BE_CS_Single_Match : forall TC GC G p t vm v,
    matchpatt p vm -> basic_eval TC GC G t v ->
    basic_eval_cs TC GC G (singleclause p t) vm v
| BE_CS_Add_NoMatch : forall TC GC G p t cs vm v,
    ~(matchpatt p vm) -> basic_eval_cs TC GC G cs vm v ->
    basic_eval_cs TC GC G (addclause p t cs) vm v
| BE_CS_Add_Match : forall TC GC G p t cs vm v,
    matchpatt p vm -> basic_eval TC GC G t v ->
    basic_eval_cs TC GC G (addclause p t cs) vm v

with basic_eval_equation : treectx -> grammarctx -> evalctx ->
                           equation -> value -> Prop :=
| BEEQ_Basic : forall TC GC G tr a body v,
    basic_eval TC GC G body v ->
    basic_eval_equation TC GC G (basic_equ tr a body) v.

Scheme beval_mut_ind := Induction for basic_eval Sort Prop
  with beval_cs_mut_ind := Induction for basic_eval_cs Sort Prop
  with beval_eq_mut_ind := Induction for basic_eval_equation Sort Prop.

Combined Scheme beval_combined_mut_ind from beval_mut_ind,
beval_cs_mut_ind, beval_eq_mut_ind.

Definition beval_unique TC GC G t v1
         (be1 : basic_eval TC GC G t v1) :=
  forall v2, basic_eval TC GC G t v2 -> v1 = v2.
Definition beval_cs_unique TC GC G cs vm v1
         (be1 : basic_eval_cs TC GC G cs vm v1) :=
  forall v2, basic_eval_cs TC GC G cs vm v2 -> v1 = v2.
Definition beval_eq_unique TC GC G eq v1
         (be1 : basic_eval_equation TC GC G eq v1) :=
  forall v2, basic_eval_equation TC GC G eq v2 -> v1 = v2.

Theorem basic_eval_unique_mut :
  (forall TC GC G t v1 be1,
      beval_unique TC GC G t v1 be1) /\
  (forall TC GC G cs vm v1 be1,
      beval_cs_unique TC GC G cs vm v1 be1) /\
  (forall TC GC G eq v1 be1,
      beval_eq_unique TC GC G eq v1 be1).
Proof.
  apply beval_combined_mut_ind; intros TC GC G.
  (*attr*)
  - intros t a aty trid prod chil parentid top topty ch eqs e G' v'.
    intros betree IHbetree H0 H1 H2 H3 H4 beeq IHbeeq.
    unfold beval_unique. intros v2 be2. inversion be2.
    + unfold beval_unique in IHbetree.
      unfold beval_eq_unique in IHbeeq.
      apply IHbetree in H6.
      injection H6. rewrite H0 in H7. injection H7. intros.
      subst G'. subst G'0. subst. rewrite H1 in H8. injection H8.
      intros. subst. rewrite H2 in H9. injection H9. intros. subst.
      rewrite H3 in H10. injection H10. intros. subst.
      apply IHbeeq in H16. assumption.
    + rewrite H0 in H7. injection H7. intros. discriminate H19.
  - intros t a trid cprod cchil parentid prod chil pparentid top.
    intros topty ch eqs e aty trname G' v betree IHbetree.
    intros H0 H1 H2 H3 H4 H5 H6 beeq IHbeeq.
    unfold beval_unique. intros v2 be2. inversion be2.
    + rewrite H0 in H9. injection H9. intros. inversion H19.
    + unfold beval_unique in IHbetree.
      unfold beval_eq_unique in IHbeeq. subst G'. subst G'0.
      apply IHbetree in H8. injection H8. rewrite H0 in H9.
      injection H9. intros. subst. rewrite H1 in H10. injection H10.
      intros. subst. rewrite H2 in H11. injection H11. intros. subst.
      rewrite H3 in H12. injection H12. intros. subst.
      rewrite H4 in H13. injection H13. intros. subst.
      rewrite H5 in H14. injection H14. intros. subst.
      apply IHbeeq in H20. assumption.
  (*true, false*)
  - unfold beval_unique. intros v2 be2. inversion be2. reflexivity.
  - unfold beval_unique. intros v2 be2. inversion be2. reflexivity.
  (*and*)
  - unfold beval_unique. intros t1 t2 bet1 IHt1 bet2 IHt2 v2 be2.
    inversion be2.
    + reflexivity.
    + apply IHt1 in H5. assumption.
    + apply IHt2 in H6. assumption.
  - unfold beval_unique. intros t1 t2 bet1 IHt1 v2 be2. inversion be2.
    + apply IHt1 in H4. assumption.
    + reflexivity.
    + reflexivity.
  - unfold beval_unique. intros t1 t2 bet1 IHt1 bet2 IHt2 v2 be2.
    inversion be2.
    + apply IHt2 in H6. assumption.
    + reflexivity.
    + reflexivity.
  (*var*)
  - unfold beval_unique. intros x v lkp v2 be2. inversion be2. subst.
    apply lookup_unique with G x; assumption.
  (*lam*)
  - unfold beval_unique. intros x xty t v2 be2. inversion be2.
    reflexivity.
  (*app*)
  - unfold beval_unique. intros t1 t2 cG x xty t vt2 v bet1 IHt1.
    intros bet2 IHt2 bebody IHbody v2 be2. inversion be2.
    apply IHt1 in H1. injection H1. intros. subst.
    apply IHt2 in H5. subst.
    apply IHbody in H7. assumption.
  (*if-then-else*)
  - unfold beval_unique. intros c t1 t2 v bec IHc be1 IH1 v2 be2.
    inversion be2.
    + apply IH1 in H7. assumption.
    + apply IHc in H6. discriminate H6.
  - unfold beval_unique. intros c t1 t2 v bec IHc bet2 IH2 v2 be2.
    inversion be2.
    + apply IHc in H6. discriminate H6.
    + apply IH2 in H7. assumption.
  (*return, fail*)
  - unfold beval_unique. intros t v be IHbe v2 be2. inversion be2.
    apply IHbe in H3. subst. reflexivity.
  - unfold beval_unique. intros s v2 be2. inversion be2. reflexivity.
  (*bind*)
  - unfold beval_unique. intros t1 t2 v cG x xty t vfinal.
    intros bet1 IHt1 bet2 IHt2 bebody IHbody v2 be2. inversion be2.
    + apply IHt1 in H1. injection H1. intros. subst.
      apply IHt2 in H5. injection H5. intros. subst.
      apply IHbody in H7. assumption.
    + apply IHt1 in H5. discriminate H5.
  - unfold beval_unique. intros t1 t2 bet1 IHt1 v2 be2. inversion be2.
    + apply IHt1 in H1. discriminate H1.
    + reflexivity.
  (*mzero, mplus*)
  - unfold beval_unique. intros v2 be2. inversion be2. reflexivity.
  - unfold beval_unique. intros t1 t2 v bet1 IHt1 v2 be2.
    inversion be2.
    + apply IHt1 in H5. assumption.
    + apply IHt1 in H4. discriminate H4.
  - unfold beval_unique. intros t1 t2 vt2 bet1 IHt1 bet2 IHt2 v2 be2.
    inversion be2.
    + apply IHt1 in H5. discriminate H5.
    + apply IHt2 in H6. assumption.
  (*let*)
  - unfold beval_unique. intros x xty t1 t2 vt1 vt2 bet1 IHt1.
    intros bet2 IHt2 v2 be2. inversion be2.
    apply IHt1 in H7. subst. apply IHt2 in H8. assumption.
  (*case*)
  - unfold beval_unique. unfold beval_cs_unique.
    intros t cs vt v bet IHt becs IHcs v2 be2. inversion be2.
    apply IHt in H4. subst. apply IHcs in H6. assumption.
  (*clauses*)
  - unfold beval_unique. unfold beval_cs_unique.
    intros p t vm v m bet IHt v2 be2. inversion be2. apply IHt in H7.
    assumption.
  - unfold beval_cs_unique. intros p t cs vm v nm becs IHcs v2 be2.
    inversion be2.
    + apply IHcs in H8. assumption.
    + exfalso. apply nm. assumption.
  - unfold beval_cs_unique. unfold beval_unique.
    intros p t cs vm v m bet IHt v2 be2. inversion be2.
    + exfalso. apply H7. assumption.
    + apply IHt in H8. assumption.
  (*equation*)
  - unfold beval_unique. unfold beval_eq_unique.
    intros tr a body v bebody IHbody v2 be2. inversion be2.
    apply IHbody in H6. assumption.
Time Qed.


Theorem basic_eval_unique : forall TC GC G t v1 v2,
    basic_eval TC GC G t v1 -> basic_eval TC GC G t v2 -> v1 = v2.
Proof.
  destruct basic_eval_unique_mut as [bet [becs beeq]].
  unfold beval_unique in bet. intros.
  apply bet with TC GC G t; assumption.
Qed.

Theorem basic_eval_cs_unique : forall TC GC G cs vm v1 v2,
    basic_eval_cs TC GC G cs vm v1 ->
    basic_eval_cs TC GC G cs vm v2 -> v1 = v2.
Proof.
  destruct basic_eval_unique_mut as [bet [becs beeq]].
  unfold beval_cs_unique in becs. intros.
  apply becs with TC GC G cs vm; assumption.
Qed.

Theorem basic_eval_equation_unique : forall TC GC G eq v1 v2,
    basic_eval_equation TC GC G eq v1 ->
    basic_eval_equation TC GC G eq v2 -> v1 = v2.
Proof.
  destruct basic_eval_unique_mut as [bet [becs beeq]].
  unfold beval_eq_unique in beeq. intros.
  apply beeq with TC GC G eq; assumption.
Qed.

