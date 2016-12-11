import init.meta.tactic

inductive type
| base : string -> type
| arrow : type -> type -> type

inductive term
| const : type -> term
| var : string -> term
| abstraction : string -> type -> term -> term
| apply : term -> term -> term

@[reducible] def context :=
  list (string × type)

def lookup : context -> string -> option type
| [] _ := none
| ((n, t) :: delta) n' :=
  if n = n'
  then some t
  else none

inductive typed : context -> term -> type -> Prop
| well_typed_var :
  forall ctxt n t,
    lookup ctxt n = some t ->
    typed ctxt (term.var n) t
| well_typed_const :
  forall ctxt T,
    typed ctxt (term.const T) T
| well_typed_abs :
  forall ctxt n tA tB body,
    typed ((n, tA) :: ctxt) body tB ->
    typed ctxt (term.abstraction n tA body) (type.arrow tA tB)
| well_typed_apply :
  forall ctxt f arg tA tB,
    typed ctxt f (type.arrow tA tB) ->
    typed ctxt arg tA ->
    typed ctxt (term.apply f arg) tB

inductive value : term -> Prop

inductive subst : term → term → string → term → Prop
| const : forall T e x, subst (term.const T) e x (term.const T)
| var_equal :
  forall x e,
    subst (term.var x) e x e
| var_else :
  forall x x' e,
    not (x = x') ->
    subst (term.var x) e x' (term.var x)
| abs_equal :
  forall x t e body,
    subst (term.abstraction x t body) e x (term.abstraction x t body)
| abs_else :
  forall x x' t e body body',
    not (x = x') ->
    subst body e x' body' ->
    subst (term.abstraction x t body) e x' (term.abstraction x t body')
| app : forall x e f f' g g',
  subst f e x f' ->
  subst g e x g' ->
  subst (term.apply f g) e x (term.apply f' g')

lemma subst_deterministic :
  ∀ e1 e2 x e3,
  subst e1 e2 x e3 ->
    ∀ e3',
    subst e1 e2 x e3' ->
    e3 = e3' :=
begin
  intro,
  induction e1,
    intros,
    cases a_1,
    cases a_2,
    reflexivity,

    intros,
    rename a s,
    cases a_1,
    cases a_2,
    reflexivity,
    cases a_1,
    rename a b,
    exfalso,
    unfold not at b,
    apply b,
    reflexivity,
    reflexivity,
    cases a_2,
    rename a b,
    unfold not at b,
    exfalso,
    apply b,
    reflexivity,
    reflexivity,

    intros,
    rename a_1 b,
    cases b,
    cases a_2,
    reflexivity,
    rename a b,
    rename a d,
    exfalso,
    apply b,
    reflexivity,
    cases a_2,
    rename a b,
    rename a d,
    exfalso,
    apply d,
    reflexivity,
    rename a b,
    rename a d,
    rename a d,
    pose Y := ih_1 _ _ _ d _ b,
    rewrite Y,

    intros,
    cases a_1,
    cases a_2,
    rename a b,
    rename a c,
    rename a d,
    pose x := ih_1 _ _ _ a _ c,
    pose x' := ih_2 _ _ _ d _ b,
    rewrite [x, x'],
end

meta def tactic.interactive.destruct : pexpr → tactic unit
| e := do
  tactic.refine `(dite %%e _ _),
  -- I think I want something like semicolon instead of
  -- all_goals
  tactic.all_goals (tactic.intros >> return ())

lemma can_subst :
  forall e1 e2 x,
    exists e3, subst e1 e2 x e3 :=
 begin
   intros,
   induction e1,
   constructor,
   constructor,
   -- this use of refine is actually dope, 
   destruct `(x = a),
   -- tactic.all_goals tactic.constructor,
   constructor,
   rewrite a_1,
   constructor,
   constructor,
   constructor,
   unfold not at a_1,
   unfold not,
   intros,
   apply a_1,
   subst a_2,
   cases ih_1,
   rename a b,
   rename a c,
   rename a d,
   rename a e,
   destruct `(a = x),
   constructor,
   rewrite a_1,
   tactic.refine `(subst.abs_equal _ _ _ _),
   constructor,
   constructor,
   exact a_1,
   exact b,
   cases ih_1,
   cases ih_2,
   constructor,
   constructor,
   rename a b,
   rename a c,
   rename a d,
   rename a e,
   rename a f,
   exact d,
   rename a b,
   rename a c,
   rename a d,
   rename a e,
   rename a f,
   exact b,
end

inductive free : term → string → Prop
| var :
  forall x, free (term.var x) x
| app_l :
  forall x e1 e2,
    free e1 x ->
    free (term.apply e1 e2) x
| app_r :
  forall x e1 e2,
    free e2 x →
    free (term.apply e1 e2) x
| abstraction :
  forall x1 t x2 e,
    not (x1 = x2) ->
    free e x1 ->
    free (term.abstraction x2 t e) x1

lemma freething :
  forall body x x' t,
    not (x' = x) ->
    ¬ (free (term.abstraction x t body) x') ->
    ¬ (free body x') :=
begin
  intros,
  unfold not at a_1,
  unfold not,
  intros,
  apply a_1,
  constructor,
  exact a,
  exact a_2,
end

lemma subst_only_free :
  forall e1 e2 x e3,
    subst e1 e2 x e3 →
    not (free e1 x) →
    e1 = e3 :=
begin
  intro,
  induction e1,
  tactic.all_goals (tactic.intros >> return ()),
  cases a_1,
  reflexivity,
  cases a_1,
  exfalso,
  apply a_2,
  constructor,
  trivial,
  cases a_1,
  trivial,
  assert P : body = body',
  apply ih_1,
  exact a,
  apply freething,
  rename a b,
  unfold not at a,
  unfold not, intros,
  apply a,
  rewrite a_3,
  exact a_2,
  rewrite P,
  cases a_1,
  assert IHEq : f = f',
  apply ih_1,
  rename a b,
  exact a,
  unfold not at a_2,
  unfold not, intros,
  apply a_2,
  apply free.app_l,
  exact a_3,
  assert IHeq2 : g = g',
  apply ih_2,
  exact a,
  unfold not at a_2,
  unfold not,
  intros, apply a_2,
  apply free.app_r,
  exact a_3,
  rewrite [IHEq, IHeq2],
end

def closed (t : term) : Prop :=
  forall x, not $ free t x

lemma closed_app_intro :
  forall e1 e2,
    closed e1 →
    closed e2 →
    closed (term.apply e1 e2) :=
 begin
   intros,
   unfold closed,
   unfold not,
   intros,
   cases a_2,
   unfold closed at a,
   apply a,
   rename a b,
   exact a,
   unfold closed at a_1,
   apply a_1,
   rename a b,
   exact a,
 end

lemma closed_app_inv :
  forall e1 e2,
    closed (term.apply e1 e2) →
    closed e1 ∧ closed e2 :=
 begin
   intros,
   unfold closed at a,
   unfold not at a,
   unfold closed,
   unfold not,
   split, tactic.all_goals (tactic.intros >> return ()),
   apply a,
   apply free.app_l,
   exact a_1,
   apply a,
   apply free.app_r,
   apply a_1,
 end

lemma closed_lam_intro :
  forall x t e,
    (forall y, not (y = x) -> not (free e y)) →
    closed (term.abstraction x t e) :=
begin
  unfold closed,
  unfold not,
  intros,
  cases a_1,
  rename a b,
  rename a c,
  rename a d,
  pose P := b _ d c,
  exact P
end

check subst.var_equal

-- lemma subst_preserves_closed (e1 e2 : term) (x : string) (e3 : term) :
--     subst e1 e2 x e3 ->
--     closed e1 ->
--     closed e2 ->
--     closed e3
-- | (subst.var_equal s _) cl1 cl2 := sorry
-- | _ := sorry
