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

