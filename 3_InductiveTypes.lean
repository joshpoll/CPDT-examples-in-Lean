import mini_crush

namespace hide
-- *Introducing Inductive Types

-- **Proof Terms
#check (fun x : ℕ, x)

#check (fun x : true, x)

#check true.intro

#check (λ _ : false, true.intro)

#check (λ x : false, x)

-- **Enumerations

-- unit
inductive unit : Type
| tt

#check unit
#check unit.tt

theorem unit_singleton_verbose (x : unit) : x = unit.tt :=
by induction x; refl

theorem unit_singleton_concise : ∀ x : unit, x = unit.tt
| unit.tt := rfl

-- TODO: is cases_on like unit_ind?
-- TODO: hovering over #check gives a different type than hovering over the expression itself (which yields the "correct" answer)
#check unit.cases_on

-- empty
inductive empty : Type

-- TODO: cases vs induction?
theorem the_sky_is_falling (x : empty) : 2 + 2 = 5 :=
by cases x

#check empty.cases_on

-- empty to unit
def e2u (e : empty) : unit := match e with end

-- booleans
inductive bool : Type
| true
| false

-- bool negation
def negb : bool → bool
| bool.true  := bool.false
| bool.false := bool.true

-- TODO: negb' ? is there a version of ite that works for any type w/ 2 constructors?

-- proof that negb is its own inverse operation
theorem negb_inverse : ∀ b : bool, negb (negb b) = b
| bool.true  := rfl
| bool.false := rfl

-- proof that negb has no fixpoint
theorem negb_ineq (b : bool) : negb b ≠ b :=
by cases b; contradiction

-- **Simple Recursive Types

-- nat and some functions
inductive nat : Type
| O : nat
| S : nat → nat

def is_zero : nat → bool
| nat.O     := bool.true
| (nat.S _) := bool.false

def pred : nat → nat
| nat.O     := nat.O
| (nat.S n) := n

def plus : nat → nat → nat
| nat.O m     := m
| (nat.S n) m := nat.S (plus n m)

theorem O_plus_n : ∀ n : nat, plus nat.O n = n :=
begin
simp [plus]
end

theorem O_plus_n_crush : ∀ n : nat, plus nat.O n = n :=
by mini_crush

theorem n_plus_O : ∀ n : nat, plus n nat.O = n :=
begin
intro n,
induction n,
{refl},
simp [plus],
rw ih_1
end

theorem n_plus_O_crush : ∀ n : nat, plus n nat.O = n :=
by mini_crush

theorem s_inj : ∀ n m : nat, nat.S n = nat.S m → n = m :=
begin
intros n m succ_eq,
injection succ_eq
end

theorem s_inj_crush : ∀ n m : nat, nat.S n = nat.S m → n = m :=
by mini_crush

inductive nat_list : Type
| NNil  : nat_list
| NCons : nat → nat_list → nat_list

-- length
def nlength : nat_list → nat
| nat_list.NNil         := nat.O
| (nat_list.NCons _ ls) := nat.S (nlength ls)

-- apppend
def napp : nat_list → nat_list → nat_list
| nat_list.NNil          ls2 := ls2
| (nat_list.NCons n ls1) ls2 := nat_list.NCons n (napp ls1 ls2)

-- the length of an appended list made from ls1 and ls2 is the sum of the lengths of ls1 and ls2
theorem nlength_napp : ∀ ls1 ls2 : nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2) :=
begin
intros,
induction ls1; simp [nlength, plus, napp],
rw ih_1
end

theorem nlength_napp_crush : ∀ ls1 ls2 : nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2) :=
by mini_crush

-- binary tree
inductive nat_btree : Type
| NLeaf : nat_btree
| NNode : nat_btree → nat → nat_btree → nat_btree

def nsize : nat_btree → nat
| nat_btree.NLeaf             := nat.S nat.O
| (nat_btree.NNode tr1 _ tr2) := plus (nsize tr1) (nsize tr2)

def nsplice : nat_btree → nat_btree → nat_btree
| nat_btree.NLeaf               tr2 := nat_btree.NNode tr2 nat.O nat_btree.NLeaf
| (nat_btree.NNode tr1' n tr2') tr2 := nat_btree.NNode (nsplice tr1' tr2) n tr2'

theorem plus_assoc : ∀ n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3) :=
begin
intros,
induction n1; simp [plus],
rw ih_1
end

theorem nsize_nsplice : ∀ tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1) :=
begin
intros,
induction tr1; simp [nsize, nsplice],
simp [ih_1, ih_2, plus_assoc]
end

#check nat_btree.cases_on

-- **Parameterized Types
-- TODO: is there a way to remove type annotations nearly everywhere ala CPDT p. 50?

universe variable u

inductive list (α : Type u) : Type u
| Nil {} : list
| Cons   : α → list → list

def length {α : Type u} : list α → nat
| list.Nil        := nat.O
| (list.Cons _ l) := nat.S (length l)

def app {α : Type u} : list α → list α → list α
| list.Nil          ls2 := ls2
| (list.Cons x ls1) ls2 := list.Cons x (app ls1 ls2)

-- nearly identical to nlength_napp
theorem length_app : Π (α : Type u), ∀ ls1 ls2 :
list α, length (app ls1 ls2) = plus (length ls1) (length ls2) :=
begin
intros,
induction ls1; simp [length, plus, app],
rw ih_1
end

theorem length_app_crush : Π (α : Type u), ∀ ls1 ls2 :
list α, length (app ls1 ls2) = plus (length ls1) (length ls2) :=
by mini_crush

-- **Mutually Inductive Types

-- even and odd lists
mutual inductive even_list, odd_list
with even_list : Type
| ENil  : even_list
| ECons : nat → odd_list → even_list
with odd_list : Type
| OCons : nat → even_list → odd_list

mutual def elength, olength
with elength : even_list → nat
| even_list.ENil         := nat.O
| (even_list.ECons _ ol) := nat.S (olength ol)
with olength : odd_list → nat
| (odd_list.OCons _ el) := nat.S (elength el)

mutual def eapp, oapp
with eapp : even_list → even_list → even_list
| even_list.ENil         el2 := el2
| (even_list.ECons n ol) el2 := even_list.ECons n (oapp ol el2)
with oapp : odd_list → even_list → odd_list
| (odd_list.OCons n el') el := odd_list.OCons n (eapp el' el)


-- TODO: come back to this one
theorem elength_eapp : ∀ el1 el2 : even_list,
elength (eapp el1 el2) = plus (elength el1) (elength el2) :=
begin
intros,
induction el1; simp [elength, eapp, plus],
admit
end

-- **Reflexive Types

-- a reflexive type A includes at least one constructor that takes an argument of type B → A

-- subset of predicate logic
inductive pformula : Type
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula → pformula → pformula

-- pformula denotational semantics
def pformulaDenote : pformula → Prop
| pformula.Truth := true
| pformula.Falsehood := false
| (pformula.Conjunction f1 f2) := pformulaDenote f1 ∧ pformulaDenote f2

inductive formula : Type
| Eq : nat → nat → formula
| And : formula → formula → formula
| Forall : (nat → formula) → formula
-- variables implicitly defined using lean functions
-- e.g. ∀ x : nat, x = x is encoded as
example forall_refl : formula := formula.Forall (fun x, formula.Eq x x)

-- formula denotational semantics
def formulaDenote : formula → Prop
| (formula.Eq n1 n2)  := n1 = n2
| (formula.And f1 f2) := formulaDenote f1 ∧ formulaDenote f2
| (formula.Forall f)  := ∀ n : nat, formulaDenote (f n)

-- a trivial formula transformation
def swapper : formula → formula
| (formula.Eq n1 n2)  := formula.Eq n2 n1
| (formula.And f1 f2) := formula.And (swapper f2) (swapper f1)
| (formula.Forall f)  := formula.Forall (fun n, swapper (f n))

theorem swapper_preserves_truth (f : formula) : formulaDenote f → formulaDenote (swapper f) :=
by mini_crush

#check formula.cases_on

/-
inductive term : Type
| App : term → term → term
| Abs : (term → term) → term
open term

def uhoh (t : term) : term
| (Abs f) := f t
| _ := t
-/

-- **An Interlude on Induction Principles

-- TODO: equiv to nat_ind? nat_rect? nat_rec?
#check @nat.rec
#check @nat.cases_on

-- skipping the rest of this section for now

-- **Nested Inductive Types

-- tree with arbitrary finite branching
inductive nat_tree : Type
| NNode' : nat → list nat_tree → nat_tree

#check nat_tree.rec

section All
variable T : Type
variable P : T → Prop

def All : list T → Prop
| list.Nil        := true
| (list.Cons h t) := P h ∧ All t

end All

#print true
#print ∧
#print and

section nat_tree_ind'
variable P : nat_tree → Prop

-- TODO

end nat_tree_ind'

-- TODO: rest of 3.8

-- **Manual Proofs About Constructors

-- todo
theorem true_neq_false : tt ≠ ff :=
begin
change ¬(tt = ff), -- TODO: replace this with something else?
change (tt = ff) → false,
intro H,
admit -- TODO: need a version of ite that takes any type w/ 2 constructors
end

theorem S_inj' : ∀ n m : nat, nat.S n = nat.S m → n = m :=
begin
intros n m H,
change (pred (nat.S n) = pred (nat.S m)),
rw H
end

end hide