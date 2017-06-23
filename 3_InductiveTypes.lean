namespace hide
-- *Introducing Inductive Types

-- *Proof Terms
#check (fun x : ℕ, x)

#check (fun x : true, x)

-- TODO: how to write I?
-- *Enumerations

-- unit
inductive unit : Type
| tt

#check unit
#check unit.tt

theorem unit_singleton_verbose : ∀ x : unit, x = unit.tt :=
begin
intro x,
induction x,
refl
end

theorem unit_singleton_concise : ∀ x : unit, x = unit.tt
| unit.tt := rfl

-- TODO: is cases_on like unit_ind?
#check unit.cases_on

-- empty
inductive empty : Type

-- TODO: Is this the right way to write this?
-- TODO: cases vs induction?
theorem the_sky_is_falling : ∀ x : empty, 2 + 2 = 5 :=
begin
intro x,
induction x
end

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

-- TODO: negb' ?

-- proof that negb is its own inverse operation
theorem negb_inverse : ∀ b : bool, negb (negb b) = b
| bool.true  := rfl
| bool.false := rfl

-- proof that negb has no fixpoint
-- TODO: prove!
theorem negb_ineq : ∀ b : bool, negb b ≠ b := sorry

-- *Simple Recursive Types

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

theorem n_plus_O : ∀ n : nat, plus n nat.O = n :=
begin
intro n,
induction n,
{refl},
simp [plus],
rw ih_1
end

theorem s_inj : ∀ n m : nat, nat.S n = nat.S m → n = m :=
begin
intros n m succ_eq,
injection succ_eq
end

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

-- *Parameterized Types
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

-- *Mutually Inductive Types

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
end

-- *Reflexive Types

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

-- TODO?
theorem Eq_refl : ∀ n1 n2, formula.Eq n1 n2 = formula.Eq n2 n1 := sorry

/-
theorem swapper_preserves_truth : ∀ f, formulaDenote f → formulaDenote (swapper f) :=
begin
intros,
induction f,
-- TODO:
end

inductive term : Type
| App : term → term → term
| Abs : (term → term) → term-/

-- *An Interlude on Induction Principles

-- equiv to nat_ind? nat_rect? nat_rec?
#check nat.cases_on

-- *Nested Inductive Types

-- tree with arbitrary finite branching
inductive nat_tree : Type
| NNode' : nat → list nat_tree → nat_tree

#check nat_tree.cases_on

-- TODO: rest of chapter

#print _root_.list.rec

protected eliminator list.rec :
Π {T : Type u} {C : list T → Sort l},
  C list.nil →
  (Π (a : T) (a_1 : list T), C a_1 → C (a :: a_1)) →
   Π (n : list T), C n

end hide
