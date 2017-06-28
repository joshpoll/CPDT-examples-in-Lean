import mini_crush

namespace hide
-- *Inductive Predicates

#print unit
#print true

-- term T : Type is a type of programs
-- it is inhabited by programs
-- term T : Prop is a logical proposition
-- it is inhabited by proofs

-- there *is* a difference between programming and proving in practice

-- proof irrelevance
-- to an engineer: not all functions of type A → B are created equal but all proofs P → Q are
-- ofc this is not true for mathematicians, but they have different criterion for good proofs than programmers have for good programs (right?)

-- **Propositional Logic
section Propositional
variables P Q R : Prop

theorem obvious : true :=
by apply true.intro

theorem obvious' : true :=
by constructor

#print false

theorem false_imp : false → 2 + 2 = 5 :=
by intro f; destruct f

theorem false_imp_lean : false → 2 + 2 = 5 :=
by contradiction

-- TODO: not sure how to prove this in lean. Is there an elimtype analogue?
theorem arith_neq : 2 + 2 = 5 → 9 + 9 = 835 :=
begin
intro,
exfalso,
admit
end

#print not

theorem arith_neq' : ¬(2 + 2 = 5) :=
begin
unfold not,
-- what to use next?
admit
end

#print and

theorem and_comm : P ∧ Q → Q ∧ P :=
begin
intro p,
destruct p,
intros h1 h2,
split; assumption
end

theorem and_comm_idiomatic : P ∧ Q → Q ∧ P := by intros; simp; assumption

theorem and_comm_lean (h:P ∧ Q):Q ∧ P:=
and.intro (and.right h) (and.left h)

theorem and_comm_lean_short (h:P ∧ Q):Q ∧ P:=
⟨h.right, h.left⟩

#print or

theorem or_comm (h:P ∨ Q) : Q ∨ P :=
begin
exact h.elim
    (assume hp : P, or.inr hp)
    (assume hq : Q, or.inl hq)
end

universe variable u

def length {α : Type u} : list α → nat
| list.nil        := nat.zero
| (list.cons _ l) := nat.succ (length l)

-- TODO:
theorem arith_comm : ∀ ls1 ls2 : list nat,
    length ls1 = length ls2 ∨ length ls1 + length ls2 = 6
    → length (ls1 ++ ls2) = 6 ∨ length ls1 = length ls2 :=
begin
admit
end

end Propositional

-- **What Does It Mean to Be Constructive?
-- **First-Order Logic
#print Exists

theorem exist1 : ∃ x : ℕ, x + 1 = 2 :=
⟨1, by simp⟩

-- TODO: simpler way?
theorem exist2 : ∀ n m : ℕ, (∃ x : ℕ, n + x = m) → n ≤ m :=
begin
intros,
destruct a,
intros,
subst a_2,
apply nat.le_add_right
end

-- **Predicates with Implicit Equality
inductive isZero : ℕ → Prop
| IsZero : isZero 0

theorem isZero_zero : isZero 0 := by constructor

#print eq

-- Notice destruct does not work here, must use induction instead
-- TODO: is this the "correct" tactic?
theorem isZero_plus : ∀ n m : ℕ, isZero m → n + m = n :=
begin
intros,
induction a,
simp
end

theorem isZero_contra : isZero 1 → false :=
begin
intros,
cases a
end

#check @isZero.rec

-- **Recursive Predicates
inductive even : ℕ → Prop
| EvenO  : even nat.zero
| EvenSS : ∀ n, even n → even (nat.succ (nat.succ n))

theorem even_0 : even 0 := by constructor

theorem even_4 : even 4 := by repeat {constructor}

-- TODO: hints?

theorem even_1_contra : even 1 → false :=
begin
intros,
cases a
end

theorem even_3_contra : even 3 → false :=
begin
intros,
cases a,
cases a_2
end

theorem even_plus_on_n : ∀ n m, even n → even m → even (n + m) :=
begin
intro n,
induction n,
case nat.zero {mini_crush},
case nat.succ {
    intros,
    note h : ∀ x y, nat.succ x + y = nat.succ (x + y) := by apply nat.succ_add,
    rw h,
    cases a_1,
    rw h,
    constructor,
    admit
}
end

theorem even_plus_on_a : ∀ n m, even n → even m → even (n + m) :=
begin
intros,
induction a,
{mini_crush},
{
    simp,
    constructor,
    rw nat.add_comm,
    assumption
}
end

-- Note: mini_crush doesn't work for even_plus

-- TODO: finish this
lemma even_contra' : ∀ n', even n' → ∀ n, n' = nat.succ (n + n) → false :=
begin
intros n a,
induction a,
{mini_crush},
{
    intros,
    apply (ih_1 n_2),
    symmetry,
    admit
}
end

-- TODO
theorem even_contra : ∀ n, even (nat.succ (n + n)) → false :=
begin
intros,
admit
end

end hide