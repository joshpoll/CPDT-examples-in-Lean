namespace hide
-- *Inductive Predicates

#print unit
#print true

-- term T : Type is a type of programs
-- it is inhabited by programs
-- term T : Prop is a logical proposition
-- it is inhabited by proofs

-- there *is* a differeence between programming and proving in practice

-- proof irrelevance
-- to an engineer: not all functions of type A → B are created equal but all proofs P → Q are
-- ofc this is not true for mathematicians, but they have different criterion for good proofs than programmers have for good programs (right?)

-- *Propositional Logic
section Propositional
variables P Q R : Prop

theorem obvious : true :=
begin
apply true.intro
end

theorem obvious' : true :=
begin
constructor
end

#print false

theorem false_imp : false → 2 + 2 = 5 :=
begin
intro f,
destruct f
end

-- TODO: not sure how to prove this in lean. Is there an elimtype analogue?
theorem arith_neq : 2 + 2 = 5 → 9 + 9 = 835 := sorry

#print not

theorem arith_neq' : ¬(2 + 2 = 5) :=
begin
unfold not,
-- what to use next?
end

#print and

theorem and_comm : P ∧ Q → Q ∧ P :=
begin
intro p,
destruct p,
intros h1 h2,
split; assumption
end

theorem and_comm_lean (h:P ∧ Q):Q ∧ P:=
and.intro (and.right h) (and.left h)

theorem and_comm_lean_short (h:P ∧ Q):Q ∧ P:=
⟨h.right, h.left⟩

theorem and_comm_lean_finish (h:P ∧ Q):Q ∧ P:= sorry

#print or

theorem or_comm (h:P ∨ Q) : Q ∨ P :=
begin
exact h.elim
    (assume hp : P, or.inr hp)
    (assume hq : Q, or.inl hq)
end

end Propositional

end hide

import system.io
-- system/io.lean or system/io/default.lean
-- put things in namespaces to avoid polluting global namespace
-- _root_ is global namespace