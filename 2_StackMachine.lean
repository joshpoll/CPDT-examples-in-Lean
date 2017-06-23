section -- Artihmetic Expressions Over Natural Numbers
section -- Source Language (Arithmetic Expressions)

-- binary operation syntax
inductive binop : Type
| Plus
| Times

-- arithmetic expression syntax
inductive exp : Type
| Const : ℕ → exp
| Binop : binop → exp → exp → exp

-- binop denotational semantics
def binopDenote : binop → ℕ → ℕ → ℕ
| binop.Plus  := nat.add
| binop.Times := nat.mul

-- exp denotational semantics
def expDenote : exp → ℕ
| (exp.Const n)       := n
| (exp.Binop b e1 e2) := (binopDenote b) (expDenote e1) (expDenote e2)

-- tests using both #reduce and #eval
#reduce (decidable.to_bool(expDenote (exp.Const 42) = 42))
#eval   (decidable.to_bool(expDenote (exp.Const 42) = 42))

#reduce (decidable.to_bool(expDenote (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) = 4))
#eval   (decidable.to_bool(expDenote (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) = 4))

#reduce (decidable.to_bool(expDenote (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) (exp.Const 7)) = 28))
#eval   (decidable.to_bool(expDenote (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) (exp.Const 7)) = 28))

end -- Source Language (Arithmetic Expressions)
section -- Target Language (Stack Machine)

-- instruction syntax
inductive instr : Type
| iConst : ℕ → instr
| iBinop : binop → instr

-- program and stack syntax
-- mark as reducible so lean can unfold the definitions during typechecking
@[reducible] def prog : Type := list instr
@[reducible] def stack : Type := list ℕ

-- instr denotational semantics
def instrDenote (i : instr) (s : stack) : option stack :=
    match i with
    | (instr.iConst n) := some (n :: s)
    | (instr.iBinop b) :=
        match s with
        | arg1 :: arg2 :: s' := some ((binopDenote b) arg1 arg2 :: s')
        | _ := none
        end
    end

-- prog denotational semantics
def progDenote : prog → stack → option stack
| [] s := some s
| (i :: p') s :=
    match instrDenote i s with
    | none    := none
    | some s' := progDenote p' s'
    end

end -- Target Language (Stack Machine)
section -- Translation

def compile : exp → prog
| (exp.Const n)       := instr.iConst n :: []
| (exp.Binop b e1 e2) := compile e2 ++ compile e1 ++ instr.iBinop b :: []

-- compilation examples
#reduce compile (exp.Const 42)
#reduce compile (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2))
#reduce compile (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2))(exp.Const 7))

-- compilation-evaluation examples
#reduce progDenote (compile (exp.Const 42)) []
#reduce progDenote (compile (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2))) []
#reduce progDenote (compile (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2))(exp.Const 7))) []

end -- Translation
section -- Translation Correctness
--TODO: prove!!
lemma compile_correct' : ∀ e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s) := sorry

theorem compile_correct : ∀ e, progDenote (compile e) [] = some (expDenote e :: []) := sorry


end -- Translation Correctness
end -- Artihmetic Expressions Over Natural Numbers

section  -- Typed Expressions

-- atomic types
inductive type : Type
| Nat
| Bool

-- binop types
inductive tbinop : type → type → type → Type
| TPlus  : tbinop type.Nat type.Nat type.Nat
| TTimes : tbinop type.Nat type.Nat type.Nat
| TEq    : ∀ t, tbinop t t type.Bool
| TLt    : tbinop type.Nat type.Nat type.Bool

-- expression types
inductive texp : type → Type
| TNConst : ℕ → texp type.Nat
| TBConst : bool → texp type.Bool
| TBinop : ∀ t1 t2 t, tbinop t1 t2 t → texp t1 → texp t2 → texp t

-- map from source object types to meta types
def typeDenote : type → Type
| type.Nat := ℕ
| type.Bool := bool

def tbinopDenote {arg1 arg2 res : type} (b : tbinop arg1 arg2 res) : typeDenote arg1 → typeDenote arg2 → typeDenote res :=
match b with
| tbinop.TPlus         := nat.add
| tbinop.TTimes        := nat.mul
| tbinop.TEq type.Nat  := nat.decidable_eq
| tbinop.TEq type.Bool := bool.decidable_eq
| tbinop.TLt           := nat.le
end

end -- Typed Expressions