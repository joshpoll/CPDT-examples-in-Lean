import tools.auto.finish
import _target.deps.mini_crush.src.mini_crush

namespace arith
-- *Artihmetic Expressions Over Natural Numbers
-- **Source Language

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

-- **Target Language

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

-- **Translation

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

-- **Translation Correctness

lemma compile_correct' (e : exp) : ∀ p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s) :=
begin
induction e; intros,
case exp.Const {
    unfold compile,
    unfold expDenote,
    simp,
    unfold progDenote,
    unfold instrDenote,
    simp,
    unfold instrDenote._match_1,
    unfold progDenote._match_1,
    refl
},
case exp.Binop {
    unfold compile,
    unfold expDenote,
    simp,    /- can replace these lines with simph -/
    rw ih_2, /- -/
    rw ih_1, /- -/
    unfold progDenote,
    unfold instrDenote,
    simp,
    unfold instrDenote._match_1,
    unfold instrDenote._match_2,
    unfold progDenote._match_1,
    refl
}
end

lemma compile_correct'_lean (e : exp) : ∀ p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s) :=
begin
induction e; intros,
case exp.Const {refl},
case exp.Binop {
    unfold compile expDenote,
    simph,
    refl
}
end

@[simp] lemma compile_correct'_crush (e : exp) : ∀ p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s) :=
by mini_crush

lemma app_nil_end {A : Type} (l : list A) : l = l ++ list.nil := by induction l; simph

theorem compile_correct (e : exp) : progDenote (compile e) [] = some (expDenote e :: []) :=
begin
rw app_nil_end (compile e),
rw compile_correct',
refl
end

-- TODO: excessive memory consumption
theorem compile_correct_crush (e : exp) : progDenote (compile e) [] = some (expDenote e :: []) :=
by mini_crush

end arith

namespace typed
-- *Typed Expressions
-- **Source Language

-- atomic types
inductive type : Type
| Nat
| Bool
open type

-- binop types
inductive tbinop : type → type → type → Type
| TPlus  : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq    : ∀ t, tbinop t t Bool
| TLt    : tbinop Nat Nat Bool
open tbinop

-- expression types
inductive texp : type → Type
| TNConst : ℕ → texp Nat
| TBConst : bool → texp Bool
| TBinop : ∀ {t1 t2 t}, tbinop t1 t2 t → texp t1 → texp t2 → texp t
open texp

-- type denotational semantics
def typeDenote : type → Type
| Nat := ℕ
| Bool := bool

-- tbinop denotational semantics
def tbinopDenote : ∀ {arg1 arg2 res} (b : tbinop arg1 arg2 res),
    typeDenote arg1 → typeDenote arg2 → typeDenote res
| ._ ._ ._ TPlus      := nat.add
| ._ ._ ._ TTimes     := nat.mul
| ._ ._ ._ (TEq Nat)  := (λ x y, decidable.to_bool $ x = y)
| ._ ._ ._ (TEq Bool) := (λ x y, decidable.to_bool $ x = y)
| ._ ._ ._ TLt        := (λ x y, decidable.to_bool $ nat.le x y)

-- texp denotational semantics
def texpDenote : ∀ {t}, texp t → typeDenote t
| ._ (TNConst n) := n
| ._ (TBConst b) := b
| ._ (@TBinop _ _ _ b e1 e2) := (tbinopDenote b) (texpDenote e1) (texpDenote e2)

#reduce texpDenote (TNConst 42)
#reduce texpDenote (TBConst true)
-- TODO: is there a way to remove need for _'s?
#reduce texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
#reduce texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
#reduce texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))

-- **Target Language

-- stack type to describe how expressions affect the stack
@[reducible] def tstack := list type

inductive tinstr : tstack → tstack → Type
| TiNConst : ∀ s, ℕ → tinstr s (Nat :: s)
| TiBConst : ∀ s, bool → tinstr s (Bool :: s)
| TiBinop  : ∀ arg1 arg2 res s,
    tbinop arg1 arg2 res
    → tinstr (arg1 :: arg2 :: s) (res :: s)
open tinstr

inductive tprog : tstack → tstack → Type
| TNil  : ∀ s, tprog s s
| TCons : ∀ s1 s2 s3,
    tinstr s1 s2
    → tprog s2 s3
    → tprog s1 s3
open tprog

def vstack : tstack → Type
| []      := unit
| (t :: ts) := typeDenote t × vstack ts

def tinstrDenote : ∀ {ts} {ts'}, tinstr ts ts' → vstack ts → vstack ts'
| ._ ._ (TiNConst _ n)      := (λ s, (n, s))
| ._ ._ (TiBConst _ b)      := (λ s, (b, s))
| ._ ._ (TiBinop _ _ _ _ b) := (λ s,
    let (arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s'))

def tprogDenote : ∀ {ts} {ts'}, tprog ts ts' → vstack ts → vstack ts'
| ._ ._ (TNil _) := (λ s, s)
| ._ ._ (TCons _ _ _ i p) := (λ s, tprogDenote p (tinstrDenote i s))

-- **Translation

def tconcat : ∀ {ts} {ts'} {ts''}, tprog ts ts' → tprog ts' ts'' → tprog ts ts''
| ._ ._ ts'' (TNil _) := (λ p, p)
| ._ ._ ts'' (TCons _ _ _ i p1) := (λ p, TCons _ _ _ i (tconcat p1 p))

def tcompile : ∀ {t} (e : texp t) (ts : tstack), tprog ts (t :: ts)
| ._ (TNConst n) _ := TCons _ _ _ (TiNConst _ n) (TNil _)
| ._ (TBConst b) _ := TCons _ _ _ (TiBConst _ b) (TNil _)
| ._ (@TBinop _ _ _ b e1 e2) _ := tconcat (tcompile e2 _)
    (tconcat (tcompile e1 _) (TCons _ _ _ (TiBinop _ _ _ _ b) (TNil _)))

#reduce tprogDenote (tcompile (TNConst 42) []) ()
#reduce tprogDenote (tcompile (TBConst true) []) ()
#reduce tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
    (TNConst 2)) (TNConst 7)) []) ()
#reduce tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2)
    (TNConst 2)) (TNConst 7)) []) ()
#reduce  tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
    (TNConst 7)) []) ()

-- **Translation Correctness

@[simp] lemma tconcat_correct : ∀ ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts),
    tprogDenote (tconcat p p') s = tprogDenote p' (tprogDenote p s) :=
by mini_crush

@[simp] lemma tcompile_correct' : ∀ t (e : texp t) ts (s : vstack ts),
    tprogDenote (tcompile e ts) s = (texpDenote e, s) :=
by mini_crush

theorem tcompile_correct : ∀ t (e : texp t),
    tprogDenote (tcompile e []) () = (texpDenote e, ()) := by mini_crush

end typed