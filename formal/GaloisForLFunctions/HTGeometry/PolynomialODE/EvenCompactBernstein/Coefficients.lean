module
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.RawCoefficients

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum

/-! Exact coefficient and reconstruction component for the compensated compact last-row margin. -/

@[expose] public section

namespace HTGeometry.EvenCompactBernstein
noncomputable section
set_option maxRecDepth 2048

structure IntegerCoefficientCertificate (source : ℤ) where
  value : ℤ
  eq_value : source = value

open Lean Meta Elab Term Tactic
meta section
elab "evenCompactIntegerCoefficientCertified% " cnv:conv " => " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Int))
  let (rhs, g) ← Conv.mkConvGoalFor e
  let goals ← Tactic.run g.mvarId! do
    evalTactic cnv
    for goal in (← getGoals) do
      goal.refl
    pruneSolvedGoals
  unless goals.isEmpty do
    throwError "integer coefficient normalization left open goals"
  let rhs ← instantiateMVars rhs
  let proof ← instantiateMVars g
  return mkApp3 (mkConst ``IntegerCoefficientCertificate.mk) e rhs proof
end


def n0_0_0Certificate : IntegerCoefficientCertificate n0_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n0_0_0]) => n0_0_0

def n0_1_0Certificate : IntegerCoefficientCertificate n0_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n0_1_0]) => n0_1_0

def n0_2_0Certificate : IntegerCoefficientCertificate n0_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n0_2_0]) => n0_2_0

def numeratorCoefficient0 (a b : ℕ) : ℤ :=
  ((if 0 ≤ a ∧ 0 ≤ b then n0_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 0 ≤ b then n0_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 0 ≤ b then n0_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)))

def n1_0_0Certificate : IntegerCoefficientCertificate n1_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_0_0]) => n1_0_0

def n1_1_0Certificate : IntegerCoefficientCertificate n1_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_1_0]) => n1_1_0

def n1_2_0Certificate : IntegerCoefficientCertificate n1_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_2_0]) => n1_2_0

def n1_3_0Certificate : IntegerCoefficientCertificate n1_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_3_0]) => n1_3_0

def n1_0_1Certificate : IntegerCoefficientCertificate n1_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_0_1]) => n1_0_1

def n1_0_2Certificate : IntegerCoefficientCertificate n1_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_0_2]) => n1_0_2

def n1_1_1Certificate : IntegerCoefficientCertificate n1_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_1_1]) => n1_1_1

def n1_1_2Certificate : IntegerCoefficientCertificate n1_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_1_2]) => n1_1_2

def n1_2_1Certificate : IntegerCoefficientCertificate n1_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n1_2_1]) => n1_2_1

def numeratorCoefficient1 (a b : ℕ) : ℤ :=
  ((((if 0 ≤ a ∧ 0 ≤ b then n1_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 0 ≤ b then n1_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 0 ≤ b then n1_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 0 ≤ b then n1_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 1 ≤ b then n1_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 2 ≤ b then n1_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 1 ≤ b then n1_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 2 ≤ b then n1_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 1 ≤ b then n1_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)))))

def n2_0_0Certificate : IntegerCoefficientCertificate n2_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_0_0]) => n2_0_0

def n2_1_0Certificate : IntegerCoefficientCertificate n2_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_1_0]) => n2_1_0

def n2_2_0Certificate : IntegerCoefficientCertificate n2_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_2_0]) => n2_2_0

def n2_3_0Certificate : IntegerCoefficientCertificate n2_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_3_0]) => n2_3_0

def n2_4_0Certificate : IntegerCoefficientCertificate n2_4_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_4_0]) => n2_4_0

def n2_0_1Certificate : IntegerCoefficientCertificate n2_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_0_1]) => n2_0_1

def n2_0_2Certificate : IntegerCoefficientCertificate n2_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_0_2]) => n2_0_2

def n2_1_1Certificate : IntegerCoefficientCertificate n2_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_1_1]) => n2_1_1

def n2_1_2Certificate : IntegerCoefficientCertificate n2_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_1_2]) => n2_1_2

def n2_2_1Certificate : IntegerCoefficientCertificate n2_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_2_1]) => n2_2_1

def n2_2_2Certificate : IntegerCoefficientCertificate n2_2_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_2_2]) => n2_2_2

def n2_3_1Certificate : IntegerCoefficientCertificate n2_3_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_3_1]) => n2_3_1

def n2_3_2Certificate : IntegerCoefficientCertificate n2_3_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_3_2]) => n2_3_2

def n2_0_3Certificate : IntegerCoefficientCertificate n2_0_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_0_3]) => n2_0_3

def n2_0_4Certificate : IntegerCoefficientCertificate n2_0_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_0_4]) => n2_0_4

def n2_1_3Certificate : IntegerCoefficientCertificate n2_1_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_1_3]) => n2_1_3

def n2_1_4Certificate : IntegerCoefficientCertificate n2_1_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_1_4]) => n2_1_4

def n2_2_3Certificate : IntegerCoefficientCertificate n2_2_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n2_2_3]) => n2_2_3

def numeratorCoefficient2 (a b : ℕ) : ℤ :=
  (((((if 0 ≤ a ∧ 0 ≤ b then n2_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 0 ≤ b then n2_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 0 ≤ b then n2_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 0 ≤ b then n2_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))) +
    (((if 4 ≤ a ∧ 0 ≤ b then n2_4_0Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 1 ≤ b then n2_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)) +
    ((if 0 ≤ a ∧ 2 ≤ b then n2_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 1 ≤ b then n2_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 2 ≤ b then n2_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))))) +
    ((((if 2 ≤ a ∧ 1 ≤ b then n2_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 2 ≤ b then n2_2_2Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 1 ≤ b then n2_3_1Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 2 ≤ b then n2_3_2Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 3 ≤ b then n2_0_3Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 4 ≤ b then n2_0_4Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 3 ≤ b then n2_1_3Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 4 ≤ b then n2_1_4Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 3 ≤ b then n2_2_3Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0))))))

def n3_0_0Certificate : IntegerCoefficientCertificate n3_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_0]) => n3_0_0

def n3_1_0Certificate : IntegerCoefficientCertificate n3_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_0]) => n3_1_0

def n3_2_0Certificate : IntegerCoefficientCertificate n3_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_0]) => n3_2_0

def n3_3_0Certificate : IntegerCoefficientCertificate n3_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_3_0]) => n3_3_0

def n3_4_0Certificate : IntegerCoefficientCertificate n3_4_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_4_0]) => n3_4_0

def n3_5_0Certificate : IntegerCoefficientCertificate n3_5_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_5_0]) => n3_5_0

def n3_0_1Certificate : IntegerCoefficientCertificate n3_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_1]) => n3_0_1

def n3_0_2Certificate : IntegerCoefficientCertificate n3_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_2]) => n3_0_2

def n3_1_1Certificate : IntegerCoefficientCertificate n3_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_1]) => n3_1_1

def n3_1_2Certificate : IntegerCoefficientCertificate n3_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_2]) => n3_1_2

def n3_2_1Certificate : IntegerCoefficientCertificate n3_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_1]) => n3_2_1

def n3_2_2Certificate : IntegerCoefficientCertificate n3_2_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_2]) => n3_2_2

def n3_3_1Certificate : IntegerCoefficientCertificate n3_3_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_3_1]) => n3_3_1

def n3_3_2Certificate : IntegerCoefficientCertificate n3_3_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_3_2]) => n3_3_2

def n3_4_1Certificate : IntegerCoefficientCertificate n3_4_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_4_1]) => n3_4_1

def n3_4_2Certificate : IntegerCoefficientCertificate n3_4_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_4_2]) => n3_4_2

def n3_0_3Certificate : IntegerCoefficientCertificate n3_0_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_3]) => n3_0_3

def n3_0_4Certificate : IntegerCoefficientCertificate n3_0_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_4]) => n3_0_4

def n3_1_3Certificate : IntegerCoefficientCertificate n3_1_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_3]) => n3_1_3

def n3_1_4Certificate : IntegerCoefficientCertificate n3_1_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_4]) => n3_1_4

def n3_2_3Certificate : IntegerCoefficientCertificate n3_2_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_3]) => n3_2_3

def n3_2_4Certificate : IntegerCoefficientCertificate n3_2_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_4]) => n3_2_4

def n3_3_3Certificate : IntegerCoefficientCertificate n3_3_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_3_3]) => n3_3_3

def n3_3_4Certificate : IntegerCoefficientCertificate n3_3_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_3_4]) => n3_3_4

def n3_0_5Certificate : IntegerCoefficientCertificate n3_0_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_5]) => n3_0_5

def n3_0_6Certificate : IntegerCoefficientCertificate n3_0_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_0_6]) => n3_0_6

def n3_1_5Certificate : IntegerCoefficientCertificate n3_1_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_5]) => n3_1_5

def n3_1_6Certificate : IntegerCoefficientCertificate n3_1_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_1_6]) => n3_1_6

def n3_2_5Certificate : IntegerCoefficientCertificate n3_2_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n3_2_5]) => n3_2_5

def numeratorCoefficient3 (a b : ℕ) : ℤ :=
  (((((if 0 ≤ a ∧ 0 ≤ b then n3_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 0 ≤ b then n3_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 0 ≤ b then n3_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))) +
    (((if 3 ≤ a ∧ 0 ≤ b then n3_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 0 ≤ b then n3_4_0Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 5 ≤ a ∧ 0 ≤ b then n3_5_0Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 1 ≤ b then n3_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)))) +
    (((if 0 ≤ a ∧ 2 ≤ b then n3_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 1 ≤ b then n3_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 2 ≤ b then n3_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))) +
    (((if 2 ≤ a ∧ 1 ≤ b then n3_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 2 ≤ b then n3_2_2Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 1 ≤ b then n3_3_1Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 2 ≤ b then n3_3_2Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))))) +
    ((((if 4 ≤ a ∧ 1 ≤ b then n3_4_1Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 4 ≤ a ∧ 2 ≤ b then n3_4_2Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 3 ≤ b then n3_0_3Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 4 ≤ b then n3_0_4Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 3 ≤ b then n3_1_3Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 4 ≤ b then n3_1_4Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 3 ≤ b then n3_2_3Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)))) +
    ((((if 2 ≤ a ∧ 4 ≤ b then n3_2_4Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 3 ≤ b then n3_3_3Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 4 ≤ b then n3_3_4Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 5 ≤ b then n3_0_5Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 6 ≤ b then n3_0_6Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 5 ≤ b then n3_1_5Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 6 ≤ b then n3_1_6Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 5 ≤ b then n3_2_5Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0))))))

def n4_0_0Certificate : IntegerCoefficientCertificate n4_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_0]) => n4_0_0

def n4_1_0Certificate : IntegerCoefficientCertificate n4_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_0]) => n4_1_0

def n4_2_0Certificate : IntegerCoefficientCertificate n4_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_0]) => n4_2_0

def n4_3_0Certificate : IntegerCoefficientCertificate n4_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_0]) => n4_3_0

def n4_4_0Certificate : IntegerCoefficientCertificate n4_4_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_4_0]) => n4_4_0

def n4_5_0Certificate : IntegerCoefficientCertificate n4_5_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_5_0]) => n4_5_0

def n4_6_0Certificate : IntegerCoefficientCertificate n4_6_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_6_0]) => n4_6_0

def n4_0_1Certificate : IntegerCoefficientCertificate n4_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_1]) => n4_0_1

def n4_0_2Certificate : IntegerCoefficientCertificate n4_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_2]) => n4_0_2

def n4_1_1Certificate : IntegerCoefficientCertificate n4_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_1]) => n4_1_1

def n4_1_2Certificate : IntegerCoefficientCertificate n4_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_2]) => n4_1_2

def n4_2_1Certificate : IntegerCoefficientCertificate n4_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_1]) => n4_2_1

def n4_2_2Certificate : IntegerCoefficientCertificate n4_2_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_2]) => n4_2_2

def n4_3_1Certificate : IntegerCoefficientCertificate n4_3_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_1]) => n4_3_1

def n4_3_2Certificate : IntegerCoefficientCertificate n4_3_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_2]) => n4_3_2

def n4_4_1Certificate : IntegerCoefficientCertificate n4_4_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_4_1]) => n4_4_1

def n4_4_2Certificate : IntegerCoefficientCertificate n4_4_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_4_2]) => n4_4_2

def n4_5_1Certificate : IntegerCoefficientCertificate n4_5_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_5_1]) => n4_5_1

def n4_5_2Certificate : IntegerCoefficientCertificate n4_5_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_5_2]) => n4_5_2

def n4_0_3Certificate : IntegerCoefficientCertificate n4_0_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_3]) => n4_0_3

def n4_0_4Certificate : IntegerCoefficientCertificate n4_0_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_4]) => n4_0_4

def n4_1_3Certificate : IntegerCoefficientCertificate n4_1_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_3]) => n4_1_3

def n4_1_4Certificate : IntegerCoefficientCertificate n4_1_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_4]) => n4_1_4

def n4_2_3Certificate : IntegerCoefficientCertificate n4_2_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_3]) => n4_2_3

def n4_2_4Certificate : IntegerCoefficientCertificate n4_2_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_4]) => n4_2_4

def n4_3_3Certificate : IntegerCoefficientCertificate n4_3_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_3]) => n4_3_3

def n4_3_4Certificate : IntegerCoefficientCertificate n4_3_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_4]) => n4_3_4

def n4_4_3Certificate : IntegerCoefficientCertificate n4_4_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_4_3]) => n4_4_3

def n4_4_4Certificate : IntegerCoefficientCertificate n4_4_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_4_4]) => n4_4_4

def n4_0_5Certificate : IntegerCoefficientCertificate n4_0_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_5]) => n4_0_5

def n4_0_6Certificate : IntegerCoefficientCertificate n4_0_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_6]) => n4_0_6

def n4_1_5Certificate : IntegerCoefficientCertificate n4_1_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_5]) => n4_1_5

def n4_1_6Certificate : IntegerCoefficientCertificate n4_1_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_6]) => n4_1_6

def n4_2_5Certificate : IntegerCoefficientCertificate n4_2_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_5]) => n4_2_5

def n4_2_6Certificate : IntegerCoefficientCertificate n4_2_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_6]) => n4_2_6

def n4_3_5Certificate : IntegerCoefficientCertificate n4_3_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_5]) => n4_3_5

def n4_3_6Certificate : IntegerCoefficientCertificate n4_3_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_3_6]) => n4_3_6

def n4_0_7Certificate : IntegerCoefficientCertificate n4_0_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_7]) => n4_0_7

def n4_0_8Certificate : IntegerCoefficientCertificate n4_0_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_0_8]) => n4_0_8

def n4_1_7Certificate : IntegerCoefficientCertificate n4_1_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_7]) => n4_1_7

def n4_1_8Certificate : IntegerCoefficientCertificate n4_1_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_1_8]) => n4_1_8

def n4_2_7Certificate : IntegerCoefficientCertificate n4_2_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n4_2_7]) => n4_2_7

def numeratorCoefficient4 (a b : ℕ) : ℤ :=
  ((((((if 0 ≤ a ∧ 0 ≤ b then n4_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 0 ≤ b then n4_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 0 ≤ b then n4_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 0 ≤ b then n4_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 0 ≤ b then n4_4_0Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)))) +
    (((if 5 ≤ a ∧ 0 ≤ b then n4_5_0Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 6 ≤ a ∧ 0 ≤ b then n4_6_0Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 0 ≤ a ∧ 1 ≤ b then n4_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 2 ≤ b then n4_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 1 ≤ b then n4_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0))))) +
    ((((if 1 ≤ a ∧ 2 ≤ b then n4_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 1 ≤ b then n4_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 2 ≤ b then n4_2_2Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 1 ≤ b then n4_3_1Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 2 ≤ b then n4_3_2Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)))) +
    (((if 4 ≤ a ∧ 1 ≤ b then n4_4_1Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 4 ≤ a ∧ 2 ≤ b then n4_4_2Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 1 ≤ b then n4_5_1Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0))) +
    ((if 5 ≤ a ∧ 2 ≤ b then n4_5_2Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 3 ≤ b then n4_0_3Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 4 ≤ b then n4_0_4Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)))))) +
    (((((if 1 ≤ a ∧ 3 ≤ b then n4_1_3Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 4 ≤ b then n4_1_4Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 3 ≤ b then n4_2_3Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    ((if 2 ≤ a ∧ 4 ≤ b then n4_2_4Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 3 ≤ b then n4_3_3Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)))) +
    (((if 3 ≤ a ∧ 4 ≤ b then n4_3_4Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 3 ≤ b then n4_4_3Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)) +
    ((if 4 ≤ a ∧ 4 ≤ b then n4_4_4Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 5 ≤ b then n4_0_5Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 6 ≤ b then n4_0_6Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0))))) +
    ((((if 1 ≤ a ∧ 5 ≤ b then n4_1_5Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 6 ≤ b then n4_1_6Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 5 ≤ b then n4_2_5Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    ((if 2 ≤ a ∧ 6 ≤ b then n4_2_6Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 5 ≤ b then n4_3_5Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0)))) +
    (((if 3 ≤ a ∧ 6 ≤ b then n4_3_6Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 7 ≤ b then n4_0_7Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 8 ≤ b then n4_0_8Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0))) +
    ((if 1 ≤ a ∧ 7 ≤ b then n4_1_7Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 8 ≤ b then n4_1_8Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 7 ≤ b then n4_2_7Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0)))))))

def n5_0_0Certificate : IntegerCoefficientCertificate n5_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_0]) => n5_0_0

def n5_1_0Certificate : IntegerCoefficientCertificate n5_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_0]) => n5_1_0

def n5_2_0Certificate : IntegerCoefficientCertificate n5_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_0]) => n5_2_0

def n5_3_0Certificate : IntegerCoefficientCertificate n5_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_0]) => n5_3_0

def n5_4_0Certificate : IntegerCoefficientCertificate n5_4_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_0]) => n5_4_0

def n5_5_0Certificate : IntegerCoefficientCertificate n5_5_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_5_0]) => n5_5_0

def n5_6_0Certificate : IntegerCoefficientCertificate n5_6_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_6_0]) => n5_6_0

def n5_7_0Certificate : IntegerCoefficientCertificate n5_7_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_7_0]) => n5_7_0

def n5_0_1Certificate : IntegerCoefficientCertificate n5_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_1]) => n5_0_1

def n5_0_2Certificate : IntegerCoefficientCertificate n5_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_2]) => n5_0_2

def n5_1_1Certificate : IntegerCoefficientCertificate n5_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_1]) => n5_1_1

def n5_1_2Certificate : IntegerCoefficientCertificate n5_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_2]) => n5_1_2

def n5_2_1Certificate : IntegerCoefficientCertificate n5_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_1]) => n5_2_1

def n5_2_2Certificate : IntegerCoefficientCertificate n5_2_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_2]) => n5_2_2

def n5_3_1Certificate : IntegerCoefficientCertificate n5_3_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_1]) => n5_3_1

def n5_3_2Certificate : IntegerCoefficientCertificate n5_3_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_2]) => n5_3_2

def n5_4_1Certificate : IntegerCoefficientCertificate n5_4_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_1]) => n5_4_1

def n5_4_2Certificate : IntegerCoefficientCertificate n5_4_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_2]) => n5_4_2

def n5_5_1Certificate : IntegerCoefficientCertificate n5_5_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_5_1]) => n5_5_1

def n5_5_2Certificate : IntegerCoefficientCertificate n5_5_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_5_2]) => n5_5_2

def n5_6_1Certificate : IntegerCoefficientCertificate n5_6_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_6_1]) => n5_6_1

def n5_6_2Certificate : IntegerCoefficientCertificate n5_6_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_6_2]) => n5_6_2

def n5_0_3Certificate : IntegerCoefficientCertificate n5_0_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_3]) => n5_0_3

def n5_0_4Certificate : IntegerCoefficientCertificate n5_0_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_4]) => n5_0_4

def n5_1_3Certificate : IntegerCoefficientCertificate n5_1_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_3]) => n5_1_3

def n5_1_4Certificate : IntegerCoefficientCertificate n5_1_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_4]) => n5_1_4

def n5_2_3Certificate : IntegerCoefficientCertificate n5_2_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_3]) => n5_2_3

def n5_2_4Certificate : IntegerCoefficientCertificate n5_2_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_4]) => n5_2_4

def n5_3_3Certificate : IntegerCoefficientCertificate n5_3_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_3]) => n5_3_3

def n5_3_4Certificate : IntegerCoefficientCertificate n5_3_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_4]) => n5_3_4

def n5_4_3Certificate : IntegerCoefficientCertificate n5_4_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_3]) => n5_4_3

def n5_4_4Certificate : IntegerCoefficientCertificate n5_4_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_4]) => n5_4_4

def n5_5_3Certificate : IntegerCoefficientCertificate n5_5_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_5_3]) => n5_5_3

def n5_5_4Certificate : IntegerCoefficientCertificate n5_5_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_5_4]) => n5_5_4

def n5_0_5Certificate : IntegerCoefficientCertificate n5_0_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_5]) => n5_0_5

def n5_0_6Certificate : IntegerCoefficientCertificate n5_0_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_6]) => n5_0_6

def n5_1_5Certificate : IntegerCoefficientCertificate n5_1_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_5]) => n5_1_5

def n5_1_6Certificate : IntegerCoefficientCertificate n5_1_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_6]) => n5_1_6

def n5_2_5Certificate : IntegerCoefficientCertificate n5_2_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_5]) => n5_2_5

def n5_2_6Certificate : IntegerCoefficientCertificate n5_2_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_6]) => n5_2_6

def n5_3_5Certificate : IntegerCoefficientCertificate n5_3_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_5]) => n5_3_5

def n5_3_6Certificate : IntegerCoefficientCertificate n5_3_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_6]) => n5_3_6

def n5_4_5Certificate : IntegerCoefficientCertificate n5_4_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_5]) => n5_4_5

def n5_4_6Certificate : IntegerCoefficientCertificate n5_4_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_4_6]) => n5_4_6

def n5_0_7Certificate : IntegerCoefficientCertificate n5_0_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_7]) => n5_0_7

def n5_0_8Certificate : IntegerCoefficientCertificate n5_0_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_8]) => n5_0_8

def n5_1_7Certificate : IntegerCoefficientCertificate n5_1_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_7]) => n5_1_7

def n5_1_8Certificate : IntegerCoefficientCertificate n5_1_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_8]) => n5_1_8

def n5_2_7Certificate : IntegerCoefficientCertificate n5_2_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_7]) => n5_2_7

def n5_2_8Certificate : IntegerCoefficientCertificate n5_2_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_8]) => n5_2_8

def n5_3_7Certificate : IntegerCoefficientCertificate n5_3_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_7]) => n5_3_7

def n5_3_8Certificate : IntegerCoefficientCertificate n5_3_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_3_8]) => n5_3_8

def n5_0_9Certificate : IntegerCoefficientCertificate n5_0_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_9]) => n5_0_9

def n5_0_10Certificate : IntegerCoefficientCertificate n5_0_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_0_10]) => n5_0_10

def n5_1_9Certificate : IntegerCoefficientCertificate n5_1_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_9]) => n5_1_9

def n5_1_10Certificate : IntegerCoefficientCertificate n5_1_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_1_10]) => n5_1_10

def n5_2_9Certificate : IntegerCoefficientCertificate n5_2_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n5_2_9]) => n5_2_9

def numeratorCoefficient5 (a b : ℕ) : ℤ :=
  ((((((if 0 ≤ a ∧ 0 ≤ b then n5_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 0 ≤ b then n5_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 0 ≤ b then n5_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))) +
    (((if 3 ≤ a ∧ 0 ≤ b then n5_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 0 ≤ b then n5_4_0Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 5 ≤ a ∧ 0 ≤ b then n5_5_0Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 6 ≤ a ∧ 0 ≤ b then n5_6_0Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)))) +
    (((if 7 ≤ a ∧ 0 ≤ b then n5_7_0Certificate.value*(((8-7).choose (a-7) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 1 ≤ b then n5_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 2 ≤ b then n5_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))) +
    (((if 1 ≤ a ∧ 1 ≤ b then n5_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 2 ≤ b then n5_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 1 ≤ b then n5_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 2 ≤ b then n5_2_2Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))))) +
    ((((if 3 ≤ a ∧ 1 ≤ b then n5_3_1Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 2 ≤ b then n5_3_2Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 1 ≤ b then n5_4_1Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0))) +
    (((if 4 ≤ a ∧ 2 ≤ b then n5_4_2Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 1 ≤ b then n5_5_1Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)) +
    ((if 5 ≤ a ∧ 2 ≤ b then n5_5_2Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 6 ≤ a ∧ 1 ≤ b then n5_6_1Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)))) +
    (((if 6 ≤ a ∧ 2 ≤ b then n5_6_2Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 3 ≤ b then n5_0_3Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 4 ≤ b then n5_0_4Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0))) +
    (((if 1 ≤ a ∧ 3 ≤ b then n5_1_3Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 4 ≤ b then n5_1_4Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 3 ≤ b then n5_2_3Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 4 ≤ b then n5_2_4Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)))))) +
    (((((if 3 ≤ a ∧ 3 ≤ b then n5_3_3Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 4 ≤ b then n5_3_4Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 3 ≤ b then n5_4_3Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0))) +
    (((if 4 ≤ a ∧ 4 ≤ b then n5_4_4Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 3 ≤ b then n5_5_3Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)) +
    ((if 5 ≤ a ∧ 4 ≤ b then n5_5_4Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 5 ≤ b then n5_0_5Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0)))) +
    (((if 0 ≤ a ∧ 6 ≤ b then n5_0_6Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 5 ≤ b then n5_1_5Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 6 ≤ b then n5_1_6Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0))) +
    (((if 2 ≤ a ∧ 5 ≤ b then n5_2_5Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 6 ≤ b then n5_2_6Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 5 ≤ b then n5_3_5Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 6 ≤ b then n5_3_6Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0))))) +
    ((((if 4 ≤ a ∧ 5 ≤ b then n5_4_5Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    ((if 4 ≤ a ∧ 6 ≤ b then n5_4_6Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 7 ≤ b then n5_0_7Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 8 ≤ b then n5_0_8Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 7 ≤ b then n5_1_7Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 8 ≤ b then n5_1_8Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 7 ≤ b then n5_2_7Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0)))) +
    ((((if 2 ≤ a ∧ 8 ≤ b then n5_2_8Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 7 ≤ b then n5_3_7Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 8 ≤ b then n5_3_8Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 9 ≤ b then n5_0_9Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0))) +
    (((if 0 ≤ a ∧ 10 ≤ b then n5_0_10Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 9 ≤ b then n5_1_9Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 10 ≤ b then n5_1_10Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 9 ≤ b then n5_2_9Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0)))))))

def n6_0_0Certificate : IntegerCoefficientCertificate n6_0_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_0]) => n6_0_0

def n6_1_0Certificate : IntegerCoefficientCertificate n6_1_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_0]) => n6_1_0

def n6_2_0Certificate : IntegerCoefficientCertificate n6_2_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_0]) => n6_2_0

def n6_3_0Certificate : IntegerCoefficientCertificate n6_3_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_0]) => n6_3_0

def n6_4_0Certificate : IntegerCoefficientCertificate n6_4_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_0]) => n6_4_0

def n6_5_0Certificate : IntegerCoefficientCertificate n6_5_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_0]) => n6_5_0

def n6_6_0Certificate : IntegerCoefficientCertificate n6_6_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_6_0]) => n6_6_0

def n6_7_0Certificate : IntegerCoefficientCertificate n6_7_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_7_0]) => n6_7_0

def n6_8_0Certificate : IntegerCoefficientCertificate n6_8_0 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_8_0]) => n6_8_0

def n6_0_1Certificate : IntegerCoefficientCertificate n6_0_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_1]) => n6_0_1

def n6_0_2Certificate : IntegerCoefficientCertificate n6_0_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_2]) => n6_0_2

def n6_1_1Certificate : IntegerCoefficientCertificate n6_1_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_1]) => n6_1_1

def n6_1_2Certificate : IntegerCoefficientCertificate n6_1_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_2]) => n6_1_2

def n6_2_1Certificate : IntegerCoefficientCertificate n6_2_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_1]) => n6_2_1

def n6_2_2Certificate : IntegerCoefficientCertificate n6_2_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_2]) => n6_2_2

def n6_3_1Certificate : IntegerCoefficientCertificate n6_3_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_1]) => n6_3_1

def n6_3_2Certificate : IntegerCoefficientCertificate n6_3_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_2]) => n6_3_2

def n6_4_1Certificate : IntegerCoefficientCertificate n6_4_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_1]) => n6_4_1

def n6_4_2Certificate : IntegerCoefficientCertificate n6_4_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_2]) => n6_4_2

def n6_5_1Certificate : IntegerCoefficientCertificate n6_5_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_1]) => n6_5_1

def n6_5_2Certificate : IntegerCoefficientCertificate n6_5_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_2]) => n6_5_2

def n6_6_1Certificate : IntegerCoefficientCertificate n6_6_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_6_1]) => n6_6_1

def n6_6_2Certificate : IntegerCoefficientCertificate n6_6_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_6_2]) => n6_6_2

def n6_7_1Certificate : IntegerCoefficientCertificate n6_7_1 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_7_1]) => n6_7_1

def n6_7_2Certificate : IntegerCoefficientCertificate n6_7_2 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_7_2]) => n6_7_2

def n6_0_3Certificate : IntegerCoefficientCertificate n6_0_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_3]) => n6_0_3

def n6_0_4Certificate : IntegerCoefficientCertificate n6_0_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_4]) => n6_0_4

def n6_1_3Certificate : IntegerCoefficientCertificate n6_1_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_3]) => n6_1_3

def n6_1_4Certificate : IntegerCoefficientCertificate n6_1_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_4]) => n6_1_4

def n6_2_3Certificate : IntegerCoefficientCertificate n6_2_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_3]) => n6_2_3

def n6_2_4Certificate : IntegerCoefficientCertificate n6_2_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_4]) => n6_2_4

def n6_3_3Certificate : IntegerCoefficientCertificate n6_3_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_3]) => n6_3_3

def n6_3_4Certificate : IntegerCoefficientCertificate n6_3_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_4]) => n6_3_4

def n6_4_3Certificate : IntegerCoefficientCertificate n6_4_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_3]) => n6_4_3

def n6_4_4Certificate : IntegerCoefficientCertificate n6_4_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_4]) => n6_4_4

def n6_5_3Certificate : IntegerCoefficientCertificate n6_5_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_3]) => n6_5_3

def n6_5_4Certificate : IntegerCoefficientCertificate n6_5_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_4]) => n6_5_4

def n6_6_3Certificate : IntegerCoefficientCertificate n6_6_3 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_6_3]) => n6_6_3

def n6_6_4Certificate : IntegerCoefficientCertificate n6_6_4 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_6_4]) => n6_6_4

def n6_0_5Certificate : IntegerCoefficientCertificate n6_0_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_5]) => n6_0_5

def n6_0_6Certificate : IntegerCoefficientCertificate n6_0_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_6]) => n6_0_6

def n6_1_5Certificate : IntegerCoefficientCertificate n6_1_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_5]) => n6_1_5

def n6_1_6Certificate : IntegerCoefficientCertificate n6_1_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_6]) => n6_1_6

def n6_2_5Certificate : IntegerCoefficientCertificate n6_2_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_5]) => n6_2_5

def n6_2_6Certificate : IntegerCoefficientCertificate n6_2_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_6]) => n6_2_6

def n6_3_5Certificate : IntegerCoefficientCertificate n6_3_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_5]) => n6_3_5

def n6_3_6Certificate : IntegerCoefficientCertificate n6_3_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_6]) => n6_3_6

def n6_4_5Certificate : IntegerCoefficientCertificate n6_4_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_5]) => n6_4_5

def n6_4_6Certificate : IntegerCoefficientCertificate n6_4_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_6]) => n6_4_6

def n6_5_5Certificate : IntegerCoefficientCertificate n6_5_5 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_5]) => n6_5_5

def n6_5_6Certificate : IntegerCoefficientCertificate n6_5_6 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_5_6]) => n6_5_6

def n6_0_7Certificate : IntegerCoefficientCertificate n6_0_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_7]) => n6_0_7

def n6_0_8Certificate : IntegerCoefficientCertificate n6_0_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_8]) => n6_0_8

def n6_1_7Certificate : IntegerCoefficientCertificate n6_1_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_7]) => n6_1_7

def n6_1_8Certificate : IntegerCoefficientCertificate n6_1_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_8]) => n6_1_8

def n6_2_7Certificate : IntegerCoefficientCertificate n6_2_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_7]) => n6_2_7

def n6_2_8Certificate : IntegerCoefficientCertificate n6_2_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_8]) => n6_2_8

def n6_3_7Certificate : IntegerCoefficientCertificate n6_3_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_7]) => n6_3_7

def n6_3_8Certificate : IntegerCoefficientCertificate n6_3_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_8]) => n6_3_8

def n6_4_7Certificate : IntegerCoefficientCertificate n6_4_7 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_7]) => n6_4_7

def n6_4_8Certificate : IntegerCoefficientCertificate n6_4_8 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_4_8]) => n6_4_8

def n6_0_9Certificate : IntegerCoefficientCertificate n6_0_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_9]) => n6_0_9

def n6_0_10Certificate : IntegerCoefficientCertificate n6_0_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_10]) => n6_0_10

def n6_1_9Certificate : IntegerCoefficientCertificate n6_1_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_9]) => n6_1_9

def n6_1_10Certificate : IntegerCoefficientCertificate n6_1_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_10]) => n6_1_10

def n6_2_9Certificate : IntegerCoefficientCertificate n6_2_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_9]) => n6_2_9

def n6_2_10Certificate : IntegerCoefficientCertificate n6_2_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_10]) => n6_2_10

def n6_3_9Certificate : IntegerCoefficientCertificate n6_3_9 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_9]) => n6_3_9

def n6_3_10Certificate : IntegerCoefficientCertificate n6_3_10 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_3_10]) => n6_3_10

def n6_0_11Certificate : IntegerCoefficientCertificate n6_0_11 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_11]) => n6_0_11

def n6_0_12Certificate : IntegerCoefficientCertificate n6_0_12 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_0_12]) => n6_0_12

def n6_1_11Certificate : IntegerCoefficientCertificate n6_1_11 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_11]) => n6_1_11

def n6_1_12Certificate : IntegerCoefficientCertificate n6_1_12 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_1_12]) => n6_1_12

def n6_2_11Certificate : IntegerCoefficientCertificate n6_2_11 :=
  evenCompactIntegerCoefficientCertified% (norm_num [n6_2_11]) => n6_2_11

def numeratorCoefficient6 (a b : ℕ) : ℤ :=
  (((((((if 0 ≤ a ∧ 0 ≤ b then n6_0_0Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 0 ≤ b then n6_1_0Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 0 ≤ b then n6_2_0Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 0 ≤ b then n6_3_0Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))) +
    (((if 4 ≤ a ∧ 0 ≤ b then n6_4_0Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 0 ≤ b then n6_5_0Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0)) +
    ((if 6 ≤ a ∧ 0 ≤ b then n6_6_0Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    ((if 7 ≤ a ∧ 0 ≤ b then n6_7_0Certificate.value*(((8-7).choose (a-7) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0) +
    (if 8 ≤ a ∧ 0 ≤ b then n6_8_0Certificate.value*(((8-8).choose (a-8) : ℕ) : ℤ)*(((12-0).choose (b-0) : ℕ) : ℤ) else 0))))) +
    ((((if 0 ≤ a ∧ 1 ≤ b then n6_0_1Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 2 ≤ b then n6_0_2Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 1 ≤ b then n6_1_1Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 2 ≤ b then n6_1_2Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0))) +
    (((if 2 ≤ a ∧ 1 ≤ b then n6_2_1Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 2 ≤ b then n6_2_2Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 1 ≤ b then n6_3_1Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 2 ≤ b then n6_3_2Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 1 ≤ b then n6_4_1Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)))))) +
    (((((if 4 ≤ a ∧ 2 ≤ b then n6_4_2Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 1 ≤ b then n6_5_1Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)) +
    ((if 5 ≤ a ∧ 2 ≤ b then n6_5_2Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 6 ≤ a ∧ 1 ≤ b then n6_6_1Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0))) +
    (((if 6 ≤ a ∧ 2 ≤ b then n6_6_2Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    (if 7 ≤ a ∧ 1 ≤ b then n6_7_1Certificate.value*(((8-7).choose (a-7) : ℕ) : ℤ)*(((12-1).choose (b-1) : ℕ) : ℤ) else 0)) +
    ((if 7 ≤ a ∧ 2 ≤ b then n6_7_2Certificate.value*(((8-7).choose (a-7) : ℕ) : ℤ)*(((12-2).choose (b-2) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 3 ≤ b then n6_0_3Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 4 ≤ b then n6_0_4Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0))))) +
    ((((if 1 ≤ a ∧ 3 ≤ b then n6_1_3Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 4 ≤ b then n6_1_4Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 3 ≤ b then n6_2_3Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    ((if 2 ≤ a ∧ 4 ≤ b then n6_2_4Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 3 ≤ b then n6_3_3Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)))) +
    (((if 3 ≤ a ∧ 4 ≤ b then n6_3_4Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 3 ≤ b then n6_4_3Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0)) +
    ((if 4 ≤ a ∧ 4 ≤ b then n6_4_4Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0) +
    ((if 5 ≤ a ∧ 3 ≤ b then n6_5_3Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 4 ≤ b then n6_5_4Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0))))))) +
    ((((((if 6 ≤ a ∧ 3 ≤ b then n6_6_3Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-3).choose (b-3) : ℕ) : ℤ) else 0) +
    (if 6 ≤ a ∧ 4 ≤ b then n6_6_4Certificate.value*(((8-6).choose (a-6) : ℕ) : ℤ)*(((12-4).choose (b-4) : ℕ) : ℤ) else 0)) +
    ((if 0 ≤ a ∧ 5 ≤ b then n6_0_5Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 6 ≤ b then n6_0_6Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0))) +
    (((if 1 ≤ a ∧ 5 ≤ b then n6_1_5Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 6 ≤ b then n6_1_6Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 5 ≤ b then n6_2_5Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0) +
    ((if 2 ≤ a ∧ 6 ≤ b then n6_2_6Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 5 ≤ b then n6_3_5Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0))))) +
    ((((if 3 ≤ a ∧ 6 ≤ b then n6_3_6Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 5 ≤ b then n6_4_5Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0)) +
    ((if 4 ≤ a ∧ 6 ≤ b then n6_4_6Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 5 ≤ a ∧ 5 ≤ b then n6_5_5Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-5).choose (b-5) : ℕ) : ℤ) else 0))) +
    (((if 5 ≤ a ∧ 6 ≤ b then n6_5_6Certificate.value*(((8-5).choose (a-5) : ℕ) : ℤ)*(((12-6).choose (b-6) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 7 ≤ b then n6_0_7Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0)) +
    ((if 0 ≤ a ∧ 8 ≤ b then n6_0_8Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 7 ≤ b then n6_1_7Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 8 ≤ b then n6_1_8Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0)))))) +
    (((((if 2 ≤ a ∧ 7 ≤ b then n6_2_7Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 8 ≤ b then n6_2_8Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0)) +
    ((if 3 ≤ a ∧ 7 ≤ b then n6_3_7Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 8 ≤ b then n6_3_8Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0))) +
    (((if 4 ≤ a ∧ 7 ≤ b then n6_4_7Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-7).choose (b-7) : ℕ) : ℤ) else 0) +
    (if 4 ≤ a ∧ 8 ≤ b then n6_4_8Certificate.value*(((8-4).choose (a-4) : ℕ) : ℤ)*(((12-8).choose (b-8) : ℕ) : ℤ) else 0)) +
    ((if 0 ≤ a ∧ 9 ≤ b then n6_0_9Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0) +
    ((if 0 ≤ a ∧ 10 ≤ b then n6_0_10Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0) +
    (if 1 ≤ a ∧ 9 ≤ b then n6_1_9Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0))))) +
    ((((if 1 ≤ a ∧ 10 ≤ b then n6_1_10Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 9 ≤ b then n6_2_9Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0)) +
    ((if 2 ≤ a ∧ 10 ≤ b then n6_2_10Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0) +
    ((if 3 ≤ a ∧ 9 ≤ b then n6_3_9Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-9).choose (b-9) : ℕ) : ℤ) else 0) +
    (if 3 ≤ a ∧ 10 ≤ b then n6_3_10Certificate.value*(((8-3).choose (a-3) : ℕ) : ℤ)*(((12-10).choose (b-10) : ℕ) : ℤ) else 0)))) +
    (((if 0 ≤ a ∧ 11 ≤ b then n6_0_11Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-11).choose (b-11) : ℕ) : ℤ) else 0) +
    (if 0 ≤ a ∧ 12 ≤ b then n6_0_12Certificate.value*(((8-0).choose (a-0) : ℕ) : ℤ)*(((12-12).choose (b-12) : ℕ) : ℤ) else 0)) +
    ((if 1 ≤ a ∧ 11 ≤ b then n6_1_11Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-11).choose (b-11) : ℕ) : ℤ) else 0) +
    ((if 1 ≤ a ∧ 12 ≤ b then n6_1_12Certificate.value*(((8-1).choose (a-1) : ℕ) : ℤ)*(((12-12).choose (b-12) : ℕ) : ℤ) else 0) +
    (if 2 ≤ a ∧ 11 ≤ b then n6_2_11Certificate.value*(((8-2).choose (a-2) : ℕ) : ℤ)*(((12-11).choose (b-11) : ℕ) : ℤ) else 0))))))))

def rowCoefficient (a b : ℕ) : ℝ :=
  (numeratorCoefficient6 a b : ℝ)/501530650214400000000000000000000-3*(numeratorCoefficient5 a b : ℝ)/13931406950400000000000000000-(numeratorCoefficient4 a b : ℝ)/128994508800000000000000+8*(numeratorCoefficient3 a b : ℝ)/10749542400000000000-(31/8)*(numeratorCoefficient2 a b : ℝ)/298598400000000-(3/8)*(numeratorCoefficient1 a b : ℝ)/8294400000+(15/64)*(numeratorCoefficient0 a b : ℝ)/230400+ (((12 : ℕ).choose b : ℕ) : ℝ)*(
      (((8 : ℕ).choose a : ℕ) : ℝ)*((341/480 : ℝ)*(3*(341/480)-(6/19))-1/100)+
      (if 1 ≤ a then (((7 : ℕ).choose (a-1) : ℕ) : ℝ)*(35/480)*(6*(341/480)-(6/19)) else 0)+
      (if 2 ≤ a then (((6 : ℕ).choose (a-2) : ℕ) : ℝ)*3*(35/480)^(2 : ℕ) else 0))

end
end HTGeometry.EvenCompactBernstein
