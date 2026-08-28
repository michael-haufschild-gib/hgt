import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRetainedBoxExactClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateCeilRootedError

/-!
# Literal parameters in Matomäki--Teräväinen Proposition 2.2

Real powers are kept as the paper states them.  Natural source cutoffs use ceilings, which encode
strict inequalities on natural prime and product variables exactly.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

def mtProposition22ZReal (X : ℝ) : ℝ := X ^ (2 / 11 : ℝ)

def mtProposition22QReal (X : ℝ) : ℝ := 2 * X ^ (1 / 2 : ℝ)

def mtProposition22DReal (X epsilon : ℝ) : ℝ := X ^ (1 / 4 - 2 * epsilon)

def mtProposition22EReal (X epsilon : ℝ) : ℝ := X ^ (1 - 2 * epsilon)

def mtProposition22ZNat (X : ℝ) : ℕ := Nat.ceil (mtProposition22ZReal X)

def mtProposition22QNat (X : ℝ) : ℕ := Nat.ceil (mtProposition22QReal X)

def mtProposition22DNat (X epsilon : ℝ) : ℕ :=
  Nat.ceil (mtProposition22DReal X epsilon)

def mtProposition22ENat (X epsilon : ℝ) : ℕ :=
  Nat.ceil (mtProposition22EReal X epsilon)

theorem nat_lt_mtProposition22ZNat_iff (X : ℝ) (n : ℕ) :
    n < mtProposition22ZNat X ↔ (n : ℝ) < mtProposition22ZReal X := by
  exact Nat.lt_ceil

theorem nat_lt_mtProposition22QNat_iff (X : ℝ) (n : ℕ) :
    n < mtProposition22QNat X ↔ (n : ℝ) < mtProposition22QReal X := by
  exact Nat.lt_ceil

theorem nat_lt_mtProposition22DNat_iff (X epsilon : ℝ) (n : ℕ) :
    n < mtProposition22DNat X epsilon ↔ (n : ℝ) < mtProposition22DReal X epsilon := by
  exact Nat.lt_ceil

theorem nat_lt_mtProposition22ENat_iff (X epsilon : ℝ) (n : ℕ) :
    n < mtProposition22ENat X epsilon ↔ (n : ℝ) < mtProposition22EReal X epsilon := by
  exact Nat.lt_ceil

theorem mtProposition22ZNat_le_nat_iff (X : ℝ) (n : ℕ) :
    mtProposition22ZNat X ≤ n ↔ mtProposition22ZReal X ≤ (n : ℝ) := by
  exact Nat.ceil_le

theorem mtProposition22QNat_le_nat_iff (X : ℝ) (n : ℕ) :
    mtProposition22QNat X ≤ n ↔ mtProposition22QReal X ≤ (n : ℝ) := by
  exact Nat.ceil_le

theorem mtProposition22DNat_le_nat_iff (X epsilon : ℝ) (n : ℕ) :
    mtProposition22DNat X epsilon ≤ n ↔ mtProposition22DReal X epsilon ≤ (n : ℝ) := by
  exact Nat.ceil_le

theorem mtProposition22ENat_le_nat_iff (X epsilon : ℝ) (n : ℕ) :
    mtProposition22ENat X epsilon ≤ n ↔ mtProposition22EReal X epsilon ≤ (n : ℝ) := by
  exact Nat.ceil_le

@[simp] theorem mtProposition22ZNat_eq_ceil (X : ℝ) :
    mtProposition22ZNat X = Nat.ceil (X ^ (2 / 11 : ℝ)) := rfl

@[simp] theorem mtProposition22QNat_eq_ceil (X : ℝ) :
    mtProposition22QNat X = Nat.ceil (2 * X ^ (1 / 2 : ℝ)) := rfl

@[simp] theorem mtProposition22DNat_eq_ceil (X epsilon : ℝ) :
    mtProposition22DNat X epsilon = Nat.ceil (X ^ (1 / 4 - 2 * epsilon)) := rfl

@[simp] theorem mtProposition22ENat_eq_ceil (X epsilon : ℝ) :
    mtProposition22ENat X epsilon = Nat.ceil (X ^ (1 - 2 * epsilon)) := rfl

end


end RHTower.Sieve
