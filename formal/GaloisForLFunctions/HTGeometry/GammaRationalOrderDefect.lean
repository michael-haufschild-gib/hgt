import GaloisForLFunctions.HTGeometry.GammaSumValuationBoundary

/-!
# The Gamma-rational balance premise is one integer invariant

The valuation-boundary theorems compare two Gamma-rational data through the four-term relation
`n₁ + d₂ = n₂ + d₁` (or its shifted form with an offset), and that relation was consumed with no
producer.

It is not a four-term condition.  Each datum carries a single integer, the order defect
`numOrder − denOrder`, and the balance relation says exactly that the two defects agree; the
shifted form says their difference is the offset.  Every integer occurs as a defect, so the premise
is satisfiable at every level and pairs realizing it are explicit.
-/

namespace GaloisForLFunctions

noncomputable section

namespace GammaRationalDatum

/-- The order defect of a Gamma-rational datum: the order of vanishing of its numerator minus that
of its denominator. -/
def orderDefect (D : GammaRationalDatum) : ℤ :=
  (D.numOrder : ℤ) - (D.denOrder : ℤ)

@[simp] theorem orderDefect_one : orderDefect GammaRationalDatum.one = 0 := by
  simp [orderDefect, GammaRationalDatum.one]

/-- The datum with prescribed orders of vanishing and trivial unit factors. -/
def ofOrders (a b : ℕ) : GammaRationalDatum where
  numOrder := a
  denOrder := b
  numUnit := 1
  denUnit := 1
  numUnit_ne := by simp
  denUnit_ne := by simp

@[simp] theorem orderDefect_ofOrders (a b : ℕ) :
    orderDefect (ofOrders a b) = (a : ℤ) - (b : ℤ) := rfl

/-- **Every integer is an order defect.** -/
theorem exists_orderDefect_eq (k : ℤ) : ∃ D : GammaRationalDatum, orderDefect D = k := by
  refine ⟨ofOrders k.toNat (-k).toNat, ?_⟩
  rw [orderDefect_ofOrders]
  omega

/-- **The balance premise is equality of order defects.** -/
theorem balanced_iff_orderDefect_eq (D₁ D₂ : GammaRationalDatum) :
    D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder ↔
      orderDefect D₁ = orderDefect D₂ := by
  rw [orderDefect, orderDefect]
  omega

/-- **The shifted premise measures the defect difference.** -/
theorem shifted_iff_orderDefect_sub_eq (D₁ D₂ : GammaRationalDatum) (n : ℕ) :
    D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder) ↔
      orderDefect D₁ - orderDefect D₂ = (n : ℤ) := by
  rw [orderDefect, orderDefect]
  omega

/-- Data with equal order defects satisfy the balance premise. -/
theorem balanced_of_orderDefect_eq {D₁ D₂ : GammaRationalDatum}
    (h : orderDefect D₁ = orderDefect D₂) :
    D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder :=
  (balanced_iff_orderDefect_eq D₁ D₂).mpr h

/-- A datum is balanced against itself. -/
theorem balanced_self (D : GammaRationalDatum) :
    D.numOrder + D.denOrder = D.numOrder + D.denOrder := rfl

/-- **The premise is realized at every defect.**  For every integer there is a pair of data
balanced against each other with that common defect. -/
theorem exists_balanced_pair_orderDefect_eq (k : ℤ) :
    ∃ D₁ D₂ : GammaRationalDatum,
      orderDefect D₁ = k ∧ orderDefect D₂ = k ∧
        D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder := by
  obtain ⟨D, hD⟩ := exists_orderDefect_eq k
  exact ⟨D, D, hD, hD, balanced_self D⟩

/-- And the shifted premise is realized at every offset. -/
theorem exists_shifted_pair (n : ℕ) :
    ∃ D₁ D₂ : GammaRationalDatum,
      D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder) := by
  refine ⟨ofOrders n 0, ofOrders 0 0, ?_⟩
  rw [shifted_iff_orderDefect_sub_eq, orderDefect_ofOrders, orderDefect_ofOrders]
  omega

end GammaRationalDatum

end

end GaloisForLFunctions
