import GaloisForLFunctions.HTGeometry.PolynomialEulerJet

/-!
# Hasse reconstruction for Euler jets

At finitely many nonzero nodes, derivative jets and Euler-operator jets are related by a
bijective triangular transform.  This file packages that fact as an exact local-global
classification: every Euler packet has a unique derivative packet, equality is detected after
the transform, and the only packet with zero Euler data is zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Derivative-jet packets are linearly equivalent to their Euler-jet local profiles at nonzero
nodes. -/
def eulerTransformHasseEquiv
    {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ) :
    (Fin K × Fin m → ℂ) ≃ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  LinearEquiv.ofBijective (eulerTransform x m)
    ⟨eulerTransform_injective hx0 m, eulerTransform_surjective hx0 m⟩

/-- The Hasse equivalence evaluates as the original triangular Euler transform. -/
@[simp] theorem eulerTransformHasseEquiv_apply
    {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ)
    (v : Fin K × Fin m → ℂ) :
    eulerTransformHasseEquiv hx0 m v = eulerTransform x m v := rfl

/-- Two derivative packets agree exactly when all their Euler-jet data agree. -/
theorem eulerTransform_congr_hasse_iff
    {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ)
    (v w : Fin K × Fin m → ℂ) :
    eulerTransform x m v = eulerTransform x m w ↔ v = w :=
  (eulerTransform_injective hx0 m).eq_iff

/-- Vanishing of every Euler coordinate detects the zero derivative packet. -/
theorem eulerTransform_eq_zero_hasse_iff
    {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ)
    (v : Fin K × Fin m → ℂ) :
    eulerTransform x m v = 0 ↔ v = 0 := by
  simpa using eulerTransform_congr_hasse_iff hx0 m v 0

/-- Every finite local Euler packet has one and only one derivative-jet antecedent. -/
theorem eulerTransform_existsUnique_preimage
    {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ)
    (J : Fin K × Fin m → ℂ) :
    ∃! v, eulerTransform x m v = J := by
  exact (eulerTransformHasseEquiv hx0 m).bijective.existsUnique J

end


end GaloisForLFunctions.HTGeometry
