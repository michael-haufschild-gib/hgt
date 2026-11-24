import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HolomorphicLefschetzCorrespondence
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LefschetzDeterminantSum

/-! The exterior-degree generating function of the Hodge traces of a
finite étale correspondence is a sum of local determinant ratios. -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperTheory.Cb
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.T

/-- Weight the alternating Hodge trace in exterior degree `p` by
`(-z)^p` and evaluate the local cotangent polynomial at `-z`. -/
theorem lefschetz_weighted_fixedPoint_finite_etale_correspondence
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Z Y : Scheme.{0}} {s : Z ⟶ Spec (CommRingCat.of k)}
    {t : Y ⟶ Spec (CommRingCat.of k)}
    {d : ℕ} [SmoothOfRelativeDimension d s] {c₁ c₂ : Y ⟶ Z}
    [IsFinite c₁] [Etale c₁] [IsFinite c₂] [Etale c₂]
    (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t)
    (hp : IsProjOver s) (S : Finset (Y.BaseFieldPointOver k t))
    (hS : ∀ x, x ∈ S ↔ x.hom ≫ c₁ = x.hom ≫ c₂)
    (M : Y.BaseFieldPointOver k t → Matrix (Fin d) (Fin d) k)
    (hM : ∀ x ∈ S, W1.IsTan d h₁ h₂ x (M x) ∧ (1 - M x).det ≠ 0) (z : k) :
    ∑ p ∈ Finset.range (d + 1), (-z) ^ p *
      ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q *
        LinearMap.trace k _ (hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q) =
      ∑ x ∈ S, (1 - z • M x).det / (1 - M x).det := by
  have htrace (p : ℕ) :=
    (lefschetz_fixedPoint_finite_etale_correspondence (h₁ := h₁) (h₂ := h₂) hp S hS M hM p).2
  simp_rw [htrace, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => PD.sum_lefschetzCoefficients (M x) z

end GlobalTheory.T
