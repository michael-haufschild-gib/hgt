import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The resolvent of a normal element and the distance to its spectrum

For a normal element of a C⋆-algebra the norm equals the spectral radius.  Applying that to the
resolvent, whose spectrum is the pointwise inverse of the translated spectrum, bounds the resolvent
norm by the reciprocal of the distance from the spectral parameter to the spectrum.

This is the quantitative statement that converts an exploding resolvent into a nearby spectral
point, which is what upgrades an approximate eigenvector into genuine spectral inclusion.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped NNReal ENNReal

/-- A scalar shift of a normal element is normal: the scalar part is central. -/
theorem isStarNormal_algebraMap_sub {A : Type*} [CStarAlgebra A] (a : A) [IsStarNormal a]
    (mu : ℂ) : IsStarNormal ((algebraMap ℂ A) mu - a) := by
  constructor
  have hstar : star ((algebraMap ℂ A) mu - a)
      = (algebraMap ℂ A) (starRingEnd ℂ mu) - star a := by
    rw [star_sub, ← algebraMap_star_comm]
    rfl
  rw [hstar]
  refine Commute.sub_left ?_ ?_
  · exact Commute.sub_right (Algebra.commutes _ _) (Algebra.commutes _ _)
  · exact Commute.sub_right (Algebra.commutes _ _).symm
      (IsStarNormal.star_comm_self (x := a))

/-- **The resolvent of a normal element is bounded by the reciprocal distance to the spectrum.**
If every spectral point of `a` is at distance at least `ε` from `mu`, then the resolvent at `mu`
has norm at most `1 / ε`. -/
theorem norm_inverse_le_of_spectrum_far {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a]
    {mu : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hfar : ∀ lam ∈ spectrum ℂ a, ε ≤ ‖mu - lam‖)
    (hunit : IsUnit ((algebraMap ℂ A) mu - a)) :
    ‖Ring.inverse ((algebraMap ℂ A) mu - a)‖ ≤ 1 / ε := by
  obtain ⟨U, hU⟩ := hunit
  haveI hUnormal : IsStarNormal (U : A) := by
    rw [hU]
    exact isStarNormal_algebraMap_sub a mu
  haveI hbnormal : IsStarNormal ((U⁻¹ : Aˣ) : A) := IsStarNormal.val_inv
  have hinv : Ring.inverse ((algebraMap ℂ A) mu - a) = ((U⁻¹ : Aˣ) : A) := by
    rw [← hU, Ring.inverse_unit]
  rw [hinv]
  -- every spectral point of the inverse is small
  have hspec : ∀ k ∈ spectrum ℂ ((U⁻¹ : Aˣ) : A), ‖k‖ ≤ 1 / ε := by
    intro k hk
    rw [← spectrum.map_inv U] at hk
    have hnu : k⁻¹ ∈ spectrum ℂ (U : A) := Set.mem_inv.mp hk
    have hnuU : k⁻¹ ∈ spectrum ℂ ((algebraMap ℂ A) mu - a) := by rwa [hU] at hnu
    rw [← spectrum.singleton_sub_eq a mu] at hnuU
    obtain ⟨p, hp, q, hq, hpq⟩ := hnuU
    have hval : k⁻¹ = mu - q := by
      rw [← hpq, Set.mem_singleton_iff.mp hp]
    have hge : ε ≤ ‖k‖⁻¹ := by
      rw [← norm_inv, hval]
      exact hfar q hq
    have hkne : ‖k‖ ≠ 0 := by
      intro h
      rw [h] at hge
      simp at hge
      linarith
    rw [le_div_iff₀ hε]
    have h1 : ‖k‖ * ε ≤ ‖k‖ * ‖k‖⁻¹ := mul_le_mul_of_nonneg_left hge (norm_nonneg k)
    rwa [mul_inv_cancel₀ hkne] at h1
  -- the spectral radius is bounded, and equals the norm for normal elements
  have hpos : (0:ℝ) ≤ 1 / ε := by positivity
  have hrad : spectralRadius ℂ ((U⁻¹ : Aˣ) : A) ≤ ENNReal.ofReal (1 / ε) := by
    rw [spectralRadius]
    refine iSup₂_le fun k hk => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by simpa using hspec k hk)
  rw [IsStarNormal.spectralRadius_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal] at hrad
  have hle : ((‖((U⁻¹ : Aˣ) : A)‖₊ : ℝ)) ≤ 1 / ε :=
    (ENNReal.ofReal_le_ofReal_iff hpos).mp hrad
  simpa using hle

end GaloisForLFunctions.HTGeometry
