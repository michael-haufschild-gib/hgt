import GaloisForLFunctions.HTGeometry.RittHomogeneousBaseRelation
import GaloisForLFunctions.HTGeometry.RittScalingDenominatorEigen

/-!
# A monomial tower element at a scaling level splits its relation

The degenerate branch of the tower descent survives only when the sliced fraction is a *monomial* in
its coordinate: `W = u · t^d` with `u` in the coefficient field.  At a level where the shift acts on
the coordinate by a pure scaling, `σ t = a·t`, such a `W` turns the relation

`σ W = c·W + γ`,  `γ` in the coefficient field,

into a comparison of the two powers `t^d` and `t^(0 : ℕ)`.  Transcendence of `t` separates them, so for
`d ≠ 0` the inhomogeneity has to vanish and what is left is the *homogeneous* eigen-relation
`φ(u)·a^d = c·u`; for `d = 0` the element was already in the coefficient field.

Together with `exists_rittForm_of_scaling_eigen` this says: a monomial element at a scaling level of
the jet tower either yields Ritt's order-one relation outright, or is not really a new level at all.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- A transcendental element has no nonzero integer power in the coefficient field. -/
theorem zpow_notMem_of_transcendental {t : L} (ht : Transcendental E t) {d : ℤ} (hd : d ≠ 0)
    {w : E} : t ^ d ≠ algebraMap E L w := by
  intro h
  have ht0 : t ≠ 0 := by
    intro h0
    exact ht (by rw [h0]; exact isAlgebraic_zero)
  refine ht ?_
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · -- negative exponent: use the inverse
    refine ⟨X ^ (-d).toNat - C w⁻¹, ?_, ?_⟩
    · intro h0
      have := congrArg (fun p : E[X] => p.coeff (-d).toNat) h0
      simp only [coeff_sub, coeff_X_pow, coeff_C, coeff_zero] at this
      rw [if_neg (by omega : ¬ (-d).toNat = 0)] at this
      simp at this
    · have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact (zpow_ne_zero _ ht0) h
      have hinv : t ^ (-d) = algebraMap E L w⁻¹ := by
        rw [zpow_neg, h, ← map_inv₀]
      rw [map_sub, map_pow, aeval_X, aeval_C]
      rw [← zpow_natCast t ((-d).toNat), Int.toNat_of_nonneg (by omega), hinv]
      ring
  · refine ⟨X ^ d.toNat - C w, ?_, ?_⟩
    · intro h0
      have := congrArg (fun p : E[X] => p.coeff d.toNat) h0
      simp only [coeff_sub, coeff_X_pow, coeff_C, coeff_zero] at this
      rw [if_neg (by omega : ¬ d.toNat = 0)] at this
      simp at this
    · rw [map_sub, map_pow, aeval_X, aeval_C]
      rw [← zpow_natCast t d.toNat, Int.toNat_of_nonneg (by omega), h]
      ring

/-- **The monomial split.**  At a scaling level a monomial element with nonzero exponent forces its
inhomogeneity to vanish and leaves a homogeneous eigen-relation for its coefficient. -/
theorem monomial_scaling_split (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a c γ : E}
    (hσt : σ t = algebraMap E L a * t)
    {u : E} {d : ℤ} (hd : d ≠ 0)
    (hrel : σ (algebraMap E L u * t ^ d)
      = algebraMap E L c * (algebraMap E L u * t ^ d) + algebraMap E L γ) :
    γ = 0 ∧ φ u * a ^ d = c * u := by
  have ht0 : t ≠ 0 := by
    intro h0
    exact ht (by rw [h0]; exact isAlgebraic_zero)
  have hσW : σ (algebraMap E L u * t ^ d)
      = algebraMap E L (φ u * a ^ d) * t ^ d := by
    rw [map_mul, map_zpow₀, hcomp, hσt, mul_zpow, ← map_zpow₀,
      show algebraMap E L (φ u * a ^ d) = algebraMap E L (φ u) * algebraMap E L (a ^ d) from
        map_mul _ _ _]
    ring
  rw [hσW] at hrel
  have hsplit : algebraMap E L (φ u * a ^ d - c * u) * t ^ d = algebraMap E L γ := by
    rw [map_sub, map_mul, map_mul, sub_mul]
    rw [map_mul] at hrel
    linear_combination hrel
  by_cases hA : φ u * a ^ d - c * u = 0
  · constructor
    · have : algebraMap E L γ = 0 := by rw [← hsplit, hA, map_zero, zero_mul]
      exact (map_eq_zero_iff _ (algebraMap E L).injective).mp this
    · linear_combination hA
  · exfalso
    have hAL : algebraMap E L (φ u * a ^ d - c * u) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap E L).injective).mpr hA
    refine zpow_notMem_of_transcendental ht hd (w := γ / (φ u * a ^ d - c * u)) ?_
    rw [map_div₀, eq_div_iff hAL, mul_comm]
    exact hsplit

end GaloisForLFunctions.HTGeometry
