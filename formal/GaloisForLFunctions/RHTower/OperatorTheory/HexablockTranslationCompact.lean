import GaloisForLFunctions.RHTower.OperatorTheory.HexablockTranslations
import GaloisForLFunctions.HTGeometry.UnitaryCompactCommutant
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixOrientationAsymmetry
import GaloisForLFunctions.«arithmetic-positivity-theory».SpectralRealisationAndOperatorConstraints

/-!
# Compact rigidity of translation Brown–Halmos operators

Every nonzero real translation has no eigenvectors: its powers escape weakly,
whereas an eigenvector would retain a constant nonzero matrix-coefficient norm.
The compact-commutant theorem therefore gives a sharp classification. A compact
operator satisfies the translation slice exactly when the displacement or the
operator is zero.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.Hexablock
open GaloisForLFunctions.ArithmeticPositivityTheory
open MeasureTheory MellinL2 Filter Topology
open scoped InnerProductSpace

/-- Every eigenvector of a nonzero real translation is zero. -/
theorem additiveTranslation_hasNoEigenvectors {b : ℝ} (hb : b ≠ 0) :
    HasNoEigenvectors (additiveTranslationUnitary b) := by
  intro x μ hx
  by_contra hx0
  have hnorm := congrArg norm hx
  rw [LinearIsometryEquiv.norm_map, norm_smul] at hnorm
  have hμ : ‖μ‖ = 1 := by
    nlinarith only [hnorm, norm_pos_iff.mpr hx0]
  have hpow (n : ℕ) : additiveTranslationUnitary ((n : ℝ) * b) x = μ ^ n • x := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, additiveTranslationUnitary_zero_apply,
        pow_zero, one_smul]
    | succ n ih =>
      have he : ((n + 1 : ℕ) : ℝ) * b = b + (n : ℝ) * b := by push_cast; ring
      rw [he, ← additiveTranslationUnitary_add_apply, ih, map_smul, hx,
        smul_smul, pow_succ]
  have hescape : Tendsto (fun n : ℕ => |(n : ℝ) * b|) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (abs_pos.mpr hb)
    have he (n : ℕ) : |(n : ℝ) * b| = (n : ℝ) * |b| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    simpa only [he] using h
  have hlim := (tendsto_inner_additiveTranslationUnitary_of_abs_atTop hescape x x).norm
  have he (n : ℕ) : ‖⟪x, additiveTranslationUnitary ((n : ℝ) * b) x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    rw [hpow, inner_smul_right, norm_mul, norm_pow, hμ, one_pow, one_mul,
      inner_self_eq_norm_sq_to_K, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x)]
  have hz : ‖x‖ ^ 2 = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [he, norm_zero] using hlim)
  exact (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hx0))) hz

/-- The exact compact boundary: only zero displacement permits a nonzero compact fixed operator. -/
theorem hexablock_translation_compact_iff (b : ℝ)
    (T : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2) :
    (BrownHalmos (halfDiff (unitaryOp (additiveTranslationUnitary b)) 1)
      (halfSum (unitaryOp (additiveTranslationUnitary b)) 1)
      (halfSum (unitaryOp (additiveTranslationUnitary b)) 1)
      (unitaryOp (additiveTranslationUnitary b)) T ∧ IsCompactOperator T) ↔
    IsCompactOperator T ∧ (b = 0 ∨ T = 0) := by
  rw [hexablock_translation_brownHalmos_iff]
  constructor
  · rintro ⟨hcomm, hc⟩
    refine ⟨hc, ?_⟩
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      apply eq_zero_of_isCompactOperator_of_comm (additiveTranslation_hasNoEigenvectors hb) hc
      intro x
      exact congrArg (fun R : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 => R x) hcomm.eq
  · rintro ⟨hc, hb | hT⟩
    · subst b
      have hzero : unitaryOp (additiveTranslationUnitary 0) = 1 := by
        apply ContinuousLinearMap.ext
        intro x
        exact additiveTranslationUnitary_zero_apply x
      exact ⟨by rw [hzero]; exact Commute.one_right _, hc⟩
    · subst T
      exact ⟨Commute.zero_left _, hc⟩

end RHTower

#print axioms RHTower.additiveTranslation_hasNoEigenvectors
#print axioms RHTower.hexablock_translation_compact_iff
