import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceWindowError

/-!
# Current control on every fixed logarithmic aperture

The common source regulator absorbs any fixed logarithmic Hecke aperture.
Its compact-current error is uniform in moment order after normalization;
regularity is needed only for the omitted divisor tail.
-/

open Complex Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization

/-- Every fixed logarithmic aperture has a quadratic moving-transform envelope. -/
lemma source_regularity_window_exponent_le {b : ℝ} (hb : 0 ≤ b)
    (j n : ℕ) (L τ : ℝ) (hτ : |τ| ≤ (n : ℝ))
    (hL : (j : ℝ) * |L| ≤ b * Real.log ((n : ℝ) + 1)) :
    2 * (((n : ℝ) + 3 + |τ|) ^ 2 +
      (j : ℝ) * |L| * ((n : ℝ) + 7 / 2)) ≤
      (36 + 14 * b) * (n : ℝ) ^ 2 + (36 + 14 * b) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hlog : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
    linarith only [h]
  have hj : (j : ℝ) * |L| ≤ b * (n : ℝ) :=
    hL.trans (mul_le_mul_of_nonneg_left hlog hb)
  have hsq : ((n : ℝ) + 3 + |τ|) ^ 2 ≤ (3 * ((n : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hτ, hn]) 2
  have hp : (j : ℝ) * |L| * ((n : ℝ) + 7 / 2) ≤
      (b * ((n : ℝ) + 1)) * ((7 / 2 : ℝ) * ((n : ℝ) + 1)) := by
    apply mul_le_mul (hj.trans (mul_le_mul_of_nonneg_left (by linarith only []) hb))
      (by linarith only [hn]) (by positivity) (by positivity)
  have hquad : ((n : ℝ) + 1) ^ 2 ≤ 2 * (n : ℝ) ^ 2 + 2 := by
    nlinarith only [sq_nonneg ((n : ℝ) - 1)]
  have hmul := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 18 + 7 * b by positivity)
  nlinarith only [hsq, hp, hmul]

/-- Normalized compact-current envelope for a fixed aperture coefficient. -/
def sourceRegularityWindowError (A b : ℝ) (n : ℕ) : ℝ :=
  ((2 * Real.pi)⁻¹ * 4 * A ^ 2) *
    Real.exp (-((n : ℝ) ^ 4) + (36 + 14 * b) * (n : ℝ) ^ 2 + (36 + 14 * b))

lemma sourceRegularityWindowError_nonneg (A b : ℝ) (n : ℕ) :
    0 ≤ sourceRegularityWindowError A b n := by
  unfold sourceRegularityWindowError
  positivity

/-- The compact-current error is uniform in normalized moment order. -/
theorem sourceMomentCurrentError_le_regularity_window (f : CompactTest) {A b : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (hb : 0 ≤ b) (j n : ℕ) (L τ : ℝ) (hτ : |τ| ≤ (n : ℝ))
    (hL : (j : ℝ) * |L| ≤ b * Real.log ((n : ℝ) + 1)) :
    |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      4 ^ j * sourceRegularityWindowError A b n := by
  refine (sourceMomentCurrentError_le f hA hbound j n L τ).trans ?_
  have h := Real.exp_le_exp.mpr
    (add_le_add (show -((n : ℝ) ^ 4) ≤ -((n : ℝ) ^ 4) from le_rfl)
      (source_regularity_window_exponent_le hb j n L τ hτ hL))
  calc
    ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
        Real.exp (-((n : ℝ) ^ 4) +
          2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) ≤
      ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
        Real.exp (-((n : ℝ) ^ 4) +
          ((36 + 14 * b) * (n : ℝ) ^ 2 + (36 + 14 * b))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      unfold sourceRegularityWindowError
      rw [pow_succ]
      simp only [add_assoc]
      ring

/-- Quartic regulator decay absorbs every fixed logarithmic aperture. -/
theorem tendsto_sourceRegularityWindowError (A b : ℝ) :
    Tendsto (sourceRegularityWindowError A b) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (RiemannGaussian.tendsto_exp_neg_quadratic_add_linear_atTop
    (ε := 1) zero_lt_one 0 (36 + 14 * b) (36 + 14 * b)).comp ht
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-((n : ℝ) ^ 4) + (36 + 14 * b) * (n : ℝ) ^ 2 + (36 + 14 * b)))
      atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards with n
    change Real.exp (-1 * ((n : ℝ) ^ 2 - 0) ^ 2 +
      (36 + 14 * b) * (n : ℝ) ^ 2 + (36 + 14 * b)) = _
    congr 1
    ring
  unfold sourceRegularityWindowError
  simpa only [mul_zero] using
    he.const_mul ((2 * Real.pi)⁻¹ * 4 * A ^ 2)

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceMomentCurrentError_le_regularity_window
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_sourceRegularityWindowError
