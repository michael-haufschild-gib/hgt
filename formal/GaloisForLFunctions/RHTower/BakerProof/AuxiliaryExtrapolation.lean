import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz

/-!
# One-step Baker extrapolation

The initial matrix samples give a uniform multiplicity floor for every shifted component that stays
inside the multiindex box.  The multipoint Schwarz bound makes a later natural-sample value small;
the asymmetric algebraic-integer norm criterion then promotes that smallness to an exact new zero.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

noncomputable def initialSamplePoints (S : ℕ) : Finset ℂ :=
  Finset.univ.image (fun sample : Fin S => ((sample : ℕ) : ℂ))

theorem mem_initialSamplePoints {S : ℕ} {z : ℂ} :
    z ∈ initialSamplePoints S ↔ ∃ sample : Fin S, z = (sample : ℕ) := by
  simp [initialSamplePoints, eq_comm]

@[simp] theorem card_initialSamplePoints (S : ℕ) :
    (initialSamplePoints S).card = S := by
  rw [initialSamplePoints, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Fin.ext
    change ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) at hab
    exact_mod_cast hab

theorem norm_le_card_of_mem_initialSamplePoints {S : ℕ} {z : ℂ}
    (hz : z ∈ initialSamplePoints S) : ‖z‖ ≤ S := by
  obtain ⟨sample, rfl⟩ := mem_initialSamplePoints.mp hz
  simp only [Complex.norm_natCast]
  exact_mod_cast sample.isLt.le

/-- Explicit lower bound for the node polynomial on a circle enclosing the initial samples. -/
theorem initialSamplePoints_boundary_factor_lower {S q : ℕ} {radius : ℝ}
    (hradius : (S : ℝ) < radius) (w : ℂ) (hw : w ∈ Metric.sphere 0 radius) :
    (radius - S) ^ (q * S) ≤
      ‖∏ z ∈ initialSamplePoints S, (w - z) ^ q‖ := by
  rw [norm_prod]
  simp_rw [norm_pow]
  calc
    (radius - S) ^ (q * S) =
        ∏ _z ∈ initialSamplePoints S, (radius - S) ^ q := by
      rw [Finset.prod_const, card_initialSamplePoints, pow_mul]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro z hz
        positivity
      · intro z hz
        gcongr
        have hwNorm : ‖w‖ = radius := by
          simpa [mem_sphere_iff_norm] using hw
        have hzNorm := norm_le_card_of_mem_initialSamplePoints hz
        calc
          radius - S = ‖w‖ - S := by rw [hwNorm]
          _ ≤ ‖w‖ - ‖z‖ := sub_le_sub_left hzNorm _
          _ ≤ ‖w - z‖ := norm_sub_norm_le w z

/-- Direct finite-sum growth bound for a shifted component on a closed disc. -/
noncomputable def Relation.auxiliaryComponentAnalyticBound (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (radius : ℝ) : ℝ :=
  ∑ m, (∏ i : R.NonPivot pivot,
      ‖R.coeffEmbedding (R.scaledDirection c pivot m i)‖ ^ ν i) *
    ‖R.integralCoeffEmbedding (η m)‖ *
      Real.exp (‖R.frequency m‖ * radius)

theorem Relation.norm_auxiliaryComponent_le_analyticBound
    (R : Relation) (c : ℤ) (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ)
    {L : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    {radius : ℝ} {z : ℂ} (hz : ‖z‖ ≤ radius) :
    ‖R.auxiliaryComponent c pivot ν η z‖ ≤
      R.auxiliaryComponentAnalyticBound c pivot ν η radius := by
  unfold Relation.auxiliaryComponent Relation.auxiliaryComponentAnalyticBound
  calc
    ‖∑ m, (∏ i : R.NonPivot pivot,
        R.coeffEmbedding (R.scaledDirection c pivot m i) ^ ν i) *
      R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * z)‖
        ≤ ∑ m, ‖(∏ i : R.NonPivot pivot,
            R.coeffEmbedding (R.scaledDirection c pivot m i) ^ ν i) *
          R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * z)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_prod, norm_pow]
      gcongr
      calc
        ‖Complex.exp (R.frequency m * z)‖ ≤ Real.exp ‖R.frequency m * z‖ :=
          Complex.norm_exp_le_exp_norm _
        _ ≤ Real.exp (‖R.frequency m‖ * radius) := by
          apply Real.exp_le_exp.mpr
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

theorem Relation.auxiliaryComponent_analyticOrderAt_ge
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) (ν : R.NonPivot pivot → ℕ) (q : ℕ)
    (hνq : ∀ i, ν i + q < T) :
    q ≤ analyticOrderAt (R.auxiliaryComponent c pivot ν η) (sample : ℕ) := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero]
  · intro k hk
    apply R.auxiliaryComponent_iteratedDeriv_eq_zero_of_kernel
      c hc hint pivot η hker sample ν k
    intro i
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt hk) _) (hνq i)
  · unfold Relation.auxiliaryComponent
    fun_prop

/-- **One exact extrapolation step.**  Concrete boundary bounds feed multipoint Schwarz; if the
resulting distinguished norm times the explicit conjugate bound is below one, the later component
value vanishes exactly. -/
theorem Relation.auxiliaryComponent_eq_zero_one_step_extrapolation
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (ν : R.NonPivot pivot → ℕ) (q : ℕ) (hνq : ∀ i, ν i + q < T)
    {radius M D : ℝ} (hradius : 0 < radius) (hD : 0 < D)
    (hboundary_component : ∀ w ∈ Metric.sphere 0 radius,
      ‖R.auxiliaryComponent c pivot ν η w‖ ≤ M)
    (hboundary_factor : ∀ w ∈ Metric.sphere 0 radius,
      D ≤ ‖∏ z ∈ initialSamplePoints S, (w - z) ^ q‖)
    (sample : ℕ) (hsample : (sample : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall : (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ * (M / D)) *
      R.auxiliaryComponentHouseBound c pivot ν η sample ^
        (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  have horder : ∀ z ∈ initialSamplePoints S,
      q ≤ analyticOrderAt (R.auxiliaryComponent c pivot ν η) z := by
    intro z hz
    obtain ⟨s, rfl⟩ := mem_initialSamplePoints.mp hz
    exact R.auxiliaryComponent_analyticOrderAt_ge c hc hint pivot η hker s ν q hνq
  have hf : ∀ z, AnalyticAt ℂ (R.auxiliaryComponent c pivot ν η) z := by
    intro z
    unfold Relation.auxiliaryComponent
    fun_prop
  have hnorm := multipoint_schwarz_bound
    (R.auxiliaryComponent c pivot ν η) hf (initialSamplePoints S) q horder
    hradius hD hboundary_component hboundary_factor hsample
  apply R.auxiliaryComponent_eq_zero_of_norm_mul_houseBound_pow_lt_one
    c hint pivot ν η sample
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hnorm (pow_nonneg
      (R.auxiliaryComponentHouseBound_nonneg c pivot ν η sample) _)) hsmall

/-- One-step extrapolation with all boundary quantities discharged to the explicit finite analytic
and node-polynomial bounds.  Only the final concrete parameter inequality remains. -/
theorem Relation.auxiliaryComponent_eq_zero_one_step_explicit
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (ν : R.NonPivot pivot → ℕ) (q : ℕ) (hνq : ∀ i, ν i + q < T)
    {radius : ℝ} (hradius : (S : ℝ) < radius)
    (sample : ℕ) (hsample : (sample : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall : (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
        (R.auxiliaryComponentAnalyticBound c pivot ν η radius /
          (radius - S) ^ (q * S))) *
      R.auxiliaryComponentHouseBound c pivot ν η sample ^
        (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  apply R.auxiliaryComponent_eq_zero_one_step_extrapolation
    c hc hint pivot η hker ν q hνq
    (radius := radius)
    (M := R.auxiliaryComponentAnalyticBound c pivot ν η radius)
    (D := (radius - S) ^ (q * S))
  · exact lt_of_le_of_lt (Nat.cast_nonneg S) hradius
  · exact pow_pos (sub_pos.mpr hradius) _
  · intro w hw
    apply R.norm_auxiliaryComponent_le_analyticBound c pivot ν η
    simpa [mem_sphere_iff_norm] using hw.le
  · exact initialSamplePoints_boundary_factor_lower hradius
  · exact hsample
  · exact hsmall

end GaloisForLFunctions.RHTower.BakerProof
