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

/-- Closed upper bound for the node polynomial at a later natural sample. -/
theorem initialSamplePoints_sample_factor_upper (S q sample : ℕ) :
    ‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ ≤
      ((sample + S : ℕ) : ℝ) ^ (q * S) := by
  rw [norm_prod]
  simp_rw [norm_pow]
  calc
    ∏ z ∈ initialSamplePoints S, ‖(sample : ℂ) - z‖ ^ q ≤
        ∏ _z ∈ initialSamplePoints S, ((sample + S : ℕ) : ℝ) ^ q := by
      apply Finset.prod_le_prod
      · intro z hz
        positivity
      · intro z hz
        gcongr
        calc
          ‖(sample : ℂ) - z‖ ≤ ‖(sample : ℂ)‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ (sample : ℝ) + S := by
            rw [Complex.norm_natCast]
            exact add_le_add le_rfl (norm_le_card_of_mem_initialSamplePoints hz)
          _ = ((sample + S : ℕ) : ℝ) := by norm_num
    _ = ((sample + S : ℕ) : ℝ) ^ (q * S) := by
      rw [Finset.prod_const, card_initialSamplePoints, pow_mul]

/-- Direct finite-sum growth bound for a shifted component on a closed disc. -/
noncomputable def Relation.auxiliaryComponentAnalyticBound (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (radius : ℝ) : ℝ :=
  ∑ m, (∏ i : R.NonPivot pivot,
      ‖R.coeffEmbedding (R.scaledDirection c pivot m i)‖ ^ ν i) *
    ‖R.integralCoeffEmbedding (η m)‖ *
      Real.exp (‖R.frequency m‖ * radius)

/-- A uniform house bound for the Siegel-kernel coefficients controls the analytic boundary sum
under the distinguished embedding. -/
theorem Relation.auxiliaryComponentAnalyticBound_le_of_coefficient_house_le
    (R : Relation) (c : ℤ) (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ)
    {L : ℕ} (η : R.Column L → 𝓞 R.CoefficientField) (radius Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη) :
    R.auxiliaryComponentAnalyticBound c pivot ν η radius ≤
      ∑ m : R.Column L, (∏ i : R.NonPivot pivot,
        house (R.scaledDirection c pivot m i) ^ ν i) * Hη *
          Real.exp (‖R.frequency m‖ * radius) := by
  unfold Relation.auxiliaryComponentAnalyticBound
  apply Finset.sum_le_sum
  intro m hm
  have hdir : (∏ i : R.NonPivot pivot,
      ‖R.coeffEmbedding (R.scaledDirection c pivot m i)‖ ^ ν i) ≤
      ∏ i : R.NonPivot pivot,
        house (R.scaledDirection c pivot m i) ^ ν i := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_embedding_le_house (R.scaledDirection c pivot m i) R.coeffEmbedding) _
  have hcoeff : ‖R.integralCoeffEmbedding (η m)‖ ≤ Hη := by
    change ‖R.coeffEmbedding
      ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m))‖ ≤ Hη
    exact (norm_embedding_le_house _ R.coeffEmbedding).trans (hη m)
  calc
    (∏ i : R.NonPivot pivot,
        ‖R.coeffEmbedding (R.scaledDirection c pivot m i)‖ ^ ν i) *
          ‖R.integralCoeffEmbedding (η m)‖ * Real.exp (‖R.frequency m‖ * radius) ≤
        (∏ i : R.NonPivot pivot,
          house (R.scaledDirection c pivot m i) ^ ν i) *
          ‖R.integralCoeffEmbedding (η m)‖ * Real.exp (‖R.frequency m‖ * radius) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdir (norm_nonneg _)) (Real.exp_nonneg _)
    _ ≤ (∏ i : R.NonPivot pivot,
          house (R.scaledDirection c pivot m i) ^ ν i) * Hη *
            Real.exp (‖R.frequency m‖ * radius) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoeff
          (Finset.prod_nonneg fun i hi => pow_nonneg (house_nonneg _) _))
        (Real.exp_nonneg _)

/-- Closed analytic boundary bound in terms of the column count, direction height, coefficient
height, and the fixed prime-log weight. -/
theorem Relation.auxiliaryComponentAnalyticBound_le_closed
    (R : Relation) (c : ℤ) (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ)
    {L : ℕ} (η : R.Column L → 𝓞 R.CoefficientField) (radius Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη) (hradius : 0 ≤ radius) :
    R.auxiliaryComponentAnalyticBound c pivot ν η radius ≤
      ((L ^ R.n : ℕ) : ℝ) *
        ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
          Real.exp ((L * R.primeLogWeight) * radius)) := by
  calc
    R.auxiliaryComponentAnalyticBound c pivot ν η radius ≤
        ∑ m : R.Column L, (∏ i : R.NonPivot pivot,
          house (R.scaledDirection c pivot m i) ^ ν i) * Hη *
            Real.exp (‖R.frequency m‖ * radius) :=
      R.auxiliaryComponentAnalyticBound_le_of_coefficient_house_le
        c pivot ν η radius Hη hη
    _ ≤ ∑ _m : R.Column L,
        (2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
          Real.exp ((L * R.primeLogWeight) * radius) := by
      apply Finset.sum_le_sum
      intro m hm
      have hdir := R.scaledDirection_house_prod_pow_le c pivot m ν
      have hexp : Real.exp (‖R.frequency m‖ * radius) ≤
          Real.exp ((L * R.primeLogWeight) * radius) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (R.norm_frequency_le m) hradius
      calc
        (∏ i : R.NonPivot pivot,
          house (R.scaledDirection c pivot m i) ^ ν i) * Hη *
            Real.exp (‖R.frequency m‖ * radius) ≤
            (2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
              Real.exp (‖R.frequency m‖ * radius) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hdir hHη) (Real.exp_nonneg _)
        _ ≤ (2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
              Real.exp ((L * R.primeLogWeight) * radius) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact mul_nonneg (pow_nonneg (by
            unfold Relation.scaledCoefficientHouseSum
            exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
              (Finset.sum_nonneg fun i hi => house_nonneg _)) _) hHη
    _ = _ := by
      simp [nsmul_eq_mul]

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

/-- One-step extrapolation with the analytic and conjugate estimates reduced to closed scalar
bounds.  The remaining inequality contains only the construction parameters and fixed invariants of
the reduced relation. -/
theorem Relation.auxiliaryComponent_eq_zero_one_step_closed
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (ν : R.NonPivot pivot → ℕ) (q : ℕ) (hνq : ∀ i, ν i + q < T)
    (Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη)
    {radius : ℝ} (hradius : (S : ℝ) < radius)
    (sample : ℕ) (hsample : (sample : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall :
      (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            (R.primeProduct : ℝ) ^ (L * sample))) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  apply R.auxiliaryComponent_eq_zero_one_step_explicit
    c hc hint pivot η hker ν q hνq hradius sample hsample
  have hradius0 : 0 ≤ radius :=
    le_trans (Nat.cast_nonneg S) hradius.le
  have hA := R.auxiliaryComponentAnalyticBound_le_closed
    c pivot ν η radius Hη hη hHη hradius0
  have hH := R.auxiliaryComponentHouseBound_le_closed
    c pivot ν η sample Hη hη hHη
  have hA0 : 0 ≤ R.auxiliaryComponentAnalyticBound c pivot ν η radius := by
    unfold Relation.auxiliaryComponentAnalyticBound
    exact Finset.sum_nonneg fun m hm =>
      mul_nonneg (mul_nonneg
        (Finset.prod_nonneg fun i hi => pow_nonneg (norm_nonneg _) _)
        (norm_nonneg _)) (Real.exp_nonneg _)
  have hH0 := R.auxiliaryComponentHouseBound_nonneg c pivot ν η sample
  have hden : 0 < (radius - S) ^ (q * S) :=
    pow_pos (sub_pos.mpr hradius) _
  have hdiv := div_le_div_of_nonneg_right hA hden.le
  have hpow := pow_le_pow_left₀ hH0 hH
    (Module.finrank ℚ R.CoefficientField - 1)
  calc
    (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
        (R.auxiliaryComponentAnalyticBound c pivot ν η radius /
          (radius - S) ^ (q * S))) *
      R.auxiliaryComponentHouseBound c pivot ν η sample ^
        (Module.finrank ℚ R.CoefficientField - 1) ≤
      (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
      R.auxiliaryComponentHouseBound c pivot ν η sample ^
        (Module.finrank ℚ R.CoefficientField - 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
      · exact pow_nonneg hH0 _
    _ ≤ (‖∏ z ∈ initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            (R.primeProduct : ℝ) ^ (L * sample))) ^
          (Module.finrank ℚ R.CoefficientField - 1) := by
      apply mul_le_mul_of_nonneg_left hpow
      exact mul_nonneg (norm_nonneg _)
        (div_nonneg (hA0.trans hA) hden.le)
    _ < 1 := hsmall

/-- Fully scalar one-step extrapolation.  The node product is replaced by its closed natural-sample
bound, leaving no finite sums or products in the smallness hypothesis. -/
theorem Relation.auxiliaryComponent_eq_zero_one_step_scalar
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (ν : R.NonPivot pivot → ℕ) (q : ℕ) (hνq : ∀ i, ν i + q < T)
    (Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη)
    {radius : ℝ} (hradius : (S : ℝ) < radius)
    (sample : ℕ) (hsample : (sample : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall :
      (((sample + S : ℕ) : ℝ) ^ (q * S) *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) * Hη *
            (R.primeProduct : ℝ) ^ (L * sample))) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  apply R.auxiliaryComponent_eq_zero_one_step_closed
    c hc hint pivot η hker ν q hνq Hη hη hHη hradius sample hsample
  have hA := R.auxiliaryComponentAnalyticBound_le_closed
    c pivot ν η radius Hη hη hHη
      (le_trans (Nat.cast_nonneg S) hradius.le)
  have hA0 : 0 ≤ R.auxiliaryComponentAnalyticBound c pivot ν η radius := by
    unfold Relation.auxiliaryComponentAnalyticBound
    exact Finset.sum_nonneg fun m hm =>
      mul_nonneg (mul_nonneg
        (Finset.prod_nonneg fun i hi => pow_nonneg (norm_nonneg _) _)
        (norm_nonneg _)) (Real.exp_nonneg _)
  have hH := R.auxiliaryComponentHouseBound_le_closed
    c pivot ν η sample Hη hη hHη
  have hH0 := R.auxiliaryComponentHouseBound_nonneg c pivot ν η sample
  have hden : 0 ≤ (radius - S) ^ (q * S) :=
    (pow_pos (sub_pos.mpr hradius) _).le
  apply lt_of_le_of_lt _ hsmall
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact initialSamplePoints_sample_factor_upper S q sample
    · exact div_nonneg (hA0.trans hA) hden
  · exact pow_nonneg (hH0.trans hH) _

end GaloisForLFunctions.RHTower.BakerProof
