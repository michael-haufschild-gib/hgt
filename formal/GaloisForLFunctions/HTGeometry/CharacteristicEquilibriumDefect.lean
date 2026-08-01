import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Equilibrium defects of centered characteristic functions

This module derives two universal laws.  Centered convolution powers and their compound-Poisson
mixtures have additive second moment.  Consequently, the normalized second-order defect of any
probability characteristic function with finite positive second moment is positive definite.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem memLp_id_conv_probability
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    MemLp id 2 (μ ∗ ν) := by
  rw [Measure.conv]
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  change MemLp (fun p : ℝ × ℝ => p.1 + p.2) 2 (μ.prod ν)
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

theorem integral_id_conv_probability
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    (∫ x : ℝ, x ∂(μ ∗ ν)) = (∫ x : ℝ, x ∂μ) + ∫ x : ℝ, x ∂ν := by
  have hμint : Integrable id μ := hμ.integrable (by norm_num)
  have hνint : Integrable id ν := hν.integrable (by norm_num)
  have hfst : Integrable (fun p : ℝ × ℝ => p.1) (μ.prod ν) := by
    simpa only [id_eq] using hμint.comp_fst ν
  have hsnd : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod ν) := by
    simpa only [id_eq] using hνint.comp_snd μ
  have hfstInt : (∫ p : ℝ × ℝ, p.1 ∂μ.prod ν) = ∫ x : ℝ, x ∂μ := by
    simpa only [id_eq, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (id : ℝ → ℝ))
  have hsndInt : (∫ p : ℝ × ℝ, p.2 ∂μ.prod ν) = ∫ x : ℝ, x ∂ν := by
    simpa only [id_eq, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      (integral_fun_snd (μ := μ) (ν := ν) (id : ℝ → ℝ))
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  change (∫ p : ℝ × ℝ, p.1 + p.2 ∂μ.prod ν) = _
  rw [integral_add hfst hsnd, hfstInt, hsndInt]

theorem variance_id_conv_probability
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    Var[id; μ ∗ ν] = Var[id; μ] + Var[id; ν] := by
  change Var[id; Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)] = _
  rw [variance_id_map (by fun_prop)]
  simpa only [id_eq] using (variance_add_prod hμ hν)

/-- Centered convolution powers have exactly additive second moment. -/
theorem convPow_centered_secondMoment
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : MemLp id 2 Q) (hQmean : ∫ x : ℝ, x ∂Q = 0) (n : ℕ) :
    let μ := convPow Q n
    MemLp id 2 μ ∧
      (∫ x : ℝ, x ∂μ) = 0 ∧
      (∫ x : ℝ, x ^ 2 ∂μ) = n * ∫ x : ℝ, x ^ 2 ∂Q := by
  induction n with
  | zero =>
      haveI : IsProbabilityMeasure (convPow Q 0) :=
        isProbabilityMeasure_convPow Q 0
      refine ⟨?_, ?_, ?_⟩
      · rw [convPow]
        exact (memLp_const (0 : ℝ)).ae_eq (ae_eq_dirac id).symm
      · simp [convPow]
      · simp [convPow]
  | succ n ih =>
      let μ := convPow Q n
      haveI : IsProbabilityMeasure μ := isProbabilityMeasure_convPow Q n
      rcases ih with ⟨hμ, hμmean, hμsq⟩
      have hconv := memLp_id_conv_probability Q μ hQ hμ
      have hmean := integral_id_conv_probability Q μ hQ hμ
      have hvar := variance_id_conv_probability Q μ hQ hμ
      have hQvar : Var[id; Q] = ∫ x : ℝ, x ^ 2 ∂Q :=
        variance_of_integral_eq_zero (by fun_prop) hQmean
      have hμvar : Var[id; μ] = ∫ x : ℝ, x ^ 2 ∂μ :=
        variance_of_integral_eq_zero (by fun_prop) hμmean
      have hconvmean : ∫ x : ℝ, x ∂(Q ∗ μ) = 0 := by
        rw [hmean, hQmean, hμmean, add_zero]
      have hconvsq : ∫ x : ℝ, x ^ 2 ∂(Q ∗ μ) =
          (n + 1) * ∫ x : ℝ, x ^ 2 ∂Q := by
        rw [← variance_of_integral_eq_zero (by fun_prop) hconvmean]
        change Var[id; Q ∗ μ] = _
        rw [hvar, hQvar, hμvar, hμsq]
        ring
      simpa [convPow, μ] using And.intro hconv (And.intro hconvmean hconvsq)

theorem summable_poisson_firstMoment (lam : ℝ) :
    Summable (fun n : ℕ => Real.exp (-lam) * lam ^ n / n.factorial * n) := by
  apply (summable_nat_add_iff
    (f := fun n : ℕ => Real.exp (-lam) * lam ^ n / n.factorial * n) 1).mp
  have hs := (Real.summable_pow_div_factorial lam).mul_left
    (Real.exp (-lam) * lam)
  have heq :
      (fun n : ℕ => Real.exp (-lam) * lam ^ (n + 1) /
        (n + 1).factorial * ((n + 1 : ℕ) : ℝ)) =
      fun n : ℕ => (Real.exp (-lam) * lam) * (lam ^ n / n.factorial) := by
    funext n
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring
  rw [heq]
  exact hs

theorem tsum_poisson_firstMoment (lam : ℝ) :
    (∑' n : ℕ, Real.exp (-lam) * lam ^ n / n.factorial * n) = lam := by
  have hs := summable_poisson_firstMoment lam
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  calc
    (∑' n : ℕ, Real.exp (-lam) * lam ^ (n + 1) /
        (n + 1).factorial * ((n + 1 : ℕ) : ℝ)) =
        ∑' n : ℕ, (Real.exp (-lam) * lam) * (lam ^ n / n.factorial) := by
      apply tsum_congr
      intro n
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      field_simp
      ring
    _ = (Real.exp (-lam) * lam) * Real.exp lam := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = lam := by
      calc
        _ = lam * (Real.exp (-lam) * Real.exp lam) := by ring
        _ = lam * Real.exp (-lam + lam) := by rw [Real.exp_add]
        _ = lam := by rw [neg_add_cancel, Real.exp_zero, mul_one]

/-- A centered compound-Poisson law has second moment `λ` times its jump second moment. -/
theorem compoundPoisson_centered_secondMoment
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : MemLp id 2 Q) (hQmean : ∫ x : ℝ, x ∂Q = 0) :
    let μ := compoundPoisson lam Q
    Integrable (fun x : ℝ => x ^ 2) μ ∧
      (∫ x : ℝ, x ^ 2 ∂μ) = lam * ∫ x : ℝ, x ^ 2 ∂Q := by
  let f : ℝ → ℝ := fun x => x ^ 2
  let cR : ℕ → ℝ := fun n => Real.exp (-lam) * lam ^ n / n.factorial
  let c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (cR n)
  let μn : ℕ → Measure ℝ := fun n => c n • convPow Q n
  have hcR0 (n : ℕ) : 0 ≤ cR n := by
    dsimp [cR]
    positivity
  have hc_toReal (n : ℕ) : (c n).toReal = cR n := by
    dsimp [c]
    rw [ENNReal.toReal_ofReal (hcR0 n)]
  have hpow (n : ℕ) := convPow_centered_secondMoment Q hQ hQmean n
  have hpowInt (n : ℕ) : Integrable f (convPow Q n) := by
    exact (hpow n).1.integrable_sq
  have hμnInt (n : ℕ) : Integrable f (μn n) := by
    exact (hpowInt n).smul_measure ENNReal.ofReal_ne_top
  have hμnNorm (n : ℕ) :
      (∫ x, ‖f x‖ ∂μn n) = cR n * n * ∫ x : ℝ, x ^ 2 ∂Q := by
    rw [show (fun x => ‖f x‖) = f by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]]
    dsimp only [μn]
    rw [integral_smul_measure, hc_toReal]
    change cR n * (∫ x : ℝ, x ^ 2 ∂convPow Q n) = _
    rw [(hpow n).2.2]
    ring
  have hsumNorm : Summable (fun n => ∫ x, ‖f x‖ ∂μn n) := by
    rw [show (fun n => ∫ x, ‖f x‖ ∂μn n) =
        fun n => (cR n * n) * ∫ x : ℝ, x ^ 2 ∂Q by
      funext n
      rw [hμnNorm]]
    exact (summable_poisson_firstMoment lam).mul_right _
  have hμInt : Integrable f (Measure.sum μn) :=
    integrable_sum_measure hμnInt hsumNorm
  have hμeq : compoundPoisson lam Q = Measure.sum μn := by rfl
  refine ⟨hμeq ▸ hμInt, ?_⟩
  rw [hμeq, integral_sum_measure hμInt]
  calc
    (∑' n, ∫ x, f x ∂μn n) =
        ∑' n, (cR n * n) * ∫ x : ℝ, x ^ 2 ∂Q := by
      apply tsum_congr
      intro n
      rw [show (∫ x, f x ∂μn n) = ∫ x, ‖f x‖ ∂μn n by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]]
      rw [hμnNorm]
    _ = (∑' n, cR n * n) * ∫ x : ℝ, x ^ 2 ∂Q := by
      rw [tsum_mul_right]
    _ = lam * ∫ x : ℝ, x ^ 2 ∂Q := by
      rw [show (fun n : ℕ => cR n * (n : ℝ)) =
          fun n : ℕ => Real.exp (-lam) * lam ^ n / n.factorial * (n : ℝ) by rfl,
        tsum_poisson_firstMoment]

/-- Nonnegative continuum mixtures preserve finite-Gram positive definiteness. -/
theorem positiveDefiniteOnReal_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : X → ℝ → ℂ)
    (hKint : ∀ y, Integrable (fun x => K x y) μ)
    (hKpd : ∀ x, PositiveDefiniteOnReal (K x)) :
    PositiveDefiniteOnReal (fun y => ∫ x, K x y ∂μ) := by
  intro N t c
  let q : X → ℂ := fun x =>
    ∑ i, ∑ j, star (c i) * K x (t j - t i) * c j
  have hterm (i j : Fin N) : Integrable
      (fun x => star (c i) * K x (t j - t i) * c j) μ :=
    ((hKint (t j - t i)).const_mul (star (c i))).mul_const (c j)
  have hqint : Integrable q μ := by
    dsimp only [q]
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  have hqreal (x : X) : q x = ((q x).re : ℂ) := by
    obtain ⟨r, _, hq⟩ := hKpd x N t c
    dsimp only [q]
    rw [hq]
    simp
  have hqnonneg (x : X) : 0 ≤ (q x).re := by
    obtain ⟨r, hr, hq⟩ := hKpd x N t c
    dsimp only [q]
    rw [hq]
    exact hr
  have hqreint : Integrable (fun x => (q x).re) μ :=
    Complex.reCLM.integrable_comp hqint
  refine ⟨∫ x, (q x).re ∂μ, integral_nonneg hqnonneg, ?_⟩
  calc
    ∑ i, ∑ j, star (c i) * (∫ x, K x (t j - t i) ∂μ) * c j =
        ∑ i, ∑ j, ∫ x, star (c i) * K x (t j - t i) * c j ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ x, q x ∂μ := by
      dsimp only [q]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        intro j _
        exact hterm i j
      · intro i _
        exact integrable_finsetSum _ fun j _ => hterm i j
    _ = ∫ x, ((q x).re : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact hqreal x
    _ = ((∫ x, (q x).re ∂μ : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hqreint

theorem PositiveDefiniteOnReal.nonneg_smul
    {f : ℝ → ℂ} (hf : PositiveDefiniteOnReal f)
    {a : ℝ} (ha : 0 ≤ a) :
    PositiveDefiniteOnReal (fun y => (a : ℂ) * f y) := by
  intro N t c
  obtain ⟨r, hr, hq⟩ := hf N t c
  refine ⟨a * r, mul_nonneg ha hr, ?_⟩
  calc
    ∑ i, ∑ j, star (c i) * ((a : ℂ) * f (t j - t i)) * c j =
        (a : ℂ) * ∑ i, ∑ j, star (c i) * f (t j - t i) * c j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ((a * r : ℝ) : ℂ) := by rw [hq]; push_cast; rfl

/-- The squared sinc packet is a characteristic-function Gram kernel. -/
theorem positiveDefiniteOnReal_sinc_sq (A : ℝ) :
    PositiveDefiniteOnReal (fun y => ((Real.sinc (A * y) ^ 2 : ℝ) : ℂ)) := by
  let U : Measure ℝ := centeredUniformClockProbabilityMeasure A
  letI : IsProbabilityMeasure U := inferInstance
  have hconv : PositiveDefiniteOnReal (charFun (U ∗ U)) :=
    positiveDefiniteOnReal_charFun (U ∗ U)
  have heq : charFun (U ∗ U) =
      fun y => ((Real.sinc (A * y) ^ 2 : ℝ) : ℂ) := by
    funext y
    rw [charFun_conv]
    rw [show charFun U y = Real.sinc (A * y) by
      simpa only [U] using charFun_centeredUniformClockProbabilityMeasure A y]
    push_cast
    ring
  rw [← heq]
  exact hconv

/-- Canonical continuous extension of a normalized second-order characteristic defect. -/
def normalizedCharacteristicDefect (μ : Measure ℝ) (m y : ℝ) : ℝ :=
  if y = 0 then 1 else 2 * (1 - (charFun μ y).re) / (m * y ^ 2)

private theorem sq_mul_sinc_sq_eq_normalized_cosDefect
    {m y : ℝ} (hm : m ≠ 0) (hy : y ≠ 0) (x : ℝ) :
    x ^ 2 / m * Real.sinc (x / 2 * y) ^ 2 =
      2 * (1 - Real.cos (x * y)) / (m * y ^ 2) := by
  by_cases hx : x = 0
  · subst x
    simp
  have hz : x / 2 * y ≠ 0 := mul_ne_zero (div_ne_zero hx (by norm_num)) hy
  rw [Real.sinc_of_ne_zero hz]
  have hcos := Real.cos_two_mul_eq_one_sub (x / 2 * y)
  have harg : 2 * (x / 2 * y) = x * y := by ring
  rw [harg] at hcos
  rw [hcos]
  field_simp [hm, hy, hx]
  ring

theorem re_charFun_eq_integral_cos (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    (charFun μ y).re = ∫ x : ℝ, Real.cos (x * y) ∂μ := by
  let f : ℝ → ℂ := fun x => Complex.exp (((y * x : ℝ) : ℂ) * Complex.I)
  have hf : Integrable f μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with x
    dsimp only [f]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply_real]
  rw [show (fun x : ℝ => Complex.exp ((y : ℂ) * (x : ℂ) * Complex.I)) = f by
    funext x
    dsimp only [f]
    congr 1
    push_cast
    rfl]
  change Complex.reCLM (∫ x, f x ∂μ) = _
  rw [← Complex.reCLM.integral_comp_comm hf]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  change (Complex.exp (((y * x : ℝ) : ℂ) * Complex.I)).re = _
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

/-- **Universal equilibrium-defect law.** Every probability characteristic function with a
finite positive second moment has a positive-definite normalized second-order defect. -/
theorem positiveDefiniteOnReal_normalizedCharacteristicDefect
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    (hmoment : ∫ x : ℝ, x ^ 2 ∂μ = m) :
    PositiveDefiniteOnReal (fun y => (normalizedCharacteristicDefect μ m y : ℂ)) := by
  let K : ℝ → ℝ → ℂ := fun x y =>
    (((x ^ 2 / m) * Real.sinc (x / 2 * y) ^ 2 : ℝ) : ℂ)
  have hKpd (x : ℝ) : PositiveDefiniteOnReal (K x) := by
    have hbase := positiveDefiniteOnReal_sinc_sq (x / 2)
    have hscale : 0 ≤ x ^ 2 / m := div_nonneg (sq_nonneg x) hm.le
    have hscaled := hbase.nonneg_smul hscale
    simpa only [K, Complex.ofReal_mul] using hscaled
  have hbaseInt : Integrable (fun x : ℝ => x ^ 2 / m) μ := by
    simpa only [div_eq_mul_inv] using hsq.mul_const m⁻¹
  have hKint (y : ℝ) : Integrable (fun x => K x y) μ := by
    refine hbaseInt.mono' (by dsimp only [K]; fun_prop) ?_
    filter_upwards with x
    dsimp only [K]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (div_nonneg (sq_nonneg x) hm.le) (sq_nonneg _))]
    have hs := Real.abs_sinc_le_one (x / 2 * y)
    have hs2 : Real.sinc (x / 2 * y) ^ 2 ≤ 1 := by
      have hsq : Real.sinc (x / 2 * y) ^ 2 ≤ (1 : ℝ) ^ 2 :=
        sq_le_sq.mpr (by simpa using hs)
      simpa using hsq
    exact mul_le_of_le_one_right (div_nonneg (sq_nonneg x) hm.le) hs2
  have hmix := positiveDefiniteOnReal_integral μ K hKint hKpd
  have heq : (fun y => ∫ x, K x y ∂μ) =
      fun y => (normalizedCharacteristicDefect μ m y : ℂ) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp only [K, mul_zero, Real.sinc_zero, one_pow, mul_one,
        normalizedCharacteristicDefect, if_pos]
      calc
        (∫ x : ℝ, ((x ^ 2 / m : ℝ) : ℂ) ∂μ) =
            ((∫ x : ℝ, x ^ 2 / m ∂μ : ℝ) : ℂ) :=
          Complex.ofRealCLM.integral_comp_comm hbaseInt
        _ = (1 : ℂ) := by
          rw [integral_div, hmoment, div_self hm.ne']
          norm_num
    · rw [normalizedCharacteristicDefect, if_neg hy]
      have hcosInt : Integrable (fun x : ℝ => Real.cos (x * y)) μ := by
        refine (integrable_const (μ := μ) (1 : ℝ)).mono' (by fun_prop) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have hdefectInt :
          (∫ x : ℝ, 1 - Real.cos (x * y) ∂μ) = 1 - (charFun μ y).re := by
        rw [integral_sub (integrable_const 1) hcosInt, integral_const,
          measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
          ← re_charFun_eq_integral_cos]
      have hrealInt : Integrable
          (fun x : ℝ => x ^ 2 / m * Real.sinc (x / 2 * y) ^ 2) μ := by
        refine hbaseInt.mono' (by fun_prop) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (div_nonneg (sq_nonneg x) hm.le) (sq_nonneg _))]
        have hs := Real.abs_sinc_le_one (x / 2 * y)
        have hs2 : Real.sinc (x / 2 * y) ^ 2 ≤ 1 := by
          have hsq : Real.sinc (x / 2 * y) ^ 2 ≤ (1 : ℝ) ^ 2 :=
            sq_le_sq.mpr (by simpa using hs)
          simpa using hsq
        exact mul_le_of_le_one_right (div_nonneg (sq_nonneg x) hm.le) hs2
      rw [show (∫ x, K x y ∂μ) =
          ((∫ x : ℝ, x ^ 2 / m * Real.sinc (x / 2 * y) ^ 2 ∂μ : ℝ) : ℂ) by
        exact Complex.ofRealCLM.integral_comp_comm hrealInt]
      congr 1
      rw [show (∫ x : ℝ, x ^ 2 / m * Real.sinc (x / 2 * y) ^ 2 ∂μ) =
          ∫ x : ℝ, 2 * (1 - Real.cos (x * y)) / (m * y ^ 2) ∂μ by
        apply integral_congr_ae
        filter_upwards with x
        exact sq_mul_sinc_sq_eq_normalized_cosDefect hm.ne' hy x]
      rw [show (fun x : ℝ => 2 * (1 - Real.cos (x * y)) / (m * y ^ 2)) =
          fun x => (2 / (m * y ^ 2)) * (1 - Real.cos (x * y)) by
        funext x
        ring]
      rw [integral_const_mul, hdefectInt]
      ring
  rw [← heq]
  exact hmix

end

end GaloisForLFunctions.HTGeometry
