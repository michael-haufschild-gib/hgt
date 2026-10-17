import GaloisForLFunctions.RHTower.PrimeBurnolJumpMeasure
import GaloisForLFunctions.RHTower.PrimeBurnolOperatorExponential

/-! Every canonical finite jump datum realizes positive prime-compatible evolution with exact killing decay. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def BurnolJumpData.rate (D : BurnolJumpData) (x : ℝ) : ℝ :=
  burnolMeasureLaplace D.measure x - ((D.killing : ℝ) + (D.measure univ).toReal)

lemma BurnolJumpData.generator_prime (D : BurnolJumpData) (p : Nat.Primes) :
    D.generator (primeLogCriticalLaplaceFeatureL2 p) =
      (D.rate (Real.log (p : ℝ)) : ℂ) • primeLogCriticalLaplaceFeatureL2 p := by
  change burnolPositiveShiftMixture D.measure (primeLogCriticalLaplaceFeatureL2 p) -
    (((D.killing : ℝ) + (D.measure univ).toReal : ℝ) : ℂ) •
      primeLogCriticalLaplaceFeatureL2 p = _
  rw [(primeBurnol_positive_measure_realization D.measure).2.1 p, ← sub_smul]
  simp only [BurnolJumpData.rate, Complex.ofReal_sub]

lemma BurnolJumpData.generator_rate (D : BurnolJumpData) (x : ℝ) (hx : 0 < x) :
    D.generator (burnolRateFeature x hx) = (D.rate x : ℂ) • burnolRateFeature x hx := by
  change burnolPositiveShiftMixture D.measure (burnolRateFeature x hx) -
    (((D.killing : ℝ) + (D.measure univ).toReal : ℝ) : ℂ) • burnolRateFeature x hx = _
  rw [burnolPositiveShiftMixture_rate, ← sub_smul]
  simp only [BurnolJumpData.rate, Complex.ofReal_sub]

lemma BurnolJumpData.rate_zero_limit (D : BurnolJumpData) :
    Tendsto D.rate (𝓝[>] (0 : ℝ)) (𝓝 (-(D.killing : ℝ))) := by
  have h := (tendsto_burnolMeasureLaplace_zero D.measure).sub_const
    ((D.killing : ℝ) + (D.measure univ).toReal)
  have he : (D.measure univ).toReal - ((D.killing : ℝ) + (D.measure univ).toReal) =
      -(D.killing : ℝ) := by ring
  rwa [he] at h

/-- The evolution is the positive jump exponential multiplied by its scalar loss factor. -/
lemma BurnolJumpData.evolution_factor (D : BurnolJumpData) (t : ℝ) :
    burnolEvolution D.generator t =
      (Real.exp (-t * ((D.killing : ℝ) + (D.measure univ).toReal)) : ℂ) •
        burnolEvolution (burnolPositiveShiftMixture D.measure) t := by
  apply primeBurnol_operator_ext
  intro p
  rw [burnolEvolution_prime D.generator (fun p => (D.rate (Real.log (p : ℝ)) : ℂ))
    D.generator_prime t p, smul_apply]
  rw [burnolEvolution_prime (burnolPositiveShiftMixture D.measure)
    (fun p => (burnolMeasureLaplace D.measure (Real.log (p : ℝ)) : ℂ))
    (primeBurnol_positive_measure_realization D.measure).2.1 t p, smul_smul]
  apply congrArg (fun z : ℂ => z • primeLogCriticalLaplaceFeatureL2 p)
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [BurnolJumpData.rate, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma BurnolJumpData.evolution_positive (D : BurnolJumpData) {t : ℝ} (ht : 0 ≤ t) :
    BurnolPreservesNonnegativity (burnolEvolution D.generator t) := by
  rw [D.evolution_factor t]
  intro f hf
  change 0 ≤ Real.exp (-t * ((D.killing : ℝ) + (D.measure univ).toReal)) •
    burnolEvolution (burnolPositiveShiftMixture D.measure) t f
  exact smul_nonneg (Real.exp_nonneg _) (burnolEvolution_positive
    (fun _ hg => burnolPositiveShiftMixture_nonneg D.measure hg) ht f hf)

private lemma primeBurnol_positive_norm_of_real_rate_limit
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hp : BurnolPreservesNonnegativity T) (b : ℝ → ℝ) {c : ℝ}
    (hb : ∀ x : ℝ, ∀ hx : 0 < x,
      T (burnolRateFeature x hx) = (b x : ℂ) • burnolRateFeature x hx)
    (hlim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 c)) : ‖T‖ = c := by
  obtain ⟨τ, hτ, he⟩ := primeBurnol_packetTest_representation T a ha hp.packetTest
  letI : IsFiniteMeasure τ := hτ
  have hT : T = burnolPositiveShiftMixture τ := ContinuousLinearMap.ext he
  have hbeq : ∀ x : ℝ, 0 < x → b x = burnolMeasureLaplace τ x := by
    intro x hx
    have hn : burnolRateFeature x hx ≠ 0 := by
      simpa only [burnolComplexFeature_ofReal, burnolRateFeature] using
        burnolComplexFeature_ne_zero (z := (x : ℂ)) hx
    apply Complex.ofReal_injective
    apply smul_left_injective ℂ hn
    change (b x : ℂ) • burnolRateFeature x hx =
      (burnolMeasureLaplace τ x : ℂ) • burnolRateFeature x hx
    rw [← hb x hx, hT, burnolPositiveShiftMixture_rate]
  have hlim' : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 (τ univ).toReal) := by
    apply (tendsto_burnolMeasureLaplace_zero τ).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hbeq x hx).symm
  calc ‖T‖ = (τ univ).toReal := by rw [hT, norm_burnolPositiveShiftMixture]
    _ = c := tendsto_nhds_unique hlim' hlim

/-- Exact decay of every realized finite-jump evolution; jump mass itself causes no loss. -/
theorem BurnolJumpData.evolution_norm (D : BurnolJumpData) {t : ℝ} (ht : 0 ≤ t) :
    ‖burnolEvolution D.generator t‖ = Real.exp (-(t * (D.killing : ℝ))) := by
  apply primeBurnol_positive_norm_of_real_rate_limit (burnolEvolution D.generator t)
    (fun p => Complex.exp ((t : ℂ) * (D.rate (Real.log (p : ℝ)) : ℂ)))
    (burnolEvolution_prime D.generator _ D.generator_prime t) (D.evolution_positive ht)
    (fun x => Real.exp (t * D.rate x))
  · intro x hx
    simpa only [burnolEvolution, Complex.ofReal_exp, Complex.ofReal_mul] using
      operator_exp_eigen D.generator (D.generator_rate x hx) (t : ℂ)
  · have hc : Tendsto (fun _ : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 t) := tendsto_const_nhds
    have h : Tendsto (fun x => Real.exp (t * D.rate x)) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (t * -(D.killing : ℝ)))) :=
      Real.continuous_exp.continuousAt.tendsto.comp (hc.mul D.rate_zero_limit)
    simpa only [mul_neg] using h

lemma BurnolJumpData.evolution_contraction (D : BurnolJumpData) {t : ℝ} (ht : 0 ≤ t) :
    ‖burnolEvolution D.generator t‖ ≤ 1 := by
  rw [D.evolution_norm ht]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht D.killing.coe_nonneg))

lemma continuous_burnolEvolution (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    Continuous (burnolEvolution A) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).continuousAt

lemma burnolEvolution_add (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (s t : ℝ) :
    burnolEvolution A (s+t) = burnolEvolution A s * burnolEvolution A t := by
  change NormedSpace.exp ((s+t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A)
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl A).smul_left s).smul_right t)
    ((NormedSpace.expSeries_radius_eq_top ℝ
      (BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)).symm ▸ edist_lt_top (s • A) 0)
    ((NormedSpace.expSeries_radius_eq_top ℝ
      (BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)).symm ▸ edist_lt_top (t • A) 0)

lemma burnolEvolution_zero (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    burnolEvolution A 0 = 1 := by simp [burnolEvolution]

/-- The actual jump operator gives a norm-convergent Poisson series for every evolution time. -/
theorem BurnolJumpData.evolution_jumpSeries (D : BurnolJumpData) (t : ℝ) :
    HasSum (fun n : ℕ =>
      ((Real.exp (-t * ((D.killing : ℝ) + (D.measure univ).toReal)) : ℂ) *
        ((n.factorial : ℂ)⁻¹ * (t : ℂ)^n)) • (burnolPositiveShiftMixture D.measure)^n)
      (burnolEvolution D.generator t) := by
  rw [D.evolution_factor t]
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    ((t : ℂ) • burnolPositiveShiftMixture D.measure)).const_smul
    (Real.exp (-t * ((D.killing : ℝ) + (D.measure univ).toReal)) : ℂ)
  simpa only [smul_pow, smul_smul, burnolEvolution] using hs

/-- The canonical generator is the literal weighted jump integral minus killing. -/
theorem BurnolJumpData.generator_apply (D : BurnolJumpData) (f : BurnolHalfLineL2) :
    D.generator f = (∫ h, burnolWeightedShift h f - f ∂D.measure) -
      ((D.killing : ℝ) : ℂ) • f := by
  rw [integral_sub (integrable_burnolWeightedShift D.measure f) (integrable_const f),
    integral_const, measureReal_def]
  change (∫ h, burnolWeightedShift h f ∂D.measure) -
    (((D.killing : ℝ) + (D.measure univ).toReal : ℝ) : ℂ) • f = _
  rw [Complex.ofReal_add, add_smul]
  change (∫ h, burnolWeightedShift h f ∂D.measure) -
    ((D.killing : ℝ) • f + (D.measure univ).toReal • f) =
      (∫ h, burnolWeightedShift h f ∂D.measure) - (D.measure univ).toReal • f -
        (D.killing : ℝ) • f
  abel

lemma BurnolJumpData.rate_eq_jump_integral (D : BurnolJumpData) {x : ℝ} (hx : 0 ≤ x) :
    D.rate x = -(D.killing : ℝ) + ∫ h : ℝ≥0, (Real.exp (-(x * h)) - 1) ∂D.measure := by
  have hi : Integrable (fun h : ℝ≥0 => Real.exp (-(x * h))) D.measure := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ fun h => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx h.coe_nonneg))
  rw [integral_sub hi (integrable_const 1), integral_const, measureReal_def, smul_eq_mul, mul_one]
  unfold BurnolJumpData.rate burnolMeasureLaplace
  ring

end RHTower
