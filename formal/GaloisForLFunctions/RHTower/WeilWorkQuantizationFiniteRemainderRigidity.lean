import GaloisForLFunctions.RHTower.WeilWorkQuantizationResidualPhase
import GaloisForLFunctions.RHTower.WeilConeAlmostPeriodicSettledLock

/-!
# Finite canonical remainder forces arithmetic rigidity

Remove the integer part of each atom of the actual canonical measure. Finite
remaining mass supplies a limiting reflection phase, including arbitrary
singular-continuous mass. Signed radial cancellation and arithmetic periodicity
force every nonzero Dirichlet coefficient to one. The final dichotomy assumes
only the specified Weil-positive source and leaves infinite remainder explicit.
-/

open Complex Set Filter MeasureTheory
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz HamburgerStability HamburgerTwisted PhaseLockRigidity IntegerMassRigidity
  GaloisForLFunctions.HTGeometry

/-- The error relative to the phase selected by the actual residual measure. -/
def quantizationReflectionError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℂ :=
  quantizationReflectedTraceF hW (2 * t) -
    quantizationResidualPhase hW * quantizationTraceF hW (2 * t)

theorem measurable_quantizationReflectionError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (quantizationReflectionError hW) :=
  ((measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)).sub
    (((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).const_mul _)

theorem exists_bound_quantizationReflectionError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖quantizationReflectionError hW t‖ ≤ C * (1 + |t|) ^ (1 : ℕ) := by
  obtain ⟨C, hC, hB⟩ := exists_quantization_trace_pair_bound hW
  refine ⟨2 * C, by positivity, fun t => ?_⟩
  calc ‖quantizationReflectionError hW t‖ ≤
      ‖quantizationReflectedTraceF hW (2 * t)‖ +
        ‖quantizationResidualPhase hW * quantizationTraceF hW (2 * t)‖ := norm_sub_le _ _
    _ = ‖quantizationReflectedTraceF hW (2 * t)‖ + ‖quantizationTraceF hW (2 * t)‖ := by
      rw [norm_mul, norm_quantizationResidualPhase, one_mul]
    _ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by linarith [(hB t).1, (hB t).2]

/-- Finite residual mass removes every arithmetic radial residue of the reflection error. -/
theorem tendsto_quantization_reflection_error_radial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace (quantizationReflectionError hW)
      ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hm : AEStronglyMeasurable (quantizationReflectionError hW) volume :=
    (measurable_quantizationReflectionError hW).aestronglyMeasurable
  obtain ⟨C, _, hb⟩ := exists_bound_quantizationReflectionError hW
  rcases m with _ | m
  · exact tendsto_mul_defectLaplace_zero hm hb
  have ht := (tendsto_quantization_reflection_error_lower hW hfin
    (show 1 ≤ m + 1 by omega)).const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  rw [mul_zero] at ht
  have hlo : Tendsto (fun ε : ℝ => (ε : ℂ) *
      defectLaplace ((Iio (0 : ℝ)).indicator (quantizationReflectionError hW))
        ((ε : ℂ) + ((m + 1 : ℕ) : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    refine ht.congr' (Eventually.of_forall fun ε => ?_)
    unfold defectLaplace
    rw [mul_left_comm]
    congr 2
    rw [← integral_indicator measurableSet_Iio]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases h : t ∈ Iio (0 : ℝ)
    · simp only [indicator_of_mem h, quantizationReflectionError]
    · simp only [indicator_of_notMem h, zero_mul]
  have hup := tendsto_mul_defectLaplace_upper_radial hm hb (Y := 0) le_rfl (m + 1)
  have hmid := tendsto_mul_abelMass_indicator_Icc hm hb 0
  simp only [neg_zero] at hmid
  have hmi := tendsto_mul_defectLaplace_radial (hm.indicator measurableSet_Icc)
    (fun t => (norm_indicator_le_norm_self _ t).trans (hb t)) hmid (m + 1)
  have h := (hup.add hlo).add hmi
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [defectLaplace_split hm hb (Y := 0) le_rfl (by simpa using hε)]
  simp only [neg_zero]
  ring

/-- Arbitrary finite positive remainder, including continuous singular mass, forces rigidity. -/
theorem quantization_rigidity_of_finite_residual {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  let a := dirichletExp (lamLog lam)
  let β := betaG (quantizationCompletion hW)
  let c := quantizationResidualPhase hW
  let κ := c⁻¹
  let Φ : ℝ → ℂ := fun t => quantizationTraceF hW (2 * t)
  let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
  let g : ℝ → ℂ := fun t => Φ t - Ψ t
  let e := quantizationReflectionError hW
  have hΦm : Measurable Φ :=
    (measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)
  have hΨm : Measurable Ψ :=
    (measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)
  have hem : Measurable e := measurable_quantizationReflectionError hW
  obtain ⟨C, hC, hB⟩ := exists_quantization_trace_pair_bound hW
  have hΦb : ∀ t, ‖Φ t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    intro t
    have := (hB t).1
    have hp : 0 ≤ C * (1 + |t|) ^ (1 : ℕ) := by positivity
    linarith
  have hΨb : ∀ t, ‖Ψ t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    intro t
    have := (hB t).2
    have hp : 0 ≤ C * (1 + |t|) ^ (1 : ℕ) := by positivity
    linarith
  have heb : ∀ t, ‖e t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    intro t
    calc ‖e t‖ ≤ ‖Ψ t‖ + ‖c * Φ t‖ := norm_sub_le _ _
      _ = ‖Ψ t‖ + ‖Φ t‖ := by rw [norm_mul, norm_quantizationResidualPhase, one_mul]
      _ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by linarith [(hB t).1, (hB t).2]
  have ha := fun σ hσ => quantization_coeff_summable hW (σ := σ) hσ
  have ha2 : Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa using summable_sq_of_forall_rpow ha
  let S : ℂ → ℂ := fun τ => ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))
  let K : ℂ → ℂ := fun τ => -κ * defectLaplace e τ
  have hκ : κ * c = 1 := inv_mul_cancel₀ (quantizationResidualPhase_ne_zero hW)
  have hmain : ∀ τ : ℂ, 0 < τ.re →
      hamburgerSeries a τ = κ * S τ - κ * β / Real.pi / τ + β + K τ := by
    intro τ hτ
    have eA := quantization_hamburgerSeries_reflection hW hτ
    have eB := quantization_hamburgerSeries_eq hW hτ
    have eC := defectLaplace_indicator_eq (g := g) hΨm.aestronglyMeasurable hΨb
      hΦm.aestronglyMeasurable hΦb MeasurableSet.univ (-1)
      (fun t _ => by dsimp [g]; ring) hτ
    have eD := defectLaplace_indicator_eq (g := Ψ) hΦm.aestronglyMeasurable hΦb
      hem.aestronglyMeasurable heb MeasurableSet.univ c
      (fun t _ => by dsimp [e, Ψ, Φ, c, quantizationReflectionError]; ring) hτ
    simp only [indicator_univ] at eC eD
    change hamburgerSeries a τ = S τ - β / (Real.pi * τ) + β + defectLaplace g τ at eA
    change hamburgerSeries a τ = β + defectLaplace Φ τ at eB
    rw [show β / (Real.pi * τ) = β / Real.pi / τ by field_simp] at eA
    dsimp only [K]
    linear_combination κ * eA - (κ - 1) * eB + κ * eC - κ * eD -
      defectLaplace Φ τ * hκ
  have hper : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a (τ + I) - hamburgerSeries a τ =
      -(κ * β / Real.pi) / (τ + I) - -(κ * β / Real.pi) / τ + (K (τ + I) - K τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    have hexp : S (τ + I) = S τ := by
      dsimp only [S]
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hmain τ hτ, hmain (τ + I) hτ', hexp]
    ring
  have hKrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * K ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
    intro m
    have h := (tendsto_quantization_reflection_error_radial hW hfin m).const_mul (-κ)
    rw [mul_zero] at h
    exact h.congr' (Eventually.of_forall fun ε => by dsimp [K, e]; ring)
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (K (τ + I) - K τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (-(κ * β / Real.pi))
      (fun τ => K (τ + I) - K τ) hper n₀ ?_
    have h := (hKrad (n₀ + 1)).sub (hKrad n₀)
    rw [sub_zero] at h
    refine h.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf
  have hcoef : ∀ n : ℕ, a (n + 1) = 2 * κ * β := by
    intro n
    have h := coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect ha2 (-(κ * β / Real.pi))
      (fun τ => K (τ + I) - K τ) hper hK n
    rw [h]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have h2β : 2 * κ * β = 1 := by rw [← hcoef 0, ha1]
  have hone : ∀ n : ℕ, n ≠ 0 → a n = 1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (hcoef k).trans h2β
  exact AbelianTwist.vonMangoldt_and_RH_of_coeff_eq_one
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (differentiableOn_weilContinuation hW) (fun s hs => quantizationContinuation_eq_arch hW hs)
    (fun s hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW) hone

/-- Intrinsic source dichotomy: non-rigidity costs infinite residual mass. -/
theorem quantization_rigidity_or_infinite_residual {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      quantizationResidualMeasure hW univ = ∞ := by
  by_cases hfin : quantizationResidualMeasure hW univ = ∞
  · exact Or.inr hfin
  · exact Or.inl (quantization_rigidity_of_finite_residual hW hfin)

end RHTower.WeilSpectral
