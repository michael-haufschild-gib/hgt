import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialPower
import GaloisForLFunctions.RHTower.WeilWorkQuantizationCumulativePhase
import GaloisForLFunctions.RHTower.WeilWorkQuantizationReflectedResidue

/-!
# Actual spectral remainder: the sublinear power obstruction

A sublinear power bound on the canonical integer-floor remainder pays its
cumulative phase estimate and forces every nonzero arithmetic coefficient to
one. The final alternative assumes only the specified Weil-positive source;
it does not assert that this source supplies the residual-growth bound.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- Arithmetic residues determine the same scaled main term for every coefficient. -/
theorem tendsto_quantization_mainTwist_of_remainder_along {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) =
      κ₀ * cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * quantizationTraceF hW (2 * t))
    {m : ℕ} (hm : 1 ≤ m)
    {ι : Type*} {l : Filter ι} {e : ι → ℝ} (he : Tendsto e l (𝓝[>] 0))
    (hrem : Tendsto (fun j => (e j : ℂ) * ∫ t in Iic (-1 : ℝ),
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        quantizationRadialRemainder hW m ((e j : ℂ) + (m : ℂ) * I) t) l (𝓝 0)) :
    Tendsto (fun j => κ₀ * dirichletExp (lamLog lam) m * mainTwist β₀ C (e j / m)) l
      (𝓝 (2 * betaG (quantizationCompletion hW))) := by
  have hpi := Real.pi_pos
  set am := dirichletExp (lamLog lam) m with ham
  obtain ⟨CB, hCB, hpoly⟩ := exists_quantization_trace_pair_bound hW
  have hrefl := tendsto_quantization_lower_reflected_radial hW hm
  let Φ : ℝ → ℂ := fun t => quantizationTraceF hW (2 * t)
  let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
  let G₀ : ℂ → ℂ := fun s => quantizationCompletedTrace hW s.im
  have hphi : phiG G₀ = Φ := by
    funext t
    simp [phiG, G₀, Φ, quantizationTraceF, FractionalMassRigidity.lineS_eq]
  have hnear := tendsto_near_piece (G := G₀) hCB
    (fun t => by rw [hphi]; exact (hpoly t).1) β₀ C hm
  rw [hphi] at hnear
  have hdecomp : ∀ ε : ℝ, 0 < ε →
      ((2 * Real.pi : ℝ) : ℂ) * ((ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (Ψ))
        ((ε : ℂ) + (m : ℂ) * I)) -
        κ₀ * ((ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t) -
        κ₀ * ((ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (Φ t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) =
      κ₀ * am * mainTwist β₀ C (ε / m) := by
    intro ε hε
    rw [← mainTwist_scale β₀ C hm ε]
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
    have hphik : Integrable (fun t => Φ t * pairKernel (2 * t) τ) :=
      integrable_defectLaplace_integrand
        ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
        (fun t => (hpoly t).1) hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (Ψ) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => Ψ t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have hcongr : ∫ t in Iio (0 : ℝ), Ψ t * pairKernel (2 * t) τ =
        ∫ t in Iio (0 : ℝ), κ₀ * (cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (Φ t * pairKernel (2 * t) τ)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hlock, ae_restrict_mem measurableSet_Iio] with t ht ht0
      dsimp only [Ψ, Φ]
      rw [ht ht0]
      ring
    have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
      ext t
      simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h
        by_cases h1 : t ≤ -1
        · exact Or.inl h1
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
      Set.disjoint_left.mpr fun t h1 h2 => by
        simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
    have hint1 := integrableOn_phase_mul β₀ hC (s := Iic (-1)) hphik.integrableOn
    have hint2 := integrableOn_phase_mul β₀ hC (s := Ioo (-1) 0) hphik.integrableOn
    have hint3 := integrableOn_phase_mul β₀ hC (s := Iic (-1))
      (f := quantizationRadialRemainder hW m τ) (hphik.integrableOn.sub (hrho.const_mul am))
    have hint4 := (integrableOn_phase_mul β₀ hC hrho).const_mul am
    rw [hcongr, integral_const_mul, hsplit, setIntegral_union hdisj measurableSet_Ioo hint1 hint2]
    have hfar : ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        (Φ t * pairKernel (2 * t) τ) =
        (∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * quantizationRadialRemainder hW m τ t) +
          am * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * rhoMain m τ t := by
      rw [← integral_const_mul, ← integral_add hint3 hint4]
      refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
      simp only [quantizationRadialRemainder, Φ, ham]; ring
    rw [hfar]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    linear_combination (↑ε * (κ₀ * ((∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      quantizationRadialRemainder hW m τ t) + am * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        rhoMain m τ t) + κ₀ * ∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (Φ t * pairKernel (2 * t) τ))) * h2pi
  have hlim := ((((hrefl.comp he).const_mul ((2 * Real.pi : ℝ) : ℂ)).sub (hrem.const_mul κ₀)).sub
    ((hnear.comp he).const_mul κ₀))
  have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG (quantizationCompletion hW) / (Real.pi : ℂ)) - κ₀ * 0 - κ₀ * 0 =
      2 * betaG (quantizationCompletion hW) := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    push_cast; field_simp; ring
  rw [hval] at hlim
  exact hlim.congr' (he.eventually (eventually_nhdsWithin_of_forall fun ε hε => hdecomp ε hε))


/-- Arithmetic residues determine the same scaled main term for every coefficient. -/
theorem tendsto_quantization_mainTwist_of_remainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) =
      κ₀ * cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * quantizationTraceF hW (2 * t))
    {m : ℕ} (hm : 1 ≤ m)
    (hrem : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => κ₀ * dirichletExp (lamLog lam) m * mainTwist β₀ C (ε / m)) (𝓝[>] 0)
      (𝓝 (2 * betaG (quantizationCompletion hW))) := by
  exact tendsto_quantization_mainTwist_of_remainder_along hW hC hlock hm tendsto_id hrem

/-- A single family of quiet radial scales, with fixed rescalings, fixes every coefficient. -/
theorem quantization_rigidity_of_remainder_along {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) =
      κ₀ * cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * quantizationTraceF hW (2 * t))
    {ι : Type*} {l : Filter ι} [NeBot l] {e : ι → ℝ} (he : Tendsto e l (𝓝[>] 0))
    (hrem : ∀ m : ℕ, 1 ≤ m → ∀ r : ℝ, 0 < r →
      Tendsto (fun j => ((e j / r : ℝ) : ℂ) * ∫ t in Iic (-1 : ℝ),
        cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          quantizationRadialRemainder hW m (((e j / r : ℝ) : ℂ) + (m : ℂ) * I) t) l (𝓝 0)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set a := dirichletExp (lamLog lam) with ha_def
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have hβ : betaG (quantizationCompletion hW) ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero (differentiableOn_weilContinuation hW)
      (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW)
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) two_ne_zero
  have hone : ∀ n : ℕ, n ≠ 0 → a n = 1 := by
    intro n hn
    have hm : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hm
    have hscale : Tendsto (fun j => e j / n) l (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (he.mono_right nhdsWithin_le_nhds).div_const (n : ℝ)
      · filter_upwards [he.eventually (eventually_mem_nhdsWithin)] with j hj
        exact div_pos hj hn0
    have h1 := tendsto_quantization_mainTwist_of_remainder_along hW hC hlock le_rfl hscale
      (hrem 1 le_rfl n hn0)
    have h1' : Tendsto (fun j => κ₀ * mainTwist β₀ C (e j / n)) l
        (𝓝 (2 * betaG (quantizationCompletion hW))) := by
      refine h1.congr fun j => ?_
      rw [← ha_def, ha1, Nat.cast_one, div_one, mul_one]
    have hmrem := hrem n hm 1 zero_lt_one
    simp only [div_one] at hmrem
    have hB := tendsto_quantization_mainTwist_of_remainder_along hW hC hlock hm he hmrem
    have hB' : Tendsto (fun j => a n * (κ₀ * mainTwist β₀ C (e j / n))) l
        (𝓝 (2 * betaG (quantizationCompletion hW))) := hB.congr fun j => by rw [← ha_def]; ring
    have heq := tendsto_nhds_unique (h1'.const_mul (a n)) hB'
    exact mul_right_cancel₀ (mul_ne_zero two_ne_zero hβ) (heq.trans (one_mul _).symm)
  exact vonMangoldt_and_RH_of_coeff_eq_one
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (differentiableOn_weilContinuation hW) (fun _ hs => quantizationContinuation_eq_arch hW hs)
    (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW) hone

/-- Comparing all scaled main-term limits fixes every nonzero arithmetic coefficient. -/
theorem quantization_rigidity_of_radial_remainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) =
      κ₀ * cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * quantizationTraceF hW (2 * t))
    (hrem : ∀ m : ℕ, 1 ≤ m → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  apply quantization_rigidity_of_remainder_along hW hC hlock
    (e := fun ε : ℝ => ε) tendsto_id
  intro m hm r hr
  have hscale : Tendsto (fun ε : ℝ => ε / r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝[>] 0)).mono_right
        nhdsWithin_le_nhds).div_const r
    · exact eventually_nhdsWithin_of_forall fun ε hε => div_pos hε hr
  exact (hrem m hm).comp hscale

/-- Sublinear power mass of the actual residual measure forces arithmetic rigidity. -/
theorem quantization_rigidity_of_power_residual {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {α K : ℝ} (hα : α < 1)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (quantizationResidualMeasure hW).real (Icc (-T) T) ≤ K * T ^ α) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  let α' : ℝ := max α (1 / 2)
  let K' : ℝ := |K| + 1
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hα'1 : α' < 1 := max_lt hα (by norm_num)
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hgrowth' : ∀ T : ℝ, 1 ≤ T →
      (quantizationResidualMeasure hW).real (Icc (-T) T) ≤ K' * T ^ α' := by
    intro T hT
    calc _ ≤ K * T ^ α := hgrowth T hT
      _ ≤ K' * T ^ α := mul_le_mul_of_nonneg_right (by dsimp [K']; linarith [le_abs_self K])
        (Real.rpow_nonneg (by linarith) _)
      _ ≤ K' * T ^ α' := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (le_max_left _ _)) hK'.le
  have hC := monotone_quantizationResidualCumulative hW
  apply quantization_rigidity_of_radial_remainder hW hC.measurable
    (ae_quantizationReflectedTraceF_cumulative_phase hW)
  intro m hm
  exact tendsto_quantization_twisted_remainder_pow hW hC hα'0 hα'1
    (mul_pos hK' (Real.rpow_pos_of_pos (by norm_num) _))
    (fun x hx => quantizationResidualCumulative_power_le hW hgrowth' hx) (2 * Real.pi) hm

/-- Intrinsic source alternative: failure of rigidity exceeds every sublinear power residual bound. -/
theorem quantization_rigidity_or_residual_power_obstruction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ α : ℝ, α < 1 → ∀ K : ℝ, ∃ T : ℝ, 1 ≤ T ∧
        K * T ^ α < (quantizationResidualMeasure hW).real (Icc (-T) T) := by
  classical
  by_cases h : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl h
  right
  intro α hα K
  by_contra hn
  push Not at hn
  exact h (quantization_rigidity_of_power_residual hW hα hn)

end RHTower.WeilSpectral
