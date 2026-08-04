import GaloisForLFunctions.HTGeometry.KleinGordonRegularDense

/-!
# The regularity restriction is genuine

The range of `⟨D⟩⁻¹` is dense, but it is not everything: in any space of positive dimension the
operator fails to be surjective. So the hypothesis "the datum is in the range of `⟨D⟩⁻¹`" is a real
restriction, and the strong theory is genuinely narrower than the mild one — as it must be, since a
mild solution need not be strong.

The proof is the standard one, made explicit. Were `⟨D⟩⁻¹` surjective it would be bijective, hence
(open mapping) bounded below; but a function whose Fourier transform is supported in a far ball is
shrunk by the factor `⟨R⟩⁻¹`, which can be made smaller than any lower bound. The witness is the
indicator of a ball of positive finite measure centred at a frequency of large norm.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

section AeBound

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A pointwise bound valid only where the function lives still bounds the multiplier.** -/
theorem norm_lpBoundedMulCLM_apply_le_of_ae {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) {c : ℝ} (hc0 : 0 ≤ c) (g : Lp 𝕜 p μ)
    (hae : ∀ᵐ x ∂μ, ‖φ x * (g : α → 𝕜) x‖ ≤ c * ‖(g : α → 𝕜) x‖) :
    ‖lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC g‖ ≤ c * ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC g)]
  have hmono : eLpNorm (fun x => φ x * (g : α → 𝕜) x) p μ ≤ eLpNorm ((c : ℝ) • (g : α → 𝕜)) p μ := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hae] with x hx
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact hx
  have hval := hmono.trans_eq (eLpNorm_const_smul (c : ℝ) ((g : α → 𝕜)) p μ)
  have hfin : eLpNorm ((g : α → 𝕜)) p μ ≠ ∞ := Lp.eLpNorm_ne_top g
  have htoReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp [enorm_eq_nnnorm]) hfin) hval
  refine htoReal.trans ?_
  rw [ENNReal.toReal_mul]
  have hnorm : (‖(c : ℝ)‖ₑ).toReal = c := by
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc0]
  rw [hnorm]

end AeBound

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## A test function at high frequency -/

/-- The indicator of a ball, as an element of `L²`. -/
def kgBallFun (ξ₀ : E) (r : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  (memLp_indicator_const 2 (measurableSet_ball (x := ξ₀) (ε := r)) (1 : ℂ)
    (Or.inr measure_ball_lt_top.ne)).toLp _

theorem kgBallFun_coeFn (ξ₀ : E) (r : ℝ) :
    (kgBallFun ξ₀ r : E → ℂ) =ᵐ[volume] Set.indicator (ball ξ₀ r) fun _ => (1 : ℂ) :=
  MemLp.coeFn_toLp _

theorem kgBallFun_ne_zero (ξ₀ : E) {r : ℝ} (hr : 0 < r) : kgBallFun ξ₀ r ≠ 0 := by
  intro hzero
  have hae : (kgBallFun ξ₀ r : E → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 volume
  have hind : (Set.indicator (ball ξ₀ r) fun _ => (1 : ℂ)) =ᵐ[volume] fun _ => (0 : ℂ) :=
    (kgBallFun_coeFn ξ₀ r).symm.trans hae
  have hnull : (volume : Measure E) (ball ξ₀ r) = 0 := by
    have hsub : ball ξ₀ r
        ⊆ {x : E | ¬ (Set.indicator (ball ξ₀ r) (fun _ => (1 : ℂ)) x = 0)} := by
      intro x hx
      rw [Set.mem_setOf_eq, Set.indicator_of_mem hx]
      exact one_ne_zero
    exact measure_mono_null hsub (ae_iff.mp hind)
  exact absurd hnull (measure_ball_pos volume ξ₀ hr).ne'

/-- **The multiplier shrinks a function supported at frequencies of size at least `R`.** -/
theorem norm_kgFreqInvOp_kgBallFun_le {ξ₀ : E} {r R : ℝ} (hR : 0 ≤ R)
    (hfar : ∀ ξ ∈ ball ξ₀ r, R ≤ ‖ξ‖) :
    ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) (measurable_kgFreqInv (E := E))
        zero_le_one norm_kgFreqInv_le (kgBallFun ξ₀ r)‖
      ≤ (Real.sqrt (1 + R ^ 2))⁻¹ * ‖kgBallFun ξ₀ r‖ := by
  have hpos : 0 < Real.sqrt (1 + R ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  refine norm_lpBoundedMulCLM_apply_le_of_ae _ _ _ (le_of_lt (inv_pos.mpr hpos)) _ ?_
  filter_upwards [kgBallFun_coeFn ξ₀ r] with ξ hξ
  rw [hξ, norm_mul]
  by_cases hmem : ξ ∈ ball ξ₀ r
  · have hfreq : Real.sqrt (1 + R ^ 2) ≤ kgFreq ξ := by
      refine Real.sqrt_le_sqrt ?_
      have := hfar ξ hmem
      nlinarith [norm_nonneg ξ]
    have hle : ‖kgFreqInv (E := E) ξ‖ ≤ (Real.sqrt (1 + R ^ 2))⁻¹ := by
      rw [kgFreqInv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (kgFreq_pos ξ))]
      gcongr
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  · rw [Set.indicator_of_notMem hmem]
    simp


/-! ## Non-surjectivity -/

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A frequency of any prescribed norm exists once the space is nontrivial. -/
theorem exists_norm_eq (hd : 0 < Module.finrank ℝ E) {R : ℝ} (hR : 0 ≤ R) :
    ∃ ξ₀ : E, ‖ξ₀‖ = R := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hd
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  refine ⟨(R / ‖y‖) • y, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- **`⟨D⟩⁻¹` is not surjective** on a space of positive dimension: the frequencies are unbounded, so
the operator is not bounded below, and a bijective bounded operator would be. -/
theorem not_surjective_kgFreqInvOp (hd : 0 < Module.finrank ℝ E) :
    ¬ Function.Surjective (kgFreqInvOp (E := E)) := by
  intro hsurj
  have hker : (kgFreqInvOp (E := E) :
      Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr kgFreqInvOp_injective
  have hran : (kgFreqInvOp (E := E) :
      Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  set e := ContinuousLinearEquiv.ofBijective (kgFreqInvOp (E := E)) hker hran with he
  set K : ℝ := ‖(e.symm : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hbelow : ∀ x : Lp ℂ 2 (volume : Measure E), ‖x‖ ≤ K * ‖kgFreqInvOp (E := E) x‖ := by
    intro x
    have hx : (e.symm : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        (kgFreqInvOp (E := E) x) = x := e.symm_apply_apply x
    have hle := (e.symm : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)).le_opNorm
      (kgFreqInvOp (E := E) x)
    rwa [hx] at hle
  obtain ⟨ξ₀, hξ₀⟩ := exists_norm_eq (E := E) hd (by linarith : (0:ℝ) ≤ K + 1)
  have hfar : ∀ ξ ∈ ball ξ₀ 1, K ≤ ‖ξ‖ := by
    intro ξ hξ
    have hd1 : ‖ξ₀ - ξ‖ < 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using hξ
    have := norm_sub_norm_le ξ₀ ξ
    rw [hξ₀] at this
    linarith
  set g := kgBallFun ξ₀ (1 : ℝ) with hg
  set f := fourierL2inv E g with hf
  have hgf : fourierL2 E f = g := by rw [hf, fourierL2_fourierL2inv]
  have hnf : ‖f‖ = ‖g‖ := by rw [hf, norm_fourierL2inv_apply]
  have hgpos : 0 < ‖g‖ := by
    rw [norm_pos_iff]
    exact kgBallFun_ne_zero ξ₀ one_pos
  have hAf : ‖kgFreqInvOp (E := E) f‖
      = ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) (measurable_kgFreqInv (E := E))
          zero_le_one norm_kgFreqInv_le g‖ := by
    rw [kgFreqInvOp_eq, fourierMulCLM_apply, norm_fourierL2inv_apply, hgf]
  have hshrink := norm_kgFreqInvOp_kgBallFun_le (ξ₀ := ξ₀) (r := 1) (R := K) hK0 hfar
  have hsq : K < Real.sqrt (1 + K ^ 2) := by
    have h1 : K ^ 2 < 1 + K ^ 2 := by linarith
    have h2 : Real.sqrt (K ^ 2) < Real.sqrt (1 + K ^ 2) := by
      exact Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq hK0] at h2
  have hpos : 0 < Real.sqrt (1 + K ^ 2) := lt_of_le_of_lt hK0 hsq
  have hchain : ‖f‖ ≤ K * ((Real.sqrt (1 + K ^ 2))⁻¹ * ‖g‖) := by
    refine le_trans (hbelow f) ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [hAf]
    exact hshrink
  rw [hnf] at hchain
  have hlt : K * ((Real.sqrt (1 + K ^ 2))⁻¹ * ‖g‖) < ‖g‖ := by
    have hfac : K * (Real.sqrt (1 + K ^ 2))⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hpos, one_mul]
      exact hsq
    calc K * ((Real.sqrt (1 + K ^ 2))⁻¹ * ‖g‖)
        = (K * (Real.sqrt (1 + K ^ 2))⁻¹) * ‖g‖ := by ring
      _ < 1 * ‖g‖ := by exact mul_lt_mul_of_pos_right hfac hgpos
      _ = ‖g‖ := one_mul _
  linarith

end GaloisForLFunctions.HTGeometry
