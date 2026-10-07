import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialRemainder
import GaloisForLFunctions.RHTower.WeilAbelianTwistPowerRigidity

/-!
# Sublinear phase cancellation for the actual radial remainder

Measurability replaces continuous critical-edge assumptions. The source refined
remainder bound and generic measure layer cake pay every unbounded monotone
phase profile of sublinear power growth.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- The actual trace after removing one arithmetic resonant coefficient. -/
def quantizationRadialRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (m : ℕ) (τ : ℂ) (t : ℝ) : ℂ :=
  quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ -
    dirichletExp (lamLog lam) m * rhoMain m τ t

theorem measurable_quantizationRadialRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ : τ ≠ 0) : Measurable (quantizationRadialRemainder hW m τ) :=
  (((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).mul
    (continuous_pairKernel_two_mul hτ).measurable).sub
      ((continuous_rhoMain hm hτ).measurable.const_mul _)

theorem integrableOn_quantizationRadialRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) :
    IntegrableOn (quantizationRadialRemainder hW m τ) (Iic (-1)) := by
  obtain ⟨CB, _, hpoly⟩ := exists_quantization_trace_pair_bound hW
  have hphik : Integrable (fun t : ℝ => quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) := integrable_defectLaplace_integrand
    ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    (fun t => (hpoly t).1) hτre
  exact hphik.integrableOn.sub ((integrableOn_rhoMain hm hτre hτ1).const_mul _)

theorem norm_quantizationRadialRemainder_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖quantizationTraceF hW (2 * t)‖ ≤ CB * (1 + |t|) ^ N) {m : ℕ} (hm : 1 ≤ m) {τ : ℂ}
    (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {t : ℝ} (ht : t ≤ -1) :
    ‖quantizationRadialRemainder hW m τ t‖ ≤ (3 * CB + ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖)) *
      ((1 + |t|) ^ N * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) := by
  have hpow : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hτs : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
  have hk := norm_pairKernel_two_mul_le t hτre
  have hr := norm_rhoMain_le hm hτre hτ1 ht
  set E := Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold quantizationRadialRemainder
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖quantizationTraceF hW (2 * t)‖ * ‖pairKernel (2 * t) τ‖ ≤ 3 * CB * ((1 + |t|) ^ N * E) := by
    calc ‖quantizationTraceF hW (2 * t)‖ * ‖pairKernel (2 * t) τ‖
        ≤ (CB * (1 + |t|) ^ N) * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * E) :=
          mul_le_mul (hpoly t) hk (norm_nonneg _) (by positivity)
      _ ≤ (CB * (1 + |t|) ^ N) * (3 * 1 * E) := by gcongr
      _ = 3 * CB * ((1 + |t|) ^ N * E) := by ring
  have h2 : ‖dirichletExp (lamLog lam) m‖ * ‖rhoMain m τ t‖ ≤ ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
      ((1 + |t|) ^ N * E) := by
    calc ‖dirichletExp (lamLog lam) m‖ * ‖rhoMain m τ t‖ ≤ ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * E) :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ ≤ ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * ((1 + |t|) ^ N * E)) := by
          gcongr; nlinarith
      _ = _ := by ring
  linarith

theorem integrableOn_quantization_phase_mul_remainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖quantizationTraceF hW (2 * t)‖ ≤ CB * (1 + |t|) ^ N)
    {C : ℝ → ℝ} (hC : Monotone C) {K₁ : ℝ}
    (hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K₁ * (x + 1)) {m : ℕ} (hm : 1 ≤ m) {τ : ℂ}
    (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) (c : ℂ) :
    IntegrableOn (fun t => (C (-t) - C 1) * ‖c * quantizationRadialRemainder hW m τ t‖) (Iic (-1)) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτn : 0 < ‖τ‖ := by linarith
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := by positivity
  set D := 3 * CB + ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) with hD
  have hD0 : 0 ≤ D := by positivity
  set A := 2 * |K₁| + |C 1| with hA
  have hdom := ((integrable_one_add_abs_pow_mul_exp hδ (N + 1)).const_mul
    (A * (‖c‖ * D))).integrableOn (s := Iic (-1))
  have hmeas : AEStronglyMeasurable (fun t => (C (-t) - C 1) * ‖c * quantizationRadialRemainder hW m τ t‖)
      (volume.restrict (Iic (-1))) :=
    (((hC.measurable.comp measurable_neg).sub_const _).mul
      ((measurable_quantizationRadialRemainder hW hm hτ0).const_mul c).norm).aestronglyMeasurable
  refine hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Iic).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : t ≤ -1 := ht
  have hC1 : C 1 ≤ C (-t) := hC (by linarith)
  have habs : |t| = -t := abs_of_neg (by linarith)
  have hCt : C (-t) - C 1 ≤ A * (1 + |t|) := by
    have h0 := hK₁ (-t) (by linarith)
    have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hk1 : K₁ * (-t + 1) ≤ |K₁| * (2 * (1 + |t|)) := by
      rw [habs]
      calc K₁ * (-t + 1) ≤ |K₁ * (-t + 1)| := le_abs_self _
        _ = |K₁| * (-t + 1) := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < -t + 1 by linarith)]
        _ ≤ |K₁| * (2 * (1 + -t)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    have hc1 := neg_abs_le (C 1)
    nlinarith [abs_nonneg K₁, abs_nonneg (C 1)]
  have hr := norm_quantizationRadialRemainder_le hW hCB hpoly hm hτre hτ1 ht'
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _)), norm_mul]
  set E := Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc (C (-t) - C 1) * (‖c‖ * ‖quantizationRadialRemainder hW m τ t‖)
      ≤ (A * (1 + |t|)) * (‖c‖ * (D * ((1 + |t|) ^ N * E))) := by
        gcongr
    _ = A * (‖c‖ * D) * ((1 + |t|) ^ (N + 1) * E) := by ring


/-- Unbounded monotone phase profiles of sublinear power growth have vanishing radial error. -/
theorem tendsto_quantization_layer_remainder_pow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
      quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) := by
  set ν : ℝ := (1 - α) / 2 with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  have hν1 : ν ≤ 1 := by rw [hν]; linarith
  obtain ⟨Kr, hKr⟩ := exists_norm_quantization_radialError_le hW hν0 hν1 hm
  obtain ⟨CB, hCB, hpoly⟩ := exists_quantization_trace_pair_bound hW
  have hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K * (x + 1) := fun x hx => by
    have h1 : x ^ α ≤ x := by
      calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hα1.le
        _ = x := Real.rpow_one x
    nlinarith [hgrowth x hx]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set A : ℝ := |Kr| * (‖Ψ (C 1)‖ + L * max 0 (-C 1)) with hA
  set B : ℝ := |Kr| * L * (2 * K * ((m : ℝ) + 1) ^ α) with hB
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
        A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by
    intro ε hε hε1
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
    have hτM : ‖τ‖ ≤ m + 1 := by
      have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_pos hε] at h
      linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := ε / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hε hτpos
    set d : ℝ → ℂ := fun t => (ε : ℂ) * quantizationRadialRemainder hW m τ t with hd
    have hdm : Measurable d := (measurable_quantizationRadialRemainder hW hm hτ0).const_mul _
    have hphik : Integrable (fun t : ℝ => quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) := integrable_defectLaplace_integrand
      ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
      (fun t => (hpoly t).1) hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    have hdint : IntegrableOn d (Iic (-1)) :=
      (hphik.integrableOn.sub (hrho.const_mul (dirichletExp (lamLog lam) m))).const_mul (ε : ℂ)
    have hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)) :=
      integrableOn_quantization_phase_mul_remainder hW hCB (fun t => (hpoly t).1) hC hK₁ hm hτre0 hτ1 _
    have herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ (|Kr| * ε ^ (1 - ν)) * Real.exp (b * δ) := by
      intro b hb
      have h1 : ∫ t in Iic b, d t = (ε : ℂ) * ((∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
          dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m τ t) := by
        simp only [hd, quantizationRadialRemainder]
        rw [integral_const_mul, integral_sub hphik.integrableOn
          ((hrho.mono_set (Iic_subset_Iic.mpr hb)).const_mul (dirichletExp (lamLog lam) m)), integral_const_mul]
      rw [h1]
      refine (hKr ε hε hε1 b hb).trans ?_
      gcongr
      exact le_abs_self Kr
    have htw := norm_setIntegral_layer_le_pow hC hL hψm hψL hΨ hδ0 hα0 hα1.le hK
      (by positivity) hgrowth hdm.aestronglyMeasurable hdint hdom herr
    have e1 : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        quantizationRadialRemainder hW m τ t = ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t := by
      rw [← integral_const_mul]; congr 1; funext t; simp only [hd]; ring
    rw [e1]
    refine htw.trans ?_
    have hδα : δ ^ (-α) ≤ ((m : ℝ) + 1) ^ α * ε ^ (-α) := by
      rw [hδ, Real.div_rpow hε.le hτpos.le, Real.rpow_neg hτpos.le, div_inv_eq_mul, mul_comm]
      gcongr
    have hεmul : ε ^ (1 - ν) * ε ^ (-α) = ε ^ (1 - ν - α) := by
      rw [← Real.rpow_add hε]; ring_nf
    have hM0 : 0 ≤ max 0 (-C 1) := le_max_left _ _
    calc |Kr| * ε ^ (1 - ν) * (‖Ψ (C 1)‖ + L * (max 0 (-C 1) + 2 * K * δ ^ (-α)))
        = A * ε ^ (1 - ν) + |Kr| * L * (2 * K) * (ε ^ (1 - ν) * δ ^ (-α)) := by
          rw [hA]; ring
      _ ≤ A * ε ^ (1 - ν) + |Kr| * L * (2 * K) *
            (ε ^ (1 - ν) * (((m : ℝ) + 1) ^ α * ε ^ (-α))) := by gcongr
      _ = A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by rw [hB, ← hεmul]; ring
  have hp : 0 < 1 - ν := by linarith
  have hq : 0 < 1 - ν - α := by rw [hν]; linarith
  have hlim : Tendsto (fun ε : ℝ => A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (1 - ν)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν))) :=
      ((Real.continuous_rpow_const hp.le).tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν - α))) :=
      ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne'] at h1
    rw [Real.zero_rpow hq.ne'] at h2
    simpa using (h1.const_mul A).add (h2.const_mul B)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact hbound ε hε.1 hε.2.le


theorem tendsto_quantization_twisted_remainder_pow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α) (β₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) :=
  tendsto_quantization_layer_remainder_pow hW hC hα0 hα1 hK hgrowth
    (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I)) (ψ := phaseDensity β₀) (abs_nonneg β₀)
    (continuous_phaseDensity β₀).measurable (fun x => (norm_phaseDensity β₀ x).le)
    (fun _ _ huv => phase_eq_add_setIntegral β₀ huv) hm

end RHTower.WeilSpectral
