import GaloisForLFunctions.BiScaleUncertainty.ProbeResolutionLaw
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import Zeta23.WeilEF.Main
import Zeta23.Statement.SeamClosed
import Zeta23.ExplicitFormula.Bridge

/-!
# Probe Parseval law: a compact source's packet is an almost periodic zero series

For a real compact `C²` source `f` with `f(v) = 0` for `|v| > w`, the stationary prime–polar
packet at shift `τ`,

`P_f(τ) = Σ_n Λ(n) n^{-1/2} f(log n − τ) − ∫_0^∞ 2 cosh(x/2) f(x − τ) dx`,

is, for every `τ > w`, **exactly** an absolutely convergent zero series plus an archimedean tail:

`Σ_ρ m_ρ e^{iγ_ρ τ} f̂(γ_ρ) = A_f(τ) − P_f(τ)`, `A_f(τ) = (1/2π) ∫ e^{irτ} f̂(r) γ(r) dr → 0`.

This is the explicit formula (Zeta23's `EF_lit_zetaZeroConfig`) for the translate `f(· − τ)`:
beyond the support the negative logarithms drop out and the two pole terms are exactly the polar
density of `ν`.

**Parseval law.** Under RH the ordinates are real and distinct, so `P_f` is a Bohr almost periodic
function with Fourier coefficients `−m_ρ f̂(γ_ρ)` plus a tail tending to zero, and

`(1/L) ∫_w^L P_f² → Σ_ρ m_ρ² |f̂(γ_ρ)|²`.

The probe band slope of `sum_order_sq_mul_probe_le` is therefore attained: every compact probe
reads exactly its weighted zero energy, and its packet is bounded.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-! ## Mean square of an absolutely convergent almost periodic series -/

/-- `(1/L) ∫_0^L e^{iΔτ} dτ`. -/
def characterMean (Δ L : ℝ) : ℂ := (∫ τ in (0 : ℝ)..L, Complex.exp ((Δ * τ : ℝ) * I)) / L

theorem norm_characterMean_le (Δ : ℝ) {L : ℝ} (hL : 0 < L) : ‖characterMean Δ L‖ ≤ 1 := by
  rw [characterMean, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
    div_le_one hL]
  calc ‖∫ τ in (0 : ℝ)..L, Complex.exp ((Δ * τ : ℝ) * I)‖ ≤ 1 * |L - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => by
          rw [Complex.norm_exp_ofReal_mul_I]
    _ = L := by rw [sub_zero, abs_of_pos hL, one_mul]

theorem characterMean_zero {L : ℝ} (hL : 0 < L) : characterMean 0 L = 1 := by
  simp [characterMean, hL.ne']

theorem tendsto_characterMean {Δ : ℝ} (hΔ : Δ ≠ 0) :
    Tendsto (characterMean Δ) atTop (𝓝 0) := by
  have hint : ∀ L : ℝ, ∫ τ in (0 : ℝ)..L, Complex.exp ((Δ * τ : ℝ) * I) =
      (Complex.exp ((Δ * L : ℝ) * I) - 1) / (Δ * I) := by
    intro L
    have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ
    have hΔI : (Δ : ℂ) * I ≠ 0 := mul_ne_zero hΔc I_ne_zero
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun τ : ℝ => Complex.exp ((Δ * τ : ℝ) * I) / (Δ * I)) (fun τ _ => by
        have h1 : HasDerivAt (fun τ : ℝ => (((Δ * τ : ℝ) : ℂ) * I)) (Δ * I) τ := by
          have := ((hasDerivAt_id τ).const_mul Δ).ofReal_comp.mul_const I
          simpa using this
        exact (h1.cexp.div_const ((Δ : ℂ) * I)).congr_deriv (by field_simp))
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    ring
  have hbound : ∀ L : ℝ, 0 < L → ‖characterMean Δ L‖ ≤ 2 / (|Δ| * L) := by
    intro L hL
    rw [characterMean, hint, norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hnum : ‖Complex.exp ((Δ * L : ℝ) * I) - 1‖ ≤ 2 := by
      calc ‖Complex.exp ((Δ * L : ℝ) * I) - 1‖ ≤ ‖Complex.exp ((Δ * L : ℝ) * I)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
    have hΔ0 : 0 < |Δ| := abs_pos.mpr hΔ
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hΔ0 hL]
  refine squeeze_zero_norm' (a := fun L => 2 / (|Δ| * L)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL using hbound L hL
  · have hΔ0 : 0 < |Δ| := abs_pos.mpr hΔ
    exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hΔ0)

/-- **Parseval for an absolutely convergent almost periodic series.** If `Σ ‖a_i‖ < ∞` and the
real frequencies `γ_i` are distinct, then `(1/L) ∫_0^L |Σ_i a_i e^{iγ_i τ}|² dτ → Σ_i |a_i|²`. -/
theorem tendsto_mean_normSq_tsum {ι : Type*} [Countable ι] {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {γ : ι → ℝ} (hγ : Function.Injective γ) :
    Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L,
        ‖∑' i, a i * Complex.exp ((γ i * τ : ℝ) * I)‖ ^ 2) / L)
      atTop (𝓝 (∑' i, ‖a i‖ ^ 2)) := by
  classical
  set e : ι → ℝ → ℂ := fun i τ => a i * Complex.exp ((γ i * τ : ℝ) * I) with he
  have hne : ∀ i τ, ‖e i τ‖ = ‖a i‖ := fun i τ => by
    rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hes : ∀ τ, Summable fun i => ‖e i τ‖ := fun τ => by simpa [hne] using ha
  -- the pair expansion of `|A|²`
  set p : ι × ι → ℝ → ℂ := fun ij τ =>
    a ij.1 * (starRingEnd ℂ) (a ij.2) * Complex.exp (((γ ij.1 - γ ij.2) * τ : ℝ) * I) with hp
  have hpn : ∀ ij τ, ‖p ij τ‖ = ‖a ij.1‖ * ‖a ij.2‖ := fun ij τ => by
    rw [hp, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj]
  have hps : Summable fun ij : ι × ι => ‖a ij.1‖ * ‖a ij.2‖ := by
    have := Summable.mul_norm ha ha
    simpa [norm_mul] using this
  have hsq : ∀ τ : ℝ, ((‖∑' i, e i τ‖ ^ 2 : ℝ) : ℂ) = ∑' ij : ι × ι, p ij τ := by
    intro τ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Complex.conj_tsum,
      tsum_mul_tsum_of_summable_norm (hes τ)
      (by simpa [Complex.norm_conj] using hes τ)]
    refine tsum_congr fun ij => ?_
    simp only [he, hp, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_mul, Complex.conj_I]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  -- integrate termwise
  have hint : ∀ L : ℝ, 0 ≤ L → ((∫ τ in (0 : ℝ)..L, ‖∑' i, e i τ‖ ^ 2 : ℝ) : ℂ) =
      ∑' ij : ι × ι, a ij.1 * (starRingEnd ℂ) (a ij.2) *
        ∫ τ in (0 : ℝ)..L, Complex.exp (((γ ij.1 - γ ij.2) * τ : ℝ) * I) := by
    intro L hL
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hsq]
    have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := L) (F := p) (f := fun τ => ∑' ij : ι × ι, p ij τ)
      (fun (ij : ι × ι) (_ : ℝ) => ‖a ij.1‖ * ‖a ij.2‖)
      (fun ij => (Continuous.aestronglyMeasurable (by simp only [hp]; fun_prop)))
      (fun ij => Eventually.of_forall fun τ _ => (hpn ij τ).le)
      (Eventually.of_forall fun τ _ => hps)
      intervalIntegrable_const
      (Eventually.of_forall fun τ _ => (Summable.of_norm (by simpa [hpn] using hps)).hasSum)
    rw [← hsum.tsum_eq]
    refine tsum_congr fun ij => ?_
    simp only [hp]
    rw [intervalIntegral.integral_const_mul]
  -- the mean
  have hmean : ∀ L : ℝ, 0 < L → (((∫ τ in (0 : ℝ)..L, ‖∑' i, e i τ‖ ^ 2) / L : ℝ) : ℂ) =
      ∑' ij : ι × ι, a ij.1 * (starRingEnd ℂ) (a ij.2) * characterMean (γ ij.1 - γ ij.2) L := by
    intro L hL
    rw [Complex.ofReal_div, hint L hL.le, ← tsum_div_const]
    refine tsum_congr fun ij => ?_
    rw [characterMean, mul_div_assoc]
  -- the limit
  have hlimC : Tendsto (fun L : ℝ => ∑' ij : ι × ι, a ij.1 * (starRingEnd ℂ) (a ij.2) *
      characterMean (γ ij.1 - γ ij.2) L) atTop
      (𝓝 (∑' ij : ι × ι, if ij.1 = ij.2 then a ij.1 * (starRingEnd ℂ) (a ij.2) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hps (fun ij => ?_) ?_
    · by_cases hij : ij.1 = ij.2
      · rw [if_pos hij]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
        rw [hij, sub_self, characterMean_zero hL, mul_one]
      · rw [if_neg hij]
        have := (tendsto_characterMean (sub_ne_zero.mpr fun h => hij (hγ h))).const_mul
          (a ij.1 * (starRingEnd ℂ) (a ij.2))
        simpa using this
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL ij
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (by positivity) (norm_characterMean_le _ hL)
  have hdiag : (∑' ij : ι × ι, if ij.1 = ij.2 then a ij.1 * (starRingEnd ℂ) (a ij.2) else 0) =
      ((∑' i, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
    have hsumm : Summable fun ij : ι × ι =>
        if ij.1 = ij.2 then a ij.1 * (starRingEnd ℂ) (a ij.2) else 0 :=
      Summable.of_norm (hps.of_nonneg_of_le (fun _ => norm_nonneg _) fun ij => by
        split_ifs
        · rw [norm_mul, Complex.norm_conj]
        · rw [norm_zero]; positivity)
    rw [hsumm.tsum_prod]
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun i => ?_
    rw [tsum_eq_single i fun j hj => if_neg (Ne.symm hj), if_pos rfl, Complex.mul_conj']
    push_cast; ring
  rw [hdiag] at hlimC
  have hre := (Complex.continuous_re.tendsto _).comp hlimC
  simp only [Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply]
  rw [← hmean L hL, Complex.ofReal_re]

/-! ## The packet explicit formula -/

/-- The stationary prime–polar packet of `f` at shift `τ`:
`P_f(τ) = Σ_n Λ(n) n^{-1/2} f(log n − τ) − ∫_0^∞ 2 cosh(x/2) f(x − τ) dx`. -/
def stationaryPacket (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * f (Real.log n - τ)) -
    ∫ x in Ioi (0 : ℝ), 2 * Real.cosh (x / 2) * f (x - τ)

/-- The archimedean tail `A_f(τ) = (1/2π) ∫ e^{irτ} f̂(r) γ(r) dr`. -/
def packetArchTail (f : ℝ → ℝ) (τ : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, Complex.exp (I * r * τ) *
    Zeta23.paperFT (fun u => (f u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)

/-- Translation multiplies the paper transform by a phase. -/
theorem paperFT_translate (f : ℝ → ℝ) (τ : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun u => (f (u - τ) : ℂ)) z =
      Complex.exp (I * z * τ) * Zeta23.paperFT (fun u => (f u : ℂ)) z := by
  unfold Zeta23.paperFT
  have h := integral_sub_right_eq_self
    (fun v : ℝ => (f v : ℂ) * Complex.exp (I * z * ((v + τ : ℝ) : ℂ))) τ (μ := volume)
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [show I * z * ((v + τ : ℝ) : ℂ) = I * z * v + I * z * τ by push_cast; ring, Complex.exp_add]
  ring

/-- **Packet explicit formula.** For a real compact `C²` source vanishing outside `[−w, w]` and
every shift `τ > w`, `Σ_ρ m_ρ e^{iγ_ρ τ} f̂(γ_ρ) = A_f(τ) − P_f(τ)`, absolutely. -/
theorem hasSum_packet_explicit_formula {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ}
    (hτ : w < τ) :
    HasSum (fun ρ : Zeta23.zetaZeroConfig.carrier => (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        (Complex.exp (I * Zeta23.gammaOf ρ * τ) *
          Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ)))
      (packetArchTail f τ - (stationaryPacket f τ : ℂ)) := by
  set k : ℝ → ℂ := fun u => (f (u - τ) : ℂ) with hk
  have hk2 : ContDiff ℝ 2 k :=
    Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_id.sub contDiff_const))
  have hkc : HasCompactSupport k :=
    (hfc.comp_homeomorph (Homeomorph.subRight τ)).comp_left Complex.ofReal_zero
  obtain ⟨hsum, heq⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk2 hkc
  have hτw : ∀ x : ℝ, x ≤ 0 → f (x - τ) = 0 := fun x hx =>
    hw _ (by rw [abs_of_neg (by linarith)]; linarith)
  -- the zero side
  have hzero : HasSum (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * (Complex.exp (I * Zeta23.gammaOf ρ * τ) *
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ))) (Zeta23.EF.literatureRHS k) := by
    rw [← heq]
    convert hsum.hasSum using 2 with ρ
    rw [hk, paperFT_translate]
  convert hzero using 1
  -- the literature right-hand side
  rw [Zeta23.EF.literatureRHS]
  have hprime : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) =
      ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * f (Real.log n - τ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hk]
    simp only
    rw [hτw (-Real.log n) (by linarith [Real.log_natCast_nonneg n])]
    push_cast; ring
  have hpole : Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) =
      ((∫ x in Ioi (0 : ℝ), 2 * Real.cosh (x / 2) * f (x - τ) : ℝ) : ℂ) := by
    have hcont : Continuous fun x : ℝ => f (x - τ) := hf.continuous.comp (by fun_prop)
    have hcs : HasCompactSupport fun x : ℝ => f (x - τ) :=
      hfc.comp_homeomorph (Homeomorph.subRight τ)
    have hint1 : Integrable fun x : ℝ => ((f (x - τ) * Real.exp (-x / 2) : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp (hcont.mul (by fun_prop))).integrable_of_hasCompactSupport
        ((hcs.mul_right).comp_left Complex.ofReal_zero)
    have hint2 : Integrable fun x : ℝ => ((f (x - τ) * Real.exp (x / 2) : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp (hcont.mul (by fun_prop))).integrable_of_hasCompactSupport
        ((hcs.mul_right).comp_left Complex.ofReal_zero)
    have h1 : Zeta23.paperFT k (I / 2) = ∫ x : ℝ, ((f (x - τ) * Real.exp (-x / 2) : ℝ) : ℂ) := by
      unfold Zeta23.paperFT
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hk]
      rw [show I * (I / 2) * (x : ℂ) = ((-x / 2 : ℝ) : ℂ) by
        push_cast; rw [show I * (I / 2) * (x : ℂ) = (I * I) * (x / 2) by ring, Complex.I_mul_I];
        ring, ← Complex.ofReal_exp]
      push_cast; ring
    have h2 : Zeta23.paperFT k (-I / 2) = ∫ x : ℝ, ((f (x - τ) * Real.exp (x / 2) : ℝ) : ℂ) := by
      unfold Zeta23.paperFT
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hk]
      rw [show I * (-I / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) by
        push_cast; rw [show I * (-I / 2) * (x : ℂ) = -(I * I) * (x / 2) by ring, Complex.I_mul_I];
        ring, ← Complex.ofReal_exp]
      push_cast; ring
    rw [h1, h2, ← integral_add hint1 hint2, integral_complex_ofReal,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) fun x hx => by
        rw [hτw x (not_lt.mp hx)]; push_cast; ring]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only
    rw [Real.cosh_eq]
    push_cast
    rw [show -(x / 2) = -x / 2 by ring]
    ring
  have hgamma : (1 / (2 * π) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) =
      packetArchTail f τ := by
    rw [packetArchTail]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hk]
    rw [paperFT_translate]
  rw [hprime, hpole, hgamma, stationaryPacket]
  push_cast
  ring

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
