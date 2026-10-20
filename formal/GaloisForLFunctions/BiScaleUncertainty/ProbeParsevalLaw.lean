import GaloisForLFunctions.BiScaleUncertainty.ProbeResolutionLaw
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import Zeta23.WeilEF.Main
import Zeta23.Statement.SeamClosed
import Zeta23.ExplicitFormula.Bridge
import Zeta23.Taper.Decay
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.WeilDeletionTwoBump

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
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Complex.exp (I * r * τ) *
    Zeta23.paperFT (fun u => (f u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)

/-- **Packet explicit formula.** For a real compact `C²` source vanishing outside `[−w, w]` and
every shift `τ > w`, `Σ_ρ m_ρ e^{iγ_ρ τ} f̂(γ_ρ) = A_f(τ) − P_f(τ)`, absolutely. -/
theorem hasSum_packet_explicit_formula {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ}
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
    rw [hk, RHTower.WeilDeletion.paperFT_translate]
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
    rw [h1, h2, ← integral_add hint1 hint2]
    simp_rw [← Complex.ofReal_add]
    rw [integral_complex_ofReal,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) fun x hx => by
        rw [hτw x (not_lt.mp hx)]; ring]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Real.cosh_eq, show -(x / 2) = -x / 2 by ring]
    ring
  have hgamma : (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) =
      packetArchTail f τ := by
    rw [packetArchTail]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hk]
    rw [RHTower.WeilDeletion.paperFT_translate]
  rw [hprime, hpole, hgamma, stationaryPacket]
  push_cast
  ring

/-! ## The archimedean tail vanishes at infinity -/

theorem integrable_paperFT_mul_gammaBracket {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) :
    Integrable fun r : ℝ => Zeta23.paperFT (fun u => (f u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ) := by
  set f₀ : ℝ → ℂ := fun u => (f u : ℂ)
  have hf₀ : ContDiff ℝ 2 f₀ := Complex.ofRealCLM.contDiff.comp hf
  have hΛ : ∀ u, f₀ u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    exact hu (by simp only [f₀]; rw [hw u (not_le.mp h), Complex.ofReal_zero])
  set M := (∫ u, ‖f₀ u‖) + ∫ u, ‖deriv (deriv f₀) u‖
  set c₀ := RHTower.digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi
  have hfi : Integrable f₀ :=
    hf₀.continuous.integrable_of_hasCompactSupport
      (Zeta23.hasCompactSupport_of_support_subset_abs hΛ)
  have hcont : Continuous fun r : ℝ => Zeta23.paperFT f₀ r * (Zeta23.EF.gammaBracket r : ℂ) :=
    (Zeta23.Taper.continuous_paperFT_ofReal hfi).mul
      (Complex.continuous_ofReal.comp RHTower.WeilHerglotz.continuous_gammaBracket)
  have hdom := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2)
    (by simp; norm_num)).const_mul (M * (2 * |c₀| + 4))
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hM : ‖Zeta23.paperFT f₀ r‖ * (1 + r ^ 2) ≤ M := Zeta23.EF.norm_paperFT_mul_one_add_sq_le hf₀ hΛ r
  have hγ := RHTower.WeilSpectral.abs_gammaBracket_le_sqrt r
  set u := 1 + |r| with hu
  have hu1 : 1 ≤ u := by rw [hu]; linarith [abs_nonneg r]
  have hsq : u ^ 2 ≤ 2 * (1 + r ^ 2) := by
    rw [hu]; nlinarith [sq_abs r, abs_nonneg r, sq_nonneg (|r| - 1)]
  have hrpow : u ^ (-(3 / 2 : ℝ)) = 1 / (u * Real.sqrt u) := by
    rw [Real.rpow_neg (by linarith), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  simp only [Real.norm_eq_abs] at hdom ⊢
  rw [← hu, hrpow]
  have hsqrt1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu1
  have hsqrt2 : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
  have hpos : 0 < u * Real.sqrt u := by positivity
  have hP : ‖Zeta23.paperFT f₀ r‖ ≤ 2 * M / u ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h0 := norm_nonneg (Zeta23.paperFT f₀ r)
    nlinarith
  have hG : |Zeta23.EF.gammaBracket r| ≤ (|c₀| + 2) * Real.sqrt u := by
    have hγ' : |Zeta23.EF.gammaBracket r| ≤ c₀ + 2 * Real.sqrt u := hγ
    have h1 : c₀ ≤ |c₀| * Real.sqrt u :=
      (le_abs_self c₀).trans (le_mul_of_one_le_right (abs_nonneg c₀) hsqrt1)
    linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_of_le_of_eq (le_mul_of_one_le_right
    (norm_nonneg _) (by nlinarith [sq_nonneg r])) rfl) |>.trans hM
  calc ‖Zeta23.paperFT f₀ r‖ * |Zeta23.EF.gammaBracket r|
      ≤ (2 * M / u ^ 2) * ((|c₀| + 2) * Real.sqrt u) :=
        mul_le_mul hP hG (abs_nonneg _) (by positivity)
    _ = M * (2 * |c₀| + 4) * (1 / (u * Real.sqrt u)) := by
        field_simp
        rw [Real.sq_sqrt (by linarith)]
        ring

/-- **The archimedean tail tends to zero** (Riemann–Lebesgue). -/
theorem tendsto_packetArchTail (f : ℝ → ℝ) : Tendsto (packetArchTail f) atTop (𝓝 0) := by
  set F : ℝ → ℂ := fun r => Zeta23.paperFT (fun u => (f u : ℂ)) r *
    (Zeta23.EF.gammaBracket r : ℂ)
  have hRL := Real.tendsto_integral_exp_smul_cocompact F
  have hmap : Tendsto (fun τ : ℝ => -(τ / (2 * Real.pi))) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by positivity))).mono_right
      atBot_le_cocompact
  have hcomp := (hRL.comp hmap).const_mul (1 / (2 * Real.pi) : ℂ)
  rw [mul_zero] at hcomp
  refine hcomp.congr fun τ => ?_
  simp only [Function.comp_apply, packetArchTail]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [F, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [← mul_assoc]
  congr 2
  push_cast
  field_simp

theorem continuous_paperFT_mul_gammaBracket {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Continuous fun r : ℝ => Zeta23.paperFT (fun u => (f u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ) :=
  (Zeta23.Taper.continuous_paperFT_ofReal (hf.continuous.integrable_of_hasCompactSupport hfc
      |>.ofReal)).mul
    (Complex.continuous_ofReal.comp RHTower.WeilHerglotz.continuous_gammaBracket)

theorem continuous_packetArchTail {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {w : ℝ} (hw : ∀ v : ℝ, w < |v| → f v = 0) : Continuous (packetArchTail f) := by
  have hF := integrable_paperFT_mul_gammaBracket hf hw
  have hFc := continuous_paperFT_mul_gammaBracket hf hfc
  unfold packetArchTail
  have hcont : Continuous fun τ : ℝ => ∫ r : ℝ, Complex.exp (I * r * τ) *
      (Zeta23.paperFT (fun u => (f u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)) := by
    refine continuous_of_dominated (bound := fun r =>
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)‖)
      (fun τ => ((by fun_prop : Continuous fun r : ℝ => Complex.exp (I * r * τ)).mul
        hFc).aestronglyMeasurable)
      (fun τ => Eventually.of_forall fun r => ?_) hF.norm
      (Eventually.of_forall fun r => by fun_prop)
    rw [norm_mul, show I * (r : ℂ) * τ = ((r * τ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  refine continuous_const.mul (hcont.congr fun τ => ?_)
  congr 1
  funext r
  ring

/-! ## Cesàro means of vanishing functions -/

/-- A continuous function tending to zero has vanishing Cesàro means. -/
private theorem tendsto_mean_of_tendsto_zero {g : ℝ → ℝ} (hg : Continuous g)
    (h0 : Tendsto g atTop (𝓝 0)) (w : ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, g τ) / L) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h0) (ε / 2) (half_pos hε)
  set T' := max (max T w) 0
  set C := |∫ τ in w..T', g τ|
  refine ⟨max T' (max 1 (2 * C / ε + 1)), fun L hL => ?_⟩
  have hLT : T' ≤ L := le_of_max_le_left hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans (le_of_max_le_right hL)
  have hLC : 2 * C / ε + 1 ≤ L := (le_max_right _ _).trans (le_of_max_le_right hL)
  have hL0 : 0 < L := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) w T') (hg.intervalIntegrable (μ := volume) T' L)
  have htail : |∫ τ in T'..L, g τ| ≤ ε / 2 * |L - T'| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T') (b := L) (f := g)
      (C := ε / 2) fun τ hτ => by
        rw [uIoc_of_le hLT] at hτ
        have := hT τ ((le_max_left T w).trans ((le_max_left _ 0).trans hτ.1.le))
        rw [Real.dist_eq, sub_zero] at this
        exact (Real.norm_eq_abs _).le.trans this.le
    simpa [Real.norm_eq_abs] using this
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hL0, div_lt_iff₀ hL0, ← hsplit]
  have hCL : C < ε / 2 * L := by
    have := (div_lt_iff₀ hε).mp (show 2 * C / ε < L by linarith)
    linarith
  calc |(∫ τ in w..T', g τ) + ∫ τ in T'..L, g τ| ≤ C + |∫ τ in T'..L, g τ| := abs_add_le _ _
    _ ≤ C + ε / 2 * |L - T'| := by linarith
    _ < ε * L := by
        rw [abs_of_nonneg (by linarith)]
        have hT'0 : 0 ≤ T' := le_max_right _ 0
        have : ε / 2 * (L - T') ≤ ε / 2 * L := by nlinarith
        linarith

/-! ## The Parseval law under RH -/

theorem re_eq_half_of_mem (hRH : RiemannHypothesis) (ρ : Zeta23.zetaZeroConfig.carrier) :
    (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨hz, hre0, hre1⟩ := ρ.2
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rw [this] at hre0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at hre1; simp at hre1

theorem gammaOf_eq_im (hRH : RiemannHypothesis) (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.gammaOf ρ = (((ρ : ℂ).im : ℝ) : ℂ) := by
  have hre := re_eq_half_of_mem hRH ρ
  unfold Zeta23.gammaOf
  have : (ρ : ℂ) - 1 / 2 = (((ρ : ℂ).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [this, mul_div_cancel_right₀ _ I_ne_zero]

theorem im_injective (hRH : RiemannHypothesis) :
    Function.Injective fun ρ : Zeta23.zetaZeroConfig.carrier => (ρ : ℂ).im := by
  intro ρ ρ' h
  apply Subtype.ext
  apply Complex.ext
  · rw [re_eq_half_of_mem hRH ρ, re_eq_half_of_mem hRH ρ']
  · exact h

/-- **Probe Parseval law.** Under RH, for a real compact `C²` source `f` vanishing outside
`[−w, w]`, the stationary packet has mean square `(1/L)∫_w^L P_f² → Σ_ρ m_ρ² |f̂(γ_ρ)|²`. -/
theorem tendsto_mean_sq_stationaryPacket (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → f v = 0) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket f τ ^ 2) / L) atTop
      (𝓝 (∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult ρ : ℝ) ^ 2 * ‖probeTransform f ((ρ : ℂ).im)‖ ^ 2)) := by
  set f₀ : ℝ → ℂ := fun u => (f u : ℂ)
  set a : Zeta23.zetaZeroConfig.carrier → ℂ := fun ρ =>
    (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT f₀ (((ρ : ℂ).im : ℝ) : ℂ) with ha
  -- absolute summability of the coefficients
  have hsumm : Summable fun ρ => ‖a ρ‖ := by
    obtain ⟨hs, -⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig f₀ (Complex.ofRealCLM.contDiff.comp hf)
      (hfc.comp_left Complex.ofReal_zero)
    rw [summable_norm_iff]
    refine hs.congr fun ρ => ?_
    simp only [ha, gammaOf_eq_im hRH ρ]
  set S₁ := ∑' ρ, ‖a ρ‖
  set A : ℝ → ℂ := fun τ => ∑' ρ, a ρ * Complex.exp ((((ρ : ℂ).im * τ : ℝ) : ℂ) * I) with hA
  have hnormA : ∀ τ ρ, ‖a ρ * Complex.exp ((((ρ : ℂ).im * τ : ℝ) : ℂ) * I)‖ = ‖a ρ‖ :=
    fun τ ρ => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hAbound : ∀ τ, ‖A τ‖ ≤ S₁ := fun τ =>
    (norm_tsum_le_tsum_norm (hsumm.congr fun ρ => (hnormA τ ρ).symm)).trans
      (le_of_eq (tsum_congr fun ρ => hnormA τ ρ))
  have hAc : Continuous A := continuous_tsum (fun ρ => by fun_prop) hsumm fun ρ τ => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- the packet explicit formula
  have hEF : ∀ τ, w < τ → (stationaryPacket f τ : ℂ) = packetArchTail f τ - A τ := by
    intro τ hτ
    have h := hasSum_packet_explicit_formula hf hfc hw0 hw hτ
    have hA' : HasSum (fun ρ => a ρ * Complex.exp ((((ρ : ℂ).im * τ : ℝ) : ℂ) * I))
        (packetArchTail f τ - (stationaryPacket f τ : ℂ)) := by
      convert h using 2 with ρ
      simp only [ha, gammaOf_eq_im hRH ρ]
      rw [show (((ρ : ℂ).im * τ : ℝ) : ℂ) * I = I * (((ρ : ℂ).im : ℝ) : ℂ) * τ by push_cast; ring]
      ring
    have hAτ : A τ = packetArchTail f τ - (stationaryPacket f τ : ℂ) := hA'.tsum_eq
    rw [hAτ]; ring
  have hsq : ∀ τ, w < τ → stationaryPacket f τ ^ 2 = ‖packetArchTail f τ - A τ‖ ^ 2 := by
    intro τ hτ
    rw [← hEF τ hτ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the archimedean error
  set D : ℝ → ℝ := fun τ => ‖packetArchTail f τ - A τ‖ ^ 2 - ‖A τ‖ ^ 2 with hD
  have hArc := continuous_packetArchTail hf hfc hw
  have hDc : Continuous D := by simp only [hD]; fun_prop
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have harch := tendsto_packetArchTail f
    have hb : ∀ τ, |D τ| ≤ ‖packetArchTail f τ‖ * (2 * S₁ + ‖packetArchTail f τ‖) := by
      intro τ
      have h1 := norm_sub_le (packetArchTail f τ) (A τ)
      have h2 := norm_sub_rev (packetArchTail f τ) (A τ) ▸ norm_sub_norm_le (A τ) (packetArchTail f τ)
      have h3 := hAbound τ
      have h4 := abs_norm_sub_norm_le (packetArchTail f τ - A τ) (-(A τ))
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at h4
      have hnn := norm_nonneg (packetArchTail f τ)
      have hnA := norm_nonneg (A τ)
      rw [abs_le]
      constructor <;> nlinarith [abs_le.mp h4, norm_nonneg (packetArchTail f τ - A τ)]
    have hlim : Tendsto (fun τ => ‖packetArchTail f τ‖ * (2 * S₁ + ‖packetArchTail f τ‖)) atTop
        (𝓝 (‖(0 : ℂ)‖ * (2 * S₁ + ‖(0 : ℂ)‖))) :=
      harch.norm.mul (tendsto_const_nhds.add harch.norm)
    rw [norm_zero, zero_mul] at hlim
    exact squeeze_zero_norm (fun τ => by rw [Real.norm_eq_abs]; exact hb τ) hlim
  -- assemble the mean
  haveI : Countable Zeta23.zetaZeroConfig.carrier :=
    RHTower.WeilConditional.countable_carrier.to_subtype
  have hmain := tendsto_mean_normSq_tsum hsumm (im_injective hRH)
  have hcesaro := tendsto_mean_of_tendsto_zero hDc hD0 w
  have hconst : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..w, ‖A τ‖ ^ 2) / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (hmain.sub hconst).add hcesaro
  rw [sub_zero, add_zero] at hsum
  have htarget : (∑' ρ, ‖a ρ‖ ^ 2) = ∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) ^ 2 * ‖probeTransform f ((ρ : ℂ).im)‖ ^ 2 := by
    refine tsum_congr fun ρ => ?_
    simp only [ha, norm_mul, Complex.norm_natCast, mul_pow]
    congr 2
    unfold Zeta23.paperFT probeTransform
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [f₀]
    rw [mul_comm]
    congr 2
    push_cast; ring
  rw [htarget] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop w] with L hL
  have hAI : ∀ a b : ℝ, IntervalIntegrable (fun τ => ‖A τ‖ ^ 2) volume a b :=
    fun a b => (hAc.norm.pow 2).intervalIntegrable a b
  have hcongr : (∫ τ in w..L, stationaryPacket f τ ^ 2) =
      ∫ τ in w..L, (‖A τ‖ ^ 2 + D τ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
    rw [uIoc_of_le hL] at hτ
    rw [hsq τ hτ.1]; simp only [hD]; ring
  rw [hcongr, intervalIntegral.integral_add (hAI w L) (hDc.intervalIntegrable w L),
    ← intervalIntegral.integral_interval_sub_left (hAI 0 L) (hAI 0 w)]
  field_simp
  ring

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
