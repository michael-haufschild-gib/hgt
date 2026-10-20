import GaloisForLFunctions.BiScaleUncertainty.PairingRecurrenceLaw
import GaloisForLFunctions.RHTower.WeilDeletionTestKit

/-!
# An explicit universal probe: the boosted cubic spline

A universal probe (`SeesAllZeros`) decides RH, the zero width and simplicity through one packet.
All but countably many boosts of a nonzero source are universal, but that exceptional set is not
explicit. This module makes the boost explicit.

**Real-rooted sources.** Suppose `φ̂` has no zeros off the real axis. Then every boost with
`|t| ≥ 1/2` is a universal probe (`seesAllZeros_tiltedSource_of_im_ne_zero`). A boost translates
the transform vertically, `(e^{t·}φ)^(γ_ρ) = φ̂(γ_ρ − it)`, and every zero has `|Im γ_ρ| < 1/2`.
So the evaluation point leaves the real axis.

**Box smoothing gains one derivative.** `(U_w ⋆ g)(x) = (G(x+w) − G(x−w))/(2w)` with `G` the
primitive of `g`, so `U_w^{⋆(k+2)}` is `Cᵏ` (`contDiff_upow`).

**The cubic spline.** Let `B = U_1^{⋆4}` be the four-fold convolution of the uniform density on
`[−1, 1]`. It is `C²` and supported in `[−4, 4]`. Its transform is `(sin z / z)⁴`, which is
real-rooted. Hence `U(u) = eᵘ B(u)` is a universal probe (`seesAllZeros_splineProbe`), and

`RH ⟺ Σ_n Λ(n) √n B(log n − τ) ≤ ∫_0^∞ 2cosh(x/2) eˣ B(x − τ) dx + K e^τ` for all large `τ`

(`riemannHypothesis_iff_spline_prime_sum_le`): one fixed spline-weighted prime sum is compared
against its polar prediction. With `e^{(1+β)τ}` in place of `e^τ` the same comparison is the zero
width bound `Re ρ ≤ 1/2 + β`. The single packet `P_U` also gives the band criterion, and its
asymptotic mean square gives RH together with the simplicity of every zero.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Convolution
open RHTower.WeilDeletion (unif upow integrable_upow hasCompactSupport_upow paperFT_unif paperFT_upow
  support_upow_subset)

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Real-rooted sources boost to universal probes -/

/-- **Real-rooted boost law.** If `φ̂` vanishes only on the real axis, every boost with
`|t| ≥ 1/2` sees every zero. -/
theorem seesAllZeros_tiltedSource_of_im_ne_zero {φ : ℝ → ℝ}
    (hφ : ∀ z : ℂ, z.im ≠ 0 → Zeta23.paperFT (fun u => (φ u : ℂ)) z ≠ 0) {t : ℝ}
    (ht : 1 / 2 ≤ |t|) : SeesAllZeros (tiltedSource φ t) := fun ρ => by
  rw [paperFT_tiltedSource]
  refine hφ _ fun h => ?_
  have hγ := Zeta23.WeilEF.abs_gammaOf_im_lt (ρ := (ρ : ℂ)) ⟨ρ.property.2.1, ρ.property.2.2⟩
  have him : (Zeta23.gammaOf ρ).im = t := by simpa [sub_eq_zero] using h
  rw [him] at hγ
  linarith

/-! ## Box smoothing gains one derivative -/

/-- Box smoothing is a difference of primitives: `(U_w ⋆ g)(x) = (G(x+w) − G(x−w))/(2w)`. -/
theorem unif_convolution_eq {w : ℝ} (hw : 0 < w) {g : ℝ → ℝ} (hg : Integrable g) (x : ℝ) :
    (unif w ⋆ g) x =
      1 / (2 * w) * ((∫ t in (0 : ℝ)..x + w, g t) - ∫ t in (0 : ℝ)..x - w, g t) := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hind : (fun t => unif w t * g (x - t)) =
      (Icc (-w) w).indicator (fun t => 1 / (2 * w) * g (x - t)) := by
    funext t
    unfold unif
    by_cases ht : t ∈ Icc (-w) w
    · rw [indicator_of_mem ht, indicator_of_mem ht]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left g x, sub_neg_eq_add,
    intervalIntegral.integral_interval_sub_left hg.intervalIntegrable hg.intervalIntegrable]

/-- The primitive of a `Cᵏ` function is `Cᵏ⁺¹`. -/
theorem contDiff_primitive {g : ℝ → ℝ} {k : ℕ} (hg : ContDiff ℝ k g) :
    ContDiff ℝ (k + 1 : ℕ) (fun x => ∫ t in (0 : ℝ)..x, g t) := by
  have hd : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g x) x := fun x =>
    (hg.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  rw [Nat.cast_succ, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
  rwa [show deriv (fun x => ∫ t in (0 : ℝ)..x, g t) = g from funext fun x => (hd x).deriv]

theorem continuous_unif_convolution {w : ℝ} (hw : 0 < w) {g : ℝ → ℝ} (hg : Integrable g) :
    Continuous (unif w ⋆ g) := by
  have hP := intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ => hg.intervalIntegrable) 0
  rw [funext (unif_convolution_eq hw hg)]
  exact continuous_const.mul ((hP.comp (continuous_id.add continuous_const)).sub
    (hP.comp (continuous_id.sub continuous_const)))

theorem contDiff_unif_convolution {w : ℝ} (hw : 0 < w) {g : ℝ → ℝ} (hg : Integrable g) {k : ℕ}
    (hk : ContDiff ℝ k g) : ContDiff ℝ (k + 1 : ℕ) (unif w ⋆ g) := by
  have hP := contDiff_primitive hk
  rw [funext (unif_convolution_eq hw hg)]
  exact contDiff_const.mul ((hP.comp (contDiff_id.add contDiff_const)).sub
    (hP.comp (contDiff_id.sub contDiff_const)))

/-- `U_w^{⋆(k+2)}` is `Cᵏ`. -/
theorem contDiff_upow {w : ℝ} (hw : 0 < w) : ∀ k : ℕ, ContDiff ℝ k (upow w (k + 1))
  | 0 => by
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_unif_convolution hw (integrable_upow w 0)
  | k + 1 => contDiff_unif_convolution hw (integrable_upow w (k + 1)) (contDiff_upow hw k)

/-! ## The cubic spline -/

/-- The uniform density has a real-rooted transform `sin(wz)/(wz)`. -/
theorem paperFT_unif_ne_zero {w : ℝ} (hw : 0 < w) {z : ℂ} (hz : z.im ≠ 0) :
    Zeta23.paperFT (fun x => (unif w x : ℂ)) z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => hz (by rw [h, zero_im])
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [paperFT_unif hw hz0]
  refine div_ne_zero (fun h => ?_)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hz0) hw')
  have h1 : Complex.exp (2 * (I * z * w)) = 1 := by
    rw [two_mul, Complex.exp_add]
    nth_rewrite 2 [sub_eq_zero.mp h]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hre := congrArg Complex.re hn
  simp [Complex.mul_re, Complex.mul_im] at hre
  exact hre.elim hz hw.ne'

/-- The cubic spline `B = U_1^{⋆4}`. -/
def cubicSpline : ℝ → ℝ := upow 1 3

theorem contDiff_cubicSpline : ContDiff ℝ 2 cubicSpline := by
  exact_mod_cast contDiff_upow one_pos 2

theorem hasCompactSupport_cubicSpline : HasCompactSupport cubicSpline := hasCompactSupport_upow 1 3

theorem cubicSpline_eq_zero {v : ℝ} (hv : 4 < |v|) : cubicSpline v = 0 := by
  by_contra h
  have hm := support_upow_subset one_pos 3 h
  have := abs_le.mpr ⟨hm.1, hm.2⟩
  norm_num at this
  linarith

/-- `B̂(z) = (sin z / z)⁴` has no zeros off the real axis. -/
theorem paperFT_cubicSpline_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Zeta23.paperFT (fun x => (cubicSpline x : ℂ)) z ≠ 0 := by
  unfold cubicSpline
  rw [paperFT_upow]
  exact pow_ne_zero _ (paperFT_unif_ne_zero one_pos hz)

/-- Every boost `|t| ≥ 1/2` of every uniform spline is a universal probe. -/
theorem seesAllZeros_tiltedSource_upow {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    SeesAllZeros (tiltedSource (upow w n) t) :=
  seesAllZeros_tiltedSource_of_im_ne_zero (fun _ hz => by
    rw [paperFT_upow]; exact pow_ne_zero _ (paperFT_unif_ne_zero hw hz)) ht

/-! ## The explicit probe and its criteria -/

/-- The explicit universal probe `U(u) = eᵘ B(u)`. -/
def splineProbe : ℝ → ℝ := tiltedSource cubicSpline 1

theorem contDiff_splineProbe : ContDiff ℝ 2 splineProbe :=
  contDiff_tiltedSource contDiff_cubicSpline 1

theorem hasCompactSupport_splineProbe : HasCompactSupport splineProbe :=
  hasCompactSupport_tiltedSource hasCompactSupport_cubicSpline 1

theorem splineProbe_eq_zero {v : ℝ} (hv : 4 < |v|) : splineProbe v = 0 := by
  simp [splineProbe, tiltedSource, cubicSpline_eq_zero hv]

theorem seesAllZeros_splineProbe : SeesAllZeros splineProbe :=
  seesAllZeros_tiltedSource_of_im_ne_zero (fun _ hz => paperFT_cubicSpline_ne_zero hz)
    (by norm_num)

/-- **RH from one explicit packet.** -/
theorem riemannHypothesis_iff_splineProbe_packet_bddAbove :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket splineProbe τ ≤ K :=
  riemannHypothesis_iff_packet_bddAbove_of_universal contDiff_splineProbe
    hasCompactSupport_splineProbe seesAllZeros_splineProbe

/-- **The zero width from one explicit packet.** -/
theorem xiZeroHalfPlaneBound_iff_splineProbe_packet_upper {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket splineProbe τ ≤ K * Real.exp (β * τ) :=
  xiZeroHalfPlaneBound_iff_packet_upper_of_universal contDiff_splineProbe
    hasCompactSupport_splineProbe seesAllZeros_splineProbe hβ

/-- **The band criterion for one explicit packet.** -/
theorem riemannHypothesis_iff_splineProbe_band :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ L : ℝ, T ≤ L →
      ∫ τ in T..L, stationaryPacket splineProbe τ ^ 2 ≤ K * (1 + L) :=
  riemannHypothesis_iff_packet_band_of_universal contDiff_splineProbe
    hasCompactSupport_splineProbe seesAllZeros_splineProbe

/-- **RH and simple zeros from one explicit packet**: bounded above, with asymptotic mean square
equal to the Weil functional of its autocorrelation. -/
theorem riemannHypothesis_and_simple_iff_splineProbe :
    (RiemannHypothesis ∧ ∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult (ρ : ℂ) = 1) ↔
      (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket splineProbe τ ≤ K) ∧
        Tendsto (fun L : ℝ => (∫ τ in (4 : ℝ)..L, stationaryPacket splineProbe τ ^ 2) / L) atTop
          (𝓝 (Zeta23.EF.literatureRHS
            (Zeta23.EF.weilTest (fun u => (splineProbe u : ℂ)) (fun u => (splineProbe u : ℂ)))).re) :=
  riemannHypothesis_and_simple_iff_of_universal contDiff_splineProbe hasCompactSupport_splineProbe
    seesAllZeros_splineProbe (by norm_num) fun _ hv => splineProbe_eq_zero hv

/-! ## The prime-side form -/

/-- The spline-weighted prime sum `Σ_n Λ(n) √n B(log n − τ)`. -/
def splinePrimeSum (τ : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.sqrt n * cubicSpline (Real.log n - τ)

/-- Its polar prediction `∫_0^∞ 2cosh(x/2) eˣ B(x − τ) dx`. -/
def splinePolarMass (τ : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), 2 * Real.cosh (x / 2) * Real.exp x * cubicSpline (x - τ)

/-- The packet of `U` is the excess of the spline prime sum over its polar prediction, scaled by
`e^{−τ}`. -/
theorem exp_mul_stationaryPacket_splineProbe (τ : ℝ) :
    Real.exp τ * stationaryPacket splineProbe τ = splinePrimeSum τ - splinePolarMass τ := by
  unfold stationaryPacket splinePrimeSum splinePolarMass splineProbe tiltedSource
  rw [mul_sub, ← tsum_mul_left, ← integral_const_mul]
  congr 1
  · refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_mul, Real.exp_sub, Real.exp_log hn', ← Real.div_sqrt (x := (n : ℝ))]
      field_simp
      rw [Real.sq_sqrt hn'.le]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [one_mul, Real.exp_sub]
    field_simp

private theorem le_iff_exp_mul {P K S M : ℝ} (τ : ℝ) (h : Real.exp τ * P = S - M) :
    P ≤ K ↔ S ≤ M + K * Real.exp τ := by
  have he := Real.exp_pos τ
  rw [← mul_le_mul_iff_of_pos_left he, h]
  constructor <;> intro h' <;> linarith

/-- **RH as one spline-weighted prime inequality.** RH holds iff, for all large `τ`,
`Σ_n Λ(n) √n B(log n − τ) ≤ ∫_0^∞ 2cosh(x/2) eˣ B(x − τ) dx + K e^τ`. -/
theorem riemannHypothesis_iff_spline_prime_sum_le :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
      splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp τ := by
  rw [riemannHypothesis_iff_splineProbe_packet_bddAbove]
  refine exists_congr fun T => exists_congr fun K => forall_congr' fun τ =>
    imp_congr_right fun _ => le_iff_exp_mul τ (exp_mul_stationaryPacket_splineProbe τ)

/-- **The zero width as one spline-weighted prime inequality**: every zero has
`Re ρ ≤ 1/2 + β` iff the spline prime sum exceeds its polar prediction by `O(e^{(1+β)τ})`. -/
theorem xiZeroHalfPlaneBound_iff_spline_prime_sum_le {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
      splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ) := by
  rw [xiZeroHalfPlaneBound_iff_splineProbe_packet_upper hβ]
  refine exists_congr fun T => exists_congr fun K => forall_congr' fun τ =>
    imp_congr_right fun _ => ?_
  rw [le_iff_exp_mul τ (exp_mul_stationaryPacket_splineProbe τ), mul_assoc, ← Real.exp_add]
  ring_nf

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
