import GaloisForLFunctions.RHTower.LiClockCenterAverage
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# The Euler shadow of the center-averaged Li clock

Averaging the centered Li clock over its center with the Cauchy weight keeps, for a zero on the
critical line, only the decaying exponential `Re(1 − e^{it/(a−i)})` (`LiClockCenterAverage`).  For the
spectral point `a = −i(ρ − ½)` of a zero `ρ` this is `Re(1 − e^{−t/(ρ+½)})`.  The **Euler shadow**

`F(t) = Σ_q Re(1 − e^{−t/(ρ_q+½)})`

uses this projected atom for every zero, on or off the line.

* `liClockEulerShadow_nonneg`: `F(t) ≥ 0` for `t ≥ 0`, unconditionally, since `Re(ρ+½) > 0`.
* `riemannHypothesis_iff_liClockCenterAverage_eq_eulerShadow`: **RH holds iff the center-averaged
  clock equals its Euler shadow** at every clock `t ≥ 0`.
* `integral_exp_mul_liClockEulerShadow`: for `p > 0`,
  `∫_0^∞ e^{−pt} F(t) dt = Re ξ'/ξ(3/2 + 1/p) / p²`.

So the shadow is determined by the logarithmic derivative of `ξ` on the half-line `(3/2, ∞)`, where the
Euler product converges absolutely; RH is the statement that the line-centered average carries no
more than this Euler-region datum.  Each atom has Laplace transform
`1/p − 1/(p + 1/(ρ+½)) = p^{−2}(ρ + ½ + 1/p)^{−1}`; the reflection `ρ ↦ 1 − ρ` turns
`Σ_q Re(ρ_q + ½ + 1/p)^{−1}` into the Hadamard sum `Σ_q Re(3/2 + 1/p − ρ_q)^{−1} = Re ξ'/ξ(3/2 + 1/p)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- The projected (Euler) atom of a spectral point: `Re(1 − e^{it/(a−i)})`. -/
def centerClockShadowAtom (t : ℝ) (a : ℂ) : ℝ := (1 - Complex.exp (I * t / (a - I))).re

/-- The Euler shadow of the center-averaged Li clock. -/
def liClockEulerShadow (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, centerClockShadowAtom t (xiSpectralPoint q)

private theorem spectralPoint_sub_I (q : XiZeroCopy) :
    xiSpectralPoint q - I = -I * ((q.1 : ℂ) + 1 / 2) := by
  rw [xiSpectralPoint]; ring

private theorem re_add_half_pos (q : XiZeroCopy) : 0 < ((q.1 : ℂ) + 1 / 2).re := by
  have := (xi_divisor_support_re_mem_open_unit q.1).1
  simp only [Complex.add_re]
  norm_num
  linarith

private theorem add_half_ne_zero (q : XiZeroCopy) : (q.1 : ℂ) + 1 / 2 ≠ 0 := by
  intro h
  have := re_add_half_pos q
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- The shadow atom of a zero copy is `Re(1 − e^{−t/(ρ+½)})`. -/
theorem centerClockShadowAtom_xiSpectralPoint (t : ℝ) (q : XiZeroCopy) :
    centerClockShadowAtom t (xiSpectralPoint q) =
      (1 - Complex.exp (-(t : ℂ) * ((q.1 : ℂ) + 1 / 2)⁻¹)).re := by
  unfold centerClockShadowAtom
  have hne := add_half_ne_zero q
  congr 3
  rw [spectralPoint_sub_I]
  field_simp

/-- `Re(1 − e^{−tw}) ≥ 0` whenever `t ≥ 0` and `Re w ≥ 0`. -/
theorem one_sub_exp_neg_mul_re_nonneg {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 ≤ w.re) :
    0 ≤ (1 - Complex.exp (-(t : ℂ) * w)).re := by
  have hle : (Complex.exp (-(t : ℂ) * w)).re ≤ 1 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have : (-(t : ℂ) * w).re = -(t * w.re) := by simp [Complex.mul_re]
    rw [this]
    exact neg_nonpos.mpr (mul_nonneg ht hw)
  rw [Complex.sub_re, Complex.one_re]
  linarith

private theorem re_inv_add_half_nonneg (q : XiZeroCopy) : 0 ≤ (((q.1 : ℂ) + 1 / 2)⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg (re_add_half_pos q).le (Complex.normSq_nonneg _)

/-- Every shadow atom of a zero copy is nonnegative at nonnegative clocks. -/
theorem centerClockShadowAtom_nonneg {t : ℝ} (ht : 0 ≤ t) (q : XiZeroCopy) :
    0 ≤ centerClockShadowAtom t (xiSpectralPoint q) := by
  rw [centerClockShadowAtom_xiSpectralPoint]
  exact one_sub_exp_neg_mul_re_nonneg ht (re_inv_add_half_nonneg q)

/-- **The Euler shadow is nonnegative**, unconditionally. -/
theorem liClockEulerShadow_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ liClockEulerShadow t :=
  tsum_nonneg fun q => centerClockShadowAtom_nonneg ht q

private theorem spectralPoint_im_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have h := (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) _
    (xi_eq_zero_of_mem_divisor_support q.1)
  rw [xiSpectralPoint]
  simp [Complex.mul_im, h]

/-- **RH is the equality of the center-averaged clock with its Euler shadow.** -/
theorem riemannHypothesis_iff_liClockCenterAverage_eq_eulerShadow :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 ≤ t → liClockCenterAverage t = liClockEulerShadow t := by
  constructor
  · intro hRH t ht
    unfold liClockCenterAverage liClockEulerShadow
    refine tsum_congr fun q => ?_
    exact centerClockAverage_eq_of_im_eq_zero (spectralPoint_im_eq_zero_of_rh hRH q) ht
  · intro h
    rw [riemannHypothesis_iff_liClockCenterAverage_nonneg]
    intro n
    rw [h n (Nat.cast_nonneg n)]
    exact liClockEulerShadow_nonneg (Nat.cast_nonneg n)

/-! ## The Laplace transform of the shadow -/

private theorem integrableOn_exp_neg_mul_complex {b : ℂ} (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-b * t)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hb) 0

private theorem integral_exp_neg_mul_complex {b : ℂ} (hb : 0 < b.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-b * t) = b⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hb) 0]
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- The Laplace transform of one atom `e^{−pt} Re(1 − e^{−tw})`. -/
theorem integral_exp_mul_re_one_sub_exp {p : ℝ} (hp : 0 < p) {w : ℂ} (hw : 0 < p + w.re) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * w)).re) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * w)).re =
        ((p : ℂ)⁻¹ - ((p : ℂ) + w)⁻¹).re := by
  have hpb : 0 < ((p : ℂ)).re := by simpa using hp
  have hpw : 0 < ((p : ℂ) + w).re := by simpa using hw
  have h1 := integrableOn_exp_neg_mul_complex hpb
  have h2 := integrableOn_exp_neg_mul_complex hpw
  have hG : IntegrableOn (fun t : ℝ => Complex.exp (-(p : ℂ) * t) -
      Complex.exp (-((p : ℂ) + w) * t)) (Ioi 0) := h1.sub h2
  have hpt : ∀ t : ℝ, Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * w)).re =
      (Complex.exp (-(p : ℂ) * t) - Complex.exp (-((p : ℂ) + w) * t)).re := by
    intro t
    have e1 : Complex.exp (-(p : ℂ) * t) = (Real.exp (-(p * t)) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have e2 : Complex.exp (-((p : ℂ) + w) * t) =
        (Real.exp (-(p * t)) : ℂ) * Complex.exp (-(t : ℂ) * w) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
    rw [e1, e2, ← mul_one_sub, Complex.re_ofReal_mul]
  have hGre : IntegrableOn (fun t : ℝ => (Complex.exp (-(p : ℂ) * t) -
      Complex.exp (-((p : ℂ) + w) * t)).re) (Ioi 0) := hG.re
  refine ⟨hGre.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioi, ?_⟩
  simp_rw [hpt]
  have hre := integral_re hG
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_sub h1 h2, integral_exp_neg_mul_complex hpb,
    integral_exp_neg_mul_complex hpw]

private theorem laplace_atom_algebra {p : ℝ} (hp : 0 < p) {r : ℂ} (hr : r ≠ 0)
    (hrpos : 0 < r.re) :
    ((p : ℂ)⁻¹ - ((p : ℂ) + r⁻¹)⁻¹).re = ((r + (p : ℂ)⁻¹)⁻¹).re / p ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hden : (p : ℂ) * r + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hval : ((p : ℂ) * r + 1).re = p * r.re + 1 := by simp [Complex.mul_re]
    rw [hval, Complex.zero_re] at hre
    have : 0 < p * r.re := mul_pos hp hrpos
    linarith
  have h1 : (p : ℂ) + r⁻¹ ≠ 0 := by
    intro h; apply hden
    have : (p : ℂ) * r + 1 = r * ((p : ℂ) + r⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hr, mul_comm r (p : ℂ)]
    rw [this, h, mul_zero]
  have h2 : r + (p : ℂ)⁻¹ ≠ 0 := by
    intro h; apply hden
    have : (p : ℂ) * r + 1 = (p : ℂ) * (r + (p : ℂ)⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hp0]
    rw [this, h, mul_zero]
  have hkey : (p : ℂ)⁻¹ - ((p : ℂ) + r⁻¹)⁻¹ = (r + (p : ℂ)⁻¹)⁻¹ * (((p ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [hkey, Complex.re_mul_ofReal, div_eq_mul_inv]

private theorem shadow_laplace_value {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    ((p : ℂ)⁻¹ - ((p : ℂ) + ((q.1 : ℂ) + 1 / 2)⁻¹)⁻¹).re =
      (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re / p ^ 2 := by
  have hsum : ((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ) = ((q.1 : ℂ) + 1 / 2) + (p : ℂ)⁻¹ := by
    push_cast; ring
  rw [hsum]
  exact laplace_atom_algebra hp (add_half_ne_zero q) (re_add_half_pos q)

private theorem shadow_reflect_re (σ : ℝ) (q : XiZeroCopy) :
    (((σ : ℂ) - 1 + ((xiZeroCopyReflectEquiv q).1 : ℂ))⁻¹).re = WeilSpectral.copyPoisson σ 0 q := by
  rw [WeilSpectral.reflect_copy_coe, WeilSpectral.copyPoisson, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.add_im,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im]
  ring_nf

private theorem shadow_atom_eq (p : ℝ) (q : XiZeroCopy) :
    (fun t : ℝ => Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q)) =
      fun t => Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * ((q.1 : ℂ) + 1 / 2)⁻¹)).re := by
  funext t; rw [centerClockShadowAtom_xiSpectralPoint]

private theorem shadow_w_pos {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    0 < p + (((q.1 : ℂ) + 1 / 2)⁻¹).re := by
  linarith [re_inv_add_half_nonneg q]

/-- Each weighted shadow atom is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_mul_centerClockShadowAtom {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q))
      (Ioi 0) := by
  rw [shadow_atom_eq]; exact (integral_exp_mul_re_one_sub_exp hp (shadow_w_pos hp q)).1

/-- The Laplace transform of one shadow atom, `Re (3/2 + 1/p − 1 + ρ)^{−1}/p²`. -/
theorem integral_exp_mul_centerClockShadowAtom {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q) =
      (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re / p ^ 2 := by
  rw [shadow_atom_eq, (integral_exp_mul_re_one_sub_exp hp (shadow_w_pos hp q)).2,
    shadow_laplace_value hp q]

private theorem summable_shadow_value {p : ℝ} (hp : 0 < p) :
    Summable fun q : XiZeroCopy => (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re := by
  have hσ : 1 < 3 / 2 + 1 / p := by have := one_div_pos.mpr hp; linarith
  have hsumR := WeilSpectral.summable_copyPoisson hσ 0
  have := (xiZeroCopyReflectEquiv.symm.summable_iff).mpr hsumR
  refine this.congr fun q => ?_
  have h := shadow_reflect_re (3 / 2 + 1 / p) (xiZeroCopyReflectEquiv.symm q)
  simp only [Equiv.apply_symm_apply] at h
  simp only [Function.comp_apply]
  exact h.symm

/-- The weighted shadow atoms have summable `L¹` norms. -/
theorem summable_integral_norm_exp_mul_centerClockShadowAtom {p : ℝ} (hp : 0 < p) :
    Summable fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ),
      ‖Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q)‖ := by
  have hnorm : ∀ q : XiZeroCopy, (∫ t in Ioi (0 : ℝ),
      ‖Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q)‖) =
      (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re / p ^ 2 := fun q => by
    rw [← integral_exp_mul_centerClockShadowAtom hp q]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h0 : 0 ≤ Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q) :=
      mul_nonneg (Real.exp_pos _).le (centerClockShadowAtom_nonneg (le_of_lt ht) q)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
  simp_rw [hnorm]
  exact (summable_shadow_value hp).div_const _

/-- **The atomwise Laplace transforms of the shadow sum to the Euler-region datum.** -/
theorem hasSum_integral_exp_mul_centerClockShadowAtom {p : ℝ} (hp : 0 < p) :
    HasSum (fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ),
      Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q))
      ((logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2) := by
  have hσ : (1 : ℝ) < 3 / 2 + 1 / p := by have := one_div_pos.mpr hp; linarith
  have hfun : (fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ),
      Real.exp (-(p * t)) * centerClockShadowAtom t (xiSpectralPoint q)) =
      fun q => (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re / p ^ 2 := by
    funext q; exact integral_exp_mul_centerClockShadowAtom hp q
  rw [hfun]
  have h1 := ((summable_shadow_value hp).div_const (p ^ 2)).hasSum
  have hrefl : ∑' q : XiZeroCopy, ((((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹).re =
      ∑' q : XiZeroCopy, WeilSpectral.copyPoisson (3 / 2 + 1 / p) 0 q := by
    rw [← xiZeroCopyReflectEquiv.tsum_eq]
    exact tsum_congr fun q => shadow_reflect_re (3 / 2 + 1 / p) q
  have h2 : (∑' q : XiZeroCopy, (((3 / 2 + 1 / p : ℝ) : ℂ) - 1 + (q.1 : ℂ))⁻¹.re / p ^ 2) =
      (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 := by
    rw [tsum_div_const, hrefl, ← WeilSpectral.re_logDeriv_xi_eq_tsum_copyPoisson hσ 0]
    simp
  rw [h2] at h1
  exact h1

/-- **The Laplace transform of the Euler shadow is the Euler-region logarithmic derivative.**
For `p > 0`, `∫_0^∞ e^{−pt} F(t) dt = Re ξ'/ξ(3/2 + 1/p) / p²`. -/
theorem integral_exp_mul_liClockEulerShadow {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockEulerShadow t =
      (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 := by
  have hint : ∀ q : XiZeroCopy, Integrable (fun t : ℝ => Real.exp (-(p * t)) *
      centerClockShadowAtom t (xiSpectralPoint q)) (volume.restrict (Ioi 0)) :=
    fun q => integrableOn_exp_mul_centerClockShadowAtom hp q
  have hswap := integral_tsum_of_summable_integral_norm hint
    (summable_integral_norm_exp_mul_centerClockShadowAtom hp)
  have hpull : (fun t : ℝ => ∑' q : XiZeroCopy, Real.exp (-(p * t)) *
      centerClockShadowAtom t (xiSpectralPoint q)) =
      fun t => Real.exp (-(p * t)) * liClockEulerShadow t := by
    funext t
    simp only [liClockEulerShadow]
    exact tsum_mul_left
  rw [← hpull, ← hswap]
  exact (hasSum_integral_exp_mul_centerClockShadowAtom hp).tsum_eq

end RHTower
