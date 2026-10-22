import GaloisForLFunctions.RHTower.ThetaTailKernelGeometricDeficitSplit
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue

/-!
# Separated-packet positivity of the theta tail first-moment kernel

Positivity of `thetaTailFirstMomentKernel` on every finite node system is, through the
removable double-Laplace identity, the source side of the Bezoutian Riemann hypothesis
criterion.  This module proves the first unconditional off-diagonal stratum: the kernel is
positive semidefinite on every packet of nodes in `[1, ∞)` whose consecutive gaps exceed the
explicit threshold `thetaTailPacketSeparation`.

The mechanism is a two-sided envelope calculus.  The envelope
`E(y) = e^{9y/2}·e^{-π e^{2y}}` bounds the theta source above and below on the positive
half-line, and its shift law concentrates every kernel integral at scale `e^{-2y}`.  One
envelope slab of that width bounds the diagonal below,
`k(y,y) ≥ 2·C_l²·e^{-8π}·y·e^{-2y}·E(y)²`; the half-line Laplace evaluation bounds the
off-diagonal above, `k(x,t) ≤ (C_u²/π)·(x+t+1)·E(x)·E(t)·e^{-2t}`.  The squared correlation
ratio then decays like `e^{-(t-x)}` in the separation, and a diagonally scaled Gershgorin
argument closes every packet whose gaps beat the fixed constant
`2·log(1 + 2K)`, `K = 3·C_u²·e^{8π}/(2π·C_l²)`.  Every comparison is symbolic in `π` and the
envelope constants; the numeric inputs are `2 ≤ e` and `e < 2.72`.

Close pairs — separation below the threshold — remain the open regime of the criterion.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-! ### Elementary exponential facts -/

private theorem exp_half_le_two : Real.exp 2⁻¹ ≤ 2 := by
  have hmul : Real.exp 2⁻¹ * Real.exp 2⁻¹ = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (2⁻¹ : ℝ)]

private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

/-- Half-line first Laplace moment: `∫_{s>0} s·e^{-cs} = 1/c²`. -/
theorem integral_Ioi_id_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-(c * s))) = 1 / c ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := c)
    (by norm_num) hc
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    Real.Gamma_two] at h
  rw [h]
  ring

theorem integrableOn_Ioi_id_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(c * s))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_Ioi_id_mul_exp_neg_mul hc]
  positivity

private theorem integrableOn_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-(c * s))) (Ioi 0) :=
  MeasureTheory.IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi 0 hc)
    (fun x _ => by simp only [neg_mul]) measurableSet_Ioi

/-- Affine-weighted decaying exponentials are integrable on the half line. -/
private theorem integrableOn_affine_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    IntegrableOn (fun s : ℝ => (A + B * s) * Real.exp (-(c * s))) (Ioi 0) := by
  have h := ((integrableOn_exp_neg_mul hc).const_mul A).add
    ((integrableOn_Ioi_id_mul_exp_neg_mul hc).const_mul B)
  exact MeasureTheory.IntegrableOn.congr_fun h
    (fun s _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi

/-- Value of the affine-weighted Laplace integral. -/
private theorem integral_affine_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    (∫ s in Ioi (0 : ℝ), (A + B * s) * Real.exp (-(c * s)))
      = A / c + B / c ^ 2 := by
  have hsplit : (fun s : ℝ => (A + B * s) * Real.exp (-(c * s)))
      = fun s : ℝ => A * Real.exp (-(c * s)) + B * (s * Real.exp (-(c * s))) := by
    funext s; ring
  rw [hsplit, integral_add ((integrableOn_exp_neg_mul hc).const_mul A)
    ((integrableOn_Ioi_id_mul_exp_neg_mul hc).const_mul B),
    integral_const_mul, integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_Ioi_zero hc,
    integral_Ioi_id_mul_exp_neg_mul hc]
  ring

/-! ### Envelope monotonicity -/

/-- The theta envelope is antitone on `[1, ∞)`. -/
theorem thetaEnvelope_le_of_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    thetaEnvelope v ≤ thetaEnvelope u := by
  have h := thetaEnvelope_le_shift hu huv
  have hfac : Real.exp (-(Real.pi * Real.exp (2 * u)) * (v - u)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ Real.pi * Real.exp (2 * u) := by positivity
    nlinarith
  calc thetaEnvelope v
      ≤ thetaEnvelope u * Real.exp (-(Real.pi * Real.exp (2 * u)) * (v - u)) := h
    _ ≤ thetaEnvelope u * 1 :=
        mul_le_mul_of_nonneg_left hfac (thetaEnvelope_pos u).le
    _ = thetaEnvelope u := mul_one _

/-! ### Kernel integrand: nonnegativity, pointwise ceiling, integrability -/

private theorem orbit_nonneg {x t s : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) (hs : 0 < s) :
    0 ≤ (x + t + 2 * s) *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) := by
  have h1 := (thetaCuspFullSource_pos (x + s)).le
  have h2 := (thetaCuspFullSource_pos (t + s)).le
  have h3 : (0 : ℝ) ≤ x + t + 2 * s := by linarith
  exact mul_nonneg h3 (mul_nonneg h1 h2)

/-- Pointwise envelope ceiling for the orbit integrand, with the decay rate of the larger
node. -/
private theorem orbit_pointwise_le {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) {s : ℝ}
    (hs : 0 < s) :
    (x + t + 2 * s) * (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) ≤
      ((x + t) * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t) +
          2 * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t) * s) *
        Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by
  have hΦx : thetaCuspFullSource (x + s) ≤ thetaEnvelopeUpper * thetaEnvelope x := by
    calc thetaCuspFullSource (x + s)
        ≤ thetaEnvelopeUpper * thetaEnvelope (x + s) :=
          thetaCuspFullSource_le_envelope (by linarith)
      _ ≤ thetaEnvelopeUpper * thetaEnvelope x :=
          mul_le_mul_of_nonneg_left
            (thetaEnvelope_le_of_le hx (by linarith)) thetaEnvelopeUpper_pos.le
  have hΦt : thetaCuspFullSource (t + s) ≤
      thetaEnvelopeUpper * thetaEnvelope t *
        Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by
    have hshift := thetaEnvelope_le_shift ht (show t ≤ t + s by linarith)
    rw [show t + s - t = s by ring] at hshift
    calc thetaCuspFullSource (t + s)
        ≤ thetaEnvelopeUpper * thetaEnvelope (t + s) :=
          thetaCuspFullSource_le_envelope (by linarith)
      _ ≤ thetaEnvelopeUpper *
            (thetaEnvelope t * Real.exp (-(Real.pi * Real.exp (2 * t)) * s)) :=
          mul_le_mul_of_nonneg_left hshift thetaEnvelopeUpper_pos.le
      _ = thetaEnvelopeUpper * thetaEnvelope t *
            Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by
          rw [neg_mul]
          ring
  have hprod : thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s) ≤
      thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t *
        Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by
    calc thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)
        ≤ (thetaEnvelopeUpper * thetaEnvelope x) *
            (thetaEnvelopeUpper * thetaEnvelope t *
              Real.exp (-(Real.pi * Real.exp (2 * t) * s))) :=
          mul_le_mul hΦx hΦt (thetaCuspFullSource_pos (t + s)).le
            (mul_nonneg thetaEnvelopeUpper_pos.le (thetaEnvelope_pos x).le)
      _ = thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t *
            Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by ring
  have hw : (0 : ℝ) ≤ x + t + 2 * s := by linarith
  calc (x + t + 2 * s) *
        (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))
      ≤ (x + t + 2 * s) *
          (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t *
            Real.exp (-(Real.pi * Real.exp (2 * t) * s))) :=
        mul_le_mul_of_nonneg_left hprod hw
    _ = ((x + t) * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t) +
          2 * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t) * s) *
        Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by ring

/-- The orbit integrand of the theta tail kernel is integrable on the half line. -/
theorem integrableOn_thetaTailOrbit {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) :
    IntegrableOn (fun s => (x + t + 2 * s) *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))) (Ioi 0) := by
  have hρ : 0 < Real.pi * Real.exp (2 * t) := by positivity
  refine Integrable.mono'
    (integrableOn_affine_mul_exp_neg_mul hρ
      ((x + t) * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t))
      (2 * (thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t))) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have hΦ := contDiff_thetaCuspFullSource.continuous
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (orbit_nonneg hx ht hs)]
    exact orbit_pointwise_le hx ht hs

/-- The theta tail kernel is entrywise nonnegative on `[1, ∞)`. -/
theorem thetaTailKernel_nonneg_of_one_le {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) :
    0 ≤ thetaTailFirstMomentKernel x t := by
  rw [thetaTailFirstMomentKernel_eq_orbitShift]
  exact setIntegral_nonneg measurableSet_Ioi fun s hs => orbit_nonneg hx ht hs

/-! ### The off-diagonal ceiling -/

/-- **Off-diagonal Laplace ceiling.**  For `1 ≤ x ≤ t` the kernel is bounded by the envelope
product with the full decay `e^{-2t}` of the larger node. -/
theorem thetaTailFirstMomentKernel_le_ceiling {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t) :
    thetaTailFirstMomentKernel x t ≤
      thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
        (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t)) := by
  have ht : 1 ≤ t := hx.trans hxt
  have hρ : 0 < Real.pi * Real.exp (2 * t) := by positivity
  set C := thetaEnvelopeUpper ^ 2 * thetaEnvelope x * thetaEnvelope t with hC
  have hC0 : 0 < C := by
    rw [hC]
    exact mul_pos (mul_pos (pow_pos thetaEnvelopeUpper_pos 2)
      (thetaEnvelope_pos x)) (thetaEnvelope_pos t)
  have hρ2 : (2 : ℝ) ≤ Real.pi * Real.exp (2 * t) := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hexp : (1 : ℝ) ≤ Real.exp (2 * t) := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith
  rw [thetaTailFirstMomentKernel_eq_orbitShift]
  have hmono := MeasureTheory.setIntegral_mono_on
    (integrableOn_thetaTailOrbit hx ht)
    (integrableOn_affine_mul_exp_neg_mul hρ ((x + t) * C) (2 * C))
    measurableSet_Ioi
    (fun s hs => orbit_pointwise_le hx ht hs)
  have hval := integral_affine_mul_exp_neg_mul hρ ((x + t) * C) (2 * C)
  have hbound : (x + t) * C / (Real.pi * Real.exp (2 * t)) +
      2 * C / (Real.pi * Real.exp (2 * t)) ^ 2 ≤
      (x + t + 1) * C / (Real.pi * Real.exp (2 * t)) := by
    have h2 : 2 * C / (Real.pi * Real.exp (2 * t)) ^ 2 ≤
        C / (Real.pi * Real.exp (2 * t)) := by
      rw [pow_two,
        show 2 * C / (Real.pi * Real.exp (2 * t) * (Real.pi * Real.exp (2 * t))) =
          (2 / (Real.pi * Real.exp (2 * t))) * (C / (Real.pi * Real.exp (2 * t))) by
            ring]
      have h4 : 2 / (Real.pi * Real.exp (2 * t)) ≤ 1 := by
        rw [div_le_one hρ]
        linarith
      have h5 : 0 ≤ C / (Real.pi * Real.exp (2 * t)) := by
        exact div_nonneg hC0.le hρ.le
      nlinarith
    have h3 : (x + t + 1) * C / (Real.pi * Real.exp (2 * t)) =
        (x + t) * C / (Real.pi * Real.exp (2 * t)) +
          C / (Real.pi * Real.exp (2 * t)) := by
      ring
    linarith
  have hfinal : (x + t + 1) * C / (Real.pi * Real.exp (2 * t)) =
      thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
        (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t)) := by
    rw [hC, Real.exp_neg]
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have he : Real.exp (2 * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp
  calc (∫ s in Ioi (0 : ℝ), (x + t + 2 * s) *
        (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)))
      ≤ ∫ s in Ioi (0 : ℝ), ((x + t) * C + 2 * C * s) *
          Real.exp (-(Real.pi * Real.exp (2 * t) * s)) := by
        refine le_trans hmono (le_of_eq ?_)
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        ring
    _ = (x + t) * C / (Real.pi * Real.exp (2 * t)) +
          2 * C / (Real.pi * Real.exp (2 * t)) ^ 2 := hval
    _ ≤ (x + t + 1) * C / (Real.pi * Real.exp (2 * t)) := hbound
    _ = _ := hfinal

/-! ### The diagonal floor -/

/-- Explicit diagonal floor of the theta tail kernel: one envelope slab of width `e^{-2y}`. -/
def thetaTailDiagonalFloor (y : ℝ) : ℝ :=
  2 * thetaEnvelopeLower ^ 2 * Real.exp (-(8 * Real.pi)) * (y * Real.exp (-(2 * y))) *
    thetaEnvelope y ^ 2

theorem thetaTailDiagonalFloor_pos {y : ℝ} (hy : 1 ≤ y) :
    0 < thetaTailDiagonalFloor y := by
  unfold thetaTailDiagonalFloor
  have h3 : (0 : ℝ) < y := by linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (pow_pos thetaEnvelopeLower_pos 2)) (Real.exp_pos _))
    (mul_pos h3 (Real.exp_pos _))) (pow_pos (thetaEnvelope_pos y) 2)

/-- One-slab lower transfer of the envelope: over the concentration width `δ = e^{-2y}` the
envelope loses at most the fixed factor `e^{-4π}`. -/
private theorem thetaEnvelope_slab_ge {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (-(4 * Real.pi)) * thetaEnvelope y ≤
      thetaEnvelope (y + Real.exp (-(2 * y))) := by
  set δ := Real.exp (-(2 * y)) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδsmall : 2 * δ ≤ 2⁻¹ := by
    have h1 : δ ≤ Real.exp (-(2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(2 : ℝ)) ≤ 4⁻¹ := by
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos 2) (by norm_num)]
      have h4 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [two_le_exp_one]
    linarith
  have hexp2δ : Real.exp (2 * δ) ≤ 2 :=
    le_trans (Real.exp_le_exp.mpr hδsmall) exp_half_le_two
  have hgrow : Real.exp (2 * δ) - 1 ≤ 4 * δ := by
    have hbase := Real.add_one_le_exp (-(2 * δ))
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (2 * δ)).le
    rw [← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    nlinarith [Real.exp_pos (2 * δ)]
  have hexpo : Real.exp (2 * y) * (Real.exp (2 * δ) - 1) ≤ 4 := by
    have h2 : Real.exp (2 * y) * (Real.exp (2 * δ) - 1) ≤
        Real.exp (2 * y) * (4 * δ) := by
      apply mul_le_mul_of_nonneg_left hgrow (Real.exp_pos _).le
    have h3 : Real.exp (2 * y) * (4 * δ) = 4 := by
      rw [hδ, show Real.exp (2 * y) * (4 * Real.exp (-(2 * y))) =
        4 * (Real.exp (2 * y) * Real.exp (-(2 * y))) by ring, ← Real.exp_add]
      simp
    linarith
  unfold thetaEnvelope
  have hsplit : Real.exp (2 * (y + δ)) = Real.exp (2 * y) * Real.exp (2 * δ) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hnine : Real.exp (9 * y / 2) ≤ Real.exp (9 * (y + δ) / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hcore : Real.exp (-(4 * Real.pi)) * Real.exp (-Real.pi * Real.exp (2 * y)) ≤
      Real.exp (-Real.pi * (Real.exp (2 * y) * Real.exp (2 * δ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  calc Real.exp (-(4 * Real.pi)) *
        (Real.exp (9 * y / 2) * Real.exp (-Real.pi * Real.exp (2 * y)))
      = Real.exp (9 * y / 2) *
          (Real.exp (-(4 * Real.pi)) * Real.exp (-Real.pi * Real.exp (2 * y))) := by ring
    _ ≤ Real.exp (9 * y / 2) *
          Real.exp (-Real.pi * (Real.exp (2 * y) * Real.exp (2 * δ))) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
    _ ≤ Real.exp (9 * (y + δ) / 2) *
          Real.exp (-Real.pi * (Real.exp (2 * y) * Real.exp (2 * δ))) :=
        mul_le_mul_of_nonneg_right hnine (Real.exp_pos _).le

/-- **Diagonal floor.**  For `y ≥ 1` the theta tail kernel diagonal is bounded below by the
explicit slab value `2·C_l²·e^{-8π}·y·e^{-2y}·E(y)²`. -/
theorem thetaTailDiagonalFloor_le {y : ℝ} (hy : 1 ≤ y) :
    thetaTailDiagonalFloor y ≤ thetaTailFirstMomentKernel y y := by
  set δ := Real.exp (-(2 * y)) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hy0 : (0 : ℝ) < y := by linarith
  set c := 2 * y * (thetaEnvelopeLower * thetaEnvelope (y + δ)) ^ 2 with hc
  have hEpos := thetaEnvelope_pos (y + δ)
  have hLpos := thetaEnvelopeLower_pos
  have hpoint : ∀ s ∈ Ioc (0 : ℝ) δ, c ≤ (y + y + 2 * s) *
      (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) := by
    rintro s ⟨hs0, hsδ⟩
    have hΦ : thetaEnvelopeLower * thetaEnvelope (y + δ) ≤
        thetaCuspFullSource (y + s) := by
      calc thetaEnvelopeLower * thetaEnvelope (y + δ)
          ≤ thetaEnvelopeLower * thetaEnvelope (y + s) :=
            mul_le_mul_of_nonneg_left
              (thetaEnvelope_le_of_le (by linarith) (by linarith)) hLpos.le
        _ ≤ thetaCuspFullSource (y + s) :=
            thetaCuspFullSource_ge_envelope (by linarith)
    have hΦ0 : (0 : ℝ) ≤ thetaEnvelopeLower * thetaEnvelope (y + δ) :=
      mul_nonneg hLpos.le hEpos.le
    have hsq : (thetaEnvelopeLower * thetaEnvelope (y + δ)) ^ 2 ≤
        thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s) := by
      rw [pow_two]
      exact mul_le_mul hΦ hΦ hΦ0 (thetaCuspFullSource_pos _).le
    have hw : 2 * y ≤ y + y + 2 * s := by linarith
    calc c = 2 * y * (thetaEnvelopeLower * thetaEnvelope (y + δ)) ^ 2 := hc
      _ ≤ (y + y + 2 * s) * (thetaEnvelopeLower * thetaEnvelope (y + δ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ ≤ (y + y + 2 * s) *
            (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
  have hcont : Continuous fun s : ℝ => (y + y + 2 * s) *
      (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) := by
    have hΦ := contDiff_thetaCuspFullSource.continuous
    fun_prop
  have hslab : c * δ ≤ ∫ s in Ioc (0 : ℝ) δ, (y + y + 2 * s) *
      (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) := by
    have h := MeasureTheory.setIntegral_ge_of_const_le measurableSet_Ioc
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hpoint
      hcont.integrableOn_Ioc
    rwa [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), sub_zero, smul_eq_mul, mul_comm] at h
  have hmono : (∫ s in Ioc (0 : ℝ) δ, (y + y + 2 * s) *
      (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s))) ≤
      ∫ s in Ioi (0 : ℝ), (y + y + 2 * s) *
        (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_thetaTailOrbit hy hy) ?_
      (LE.le.eventuallyLE Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact orbit_nonneg hy hy hs
  have hfloor : thetaTailDiagonalFloor y ≤ c * δ := by
    have hEsq : (Real.exp (-(4 * Real.pi)) * thetaEnvelope y) ^ 2 ≤
        thetaEnvelope (y + δ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (thetaEnvelope_pos y).le)
        (thetaEnvelope_slab_ge hy) 2
    have h48 : Real.exp (-(4 * Real.pi)) ^ 2 = Real.exp (-(8 * Real.pi)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hyδ : (0 : ℝ) ≤ 2 * thetaEnvelopeLower ^ 2 * (y * δ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg hy0.le hδ0.le)
    calc thetaTailDiagonalFloor y
        = 2 * thetaEnvelopeLower ^ 2 * (y * δ) *
            ((Real.exp (-(4 * Real.pi)) * thetaEnvelope y) ^ 2) := by
          unfold thetaTailDiagonalFloor
          rw [mul_pow, h48, ← hδ]
          ring
      _ ≤ 2 * thetaEnvelopeLower ^ 2 * (y * δ) * (thetaEnvelope (y + δ) ^ 2) :=
          mul_le_mul_of_nonneg_left hEsq hyδ
      _ = c * δ := by rw [hc]; ring
  have hker : thetaTailFirstMomentKernel y y =
      ∫ s in Ioi (0 : ℝ), (y + y + 2 * s) *
        (thetaCuspFullSource (y + s) * thetaCuspFullSource (y + s)) :=
    thetaTailFirstMomentKernel_eq_orbitShift y y
  linarith

/-! ### The correlation constant and the squared master bound -/

/-- The packet correlation constant `K = 3·C_u²·e^{8π}/(2π·C_l²)`. -/
def thetaTailPacketRatioConstant : ℝ :=
  3 * thetaEnvelopeUpper ^ 2 * Real.exp (8 * Real.pi) /
    (2 * Real.pi * thetaEnvelopeLower ^ 2)

theorem thetaTailPacketRatioConstant_pos : 0 < thetaTailPacketRatioConstant := by
  unfold thetaTailPacketRatioConstant
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (pow_pos thetaEnvelopeUpper_pos 2))
      (Real.exp_pos _))
    (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (pow_pos thetaEnvelopeLower_pos 2))

/-- Polynomial-versus-exponential comparison behind the correlation decay:
`(x+t+1)² ≤ 9xt·e^{t-x}` for `1 ≤ x ≤ t`. -/
private theorem poly_vs_exp {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t) :
    (x + t + 1) ^ 2 ≤ 9 * (x * t) * Real.exp (t - x) := by
  have ht : 1 ≤ t := hx.trans hxt
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : (x + t + 1) ^ 2 ≤ 9 * t ^ 2 := by nlinarith
  have hlog : t / x ≤ Real.exp (t - x) := by
    have hpos : (0 : ℝ) < t / x := by positivity
    have h2 : Real.log (t / x) ≤ t / x - 1 := Real.log_le_sub_one_of_pos hpos
    have h3 : t / x - 1 ≤ t - x := by
      rw [div_sub_one hx0.ne', div_le_iff₀ hx0]
      nlinarith
    calc t / x = Real.exp (Real.log (t / x)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (t - x) := Real.exp_le_exp.mpr (by linarith)
  have h4 : t ≤ x * Real.exp (t - x) := by
    rw [div_le_iff₀ hx0] at hlog
    linarith
  have h5 : 9 * t ^ 2 ≤ 9 * (x * t) * Real.exp (t - x) := by nlinarith
  linarith

/-- Division-free core of the correlation-constant identity, with the two exponential
relations abstracted into variables. -/
private theorem ratio_identity_abstract (Cu Cl piv Ex Et xv tv e8 mtx etx mx mt : ℝ)
    (hπ : piv ≠ 0) (hCl : Cl ≠ 0) (he8 : e8 ≠ 0)
    (hbal : mtx * (mx * mt) = etx * (mt * mt)) :
    (3 * Cu ^ 2 * e8 / (2 * piv * Cl ^ 2)) ^ 2 * mtx *
      (2 * Cl ^ 2 * e8⁻¹ * (xv * mx) * Ex ^ 2 *
        (2 * Cl ^ 2 * e8⁻¹ * (tv * mt) * Et ^ 2)) =
    9 * (xv * tv) * etx * ((Cu ^ 2 / piv) ^ 2 * ((Ex * Et) ^ 2 * (mt * mt))) := by
  have hL : (3 * Cu ^ 2 * e8 / (2 * piv * Cl ^ 2)) ^ 2 * mtx *
      (2 * Cl ^ 2 * e8⁻¹ * (xv * mx) * Ex ^ 2 *
        (2 * Cl ^ 2 * e8⁻¹ * (tv * mt) * Et ^ 2)) =
      9 * (xv * tv) * (Cu ^ 2 / piv) ^ 2 * (Ex * Et) ^ 2 * (mtx * (mx * mt)) := by
    field_simp
    ring
  have hR : 9 * (xv * tv) * etx * ((Cu ^ 2 / piv) ^ 2 * ((Ex * Et) ^ 2 * (mt * mt))) =
      9 * (xv * tv) * (Cu ^ 2 / piv) ^ 2 * (Ex * Et) ^ 2 * (etx * (mt * mt)) := by
    ring
  rw [hL, hR, hbal]

/-- **Squared correlation master bound.**  For `1 ≤ x ≤ t`,
`k(x,t)² ≤ (K·e^{-(t-x)/2})²·k(x,x)·k(t,t)`. -/
theorem thetaTailFirstMomentKernel_sq_le {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t) :
    thetaTailFirstMomentKernel x t ^ 2 ≤
      (thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
        (thetaTailFirstMomentKernel x x * thetaTailFirstMomentKernel t t) := by
  have ht : 1 ≤ t := hx.trans hxt
  have hEx := thetaEnvelope_pos x
  have hEt := thetaEnvelope_pos t
  have hCu := thetaEnvelopeUpper_pos
  have hCl := thetaEnvelopeLower_pos
  have hπ := Real.pi_pos
  have hknn := thetaTailKernel_nonneg_of_one_le hx ht
  have hceil := thetaTailFirstMomentKernel_le_ceiling hx hxt
  have hsq : thetaTailFirstMomentKernel x t ^ 2 ≤
      (thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
        (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t))) ^ 2 :=
    pow_le_pow_left₀ hknn hceil 2
  -- exponential bookkeeping
  have hE1 : Real.exp (-((t - x) / 2)) ^ 2 = Real.exp (-(t - x)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE5 : Real.exp (-(t - x)) * (Real.exp (-(2 * x)) * Real.exp (-(2 * t))) =
      Real.exp (t - x) * (Real.exp (-(2 * t)) * Real.exp (-(2 * t))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  -- the middle comparison through the diagonal floors
  have hUsq : (thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
      (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t))) ^ 2 ≤
      (thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
        (thetaTailDiagonalFloor x * thetaTailDiagonalFloor t) := by
    have hpoly := poly_vs_exp hx hxt
    have hcommon : (0 : ℝ) ≤ (thetaEnvelopeUpper ^ 2 / Real.pi) ^ 2 *
        ((thetaEnvelope x * thetaEnvelope t) ^ 2 *
          (Real.exp (-(2 * t)) * Real.exp (-(2 * t)))) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    have hLHS : (thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
        (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t))) ^ 2 =
        (x + t + 1) ^ 2 * ((thetaEnvelopeUpper ^ 2 / Real.pi) ^ 2 *
          ((thetaEnvelope x * thetaEnvelope t) ^ 2 *
            (Real.exp (-(2 * t)) * Real.exp (-(2 * t))))) := by
      ring
    have hRHS : (thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
        (thetaTailDiagonalFloor x * thetaTailDiagonalFloor t) =
        (9 * (x * t) * Real.exp (t - x)) *
          ((thetaEnvelopeUpper ^ 2 / Real.pi) ^ 2 *
            ((thetaEnvelope x * thetaEnvelope t) ^ 2 *
              (Real.exp (-(2 * t)) * Real.exp (-(2 * t))))) := by
      unfold thetaTailPacketRatioConstant thetaTailDiagonalFloor
      have hπne : Real.pi ≠ 0 := ne_of_gt hπ
      have hClne : thetaEnvelopeLower ≠ 0 := ne_of_gt hCl
      rw [mul_pow, hE1,
        show Real.exp (-(8 * Real.pi)) = (Real.exp (8 * Real.pi))⁻¹ by
          rw [← Real.exp_neg]]
      exact ratio_identity_abstract thetaEnvelopeUpper thetaEnvelopeLower Real.pi
        (thetaEnvelope x) (thetaEnvelope t) x t (Real.exp (8 * Real.pi))
        (Real.exp (-(t - x))) (Real.exp (t - x)) (Real.exp (-(2 * x)))
        (Real.exp (-(2 * t))) hπne hClne (ne_of_gt (Real.exp_pos _)) hE5
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_right hpoly hcommon
  have hfl : thetaTailDiagonalFloor x * thetaTailDiagonalFloor t ≤
      thetaTailFirstMomentKernel x x * thetaTailFirstMomentKernel t t := by
    have h1 := thetaTailDiagonalFloor_le hx
    have h2 := thetaTailDiagonalFloor_le ht
    have h4 := (thetaTailDiagonalFloor_pos ht).le
    exact mul_le_mul h1 h2 h4 (thetaTailKernel_nonneg_of_one_le hx hx)
  calc thetaTailFirstMomentKernel x t ^ 2
      ≤ (thetaEnvelopeUpper ^ 2 / Real.pi * ((x + t + 1) *
          (thetaEnvelope x * thetaEnvelope t)) * Real.exp (-(2 * t))) ^ 2 := hsq
    _ ≤ (thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
          (thetaTailDiagonalFloor x * thetaTailDiagonalFloor t) := hUsq
    _ ≤ (thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
          (thetaTailFirstMomentKernel x x * thetaTailFirstMomentKernel t t) :=
        mul_le_mul_of_nonneg_left hfl (sq_nonneg _)

/-- **Correlation bound.**  For `1 ≤ x ≤ t` the kernel entry is dominated by
`K·e^{-(t-x)/2}` times the geometric mean of the diagonal entries. -/
theorem thetaTailFirstMomentKernel_le_corr {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t) :
    thetaTailFirstMomentKernel x t ≤
      thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2)) *
        (Real.sqrt (thetaTailFirstMomentKernel x x) *
          Real.sqrt (thetaTailFirstMomentKernel t t)) := by
  have ht : 1 ≤ t := hx.trans hxt
  have hknn := thetaTailKernel_nonneg_of_one_le hx ht
  have hxx := thetaTailKernel_nonneg_of_one_le hx hx
  have hKe : (0 : ℝ) ≤ thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2)) :=
    mul_nonneg thetaTailPacketRatioConstant_pos.le (Real.exp_pos _).le
  have h := thetaTailFirstMomentKernel_sq_le hx hxt
  calc thetaTailFirstMomentKernel x t
      = Real.sqrt (thetaTailFirstMomentKernel x t ^ 2) := (Real.sqrt_sq hknn).symm
    _ ≤ Real.sqrt ((thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2))) ^ 2 *
          (thetaTailFirstMomentKernel x x * thetaTailFirstMomentKernel t t)) :=
        Real.sqrt_le_sqrt h
    _ = thetaTailPacketRatioConstant * Real.exp (-((t - x) / 2)) *
          (Real.sqrt (thetaTailFirstMomentKernel x x) *
            Real.sqrt (thetaTailFirstMomentKernel t t)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKe, Real.sqrt_mul hxx]

/-! ### The separated-packet theorem -/

/-- The explicit packet separation threshold `2·log(1 + 2K)`. -/
def thetaTailPacketSeparation : ℝ :=
  2 * Real.log (1 + 2 * thetaTailPacketRatioConstant)

theorem thetaTailPacketSeparation_pos : 0 < thetaTailPacketSeparation := by
  unfold thetaTailPacketSeparation
  have hK := thetaTailPacketRatioConstant_pos
  have h1 : (1 : ℝ) < 1 + 2 * thetaTailPacketRatioConstant := by linarith
  have := Real.log_pos h1
  linarith

/-- Geometric off-diagonal row sums are bounded by two geometric tails, `2q/(1-q)`. -/
theorem geom_row_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n i : ℕ) :
    ∑ j ∈ (Finset.range n).erase i, q ^ Nat.dist i j ≤ 2 * (q / (1 - q)) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have htail : ∀ m : ℕ, ∑ k ∈ Finset.range m, q ^ (k + 1) ≤ q / (1 - q) := by
    intro m
    have hgeom : ∑ k ∈ Finset.range m, q ^ k ≤ 1 / (1 - q) := by
      rw [geom_sum_eq (ne_of_lt hq1) m,
        show (q ^ m - 1) / (q - 1) = (1 - q ^ m) / (1 - q) by
          rw [← neg_div_neg_eq]; ring_nf]
      have h0 : (0 : ℝ) ≤ q ^ m := by positivity
      have hnum : (1 : ℝ) - q ^ m ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr h1q.le)
      simpa [div_eq_mul_inv] using this
    have hstep : ∑ k ∈ Finset.range m, q ^ (k + 1) =
        q * ∑ k ∈ Finset.range m, q ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
    rw [hstep]
    calc q * ∑ k ∈ Finset.range m, q ^ k ≤ q * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left hgeom hq0
      _ = q / (1 - q) := by ring
  have hsplit : (Finset.range n).erase i =
      Finset.range (min i n) ∪ Finset.Ico (i + 1) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
      lt_min_iff]
    omega
  have hdisj : Disjoint (Finset.range (min i n)) (Finset.Ico (i + 1) n) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range, lt_min_iff] at hj
    simp only [Finset.mem_Ico] at hj'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ j ∈ Finset.range (min i n), q ^ Nat.dist i j ≤ q / (1 - q) := by
    have hcongr : ∑ j ∈ Finset.range (min i n), q ^ Nat.dist i j =
        ∑ j ∈ Finset.range (min i n), q ^ (i - j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range, lt_min_iff] at hj
      rw [Nat.dist_eq_sub_of_le_right (by omega)]
    rw [hcongr]
    calc ∑ j ∈ Finset.range (min i n), q ^ (i - j)
        ≤ ∑ j ∈ Finset.range (min i n), q ^ (min i n - 1 - j + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_range, lt_min_iff] at hj
          exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
      _ = ∑ k ∈ Finset.range (min i n), q ^ (k + 1) :=
          Finset.sum_range_reflect (fun k => q ^ (k + 1)) (min i n)
      _ ≤ q / (1 - q) := htail _
  have hright : ∑ j ∈ Finset.Ico (i + 1) n, q ^ Nat.dist i j ≤ q / (1 - q) := by
    have hcongr : ∑ j ∈ Finset.Ico (i + 1) n, q ^ Nat.dist i j =
        ∑ k ∈ Finset.range (n - (i + 1)), q ^ (k + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.dist_eq_sub_of_le (by omega)]
      congr 1
      omega
    rw [hcongr]
    exact htail _
  linarith

/-- **Separated-packet positivity of the theta tail first-moment kernel.**
For every gap `σ` at least the explicit threshold `thetaTailPacketSeparation`, every packet
`x 0 < x 1 < ⋯` in `[1, ∞)` with consecutive gaps at least `σ`, every length `n`, and every
real coefficient vector `a`, the quadratic form of the kernel is nonnegative.  Unconditional:
the first off-diagonal positivity stratum of the Bezoutian Riemann hypothesis criterion. -/
theorem thetaTailFirstMomentKernel_separatedPacket_quadraticForm_nonneg
    {σ : ℝ} (hσ : thetaTailPacketSeparation ≤ σ)
    {x : ℕ → ℝ} (hbase : 1 ≤ x 0) (hstep : ∀ m, x m + σ ≤ x (m + 1))
    (n : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
  have hK := thetaTailPacketRatioConstant_pos
  have hσ0 : 0 < σ := lt_of_lt_of_le thetaTailPacketSeparation_pos hσ
  -- packet growth
  have hgap : ∀ i j : ℕ, i ≤ j → x i + (j - i : ℕ) * σ ≤ x j := by
    intro i j hij
    induction j with
    | zero =>
      have h0 : i = 0 := Nat.le_zero.mp hij
      subst h0; simp
    | succ m ih =>
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · have him : i ≤ m := by omega
        have h1 := ih him
        have h2 := hstep m
        have hcast : ((m + 1 - i : ℕ) : ℝ) = ((m - i : ℕ) : ℝ) + 1 := by
          have : m + 1 - i = (m - i) + 1 := by omega
          rw [this]
          push_cast
          ring
        rw [hcast]
        nlinarith
      · have h0 : i = m + 1 := by omega
        subst h0; simp
  have hone : ∀ i : ℕ, 1 ≤ x i := by
    intro i
    have h := hgap 0 i (Nat.zero_le i)
    have hnn : (0 : ℝ) ≤ ((i - 0 : ℕ) : ℝ) * σ := by positivity
    simp only [Nat.sub_zero] at h hnn
    linarith
  have hmono : ∀ i j : ℕ, i ≤ j → x i ≤ x j := by
    intro i j hij
    have h := hgap i j hij
    have hnn : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) * σ := by positivity
    linarith
  set q : ℝ := Real.exp (-(σ / 2)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef, show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hqK : q * (1 + 2 * thetaTailPacketRatioConstant) ≤ 1 := by
    have h1 : Real.log (1 + 2 * thetaTailPacketRatioConstant) ≤ σ / 2 := by
      have h2 := hσ
      unfold thetaTailPacketSeparation at h2
      linarith
    have h2 : q ≤ (1 + 2 * thetaTailPacketRatioConstant)⁻¹ := by
      rw [hqdef, ← Real.exp_log
        (show (0 : ℝ) < (1 + 2 * thetaTailPacketRatioConstant)⁻¹ by
          exact inv_pos.mpr (by linarith))]
      apply Real.exp_le_exp.mpr
      rw [Real.log_inv]
      linarith
    calc q * (1 + 2 * thetaTailPacketRatioConstant)
        ≤ (1 + 2 * thetaTailPacketRatioConstant)⁻¹ *
            (1 + 2 * thetaTailPacketRatioConstant) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = 1 := by
          rw [inv_mul_cancel₀]
          linarith
  -- entrywise correlation bound at packet nodes
  have hcorr : ∀ i j : ℕ, i < j →
      thetaTailFirstMomentKernel (x i) (x j) ≤
        thetaTailPacketRatioConstant * q ^ (j - i) *
          (Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) *
            Real.sqrt (thetaTailFirstMomentKernel (x j) (x j))) := by
    intro i j hij
    have h1 := thetaTailFirstMomentKernel_le_corr (hone i) (hmono i j hij.le)
    have h2 : Real.exp (-((x j - x i) / 2)) ≤ q ^ (j - i) := by
      have h3 := hgap i j hij.le
      have h4 : q ^ (j - i) = Real.exp (-(((j - i : ℕ) : ℝ) * σ / 2)) := by
        rw [hqdef, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [h4]
      apply Real.exp_le_exp.mpr
      have h5 : ((j - i : ℕ) : ℝ) * σ ≤ x j - x i := by linarith
      linarith
    have hs1 : (0 : ℝ) ≤ Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) :=
      Real.sqrt_nonneg _
    have hs2 : (0 : ℝ) ≤ Real.sqrt (thetaTailFirstMomentKernel (x j) (x j)) :=
      Real.sqrt_nonneg _
    calc thetaTailFirstMomentKernel (x i) (x j)
        ≤ thetaTailPacketRatioConstant * Real.exp (-((x j - x i) / 2)) *
            (Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) *
              Real.sqrt (thetaTailFirstMomentKernel (x j) (x j))) := h1
      _ ≤ thetaTailPacketRatioConstant * q ^ (j - i) *
            (Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) *
              Real.sqrt (thetaTailFirstMomentKernel (x j) (x j))) := by
          have h6 := mul_le_mul_of_nonneg_left h2 hK.le
          have h7 : (0 : ℝ) ≤ Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) *
              Real.sqrt (thetaTailFirstMomentKernel (x j) (x j)) :=
            mul_nonneg hs1 hs2
          exact mul_le_mul_of_nonneg_right h6 h7
  -- the scaled coefficients
  set b : ℕ → ℝ := fun i => |a i| * Real.sqrt (thetaTailFirstMomentKernel (x i) (x i))
    with hbdef
  have hbsq : ∀ i, b i ^ 2 = a i ^ 2 * thetaTailFirstMomentKernel (x i) (x i) := by
    intro i
    rw [hbdef]
    have h := thetaTailKernel_nonneg_of_one_le (hone i) (hone i)
    rw [mul_pow, sq_abs, Real.sq_sqrt h]
  -- per-pair lower bound for the off-diagonal terms
  have hpair : ∀ i j : ℕ, i ≠ j →
      -(thetaTailPacketRatioConstant * q ^ Nat.dist i j *
          ((b i ^ 2 + b j ^ 2) / 2)) ≤
        a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
    have hmain : ∀ i j : ℕ, i < j →
        -(thetaTailPacketRatioConstant * q ^ Nat.dist i j *
            ((b i ^ 2 + b j ^ 2) / 2)) ≤
          a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
      intro i j hij
      have hk := hcorr i j hij
      have hknn := thetaTailKernel_nonneg_of_one_le (hone i) (hone j)
      have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hij.le
      have habs : -(|a i| * |a j| * thetaTailFirstMomentKernel (x i) (x j)) ≤
          a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
        have h1 : -(|a i| * |a j|) ≤ a i * a j := by
          rw [← abs_mul]
          exact neg_abs_le _
        have h2 := mul_le_mul_of_nonneg_right h1 hknn
        calc -(|a i| * |a j| * thetaTailFirstMomentKernel (x i) (x j))
            = -(|a i| * |a j|) * thetaTailFirstMomentKernel (x i) (x j) := by ring
          _ ≤ a i * a j * thetaTailFirstMomentKernel (x i) (x j) := h2
      have hup : |a i| * |a j| * thetaTailFirstMomentKernel (x i) (x j) ≤
          thetaTailPacketRatioConstant * q ^ (j - i) * (b i * b j) := by
        have h2 := mul_le_mul_of_nonneg_left hk
          (show (0 : ℝ) ≤ |a i| * |a j| by positivity)
        calc |a i| * |a j| * thetaTailFirstMomentKernel (x i) (x j)
            ≤ |a i| * |a j| * (thetaTailPacketRatioConstant * q ^ (j - i) *
                (Real.sqrt (thetaTailFirstMomentKernel (x i) (x i)) *
                  Real.sqrt (thetaTailFirstMomentKernel (x j) (x j)))) := h2
          _ = thetaTailPacketRatioConstant * q ^ (j - i) * (b i * b j) := by
              rw [hbdef]
              ring
      have hamgm : b i * b j ≤ (b i ^ 2 + b j ^ 2) / 2 := by
        nlinarith [sq_nonneg (b i - b j)]
      have hKq : (0 : ℝ) ≤ thetaTailPacketRatioConstant * q ^ (j - i) :=
        mul_nonneg thetaTailPacketRatioConstant_pos.le (pow_nonneg hq0.le _)
      rw [hdist]
      have h8 := mul_le_mul_of_nonneg_left hamgm hKq
      calc -(thetaTailPacketRatioConstant * q ^ (j - i) * ((b i ^ 2 + b j ^ 2) / 2))
          ≤ -(thetaTailPacketRatioConstant * q ^ (j - i) * (b i * b j)) := by
            linarith
        _ ≤ -(|a i| * |a j| * thetaTailFirstMomentKernel (x i) (x j)) := by
            linarith
        _ ≤ a i * a j * thetaTailFirstMomentKernel (x i) (x j) := habs
    intro i j hij
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact hmain i j hlt
    · have hlt : j < i := by omega
      have h := hmain j i hlt
      rw [Nat.dist_comm]
      calc -(thetaTailPacketRatioConstant * q ^ Nat.dist j i *
            ((b i ^ 2 + b j ^ 2) / 2))
          = -(thetaTailPacketRatioConstant * q ^ Nat.dist j i *
              ((b j ^ 2 + b i ^ 2) / 2)) := by ring
        _ ≤ a j * a i * thetaTailFirstMomentKernel (x j) (x i) := h
        _ = a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
            rw [thetaTailFirstMomentKernel_comm]
            ring
  -- row sums of the correlation weights
  have hrow : ∀ i : ℕ,
      ∑ j ∈ (Finset.range n).erase i,
        thetaTailPacketRatioConstant * q ^ Nat.dist i j ≤ 1 := by
    intro i
    rw [← Finset.mul_sum]
    have hg := geom_row_sum_le hq0.le hq1 n i
    have h2 : thetaTailPacketRatioConstant * (2 * (q / (1 - q))) ≤ 1 := by
      have h3 : thetaTailPacketRatioConstant * (2 * (q / (1 - q))) =
          2 * thetaTailPacketRatioConstant * q / (1 - q) := by
        ring
      rw [h3, div_le_one h1q]
      linarith
    calc thetaTailPacketRatioConstant *
          ∑ j ∈ (Finset.range n).erase i, q ^ Nat.dist i j
        ≤ thetaTailPacketRatioConstant * (2 * (q / (1 - q))) :=
          mul_le_mul_of_nonneg_left hg hK.le
      _ ≤ 1 := h2
  -- expand each row: diagonal plus off-diagonal
  have hexpand : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      a i * a j * thetaTailFirstMomentKernel (x i) (x j) =
      ∑ i ∈ Finset.range n, (b i ^ 2 +
        ∑ j ∈ (Finset.range n).erase i,
          a i * a j * thetaTailFirstMomentKernel (x i) (x j)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase _ _ hi]
    congr 1
    rw [hbsq i]
    ring
  rw [hexpand]
  -- lower bound each off-diagonal row by the weighted diagonal
  have hlower : ∀ i ∈ Finset.range n,
      b i ^ 2 - (∑ j ∈ (Finset.range n).erase i,
          thetaTailPacketRatioConstant * q ^ Nat.dist i j *
            ((b i ^ 2 + b j ^ 2) / 2)) ≤
        b i ^ 2 + ∑ j ∈ (Finset.range n).erase i,
          a i * a j * thetaTailFirstMomentKernel (x i) (x j) := by
    intro i _
    have h := Finset.sum_le_sum (s := (Finset.range n).erase i)
      (f := fun j => -(thetaTailPacketRatioConstant * q ^ Nat.dist i j *
        ((b i ^ 2 + b j ^ 2) / 2)))
      (g := fun j => a i * a j * thetaTailFirstMomentKernel (x i) (x j))
      (fun j hj => hpair i j (by
        simp only [Finset.mem_erase] at hj
        exact fun hij => hj.1 (hij.symm)))
    rw [Finset.sum_neg_distrib] at h
    linarith
  -- the double-count swap and the row-sum closure
  have hswap : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
      thetaTailPacketRatioConstant * q ^ Nat.dist i j * b j ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
        thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2 := by
    rw [Finset.sum_comm' (t' := Finset.range n)
      (s' := fun j => (Finset.range n).erase j)
      (by
        intro i j
        simp only [Finset.mem_erase, Finset.mem_range]
        omega)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.dist_comm]
  have hW : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
      thetaTailPacketRatioConstant * q ^ Nat.dist i j *
        ((b i ^ 2 + b j ^ 2) / 2) ≤ ∑ i ∈ Finset.range n, b i ^ 2 := by
    have hsplit : ∀ i, ∑ j ∈ (Finset.range n).erase i,
        thetaTailPacketRatioConstant * q ^ Nat.dist i j *
          ((b i ^ 2 + b j ^ 2) / 2) =
        (∑ j ∈ (Finset.range n).erase i,
          thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2) / 2 +
        (∑ j ∈ (Finset.range n).erase i,
          thetaTailPacketRatioConstant * q ^ Nat.dist i j * b j ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hA : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
        thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2 ≤
        ∑ i ∈ Finset.range n, b i ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ∑ j ∈ (Finset.range n).erase i,
          thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2 =
          (∑ j ∈ (Finset.range n).erase i,
            thetaTailPacketRatioConstant * q ^ Nat.dist i j) * b i ^ 2 := by
        rw [Finset.sum_mul]
      rw [h1]
      have h2 : (0 : ℝ) ≤ b i ^ 2 := sq_nonneg _
      calc (∑ j ∈ (Finset.range n).erase i,
            thetaTailPacketRatioConstant * q ^ Nat.dist i j) * b i ^ 2
          ≤ 1 * b i ^ 2 := mul_le_mul_of_nonneg_right (hrow i) h2
        _ = b i ^ 2 := one_mul _
    calc ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
          thetaTailPacketRatioConstant * q ^ Nat.dist i j *
            ((b i ^ 2 + b j ^ 2) / 2)
        = (∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2) / 2 +
          (∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            thetaTailPacketRatioConstant * q ^ Nat.dist i j * b j ^ 2) / 2 := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => hsplit i
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            thetaTailPacketRatioConstant * q ^ Nat.dist i j * b i ^ 2 := by
          rw [hswap]
          ring
      _ ≤ ∑ i ∈ Finset.range n, b i ^ 2 := hA
  have hfinal := Finset.sum_le_sum hlower
  rw [Finset.sum_sub_distrib] at hfinal
  linarith [hW, hfinal]

end

end RHTower
