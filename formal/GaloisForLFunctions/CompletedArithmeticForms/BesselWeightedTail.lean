import GaloisForLFunctions.CompletedArithmeticForms.BesselRadialSlice
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Positive signed combinations of weighted Bessel tails

The first weighted tail supplies a strict reserve at every real frequency.
Integration by parts transfers it to higher powers and pays their signed
endpoint values. Raising the weight by two retains the factor
`q² + q + 1/2`; the signed first-atom combination is positive whenever
`q > 1 + sqrt 2`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry
noncomputable section

/-- Real imaginary-order Schläfli carrier in the radial tail coordinate. -/
def besselRadialValue (τ u : ℝ) : ℝ :=
  (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re

/-- A real-power weighted tail of the actual radial Schläfli carrier. -/
def besselPowerTail (p τ q : ℝ) : ℝ :=
  ∫ u in Ioi q, u ^ p * besselRadialValue τ u

/-- Explicit exponential envelope for a fixed frequency and power. -/
def besselPowerTailCost (p τ : ℝ) : ℝ :=
  Real.exp 1 * besselOrderUnitMass (((2 * τ : ℝ) : ℂ) * I) * (Nat.ceil p).factorial

theorem besselPowerTailCost_nonneg (p τ : ℝ) : 0 ≤ besselPowerTailCost p τ := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le (besselOrderUnitMass_nonneg _)) (by positivity)

theorem besselPowerTail_one (τ q : ℝ) :
    besselPowerTail 1 τ q = besselFirstWeightedTail τ q := by
  simp only [besselPowerTail, Real.rpow_one, besselRadialValue, besselFirstWeightedTail]

theorem continuousAt_besselRadialValue {u : ℝ} (hu : 0 < u) (τ : ℝ) :
    ContinuousAt (besselRadialValue τ) u := by
  have hK := (hasDerivAt_modifiedBesselKOrder_arg (by linarith : 0 < 2 * u)
    (((2 * τ : ℝ) : ℂ) * I)).continuousAt.comp'
      (f := fun v : ℝ => 2 * v) (x := u) (by fun_prop)
  exact Complex.continuous_re.continuousAt.comp'
    (f := fun v : ℝ => modifiedBesselKOrder (2 * v) (((2 * τ : ℝ) : ℂ) * I))
    (x := u) hK

/-- Every fixed radial power is bounded by an explicit decaying exponential. -/
theorem norm_besselPowerIntegrand_le {u : ℝ} (hu : 1 ≤ u) (p τ : ℝ) :
    ‖u ^ p * besselRadialValue τ u‖ ≤ besselPowerTailCost p τ * Real.exp (-u) := by
  let ν : ℂ := ((2 * τ : ℝ) : ℂ) * I
  let m : ℕ := Nat.ceil p
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hm : u ^ p ≤ u ^ m := by
    have h := Real.rpow_le_rpow_of_exponent_le hu (Nat.le_ceil p)
    simpa only [Real.rpow_natCast] using h
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hpow := Real.pow_div_factorial_le_exp u hu0 m
  rw [div_le_iff₀ hfac] at hpow
  have hB : |besselRadialValue τ u| ≤ Real.exp (1 - 2 * u) * besselOrderUnitMass ν :=
    (Complex.abs_re_le_norm _).trans
      (norm_modifiedBesselKOrder_le_exp (by linarith : 1 ≤ 2 * u) ν)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0 p)]
  calc
    _ ≤ u ^ m * (Real.exp (1 - 2 * u) * besselOrderUnitMass ν) :=
      mul_le_mul hm hB (abs_nonneg _) (pow_nonneg hu0 _)
    _ ≤ (Real.exp u * (m.factorial : ℝ)) *
        (Real.exp (1 - 2 * u) * besselOrderUnitMass ν) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (Real.exp_pos _).le (besselOrderUnitMass_nonneg ν))
    _ = _ := by
      have he : Real.exp u * Real.exp (1 - 2 * u) = Real.exp 1 * Real.exp (-u) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp u * Real.exp (1 - 2 * u)) *
            besselOrderUnitMass ν * (m.factorial : ℝ) := by ring
        _ = _ := by rw [he]; dsimp only [besselPowerTailCost, ν, m]; ring

/-- Absolute convergence of every real-power tail on the positive radial ray. -/
theorem integrableOn_besselPowerIntegrand {q : ℝ} (hq : 1 ≤ q) (p τ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ p * besselRadialValue τ u) (Ioi q) := by
  have hc : ContinuousOn (fun u : ℝ => u ^ p * besselRadialValue τ u) (Ioi q) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hq.trans hu.le)
    exact ((Real.continuousAt_rpow_const u p (Or.inl hu0.ne')).mul
      (continuousAt_besselRadialValue hu0 τ)).continuousWithinAt
  refine ((integrableOn_exp_neg_Ioi q).const_mul (besselPowerTailCost p τ)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_besselPowerIntegrand_le (hq.trans hu.le) p τ

/-- The actual weighted tail has an exponential envelope uniform in its cutoff. -/
theorem abs_besselPowerTail_le {q : ℝ} (hq : 1 ≤ q) (p τ : ℝ) :
    |besselPowerTail p τ q| ≤ besselPowerTailCost p τ * Real.exp (-q) := by
  have hi := integrableOn_besselPowerIntegrand hq p τ
  have henv := (integrableOn_exp_neg_Ioi q).const_mul (besselPowerTailCost p τ)
  have hcomp : (∫ u in Ioi q, ‖u ^ p * besselRadialValue τ u‖) ≤
      ∫ u in Ioi q, besselPowerTailCost p τ * Real.exp (-u) := by
    apply integral_mono_ae hi.norm henv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_besselPowerIntegrand_le (hq.trans hu.le) p τ
  have he : (∫ u in Ioi q, Real.exp (-u)) = Real.exp (-q) := by
    simpa only [neg_one_mul, div_neg, div_one, neg_neg] using
      integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) q
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Ioi q))
    (fun u : ℝ => u ^ p * besselRadialValue τ u)
  rw [Real.norm_eq_abs] at hn
  exact hn.trans (hcomp.trans_eq (by rw [integral_const_mul, he]))

theorem continuousAt_besselPowerIntegrand {u : ℝ} (hu : 0 < u) (p τ : ℝ) :
    ContinuousAt (fun v : ℝ => v ^ p * besselRadialValue τ v) u :=
  (Real.continuousAt_rpow_const u p (Or.inl hu.ne')).mul
    (continuousAt_besselRadialValue hu τ)

/-- Differentiating the moving lower endpoint retains the actual Schläfli source. -/
theorem hasDerivAt_besselPowerTail {q : ℝ} (hq : 1 < q) (p τ : ℝ) :
    HasDerivAt (besselPowerTail p τ) (-(q ^ p * besselRadialValue τ q)) q := by
  let f : ℝ → ℝ := fun u => u ^ p * besselRadialValue τ u
  have hi : IntegrableOn f (Ioi 1) := integrableOn_besselPowerIntegrand le_rfl p τ
  have hc : ContinuousOn f (Ioi 1) := fun u hu =>
    (continuousAt_besselPowerIntegrand (zero_lt_one.trans hu) p τ).continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter f (𝓝 q) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc q hq
  have hII : IntervalIntegrable f volume 1 q :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.le).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas
    (continuousAt_besselPowerIntegrand (zero_lt_one.trans hq) p τ)
  have hd : HasDerivAt (fun y => besselPowerTail p τ 1 - ∫ u in (1 : ℝ)..y, f u)
      (-(q ^ p * besselRadialValue τ q)) q := by
    simpa only [f] using hbase.const_sub (besselPowerTail p τ 1)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hq] with y hy
  have hs : (∫ u in (1 : ℝ)..y, f u) = besselPowerTail p τ 1 - besselPowerTail p τ y :=
    (intervalIntegral.integral_Ioi_sub_Ioi' hi
      (integrableOn_besselPowerIntegrand hy.le p τ)).symm
  linarith

/-- Every real power times a weighted tail tends to zero at infinity. -/
theorem tendsto_rpow_mul_besselPowerTail_zero (a p τ : ℝ) :
    Tendsto (fun q : ℝ => q ^ a * besselPowerTail p τ q) atTop (𝓝 0) := by
  have hl : Tendsto (fun q : ℝ => besselPowerTailCost p τ * (q ^ a * Real.exp (-q)))
      atTop (𝓝 0) := by
    simpa only [neg_one_mul, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 (by norm_num)).const_mul
        (besselPowerTailCost p τ)
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hq) a)]
  calc
    _ ≤ q ^ a * (besselPowerTailCost p τ * Real.exp (-q)) :=
      mul_le_mul_of_nonneg_left (abs_besselPowerTail_le hq p τ)
        (Real.rpow_nonneg (zero_le_one.trans hq) a)
    _ = _ := by ring

/-- Positive-ray real powers are integrable against every fixed weighted Bessel tail. -/
theorem integrableOn_rpow_mul_besselPowerTail {q a : ℝ} (hq : 1 ≤ q)
    (ha : -1 < a) (p τ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ a * besselPowerTail p τ u) (Ioi q) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ a * Real.exp (-u)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow ha (show (1 : ℝ) ≤ 1 from le_rfl)
        (show (0 : ℝ) < 1 by norm_num))
  have he := (hg.mono_set (show Ioi q ⊆ Ioi (0 : ℝ) from
    fun u hu => lt_of_lt_of_le zero_lt_one (hq.trans hu.le))).const_mul
      (besselPowerTailCost p τ)
  have hc : ContinuousOn (fun u : ℝ => u ^ a * besselPowerTail p τ u) (Ioi q) := by
    intro u hu
    have hu1 : 1 < u := hq.trans_lt hu
    exact ((Real.continuousAt_rpow_const u a (Or.inl (zero_lt_one.trans hu1).ne')).mul
      (hasDerivAt_besselPowerTail hu1 p τ).continuousAt).continuousWithinAt
  refine he.mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : 1 ≤ u := hq.trans hu.le
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hu1) a)]
  calc
    _ ≤ u ^ a * (besselPowerTailCost p τ * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left (abs_besselPowerTail_le hu1 p τ)
        (Real.rpow_nonneg (zero_le_one.trans hu1) a)
    _ = _ := by ring


private theorem monotoneOn_exp_mul_first_power_tail (τ : ℝ) :
    MonotoneOn (fun q => Real.exp (2 * q) * besselPowerTail 1 τ q) (Ioi 1) := by
  intro q hq u hu hqu
  dsimp only
  rw [besselPowerTail_one, besselPowerTail_one]
  have h := besselFirstWeightedTail_exp_lower hq.le hqu τ
  calc
    _ = Real.exp (2 * u) *
        (Real.exp (-2 * (u - q)) * besselFirstWeightedTail τ q) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The first weighted tail pays the full signed value at its endpoint. -/
theorem mul_besselRadialValue_le_first_tail {q : ℝ} (hq : 1 < q) (τ : ℝ) :
    q * besselRadialValue τ q ≤ 2 * besselPowerTail 1 τ q := by
  have hd := (((hasDerivAt_id q).const_mul 2).exp).mul
    (hasDerivAt_besselPowerTail hq 1 τ)
  change HasDerivAt (fun u => Real.exp (2 * u) * besselPowerTail 1 τ u) _ q at hd
  have hn := (monotoneOn_exp_mul_first_power_tail τ).derivWithin_nonneg (x := q)
  rw [derivWithin_of_isOpen isOpen_Ioi hq, hd.deriv] at hn
  simp only [Real.rpow_one, id_eq, mul_one] at hn
  have hn' : 0 ≤ Real.exp (2 * q) *
      (2 * besselPowerTail 1 τ q - q * besselRadialValue τ q) := by
    nlinarith only [hn]
  by_contra h
  have hneg : 2 * besselPowerTail 1 τ q - q * besselRadialValue τ q < 0 := by
    linarith [lt_of_not_ge h]
  exact (not_lt_of_ge hn') (mul_neg_of_pos_of_neg (Real.exp_pos _) hneg)

private theorem hasDerivAt_rpow_mul_first_tail {u : ℝ} (hu : 1 < u) (p τ : ℝ) :
    HasDerivAt (fun v : ℝ => v ^ (p - 1) * besselPowerTail 1 τ v)
      ((p - 1) * (u ^ (p - 2) * besselPowerTail 1 τ u) -
        u ^ p * besselRadialValue τ u) u := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hr : HasDerivAt (fun v : ℝ => v ^ (p - 1))
      ((p - 1) * u ^ (p - 1 - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h := hr.mul (hasDerivAt_besselPowerTail hu 1 τ)
  apply h.congr_deriv
  have hm : u ^ (p - 1) * u = u ^ p := by
    calc
      _ = u ^ (p - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ ((p - 1) + 1) := (Real.rpow_add hu0 _ _).symm
      _ = u ^ p := by congr 1; ring
  rw [Real.rpow_one, show p - 1 - 1 = p - 2 by ring]
  calc
    _ = (p - 1) * (u ^ (p - 2) * besselPowerTail 1 τ u) -
        (u ^ (p - 1) * u) * besselRadialValue τ u := by ring
    _ = _ := by rw [hm]

/-- Integration by parts expresses every higher weighted tail through the first one. -/
theorem besselPowerTail_eq_first_tail {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (τ : ℝ) :
    besselPowerTail p τ q = q ^ (p - 1) * besselPowerTail 1 τ q +
      (p - 1) * ∫ u in Ioi q, u ^ (p - 2) * besselPowerTail 1 τ u := by
  have hA := (integrableOn_rpow_mul_besselPowerTail hq.le
    (by linarith : -1 < p - 2) 1 τ).const_mul (p - 1)
  have hB := integrableOn_besselPowerIntegrand hq.le p τ
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u hu => hasDerivAt_rpow_mul_first_tail (hq.trans_le hu) p τ)
    (hA.sub hB) (tendsto_rpow_mul_besselPowerTail_zero (p - 1) 1 τ)
  rw [integral_sub hA hB, integral_const_mul] at h
  change (p - 1) * (∫ u in Ioi q, u ^ (p - 2) * besselPowerTail 1 τ u) -
    besselPowerTail p τ q = 0 - q ^ (p - 1) * besselPowerTail 1 τ q at h
  linarith

/-- The positive first-tail head is retained in every higher weighted tail. -/
theorem first_tail_le_besselPowerTail {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (τ : ℝ) :
    q ^ (p - 1) * besselPowerTail 1 τ q ≤ besselPowerTail p τ q := by
  rw [besselPowerTail_eq_first_tail hq hp]
  have hI : 0 ≤ ∫ u in Ioi q, u ^ (p - 2) * besselPowerTail 1 τ u := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    rw [besselPowerTail_one]
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hq.le.trans hu.le)) _)
      (besselFirstWeightedTail_pos (hq.le.trans hu.le) τ).le
  have hnonneg := mul_nonneg (sub_nonneg.mpr hp.le) hI
  linarith

/-- All higher real-power Bessel tails are strictly positive at every frequency. -/
theorem besselPowerTail_pos {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (τ : ℝ) :
    0 < besselPowerTail p τ q := by
  have hfirst : 0 < besselPowerTail 1 τ q := by
    rw [besselPowerTail_one]
    exact besselFirstWeightedTail_pos hq.le τ
  exact (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _) hfirst).trans_le
    (first_tail_le_besselPowerTail hq hp τ)

/-- A higher weighted tail pays its complete signed endpoint value. -/
theorem rpow_mul_besselRadialValue_le_tail {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (τ : ℝ) :
    q ^ p * besselRadialValue τ q ≤ 2 * besselPowerTail p τ q := by
  have hm : q ^ (p - 1) * q = q ^ p := by
    calc
      _ = q ^ (p - 1) * q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ ((p - 1) + 1) := (Real.rpow_add (zero_lt_one.trans hq) _ _).symm
      _ = q ^ p := by congr 1; ring
  calc
    _ = q ^ (p - 1) * (q * besselRadialValue τ q) := by rw [← mul_assoc, hm]
    _ ≤ q ^ (p - 1) * (2 * besselPowerTail 1 τ q) :=
      mul_le_mul_of_nonneg_left (mul_besselRadialValue_le_first_tail hq τ)
        (Real.rpow_nonneg (zero_le_one.trans hq.le) _)
    _ ≤ _ := by linarith [first_tail_le_besselPowerTail hq hp τ]


/-- The exponential rescaling of a higher weighted tail has a nonnegative derivative. -/
theorem hasDerivAt_exp_mul_besselPowerTail {q : ℝ} (hq : 1 < q) (p τ : ℝ) :
    HasDerivAt (fun u => Real.exp (2 * u) * besselPowerTail p τ u)
      (Real.exp (2 * q) * (2 * besselPowerTail p τ q -
        q ^ p * besselRadialValue τ q)) q := by
  have h := (((hasDerivAt_id q).const_mul 2).exp).mul
    (hasDerivAt_besselPowerTail hq p τ)
  apply h.congr_deriv
  dsimp only [id_eq]
  ring

theorem monotoneOn_exp_mul_besselPowerTail {p : ℝ} (hp : 1 < p) (τ : ℝ) :
    MonotoneOn (fun q => Real.exp (2 * q) * besselPowerTail p τ q) (Ioi 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 1)
  · intro q hq
    exact (hasDerivAt_exp_mul_besselPowerTail hq p τ).continuousAt.continuousWithinAt
  · intro q hq
    exact (hasDerivAt_exp_mul_besselPowerTail
      (show 1 < q from interior_subset hq) p τ).hasDerivWithinAt
  · intro q hq
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
      (rpow_mul_besselRadialValue_le_tail (show 1 < q from interior_subset hq) hp τ))

/-- Every higher weighted tail retains the same exponential reserve as the first tail. -/
theorem besselPowerTail_exp_lower {q u p : ℝ}
    (hq : 1 < q) (hqu : q ≤ u) (hp : 1 < p) (τ : ℝ) :
    Real.exp (-2 * (u - q)) * besselPowerTail p τ q ≤ besselPowerTail p τ u := by
  have h := monotoneOn_exp_mul_besselPowerTail hp τ hq (hq.trans_le hqu) hqu
  calc
    _ = Real.exp (-2 * u) * (Real.exp (2 * q) * besselPowerTail p τ q) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-2 * u) * (Real.exp (2 * u) * besselPowerTail p τ u) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : -2 * u + 2 * u = 0 := by ring
      rw [he, Real.exp_zero, one_mul]

private theorem hasDerivAt_sq_mul_besselPowerTail {u : ℝ} (hu : 1 < u) (p τ : ℝ) :
    HasDerivAt (fun v : ℝ => v ^ (2 : ℕ) * besselPowerTail p τ v)
      (2 * (u * besselPowerTail p τ u) - u ^ (p + 2) * besselRadialValue τ u) u := by
  have h := ((hasDerivAt_id u).pow 2).mul (hasDerivAt_besselPowerTail hu p τ)
  apply h.congr_deriv
  have hm : u ^ (2 : ℕ) * u ^ p = u ^ (p + 2) := by
    rw [Real.rpow_add (zero_lt_one.trans hu)]
    norm_num
    ring
  dsimp only [id_eq, Pi.pow_apply]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  calc
    _ = 2 * (u * besselPowerTail p τ u) -
        (u ^ (2 : ℕ) * u ^ p) * besselRadialValue τ u := by ring
    _ = _ := by rw [hm]

/-- Raising the radial weight by two keeps the exact first moment of the preceding tail. -/
theorem besselPowerTail_add_two {q : ℝ} (hq : 1 < q) (p τ : ℝ) :
    besselPowerTail (p + 2) τ q = q ^ (2 : ℕ) * besselPowerTail p τ q +
      2 * ∫ u in Ioi q, u * besselPowerTail p τ u := by
  have hi : IntegrableOn (fun u : ℝ => u * besselPowerTail p τ u) (Ioi q) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_besselPowerTail hq.le (show (-1 : ℝ) < 1 by norm_num) p τ
  have hlim : Tendsto (fun u : ℝ => u ^ (2 : ℕ) * besselPowerTail p τ u) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_rpow_mul_besselPowerTail_zero 2 p τ
  have hB := integrableOn_besselPowerIntegrand hq.le (p + 2) τ
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u hu => hasDerivAt_sq_mul_besselPowerTail (hq.trans_le hu) p τ)
    ((hi.const_mul 2).sub hB) hlim
  rw [integral_sub (hi.const_mul 2) hB, integral_const_mul] at h
  change 2 * (∫ u in Ioi q, u * besselPowerTail p τ u) -
    besselPowerTail (p + 2) τ q = 0 - q ^ (2 : ℕ) * besselPowerTail p τ q at h
  linarith

private theorem integrableOn_mul_exp_shift {q : ℝ} (hq : 1 ≤ q) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-2 * (u - q))) (Ioi q) := by
  have hbase : IntegrableOn (fun u : ℝ => u * Real.exp (-2 * u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (show (-1 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ 1 from le_rfl) (show (0 : ℝ) < 2 by norm_num))
  have h : IntegrableOn (fun u : ℝ => Real.exp (2 * q) * (u * Real.exp (-2 * u)))
      (Ioi q) :=
    (hbase.mono_set (show Ioi q ⊆ Ioi (0 : ℝ) from
      fun u hu => lt_of_lt_of_le zero_lt_one (hq.trans hu.le))).const_mul (Real.exp (2 * q))
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  dsimp only
  rw [show -2 * (u - q) = 2 * q + -2 * u by ring, Real.exp_add]
  ring

/-- Exact first moment of the shifted exponential reserve. -/
theorem integral_mul_exp_shift {q : ℝ} (hq : 1 ≤ q) :
    (∫ u in Ioi q, u * Real.exp (-2 * (u - q))) = q / 2 + 1 / 4 := by
  let G : ℝ → ℝ := fun u => -(u / 2 + 1 / 4) * Real.exp (-2 * (u - q))
  have hD (u : ℝ) : HasDerivAt G (u * Real.exp (-2 * (u - q))) u := by
    have h := ((((hasDerivAt_id u).div_const 2).add_const (1 / 4)).neg).mul
      ((((hasDerivAt_id u).sub_const q).const_mul (-2)).exp)
    apply h.congr_deriv
    dsimp only [id_eq, Pi.neg_apply]
    ring
  have h0 : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 2 (by norm_num)
  have h1 : Tendsto (fun u : ℝ => u * Real.exp (-2 * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 2 (by norm_num)
  have hlim : Tendsto G atTop (𝓝 0) := by
    have he : G = fun u => (-Real.exp (2 * q) / 2) * (u * Real.exp (-2 * u)) +
        (-Real.exp (2 * q) / 4) * Real.exp (-2 * u) := by
      funext u
      dsimp only [G]
      rw [show -2 * (u - q) = 2 * q + -2 * u by ring, Real.exp_add]
      ring
    rw [he]
    simpa only [mul_zero, add_zero] using (h1.const_mul _).add (h0.const_mul _)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hD u)
    (integrableOn_mul_exp_shift hq) hlim
  simpa only [G, sub_self, mul_zero, Real.exp_zero, mul_one, zero_sub, neg_neg] using h

/-- The next quadratic weight has a uniform reserve beyond its endpoint contribution. -/
theorem besselPowerTail_add_two_lower {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (τ : ℝ) :
    (q ^ (2 : ℕ) + q + 1 / 2) * besselPowerTail p τ q ≤ besselPowerTail (p + 2) τ q := by
  have hi : IntegrableOn (fun u : ℝ => u * besselPowerTail p τ u) (Ioi q) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_besselPowerTail hq.le (show (-1 : ℝ) < 1 by norm_num) p τ
  have hcomp : (∫ u in Ioi q, besselPowerTail p τ q * (u * Real.exp (-2 * (u - q)))) ≤
      ∫ u in Ioi q, u * besselPowerTail p τ u := by
    apply setIntegral_mono_on
      ((integrableOn_mul_exp_shift hq.le).const_mul (besselPowerTail p τ q)) hi
      measurableSet_Ioi
    intro u hu
    have h := mul_le_mul_of_nonneg_left (besselPowerTail_exp_lower hq hu.le hp τ)
      (le_of_lt (zero_lt_one.trans (hq.trans hu)))
    convert h using 1; ring
  rw [integral_const_mul, integral_mul_exp_shift hq.le] at hcomp
  rw [besselPowerTail_add_two hq]
  nlinarith only [hcomp]

/-- The signed weighted Bessel combination at the first-atom exponents. -/
def besselFirstAtomTailDensity (τ q : ℝ) : ℝ :=
  4 * besselPowerTail (7 / 2) τ q - 6 * besselPowerTail (3 / 2) τ q -
    6 * q ^ (5 / 2 : ℝ) * besselRadialValue τ q

/-- The complete signed combination retains a positive coefficient times its lower power tail. -/
theorem besselFirstAtomTailDensity_lower {q : ℝ} (hq : 1 < q) (τ : ℝ) :
    4 * (q ^ (2 : ℕ) - 2 * q - 1) * besselPowerTail (3 / 2) τ q ≤
      besselFirstAtomTailDensity τ q := by
  have hA := besselPowerTail_add_two_lower hq (show (1 : ℝ) < 3 / 2 by norm_num) τ
  norm_num only [show (3 / 2 : ℝ) + 2 = 7 / 2 by norm_num] at hA
  have hB := mul_le_mul_of_nonneg_left
    (rpow_mul_besselRadialValue_le_tail hq (show (1 : ℝ) < 3 / 2 by norm_num) τ)
    (show 0 ≤ 6 * q by linarith)
  have hm : q ^ (5 / 2 : ℝ) = q * q ^ (3 / 2 : ℝ) := by
    have h := Real.rpow_add (zero_lt_one.trans hq) 1 (3 / 2)
    norm_num at h
    exact h
  rw [besselFirstAtomTailDensity, hm]
  nlinarith only [hA, hB]

/-- All-frequency positivity above the explicit radial threshold. -/
theorem besselFirstAtomTailDensity_pos {q : ℝ} (hq : 1 + Real.sqrt 2 < q) (τ : ℝ) :
    0 < besselFirstAtomTailDensity τ q := by
  have hq1 : 1 < q := by linarith [Real.sqrt_nonneg 2]
  have hc : 0 < q ^ (2 : ℕ) - 2 * q - 1 := by
    have hprod := mul_pos (show 0 < q - 1 - Real.sqrt 2 by linarith)
      (show 0 < q - 1 + Real.sqrt 2 by linarith [Real.sqrt_nonneg 2])
    nlinarith only [hprod, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact (mul_pos (mul_pos (by norm_num) hc)
    (besselPowerTail_pos hq1 (by norm_num : (1 : ℝ) < 3 / 2) τ)).trans_le
      (besselFirstAtomTailDensity_lower hq1 τ)

end
end GaloisForLFunctions.CompletedArithmeticForms
