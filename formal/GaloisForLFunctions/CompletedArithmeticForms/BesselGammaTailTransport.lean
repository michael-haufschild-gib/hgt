import GaloisForLFunctions.CompletedArithmeticForms.BesselPositiveCutoff
import GaloisForLFunctions.CompletedArithmeticForms.BesselCompleteGammaMass
import GaloisForLFunctions.CompletedArithmeticForms.BesselUpperTailReserve

/-!
# Exponential transport of the complete Gamma reserve

The first radial square tail pays its endpoint at every positive cutoff.
Integration by parts transfers that payment to every higher radial power.
Exponential monotonicity then transports the complete Mellin mass from
zero, retaining the natural Gamma frequency scale of the signed first atom.
-/

open Complex Filter Set MeasureTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The lower-endpoint derivative holds throughout the positive Mellin ray. -/
theorem hasDerivAt_besselPowerTail_of_pos {q p : ℝ} (hq : 0 < q) (hp : -1 < p) (τ : ℝ) :
    HasDerivAt (besselPowerTail p τ) (-(q ^ p * besselRadialValue τ q)) q := by
  let f : ℝ → ℝ := fun u => u ^ p * besselRadialValue τ u
  have hi : IntegrableOn f (Ioi 0) := integrableOn_besselPowerIntegrand_zero hp τ
  have hc : ContinuousOn f (Ioi 0) := fun u hu =>
    (continuousAt_besselPowerIntegrand hu p τ).continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter f (𝓝 q) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc q hq
  have hII : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.le).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas
    (continuousAt_besselPowerIntegrand hq p τ)
  have hd : HasDerivAt (fun y => besselPowerTail p τ 0 - ∫ u in (0 : ℝ)..y, f u)
      (-(q ^ p * besselRadialValue τ q)) q := by
    simpa only [f] using hbase.const_sub (besselPowerTail p τ 0)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hq] with y hy
  have hs : (∫ u in (0 : ℝ)..y, f u) = besselPowerTail p τ 0 - besselPowerTail p τ y :=
    (intervalIntegral.integral_Ioi_sub_Ioi' hi
      (hi.mono_set (Ioi_subset_Ioi hy.le))).symm
  linarith only [hs]

private theorem integrableOn_rpow_firstTail_of_pos {q a : ℝ}
    (hq : 0 < q) (ha : -1 < a) (τ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ a * besselPowerTail 1 τ u) (Ioi q) := by
  let U : ℝ := max q 1
  have hc : ContinuousOn (fun u : ℝ => u ^ a * besselPowerTail 1 τ u) (Icc q U) := by
    intro u hu
    have hu0 : 0 < u := hq.trans_le hu.1
    exact ((Real.continuousAt_rpow_const u a (Or.inl hu0.ne')).mul
      (hasDerivAt_besselPowerTail_of_pos hu0 (by norm_num : (-1 : ℝ) < 1) τ).continuousAt).continuousWithinAt
  have ht := integrableOn_rpow_mul_besselPowerTail
    (show 1 ≤ U from le_max_right _ _) ha 1 τ
  refine (hc.integrableOn_Icc.union ht).mono_set ?_
  intro u hu
  by_cases huU : u ≤ U
  · exact Or.inl ⟨hu.le, huU⟩
  · exact Or.inr (lt_of_not_ge huU)

private theorem monotoneOn_exp_mul_firstTail_of_pos (τ : ℝ) :
    MonotoneOn (fun q => Real.exp (2 * q) * besselPowerTail 1 τ q) (Ioi 0) := by
  intro q hq u hu hqu
  dsimp only
  rw [besselPowerTail_one, besselPowerTail_one]
  have hh := besselFirstWeightedTail_exp_lower_of_pos hq hqu τ
  calc
    _ = Real.exp (2 * u) *
        (Real.exp (-2 * (u - q)) * besselFirstWeightedTail τ q) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

private theorem endpoint_le_firstTail_of_pos {q : ℝ} (hq : 0 < q) (τ : ℝ) :
    q * besselRadialValue τ q ≤ 2 * besselPowerTail 1 τ q := by
  have hd := (((hasDerivAt_id q).const_mul 2).exp).mul
    (hasDerivAt_besselPowerTail_of_pos hq (by norm_num : (-1 : ℝ) < 1) τ)
  change HasDerivAt (fun u => Real.exp (2 * u) * besselPowerTail 1 τ u) _ q at hd
  have hn := (monotoneOn_exp_mul_firstTail_of_pos τ).derivWithin_nonneg (x := q)
  rw [derivWithin_of_isOpen isOpen_Ioi hq, hd.deriv] at hn
  simp only [Real.rpow_one, id_eq, mul_one] at hn
  have hn' : 0 ≤ Real.exp (2 * q) *
      (2 * besselPowerTail 1 τ q - q * besselRadialValue τ q) := by
    nlinarith only [hn]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hn')

private theorem hasDerivAt_rpow_firstTail_of_pos {u : ℝ} (hu : 0 < u) (p τ : ℝ) :
    HasDerivAt (fun v : ℝ => v ^ (p - 1) * besselPowerTail 1 τ v)
      ((p - 1) * (u ^ (p - 2) * besselPowerTail 1 τ u) -
        u ^ p * besselRadialValue τ u) u := by
  have hr : HasDerivAt (fun v : ℝ => v ^ (p - 1))
      ((p - 1) * u ^ (p - 1 - 1)) u := Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hh := hr.mul (hasDerivAt_besselPowerTail_of_pos hu (by norm_num : (-1 : ℝ) < 1) τ)
  apply hh.congr_deriv
  have hm : u ^ (p - 1) * u = u ^ p := by
    calc
      _ = u ^ (p - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ ((p - 1) + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  rw [Real.rpow_one, show p - 1 - 1 = p - 2 by ring]
  calc
    _ = (p - 1) * (u ^ (p - 2) * besselPowerTail 1 τ u) -
        (u ^ (p - 1) * u) * besselRadialValue τ u := by ring
    _ = _ := by rw [hm]

/-- Higher powers retain a positive first-tail head down to every positive cutoff. -/
theorem firstTail_le_besselPowerTail_of_pos {q p : ℝ} (hq : 0 < q) (hp : 1 < p) (τ : ℝ) :
    q ^ (p - 1) * besselPowerTail 1 τ q ≤ besselPowerTail p τ q := by
  have hA := (integrableOn_rpow_firstTail_of_pos hq
    (by linarith only [hp] : -1 < p - 2) τ).const_mul (p - 1)
  have hB := (integrableOn_besselPowerIntegrand_zero
    (by linarith only [hp] : -1 < p) τ).mono_set (Ioi_subset_Ioi hq.le)
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u hu => hasDerivAt_rpow_firstTail_of_pos (hq.trans_le hu) p τ)
    (hA.sub hB) (tendsto_rpow_mul_besselPowerTail_zero (p - 1) 1 τ)
  rw [integral_sub hA hB, integral_const_mul] at hh
  change (p - 1) * (∫ u in Ioi q, u ^ (p - 2) * besselPowerTail 1 τ u) -
    besselPowerTail p τ q = 0 - q ^ (p - 1) * besselPowerTail 1 τ q at hh
  have hI : 0 ≤ ∫ u in Ioi q, u ^ (p - 2) * besselPowerTail 1 τ u := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    rw [besselPowerTail_one]
    exact mul_nonneg (Real.rpow_nonneg (hq.trans hu).le _)
      (besselFirstWeightedTail_pos_of_pos (hq.trans hu) τ).le
  nlinarith only [hh, mul_nonneg (sub_nonneg.mpr hp.le) hI]

/-- The first-tail payment controls the signed endpoint at every higher power. -/
theorem endpoint_le_besselPowerTail_of_pos {q p : ℝ} (hq : 0 < q) (hp : 1 < p) (τ : ℝ) :
    q ^ p * besselRadialValue τ q ≤ 2 * besselPowerTail p τ q := by
  have hm : q ^ (p - 1) * q = q ^ p := by
    calc
      _ = q ^ (p - 1) * q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ ((p - 1) + 1) := (Real.rpow_add hq _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = q ^ (p - 1) * (q * besselRadialValue τ q) := by rw [← mul_assoc, hm]
    _ ≤ q ^ (p - 1) * (2 * besselPowerTail 1 τ q) :=
      mul_le_mul_of_nonneg_left (endpoint_le_firstTail_of_pos hq τ) (Real.rpow_nonneg hq.le _)
    _ ≤ _ := by linarith only [firstTail_le_besselPowerTail_of_pos hq hp τ]

private theorem hasDerivAt_exp_tail_of_pos {q p : ℝ} (hq : 0 < q) (hp : -1 < p) (τ : ℝ) :
    HasDerivAt (fun u => Real.exp (2 * u) * besselPowerTail p τ u)
      (Real.exp (2 * q) * (2 * besselPowerTail p τ q - q ^ p * besselRadialValue τ q)) q := by
  have hh := (((hasDerivAt_id q).const_mul 2).exp).mul
    (hasDerivAt_besselPowerTail_of_pos hq hp τ)
  apply hh.congr_deriv
  dsimp only [id_eq]
  ring

/-- Exponential transport is uniform over the entire positive radial ray. -/
theorem monotoneOn_exp_mul_besselPowerTail_of_pos {p : ℝ} (hp : 1 < p) (τ : ℝ) :
    MonotoneOn (fun q => Real.exp (2 * q) * besselPowerTail p τ q) (Ioi 0) := by
  have hp0 : -1 < p := by linarith only [hp]
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro q hq
    exact (hasDerivAt_exp_tail_of_pos hq hp0 τ).continuousAt.continuousWithinAt
  · intro q hq
    exact (hasDerivAt_exp_tail_of_pos (show 0 < q from interior_subset hq) hp0 τ).hasDerivWithinAt
  · intro q hq
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
      (endpoint_le_besselPowerTail_of_pos (show 0 < q from interior_subset hq) hp τ))

/-- Every higher weighted tail retains an explicit fraction of its complete Gamma mass. -/
theorem besselPowerTail_completeGamma_lower {q p : ℝ} (hq : 0 < q) (hp : 1 < p) (τ : ℝ) :
    Real.exp (-2 * q) / 4 *
      ‖Complex.Gamma (((p : ℂ) + 1) / 2 + (τ : ℂ) * I)‖ ^ 2 ≤ besselPowerTail p τ q := by
  have he : Tendsto (fun y : ℝ => Real.exp (2 * y)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun y : ℝ => Real.exp (2 * y)) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim := he.mul (tendsto_besselPowerTail_zero (by linarith only [hp] : -1 < p) τ)
  simp only [one_mul] at hlim
  have hup : ∀ᶠ y in 𝓝[>] (0 : ℝ), Real.exp (2 * y) * besselPowerTail p τ y ≤
      Real.exp (2 * q) * besselPowerTail p τ q := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hq).filter_mono nhdsWithin_le_nhds] with y hy hyq
    exact monotoneOn_exp_mul_besselPowerTail_of_pos hp τ hy hq hyq.le
  have hh := mul_le_mul_of_nonneg_left (le_of_tendsto hlim hup) (Real.exp_pos (-2 * q)).le
  have hcancel : Real.exp (-2 * q) * Real.exp (2 * q) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    _ = Real.exp (-2 * q) *
        ((1 / 4 : ℝ) * ‖Complex.Gamma (((p : ℂ) + 1) / 2 + (τ : ℂ) * I)‖ ^ 2) := by ring
    _ ≤ _ := hh
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

/-- The signed first atom retains the upper-power natural Gamma scale at every frequency. -/
theorem besselFirstAtomTailDensity_naturalGamma_lower {q : ℝ} (hq : 3 ≤ q) (τ : ℝ) :
    Real.exp (-2 * q) / 8 * ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      besselFirstAtomTailDensity τ q := by
  have ht := besselPowerTail_completeGamma_lower
    (by linarith only [hq] : 0 < q) (by norm_num : (1 : ℝ) < 7 / 2) τ
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at ht
  have hb := besselFirstAtomTailDensity_ge_half_upperTail hq τ
  linarith only [ht, hb]

#print axioms monotoneOn_exp_mul_besselPowerTail_of_pos
#print axioms besselPowerTail_completeGamma_lower
#print axioms besselFirstAtomTailDensity_naturalGamma_lower

end GaloisForLFunctions.CompletedArithmeticForms
