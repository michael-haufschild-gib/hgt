import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilComplexCore

/-!
# Quantitative coercivity of Suzuki's limiting logarithmic form

Suzuki's small-aperture analysis introduces, on `C_c^∞(-1,1)`, the limiting form

`L(u) = 1/4 ∫∫ |u(x)-u(y)|² / |x-y| - 1/2 ∫ log(1-x²)|u(x)|²`.

The source proves only that its ground energy is positive, by compactness and contradiction.  The
exact kernel yields a constructive strengthening.  Splitting the interval at `±1/2`, the difference
term controls the global mean while the logarithmic killing term controls the two outer halves.  A
weighted mean estimate then gives the explicit universal constant `1/24`.

The final theorem is stated on mathlib's literal complex test-function space
`C_c^∞((-1,1), ℂ)`.  No spectral, zeta-zero, or analytic-continuation hypothesis occurs.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem interval_mean_square_le (u : ℝ → ℝ) (hu : Continuous u)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, u x) ^ 2 ≤ (r - l) * ∫ x in l..r, u x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  have hu2 : Integrable (fun x => u x ^ 2) μ := by
    change IntegrableOn (fun x => u x ^ 2) (Ioc l r) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mp
      ((hu.pow 2).intervalIntegrable l r)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) μ := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ) ^ 2) (Ioc l r) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mp
      (continuous_const.intervalIntegrable l r)
  have h := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := μ) (f := fun _ : ℝ => (1 : ℝ)) (g := u)
      (by fun_prop) (by fun_prop) h1 hu2
  change (∫ x, (1 : ℝ) * u x ∂μ) ^ 2 ≤
    (∫ _ : ℝ, (1 : ℝ) ^ 2 ∂μ) * ∫ x, u x ^ 2 ∂μ at h
  simpa [μ, intervalIntegral.integral_of_le hlr,
    max_eq_left (sub_nonneg.mpr hlr)] using h

private theorem difference_square_inner_integral_eq (u : ℝ → ℝ) (hu : Continuous u)
    (x : ℝ) :
    (∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2) =
      2 * u x ^ 2 + (-2 * (∫ y in (-1 : ℝ)..1, u y)) * u x +
        ∫ y in (-1 : ℝ)..1, u y ^ 2 := by
  have hu2I : IntervalIntegrable (fun y => u y ^ 2) volume (-1 : ℝ) 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => u x ^ 2) volume (-1 : ℝ) 1 :=
    continuous_const.intervalIntegrable _ _
  have hl : IntervalIntegrable (fun y => (-2 * u x) * u y) volume (-1 : ℝ) 1 :=
    (continuous_const.mul hu).intervalIntegrable _ _
  calc
    (∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2) =
        ∫ y in (-1 : ℝ)..1, u x ^ 2 + (-2 * u x) * u y + u y ^ 2 := by
          refine intervalIntegral.integral_congr fun y _ => ?_
          ring
    _ = (∫ y in (-1 : ℝ)..1, u x ^ 2 + (-2 * u x) * u y) +
        ∫ y in (-1 : ℝ)..1, u y ^ 2 := by
          rw [intervalIntegral.integral_add (hc.add hl) hu2I]
    _ = (∫ y in (-1 : ℝ)..1, u x ^ 2) +
          (∫ y in (-1 : ℝ)..1, (-2 * u x) * u y) +
        ∫ y in (-1 : ℝ)..1, u y ^ 2 := by
          rw [intervalIntegral.integral_add hc hl]
    _ = 2 * u x ^ 2 + (-2 * (∫ y in (-1 : ℝ)..1, u y)) * u x +
        ∫ y in (-1 : ℝ)..1, u y ^ 2 := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
          ring

private theorem difference_square_integral_eq (u : ℝ → ℝ) (hu : Continuous u) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2) =
      4 * (∫ x in (-1 : ℝ)..1, u x ^ 2) -
        2 * (∫ x in (-1 : ℝ)..1, u x) ^ 2 := by
  let m : ℝ := ∫ x in (-1 : ℝ)..1, u x
  let E : ℝ := ∫ x in (-1 : ℝ)..1, u x ^ 2
  have h1 : IntervalIntegrable (fun x => 2 * u x ^ 2) volume (-1 : ℝ) 1 :=
    ((hu.pow 2).const_mul 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => (-2 * m) * u x) volume (-1 : ℝ) 1 :=
    (hu.const_mul (-2 * m)).intervalIntegrable _ _
  calc
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2) =
        ∫ x in (-1 : ℝ)..1, 2 * u x ^ 2 + (-2 * m) * u x + E := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          dsimp [m, E]
          exact difference_square_inner_integral_eq u hu x
    _ = (∫ x in (-1 : ℝ)..1, 2 * u x ^ 2) +
          (∫ x in (-1 : ℝ)..1, (-2 * m) * u x) +
          ∫ _x in (-1 : ℝ)..1, E := by
          rw [intervalIntegral.integral_add (h1.add h2)
            (continuous_const.intervalIntegrable _ _),
            intervalIntegral.integral_add h1 h2]
    _ = 4 * (∫ x in (-1 : ℝ)..1, u x ^ 2) -
        2 * (∫ x in (-1 : ℝ)..1, u x) ^ 2 := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const]
          dsimp [m, E]
          ring

private theorem limiting_difference_energy_lower (u : SuzukiRestrictedWeilCore 1) :
    (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1,
      ∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2) ≤
        suzukiFinitePartDifferenceEnergy 1 u := by
  have henergyInt := suzukiFinitePartDifferenceEnergy_intervalIntegrable
    (a := (1 : ℝ)) one_pos u.smooth
  have hinnerLe : ∀ x ∈ Icc (-1 : ℝ) 1,
      (∫ y in (-1 : ℝ)..1, (1 / 2 : ℝ) * (u x - u y) ^ 2) ≤
        ∫ y in (-1 : ℝ)..1, (u x - u y) ^ 2 * |x - y|⁻¹ := by
    intro x hx
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const.mul ((continuous_const.sub u.continuous).pow 2)).intervalIntegrable _ _)
      (henergyInt.1 x hx)
    intro y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · have hdistpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have hdistle : |x - y| ≤ (2 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      have hinv : (1 / 2 : ℝ) ≤ |x - y|⁻¹ := by
        have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hdistpos).2 hdistle
        norm_num at h ⊢
        exact h
      calc
        (1 / 2 : ℝ) * (u x - u y) ^ 2 = (u x - u y) ^ 2 * (1 / 2 : ℝ) := by
          ring
        _ ≤ (u x - u y) ^ 2 * |x - y|⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
  let m : ℝ := ∫ y in (-1 : ℝ)..1, u y
  let E : ℝ := ∫ y in (-1 : ℝ)..1, u y ^ 2
  have hpoly : Continuous (fun x => (1 / 2 : ℝ) *
      (2 * u x ^ 2 + (-2 * m) * u x + E)) := by
    exact continuous_const.mul
      ((((u.continuous.pow 2).const_mul 2).add (u.continuous.const_mul (-2 * m))).add
        continuous_const)
  have hrhsInt : IntervalIntegrable
      (fun x => ∫ y in (-1 : ℝ)..1, (1 / 2 : ℝ) * (u x - u y) ^ 2)
      volume (-1 : ℝ) 1 := by
    refine IntervalIntegrable.congr (f := fun x => (1 / 2 : ℝ) *
      (2 * u x ^ 2 + (-2 * m) * u x + E)) ?_
      (hpoly.intervalIntegrable _ _)
    intro x _
    change (1 / 2 : ℝ) * (2 * u x ^ 2 + (-2 * m) * u x + E) =
      ∫ y in (-1 : ℝ)..1, (1 / 2 : ℝ) * (u x - u y) ^ 2
    rw [intervalIntegral.integral_const_mul]
    dsimp [m, E]
    rw [difference_square_inner_integral_eq u u.continuous x]
  have hmain := intervalIntegral.integral_mono_on
    (by norm_num) hrhsInt henergyInt.2 hinnerLe
  unfold suzukiFinitePartDifferenceEnergy
  simpa only [intervalIntegral.integral_const_mul] using hmain

private theorem limiting_log_potential_outer_lower (u : SuzukiRestrictedWeilCore 1) :
    (1 / 4 : ℝ) *
        ((∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), u x ^ 2) +
          ∫ x in (1 / 2 : ℝ)..1, u x ^ 2) ≤
      -suzukiFinitePartLogPotential 1 u := by
  let p : ℝ → ℝ := fun x => -Real.log (1 - x ^ 2) * u x ^ 2
  have hlogInt := suzukiFinitePartLogPotential_integrable_upper
    (a := (1 : ℝ)) one_pos u.supportRadius_nonneg u.supportRadius_lt_aperture
      u.continuous u.support_subset
  have hpInt : IntervalIntegrable p volume (-1 : ℝ) 1 := by
    refine IntervalIntegrable.congr (f := fun x =>
      -(Real.log (1 ^ 2 - x ^ 2) * u x ^ 2)) ?_ hlogInt.1.neg
    intro x _
    dsimp [p]
    ring
  have hsub_left : uIcc (-1 : ℝ) (-1 / 2 : ℝ) ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ -1 / 2),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hsub_mid : uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ) ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hsub_right : uIcc (1 / 2 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hpLeft := hpInt.mono_set hsub_left
  have hpMid := hpInt.mono_set hsub_mid
  have hpRight := hpInt.mono_set hsub_right
  have hp_nonneg : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x := by
    intro x _
    by_cases hux : u x = 0
    · simp [p, hux]
    · have hxap := u.support_subset_aperture hux
      have hargpos : 0 < 1 - x ^ 2 := by
        have hprod : 0 < (1 - x) * (1 + x) :=
          mul_pos (by linarith [hxap.2]) (by linarith [hxap.1])
        nlinarith
      have hlog := Real.log_le_sub_one_of_pos hargpos
      have hweight : 0 ≤ -Real.log (1 - x ^ 2) := by
        nlinarith [sq_nonneg x]
      exact mul_nonneg hweight (sq_nonneg _)
  have hp_outer : ∀ x ∈ Icc (-1 : ℝ) 1, (1 / 2 : ℝ) ≤ |x| →
      (1 / 4 : ℝ) * u x ^ 2 ≤ p x := by
    intro x _ habs
    by_cases hux : u x = 0
    · simp [p, hux]
    · have hxap := u.support_subset_aperture hux
      have hargpos : 0 < 1 - x ^ 2 := by
        have hprod : 0 < (1 - x) * (1 + x) :=
          mul_pos (by linarith [hxap.2]) (by linarith [hxap.1])
        nlinarith
      have hlog := Real.log_le_sub_one_of_pos hargpos
      have hx2 : (1 / 4 : ℝ) ≤ x ^ 2 := by
        nlinarith [sq_abs x]
      have hweight : (1 / 4 : ℝ) ≤ -Real.log (1 - x ^ 2) := by
        nlinarith
      dsimp [p]
      exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
  have hleft := intervalIntegral.integral_mono_on
    (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    ((continuous_const.mul (u.continuous.pow 2)).intervalIntegrable _ _) hpLeft
    (fun x hx => hp_outer x ⟨hx.1, by linarith [hx.2]⟩ (by
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]))
  have hright := intervalIntegral.integral_mono_on
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
    ((continuous_const.mul (u.continuous.pow 2)).intervalIntegrable _ _) hpRight
    (fun x hx => hp_outer x ⟨by linarith [hx.1], hx.2⟩ (by
      rw [abs_of_nonneg (by linarith [hx.1])]
      exact hx.1))
  change (∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), (1 / 4 : ℝ) * u x ^ 2) ≤
    ∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), p x at hleft
  change (∫ x in (1 / 2 : ℝ)..1, (1 / 4 : ℝ) * u x ^ 2) ≤
    ∫ x in (1 / 2 : ℝ)..1, p x at hright
  rw [intervalIntegral.integral_const_mul] at hleft hright
  have hmid : 0 ≤ ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), p x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => hp_nonneg x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals hpLeft hpMid
  have hpLeftMid : IntervalIntegrable p volume (-1 : ℝ) (1 / 2 : ℝ) :=
    hpLeft.trans hpMid
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals hpLeftMid hpRight
  have htotal : (1 / 4 : ℝ) *
      ((∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), u x ^ 2) +
        ∫ x in (1 / 2 : ℝ)..1, u x ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, p x := by
    rw [← hadj2, ← hadj1]
    linarith
  calc
    (1 / 4 : ℝ) *
        ((∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), u x ^ 2) +
          ∫ x in (1 / 2 : ℝ)..1, u x ^ 2) ≤
        ∫ x in (-1 : ℝ)..1, p x := htotal
    _ = -suzukiFinitePartLogPotential 1 u := by
      unfold suzukiFinitePartLogPotential
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      dsimp [p]
      ring

/-- Explicit coercivity of Suzuki's limiting form on the literal real smooth core. -/
theorem suzukiLimitingLogForm_real_coercive (u : SuzukiRestrictedWeilCore 1) :
    (1 / 24 : ℝ) * (∫ x in (-1 : ℝ)..1, u x ^ 2) ≤
      suzukiFinitePartEnergy 1 u := by
  let ml : ℝ := ∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), u x
  let mi : ℝ := ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), u x
  let mr : ℝ := ∫ x in (1 / 2 : ℝ)..1, u x
  let El : ℝ := ∫ x in (-1 : ℝ)..(-1 / 2 : ℝ), u x ^ 2
  let Ei : ℝ := ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), u x ^ 2
  let Er : ℝ := ∫ x in (1 / 2 : ℝ)..1, u x ^ 2
  let m : ℝ := ∫ x in (-1 : ℝ)..1, u x
  let E : ℝ := ∫ x in (-1 : ℝ)..1, u x ^ 2
  have huI : ∀ l r : ℝ, IntervalIntegrable u volume l r :=
    fun l r => u.continuous.intervalIntegrable l r
  have hu2I : ∀ l r : ℝ, IntervalIntegrable (fun x => u x ^ 2) volume l r :=
    fun l r => (u.continuous.pow 2).intervalIntegrable l r
  have hmAdj1 := intervalIntegral.integral_add_adjacent_intervals
    (huI (-1) (-1 / 2)) (huI (-1 / 2) (1 / 2))
  have hmAdj2 := intervalIntegral.integral_add_adjacent_intervals
    (huI (-1) (1 / 2)) (huI (1 / 2) 1)
  have hEAdj1 := intervalIntegral.integral_add_adjacent_intervals
    (hu2I (-1) (-1 / 2)) (hu2I (-1 / 2) (1 / 2))
  have hEAdj2 := intervalIntegral.integral_add_adjacent_intervals
    (hu2I (-1) (1 / 2)) (hu2I (1 / 2) 1)
  have hmDecomp : m = mi + (ml + mr) := by
    dsimp [m, mi, ml, mr]
    linarith
  have hEDecomp : E = Ei + (El + Er) := by
    dsimp [E, Ei, El, Er]
    linarith
  have hmi : mi ^ 2 ≤ Ei := by
    have h := interval_mean_square_le u u.continuous
      (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    norm_num at h
    dsimp [mi, Ei]
    convert h using 1 <;> norm_num
  have hml : ml ^ 2 ≤ (1 / 2 : ℝ) * El := by
    have h := interval_mean_square_le u u.continuous
      (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    norm_num at h
    dsimp [ml, El]
    convert h using 1 <;> norm_num
  have hmr : mr ^ 2 ≤ (1 / 2 : ℝ) * Er := by
    have h := interval_mean_square_le u u.continuous
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    norm_num at h
    dsimp [mr, Er]
    convert h using 1
  have hmo : (ml + mr) ^ 2 ≤ El + Er := by
    nlinarith [sq_nonneg (ml - mr)]
  have hmBound : m ^ 2 ≤ (7 / 4 : ℝ) * Ei + (7 / 3 : ℝ) * (El + Er) := by
    have hweighted : (mi + (ml + mr)) ^ 2 ≤
        (7 / 4 : ℝ) * mi ^ 2 + (7 / 3 : ℝ) * (ml + mr) ^ 2 := by
      nlinarith [sq_nonneg (3 * mi - 4 * (ml + mr))]
    rw [hmDecomp]
    nlinarith
  have hdiff := limiting_difference_energy_lower u
  have hdiffId := difference_square_integral_eq u u.continuous
  have hD : (1 / 2 : ℝ) * (4 * E - 2 * m ^ 2) ≤
      suzukiFinitePartDifferenceEnergy 1 u := by
    dsimp [E, m]
    rw [← hdiffId]
    exact hdiff
  have hP := limiting_log_potential_outer_lower u
  have hP' : (1 / 4 : ℝ) * (El + Er) ≤
      -suzukiFinitePartLogPotential 1 u := by
    simpa [El, Er] using hP
  have hEi : 0 ≤ Ei := intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => sq_nonneg _)
  have hEl : 0 ≤ El := intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => sq_nonneg _)
  have hEr : 0 ≤ Er := intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => sq_nonneg _)
  unfold suzukiFinitePartEnergy
  dsimp [E] at hEDecomp ⊢
  nlinarith

def suzukiUnitAperture : RHTower.SuzukiPositiveAperture := ⟨1, one_pos⟩

/-- Suzuki's limiting logarithmic form on the literal complex test-function space. -/
def suzukiLimitingLogForm (u : SuzukiRestrictedWeilComplexTest 1) : ℝ :=
  suzukiFinitePartEnergy 1
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart) +
    suzukiFinitePartEnergy 1
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart)

/-- Quantitative strengthening of Suzuki's positive-ground-energy lemma:
`L(u) ≥ ‖u‖²₂ / 24` on `C_c^∞((-1,1), ℂ)`. -/
theorem suzukiLimitingLogForm_coercive (u : SuzukiRestrictedWeilComplexTest 1) :
    (1 / 24 : ℝ) * suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ≤
      suzukiLimitingLogForm u := by
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  have hr := suzukiLimitingLogForm_real_coercive ur
  have hi := suzukiLimitingLogForm_real_coercive ui
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq]
  unfold suzukiLimitingLogForm
  change (1 / 24 : ℝ) *
      ((∫ x in (-1 : ℝ)..1, ur x ^ 2) + ∫ x in (-1 : ℝ)..1, ui x ^ 2) ≤
    suzukiFinitePartEnergy 1 ur + suzukiFinitePartEnergy 1 ui
  linarith

end GaloisForLFunctions.RHTower
