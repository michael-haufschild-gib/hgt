import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Unbounded theta-source support forces growth beyond every square-root exponential

Every positive spatial window has positive full-source mass.  Its normalized mass bounds all
raw even moments from below.  A factorial estimate gives an exponential lower bound on a
quadratic clock grid, and source monotonicity extends that bound to every sufficiently large
clock.  Moving the fixed spatial window makes the square-root exponential rate arbitrarily large.
-/

open scoped Topology

open MeasureTheory Set Filter

namespace RHTower
noncomputable section

/-- The exact normalized full-source mass of one unit spatial window, including the raw factor two. -/
def liEvenCrossActualClockSpatialWindowMass (X : ℝ) : ℝ :=
  2 * (∫ x : ℝ in Icc X (X+1), thetaCuspFullSource x) /
    thetaCuspRawEvenMoment 0

/-- A positive spatial window lies in the source half-line. -/
private theorem spatialWindow_subset {X : ℝ} (hX : 0 < X) :
    Icc X (X+1) ⊆ Ioi (0 : ℝ) := fun _ hx => hX.trans_le hx.1

/-- The full theta source is integrable on each positive spatial window. -/
private theorem integrableOn_spatialSourceWindow {X : ℝ} (hX : 0 < X) :
    IntegrableOn thetaCuspFullSource (Icc X (X+1)) := by
  have hk : IntegrableOn thetaCuspFullSource (Ioi (0 : ℝ)) := by
    simpa using integrableOn_thetaCuspRawMoment 0
  exact hk.mono_set (spatialWindow_subset hX)

/-- Every positive spatial window has strictly positive normalized full-source mass. -/
theorem liEvenCrossActualClockSpatialWindowMass_pos {X : ℝ} (hX : 0 < X) :
    0 < liEvenCrossActualClockSpatialWindowMass X := by
  have hk := integrableOn_spatialSourceWindow hX
  have hnn : 0 ≤ᵐ[volume.restrict (Icc X (X+1))] thetaCuspFullSource := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (thetaCuspFullSource_pos_of_pos (spatialWindow_subset hX hx)).le
  have hsupp : Function.support thetaCuspFullSource ∩ Icc X (X+1) = Icc X (X+1) := by
    apply inter_eq_right.mpr
    intro x hx
    exact (thetaCuspFullSource_pos_of_pos (spatialWindow_subset hX hx)).ne'
  have hm : 0 < ∫ x : ℝ in Icc X (X+1), thetaCuspFullSource x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnn hk).2
    rw [hsupp, Real.volume_Icc]
    norm_num
  exact div_pos (mul_pos (by norm_num) hm) thetaCuspRawEvenMoment_zero_pos

/-- One fixed spatial window bounds every normalized raw even moment from below. -/
theorem liEvenCrossActualClockNormalizedMoment_ge_spatialWindow {X : ℝ}
    (hX : 0 < X) (j : ℕ) :
    liEvenCrossActualClockSpatialWindowMass X * X^(2*j) ≤
      thetaCuspNormalizedEvenMoment j := by
  have hk := integrableOn_spatialSourceWindow hX
  have hj := integrableOn_thetaCuspRawMoment (2*j)
  have hji := hj.mono_set (spatialWindow_subset hX)
  have hc := hk.const_mul (X^(2*j))
  have hlocal : X^(2*j) * (∫ x : ℝ in Icc X (X+1), thetaCuspFullSource x) ≤
      ∫ x : ℝ in Icc X (X+1), x^(2*j)*thetaCuspFullSource x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hc hji measurableSet_Icc
    intro x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX.le hx.1 _)
      (thetaCuspFullSource_pos_of_pos (spatialWindow_subset hX hx)).le
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => x^(2*j)*thetaCuspFullSource x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le
  have hwhole : (∫ x : ℝ in Icc X (X+1), x^(2*j)*thetaCuspFullSource x) ≤
      ∫ x : ℝ in Ioi 0, x^(2*j)*thetaCuspFullSource x :=
    setIntegral_mono_set hj hnn (Eventually.of_forall (spatialWindow_subset hX))
  calc
    liEvenCrossActualClockSpatialWindowMass X * X^(2*j) =
        2 * (X^(2*j) * ∫ x : ℝ in Icc X (X+1), thetaCuspFullSource x) /
          thetaCuspRawEvenMoment 0 := by unfold liEvenCrossActualClockSpatialWindowMass; ring
    _ ≤ 2 * (∫ x : ℝ in Ioi 0, x^(2*j)*thetaCuspFullSource x) /
          thetaCuspRawEvenMoment 0 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlocal.trans hwhole) (by norm_num))
        thetaCuspRawEvenMoment_zero_pos.le
    _ = thetaCuspNormalizedEvenMoment j := rfl

/-- The quadratic clock grid cancels the elementary factorial power envelope exactly. -/
private theorem spatialGrid_power_identity {X : ℝ} (hX : X ≠ 0) (j : ℕ)
    (hj : (j : ℝ) ≠ 0) :
    X^(2*j) * (16*(j : ℝ)^2/X)^(2*j) /
      ((2*(j : ℝ))^(2*j))^2 = (16 : ℝ)^j := by
  have hden : ((2*(j : ℝ))^(2*j))^2 = ((2*(j : ℝ))^2)^(2*j) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [← mul_pow, hden, ← div_pow]
  have hbase : X*(16*(j : ℝ)^2/X)/(2*(j : ℝ))^2 = 4 := by
    field_simp
    ring
  rw [hbase, pow_mul]
  norm_num

/-- The complete positive Borel kernel dominates the spatial exponential grid term. -/
theorem liEvenCrossActualClockBorelKernel_ge_spatialGrid {X : ℝ} (hX : 0 < X)
    {j : ℕ} (hj : 1 ≤ j) :
    liEvenCrossActualClockSpatialWindowMass X * (16 : ℝ)^j ≤
      liEvenCrossActualClockBorelKernel (16*(j : ℝ)^2/X) := by
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hfact : ((2*j).factorial : ℝ) ≤ (2*(j : ℝ))^(2*j) := by
    exact_mod_cast Nat.factorial_le_pow (2*j)
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2*j).factorial : ℝ)) hfact 2
  have hmass := (liEvenCrossActualClockSpatialWindowMass_pos hX).le
  have hmoment := liEvenCrossActualClockNormalizedMoment_ge_spatialWindow hX j
  calc
    liEvenCrossActualClockSpatialWindowMass X * (16 : ℝ)^j =
        liEvenCrossActualClockSpatialWindowMass X *
          (X^(2*j)*(16*(j : ℝ)^2/X)^(2*j) / ((2*(j : ℝ))^(2*j))^2) := by
      rw [spatialGrid_power_identity hX.ne' j hjpos.ne']
    _ = (liEvenCrossActualClockSpatialWindowMass X * X^(2*j) *
          (16*(j : ℝ)^2/X)^(2*j)) / ((2*(j : ℝ))^(2*j))^2 := by ring
    _ ≤ (liEvenCrossActualClockSpatialWindowMass X * X^(2*j) *
          (16*(j : ℝ)^2/X)^(2*j)) / ((2*j).factorial : ℝ)^2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ ≤ (thetaCuspNormalizedEvenMoment j * (16*(j : ℝ)^2/X)^(2*j)) /
          ((2*j).factorial : ℝ)^2 := by gcongr
    _ ≤ liEvenCrossActualClockBorelKernel (16*(j : ℝ)^2/X) :=
      liEvenCrossActualClockBorelTerm_le_kernel _ _


/-- Monotonicity transfers the grid lower bound to every clock beyond its first positive grid point. -/
theorem liEvenCrossActualClockBorelKernel_ge_spatialExp {X t : ℝ} (hX : 0 < X)
    (ht : 16/X ≤ t) :
    liEvenCrossActualClockSpatialWindowMass X / 16 *
      Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t) ≤
        liEvenCrossActualClockBorelKernel t := by
  have ht0 : 0 ≤ t := (div_pos (by norm_num) hX).le.trans ht
  have hXt : (16 : ℝ) ≤ X*t := by
    have hh := (div_le_iff₀ hX).mp ht
    nlinarith
  have hroot : 4 ≤ Real.sqrt (X*t) := by
    have hh := Real.sqrt_le_sqrt hXt
    norm_num at hh
    exact hh
  let u := Real.sqrt (X*t)/4
  let n : ℕ := Nat.floor u
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : 1 ≤ u := by dsimp [u]; linarith
  have hn : 1 ≤ n := (Nat.one_le_floor_iff u).mpr hu1
  have hnu : (n : ℝ) ≤ u := Nat.floor_le hu0
  have hun : u < (n : ℝ)+1 := Nat.lt_floor_add_one u
  have hsqrt : Real.sqrt (X*t)^2 = X*t := Real.sq_sqrt (mul_nonneg hX.le ht0)
  have hnsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)) hnu 2
  have hgrid : 16*(n : ℝ)^2/X ≤ t := by
    apply (div_le_iff₀ hX).mpr
    dsimp [u] at hnsq
    nlinarith
  have hkernel : liEvenCrossActualClockSpatialWindowMass X * (16 : ℝ)^n ≤
      liEvenCrossActualClockBorelKernel t :=
    (liEvenCrossActualClockBorelKernel_ge_spatialGrid hX hn).trans
      (liEvenCrossActualClockBorelKernel_mono (by positivity) hgrid)
  have huform : u = Real.sqrt X / 4 * Real.sqrt t := by
    dsimp [u]
    rw [Real.sqrt_mul hX.le]
    ring
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have harg : (Real.log 16 * Real.sqrt X / 4) * Real.sqrt t - Real.log 16 ≤
      (n : ℝ) * Real.log 16 := by
    have hh := mul_lt_mul_of_pos_right hun hlog
    rw [huform] at hh
    nlinarith
  have hexp : Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t - Real.log 16) ≤
      (16 : ℝ)^n := by
    calc
      _ ≤ Real.exp ((n : ℝ)*Real.log 16) := Real.exp_le_exp.mpr harg
      _ = (16 : ℝ)^n := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hexp_eq : Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t - Real.log 16) =
      Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t) / 16 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  calc
    liEvenCrossActualClockSpatialWindowMass X / 16 *
        Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t) =
        liEvenCrossActualClockSpatialWindowMass X *
          Real.exp ((Real.log 16 * Real.sqrt X / 4) * Real.sqrt t - Real.log 16) := by
      rw [hexp_eq]
      ring
    _ ≤ liEvenCrossActualClockSpatialWindowMass X * (16 : ℝ)^n :=
      mul_le_mul_of_nonneg_left hexp (liEvenCrossActualClockSpatialWindowMass_pos hX).le
    _ ≤ liEvenCrossActualClockBorelKernel t := hkernel

/-- The actual Borel kernel grows beyond every fixed square-root exponential scale. -/
theorem liEvenCrossActualClockBorelKernel_mul_exp_neg_sqrt_tendsto_atTop (R : ℝ) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockBorelKernel t *
      Real.exp (-R * Real.sqrt t)) atTop atTop := by
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  let Y := 4*(|R|+1)/Real.log 16
  let X := Y^2
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hcoef : Real.log 16 * Real.sqrt X / 4 = |R|+1 := by
    dsimp [X]
    rw [Real.sqrt_sq hY.le]
    dsimp [Y]
    field_simp
  have hgamma : 0 < Real.log 16 * Real.sqrt X / 4 - R := by
    rw [hcoef]
    linarith [le_abs_self R]
  have hlower : Tendsto (fun t : ℝ => liEvenCrossActualClockSpatialWindowMass X / 16 *
      Real.exp ((Real.log 16 * Real.sqrt X / 4 - R)*Real.sqrt t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp
      (Real.tendsto_sqrt_atTop.const_mul_atTop hgamma)).const_mul_atTop
        (div_pos (liEvenCrossActualClockSpatialWindowMass_pos hX) (by norm_num))
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [eventually_ge_atTop (16/X)] with t ht
  calc
    liEvenCrossActualClockSpatialWindowMass X / 16 *
        Real.exp ((Real.log 16 * Real.sqrt X / 4 - R)*Real.sqrt t) =
        (liEvenCrossActualClockSpatialWindowMass X / 16 *
          Real.exp ((Real.log 16 * Real.sqrt X / 4)*Real.sqrt t)) *
          Real.exp (-R*Real.sqrt t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ liEvenCrossActualClockBorelKernel t * Real.exp (-R*Real.sqrt t) :=
      mul_le_mul_of_nonneg_right (liEvenCrossActualClockBorelKernel_ge_spatialExp hX ht)
        (Real.exp_pos _).le

/-- The ratio to every fixed square-root exponential tends to infinity. -/
theorem liEvenCrossActualClockBorelKernel_div_exp_sqrt_tendsto_atTop (R : ℝ) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockBorelKernel t /
      Real.exp (R*Real.sqrt t)) atTop atTop := by
  convert liEvenCrossActualClockBorelKernel_mul_exp_neg_sqrt_tendsto_atTop R using 1
  funext t
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

end
end RHTower
