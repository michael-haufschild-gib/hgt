import GaloisForLFunctions.ArtinMertens.LatticePointsInADomainWithLipschitzBoundary
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Polynomial asymptotics for lattice-ball counts

Scaling identifies points in a growing ball with points of a shrinking lattice
in the unit ball. The covolume counting theorem gives the main term. Fixed
integer shifts preserve that term, and floor bounds extend nonnegative
monotone counting asymptotics from integer to real radii.
-/

open MeasureTheory Metric Set Bornology Module Filter
open scoped Pointwise Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry.LatticeBallCounting
/-- Fixed shifts of the numerator and denominator preserve a polynomially normalized limit. -/
theorem tendsto_shift_div_pow {u : ℕ → ℝ} {d : ℕ} {c : ℝ}
    (hlim : Tendsto (fun n : ℕ => u n / (n : ℝ)^d) atTop (𝓝 c)) (a b : ℕ) :
    Tendsto (fun n : ℕ => u (n + a) / (n + b : ℝ)^d) atTop (𝓝 c) := by
  have hc := (tendsto_add_atTop_iff_nat a).mpr hlim
  have hr : Tendsto (fun n : ℕ => ((n + a : ℝ) / (n + b : ℝ))^d)
      atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_add_mul_div_add_mul_atTop_nhds (a : ℝ) (b : ℝ) 1
      (d := 1) one_ne_zero).pow d
    simpa only [one_mul, add_comm (a : ℝ), add_comm (b : ℝ), div_one, one_pow] using h
  have h := hc.mul hr
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have ha : (n + a : ℝ) ≠ 0 := by positivity
  have hb : (n + b : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_add]
  rw [div_pow]
  field_simp [ha, hb]

/-- Monotonicity extends a polynomial counting asymptotic from integer to real radii. -/
theorem tendsto_real_div_pow_of_nat {F : ℝ → ℝ} {d : ℕ} {c : ℝ}
    (hmono : Monotone F) (hpos : ∀ r, 0 ≤ F r)
    (hlim : Tendsto (fun n : ℕ => F n / (n : ℝ)^d) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ => F r / r^d) atTop (𝓝 c) := by
  have hfloor : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop :=
    tendsto_atTop.mpr fun k => (eventually_ge_atTop (k : ℝ)).mono fun _ hr => Nat.le_floor hr
  have hlo := (tendsto_shift_div_pow hlim 0 1).comp hfloor
  have hhi := (tendsto_shift_div_pow hlim 1 0).comp hfloor
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_add, add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hnr : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0.le
    have hrn : r ≤ (⌊r⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one r).le
    exact (div_le_div_of_nonneg_left (hpos _) (pow_pos hr0 _)
      (pow_le_pow_left₀ hr0.le hrn d)).trans
      (div_le_div_of_nonneg_right (hmono hnr) (pow_nonneg hr0.le _))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hnr : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0.le
    have hrn : r ≤ (⌊r⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one r).le
    have hn : (0 : ℝ) < ⌊r⌋₊ := by
      exact_mod_cast (show 0 < ⌊r⌋₊ from lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor (by simpa only [Nat.cast_one] using hr)))
    exact (div_le_div_of_nonneg_right (hmono hrn) (pow_nonneg hr0.le _)).trans
      (div_le_div_of_nonneg_left (hpos _) (pow_pos hn _)
        (pow_le_pow_left₀ hn.le hnr d))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Number of lattice points in an open ball centered at zero. -/
def ballCount (r : ℝ) : ℕ := (ball (0 : E) r ∩ (L : Set E)).ncard

theorem unitBall_frontier_null : volume (frontier (ball (0 : E) 1)) = 0 := by
  apply measure_mono_null frontier_ball_subset_sphere
  exact volume.addHaar_sphere_of_ne_zero 0 (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [DiscreteTopology L] [IsZLattice ℝ L] in
theorem ballCount_scaled {r : ℝ} (hr : 0 < r) :
    ballCount L r = Nat.card (ball (0 : E) 1 ∩ r⁻¹ • (L : Set E) : Set E) := by
  have hscale : r • (ball (0 : E) 1 ∩ r⁻¹ • (L : Set E)) =
      ball (0 : E) r ∩ (L : Set E) := by
    rw [Set.smul_set_inter₀ hr.ne', _root_.smul_ball hr.ne', smul_inv_smul₀ hr.ne']
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have h := Set.natCard_smul_set (Units.mk0 r hr.ne')
    (ball (0 : E) 1 ∩ r⁻¹ • (L : Set E))
  change Nat.card (r • (ball (0 : E) 1 ∩ r⁻¹ • (L : Set E)) : Set E) = _ at h
  rw [hscale] at h
  simpa [ballCount] using h

/-- The leading lattice-point count is unit-ball volume divided by covolume. -/
theorem tendsto_ballCount :
    Tendsto (fun n : ℕ => (ballCount L n : ℝ) / (n : ℝ)^finrank ℝ E) atTop
      (𝓝 (volume.real (ball (0 : E) 1) / ZLattice.covolume L)) := by
  apply Filter.Tendsto.congr' _
    (ZLattice.covolume.tendsto_card_div_pow' L isBounded_ball measurableSet_ball
      (unitBall_frontier_null (E := E)))
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [ballCount_scaled L (Nat.cast_pos.mpr hn)]

theorem tendsto_ballCount_shift (a b : ℕ) :
    Tendsto (fun n : ℕ => (ballCount L (n + a) : ℝ) / (n + b : ℝ)^finrank ℝ E) atTop
      (𝓝 (volume.real (ball (0 : E) 1) / ZLattice.covolume L)) := by
  simpa only [Nat.cast_add] using tendsto_shift_div_pow (tendsto_ballCount L) a b

#print axioms tendsto_ballCount_shift
#print axioms tendsto_real_div_pow_of_nat
end GaloisForLFunctions.HTGeometry.LatticeBallCounting

