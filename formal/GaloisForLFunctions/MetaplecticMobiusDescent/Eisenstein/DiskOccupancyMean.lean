import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspPeriodLattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Mean disk occupancy from cubic period unfolding

The exact lattice-point count is the periodization of a disk indicator.
Unfolding over the actual cubic cusp domain computes its mean from disk
area. Consequently any threshold above the area average excludes at
least one centre, without enumerating any lattice points.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

open Set Metric MeasureTheory CubicEisenstein
open scoped ENNReal

/-- The disk indicator whose periodization counts the unscaled Eisenstein lattice. -/
def diskIndicator (r : ℝ) : ℂ → ℝ≥0∞ := (closedBall 0 (3 * r)).indicator (fun _ => 1)

private theorem mem_scaled_disk_iff (z : ℂ) (r : ℝ) (n : O) :
    z + 3 * ringComplex n ∈ closedBall 0 (3 * r) ↔ n ∈ points (-z / 3) r := by
  rw [mem_points, mem_closedBall, dist_zero_right, dist_eq_norm]
  have heq : z + 3 * ringComplex n = -(3 : ℂ) * (-z / 3 - ringComplex n) := by ring
  rw [heq, norm_mul, norm_neg, show ‖(3 : ℂ)‖ = 3 from Complex.norm_natCast 3]
  constructor <;> intro h <;> linarith only [h]

/-- Periodization of one disk indicator is exactly the integer occupancy count. -/
theorem tsum_diskIndicator (z : ℂ) (r : ℝ) :
    (∑' n : O, diskIndicator r (z + 3 * ringComplex n)) = (points (-z / 3) r).card := by
  classical
  rw [tsum_eq_sum (s := points (-z / 3) r) (fun n hn =>
    indicator_of_notMem (fun h => hn ((mem_scaled_disk_iff z r n).mp h)) (fun _ => 1))]
  calc
    ∑ n ∈ points (-z / 3) r, diskIndicator r (z + 3 * ringComplex n)
        = ∑ _n ∈ points (-z / 3) r, (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact indicator_of_mem ((mem_scaled_disk_iff z r n).mpr hn) (fun _ => 1)
    _ = (points (-z / 3) r).card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The exact occupancy integral is the area of the scaled disk. -/
theorem lintegral_occupancy (r : ℝ) :
    (∫⁻ z in periodDomain, ((points (-z / 3) r).card : ℝ≥0∞)) =
      volume (closedBall (0 : ℂ) (3 * r)) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hmeas : Measurable (diskIndicator r) :=
    measurable_const.indicator isClosed_closedBall.measurableSet
  calc
    (∫⁻ z in periodDomain, ((points (-z / 3) r).card : ℝ≥0∞))
        = ∫⁻ z in periodDomain, ∑' n : O, diskIndicator r (z + 3 * ringComplex n) := by
          apply lintegral_congr
          intro z
          exact (tsum_diskIndicator z r).symm
    _ = ∑' n : O, ∫⁻ z in periodDomain, diskIndicator r (z + 3 * ringComplex n) :=
      lintegral_tsum (fun n => (hmeas.comp (continuous_id.add continuous_const).measurable).aemeasurable)
    _ = ∫⁻ z : ℂ, diskIndicator r z := (lintegral_eq_period_lintegrals (diskIndicator r)).symm
    _ = volume (closedBall (0 : ℂ) (3 * r)) := by
      rw [diskIndicator, lintegral_indicator isClosed_closedBall.measurableSet]
      simp only [lintegral_one, Measure.restrict_apply_univ]

/-- A uniform occupancy lower bound cannot exceed disk area divided by lattice covolume. -/
theorem uniform_occupancy_area_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hk : ∀ z : ℂ, k ≤ (points z r).card) :
    (k : ℝ) * (Real.sqrt 3 / 2) ≤ Real.pi * r ^ 2 := by
  have hle : (∫⁻ _z in periodDomain, (k : ℝ≥0∞)) ≤
      ∫⁻ z in periodDomain, ((points (-z / 3) r).card : ℝ≥0∞) :=
    lintegral_mono (fun z => by exact_mod_cast hk (-z / 3))
  rw [lintegral_occupancy, lintegral_const, Measure.restrict_apply_univ,
    periodDomain_volume, Complex.volume_closedBall] at hle
  have hleft : (k : ℝ≥0∞) * ENNReal.ofReal (9 * Real.sqrt 3 / 2) =
      ENNReal.ofReal ((k : ℝ) * (9 * Real.sqrt 3 / 2)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
  have hright : ENNReal.ofReal (3 * r) ^ 2 * (NNReal.pi : ℝ≥0∞) =
      ENNReal.ofReal (Real.pi * (3 * r) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity), mul_comm, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul Real.pi_pos.le]
  rw [hleft, hright] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  nlinarith only [hreal]

/-- Above the area average, a low-occupancy centre necessarily exists. -/
theorem exists_low_occupancy_of_area_lt {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (harea : Real.pi * r ^ 2 < (k : ℝ) * (Real.sqrt 3 / 2)) :
    ∃ z : ℂ, (points z r).card < k := by
  by_contra h
  have hk : ∀ z : ℂ, k ≤ (points z r).card :=
    fun z => Nat.le_of_not_gt (fun hz => h ⟨z, hz⟩)
  exact (not_le_of_gt harea) (uniform_occupancy_area_le hr k hk)

/-- The circumscribed regular hexagon has strictly greater area than the unit disk. -/
private theorem pi_lt_two_sqrt_three : Real.pi < 2 * Real.sqrt 3 := by
  have ht := Real.lt_tan (show 0 < Real.pi / 6 by positivity)
    (show Real.pi / 6 < Real.pi / 2 by linarith only [Real.pi_pos])
  rw [Real.tan_pi_div_six] at ht
  have hs : 0 < Real.sqrt 3 := by positivity
  have hh := (lt_div_iff₀ hs).mp ht
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)
  by_contra h
  have hle : 2 * Real.sqrt 3 ≤ Real.pi := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_right hle hs.le
  nlinarith only [hh, hsq, hm]

/-- At the packing-critical radius, some disk contains strictly fewer than `k` points. -/
theorem exists_low_occupancy_critical (k : ℕ) (hk : 0 < k) :
    ∃ z : ℂ, (points z (Real.sqrt k / 2)).card < k := by
  apply exists_low_occupancy_of_area_lt (by positivity) k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm := mul_lt_mul_of_pos_right pi_lt_two_sqrt_three hkR
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  nlinarith only [hm]

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.lintegral_occupancy
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.exists_low_occupancy_of_area_lt
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.exists_low_occupancy_critical
