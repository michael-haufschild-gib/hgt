import GaloisForLFunctions.TransThresholdPairCorrelation.IntegerTriangleInterpolation
import GaloisForLFunctions.TransThresholdPairCorrelation.TotientGridPairLaw
import GaloisForLFunctions.TransThresholdPairCorrelation.FormFactorThresholdAndShiftInequality

/-!
# Form factor of the totient grid mixture

Triangle interpolation of the nonzero Fourier coefficients is continuous,
nonnegative, and even. The totient divisor identity gives the exact linear
ramp on the unit interval. A finite mixture of periodized triangles supplies
its Fourier representation.
-/

open Real Finset MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Remove the constant Fourier coefficient before interpolating the grid law. -/
def nonzeroTotientGridCoefficient (L : ℕ) (k : ℤ) : ℝ :=
  if k = 0 then 0 else totientGridCoefficient L k.natAbs

/-- Periodized triangle belonging to a grid of order `m` in a period of length `L`. -/
def gridPeriodicTriangle (L m : ℕ) (α : ℝ) : ℝ :=
  (L : ℝ) * ∑' j : ℤ, triangleFn 1 ((L : ℝ) * α + (m : ℝ) * j)

/-- Continuous interpolation of the totient mixture's nonzero Fourier coefficients. -/
def totientGridFormFactor (L : ℕ) (α : ℝ) : ℝ :=
  (L : ℝ) * integerHatInterpolation (nonzeroTotientGridCoefficient L) ((L : ℝ) * α)

theorem nonzeroTotientGridCoefficient_nonneg {L : ℕ} (hL : 1 ≤ L) (k : ℤ) :
    0 ≤ nonzeroTotientGridCoefficient L k := by
  unfold nonzeroTotientGridCoefficient
  split_ifs
  · exact le_rfl
  · exact totientGridCoefficient_nonneg hL _

theorem totientGridCoefficient_le_one {L : ℕ} (hL : 1 ≤ L) (k : ℕ) :
    totientGridCoefficient L k ≤ 1 := by
  have hs : (∑ m ∈ Finset.Icc 1 L, if m ∣ k then totientGridWeight L m else 0) ≤
      ∑ m ∈ Finset.Icc 1 L, totientGridWeight L m := by
    apply sum_le_sum
    intro m hm
    split_ifs
    · exact le_rfl
    · exact totientGridWeight_nonneg L m
  have hr : (if L + 1 ∣ k then totientGridRemainder L else 0) ≤ totientGridRemainder L := by
    split_ifs
    · exact le_rfl
    · exact totientGridRemainder_nonneg hL
  unfold totientGridCoefficient totientGridRemainder
  unfold totientGridRemainder at hr
  linarith only [hs, hr]

theorem nonzeroTotientGridCoefficient_le_one {L : ℕ} (hL : 1 ≤ L) (k : ℤ) :
    nonzeroTotientGridCoefficient L k ≤ 1 := by
  unfold nonzeroTotientGridCoefficient
  split_ifs
  · exact zero_le_one
  · exact totientGridCoefficient_le_one hL _

theorem nonzeroTotientGridCoefficient_neg (L : ℕ) (k : ℤ) :
    nonzeroTotientGridCoefficient L (-k) = nonzeroTotientGridCoefficient L k := by
  simp only [nonzeroTotientGridCoefficient, neg_eq_zero, Int.natAbs_neg]

theorem nonzeroTotientGridCoefficient_eq_ramp {L : ℕ} {k : ℤ}
    (hk0 : 0 ≤ k) (hkL : k ≤ (L : ℤ)) :
    nonzeroTotientGridCoefficient L k = (k : ℝ) / (L : ℝ) ^ 2 := by
  by_cases hk : k = 0
  · simp only [hk, nonzeroTotientGridCoefficient, ite_true, Int.cast_zero, zero_div]
  have habs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hk0
  have habsL : k.natAbs ≤ L := by
    rw [← habs] at hkL
    exact_mod_cast hkL
  have hpos : 1 ≤ k.natAbs := (Int.natAbs_pos.mpr hk)
  rw [nonzeroTotientGridCoefficient, if_neg hk,
    totientGridCoefficient_eq_ramp (Finset.mem_Icc.mpr ⟨hpos, habsL⟩)]
  congr 1
  rw [← Int.cast_natCast k.natAbs, habs]

theorem continuous_totientGridFormFactor (L : ℕ) : Continuous (totientGridFormFactor L) :=
  continuous_const.mul ((continuous_integerHatInterpolation _).comp (continuous_const.mul continuous_id))

theorem totientGridFormFactor_nonneg {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    0 ≤ totientGridFormFactor L α :=
  mul_nonneg (Nat.cast_nonneg L)
    (integerHatInterpolation_nonneg (nonzeroTotientGridCoefficient_nonneg hL) _)

theorem totientGridFormFactor_le {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    totientGridFormFactor L α ≤ L := by
  have h := integerHatInterpolation_le (nonzeroTotientGridCoefficient_le_one hL) ((L : ℝ) * α)
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) L)
  change (L : ℝ) * integerHatInterpolation (nonzeroTotientGridCoefficient L) ((L : ℝ) * α) ≤ L
  simpa only [mul_one] using hm

theorem totientGridFormFactor_neg (L : ℕ) (α : ℝ) :
    totientGridFormFactor L (-α) = totientGridFormFactor L α := by
  unfold totientGridFormFactor
  rw [mul_neg, integerHatInterpolation_neg]
  congr 1
  exact congrArg (fun a => integerHatInterpolation a ((L : ℝ) * α))
    (funext (nonzeroTotientGridCoefficient_neg L))

/-- Exact Montgomery ramp, including the edge frequency. -/
theorem totientGridFormFactor_eq_ramp {L : ℕ} (hL : 1 ≤ L) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : totientGridFormFactor L α = α := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hx : (L : ℝ) * α ∈ Set.Icc (0 : ℝ) L :=
    ⟨mul_nonneg hLR.le hα.1, by nlinarith only [mul_le_mul_of_nonneg_left hα.2 hLR.le]⟩
  have hcoeff (k : ℤ) (hk0 : 0 ≤ k) (hkL : k ≤ (L : ℤ)) :
      nonzeroTotientGridCoefficient L k = (k : ℝ) * (1 / (L : ℝ) ^ 2) := by
    rw [nonzeroTotientGridCoefficient_eq_ramp hk0 hkL]
    ring
  unfold totientGridFormFactor
  rw [integerHatInterpolation_linear_on_Icc hcoeff hx]
  field_simp

theorem totientGridFormFactor_eq_abs {L : ℕ} (hL : 1 ≤ L) {α : ℝ}
    (hα : |α| ≤ 1) : totientGridFormFactor L α = |α| := by
  rcases le_or_gt 0 α with h | h
  · rw [abs_of_nonneg h]
    exact totientGridFormFactor_eq_ramp hL ⟨h, (le_abs_self α).trans hα⟩
  · rw [← totientGridFormFactor_neg L α, abs_of_neg h]
    exact totientGridFormFactor_eq_ramp hL ⟨by linarith, (neg_le_abs α).trans hα⟩

theorem gridPeriodicTriangle_nonneg (L m : ℕ) (α : ℝ) :
    0 ≤ gridPeriodicTriangle L m α :=
  mul_nonneg (Nat.cast_nonneg L) (tsum_nonneg fun _ => triangleFn_nonneg 1 _)

/-- Selecting multiples on the integer lattice recovers a periodized triangle. -/
theorem gridPeriodicTriangle_eq_interpolation {m : ℕ} (hm : 0 < m) (L : ℕ) (α : ℝ) :
    gridPeriodicTriangle L m α = (L : ℝ) *
      integerHatInterpolation (fun k : ℤ => if (m : ℤ) ∣ k then 1 else 0) ((L : ℝ) * α) := by
  let f : ℤ → ℝ := fun k => (if (m : ℤ) ∣ k then 1 else 0) *
    triangleFn 1 ((L : ℝ) * α - k)
  let g : ℤ → ℤ := fun j => -(m : ℤ) * j
  have hmz : -(m : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hm.ne')
  have hg : Function.Injective g := fun i j h => mul_left_cancel₀ hmz h
  have hs : Function.support f ⊆ Set.range g := by
    intro k hk
    have hd : (m : ℤ) ∣ k := by
      by_contra hn
      simp only [Function.mem_support, f, if_neg hn, zero_mul, ne_eq, not_true_eq_false] at hk
    rcases hd with ⟨j, rfl⟩
    exact ⟨-j, by dsimp only [g]; ring⟩
  have heq := hg.tsum_eq hs
  have hval (j : ℤ) : f (g j) = triangleFn 1 ((L : ℝ) * α + (m : ℝ) * j) := by
    have hd : (m : ℤ) ∣ g j := ⟨-j, by dsimp only [g]; ring⟩
    simp only [f, if_pos hd, one_mul]
    congr 1
    dsimp only [g]
    push_cast
    ring
  simp only [hval] at heq
  exact congrArg (fun t : ℝ => (L : ℝ) * t) heq

/-- The interpolant is a finite mixture of grid periodizations minus its central triangle. -/
theorem totientGridFormFactor_eq_mixture (L : ℕ) (α : ℝ) :
    totientGridFormFactor L α =
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * gridPeriodicTriangle L m α) +
      totientGridRemainder L * gridPeriodicTriangle L (L + 1) α -
      (L : ℝ) * triangleFn 1 ((L : ℝ) * α) := by
  let b : ℕ → ℤ → ℝ := fun m k => if (m : ℤ) ∣ k then 1 else 0
  have ha : nonzeroTotientGridCoefficient L = fun k : ℤ =>
      ((∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * b m k) +
        totientGridRemainder L * b (L + 1) k) - (if k = 0 then 1 else 0) := by
    funext k
    by_cases hk : k = 0
    · simp only [hk, nonzeroTotientGridCoefficient, ite_true, b, dvd_zero, mul_one,
        totientGridRemainder]
      ring
    · simp only [nonzeroTotientGridCoefficient, if_neg hk, sub_zero, b,
        totientGridCoefficient, Int.natCast_dvd, mul_ite, mul_one, mul_zero]
  unfold totientGridFormFactor
  rw [ha, integerHatInterpolation_sub, integerHatInterpolation_add,
    integerHatInterpolation_sum, integerHatInterpolation_mul, integerHatInterpolation_origin]
  simp_rw [integerHatInterpolation_mul]
  rw [mul_sub, mul_add, Finset.mul_sum]
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 L) :
      (L : ℝ) * (totientGridWeight L m * integerHatInterpolation (b m) ((L : ℝ) * α)) =
      totientGridWeight L m * gridPeriodicTriangle L m α := by
    rw [gridPeriodicTriangle_eq_interpolation (Finset.mem_Icc.mp hm).1]
    ring
  rw [sum_congr rfl hterm, gridPeriodicTriangle_eq_interpolation (Nat.succ_pos L)]
  ring

/-- Nonnegative Fourier coefficients of the unit-height periodized triangle. -/
def gridSincWeight (m : ℕ) (r : ℤ) : ℝ :=
  (1 / (m : ℝ)) * sinc (π * (1 / (m : ℝ)) * r) ^ 2

theorem gridSincWeight_nonneg (m : ℕ) (r : ℤ) : 0 ≤ gridSincWeight m r := by
  unfold gridSincWeight
  positivity

@[simp] theorem gridSincWeight_zero (m : ℕ) : gridSincWeight m 0 = 1 / (m : ℝ) := by
  simp only [gridSincWeight, Int.cast_zero, mul_zero, sinc_zero, one_pow, mul_one]

/-- Poisson summation gives an absolutely convergent positive Fourier series. -/
theorem gridPeriodicTriangle_fourier {m : ℕ} (hm : 0 < m) (L : ℕ) (α : ℝ) :
    (gridPeriodicTriangle L m α : ℂ) =
      ∑' r : ℤ, ((L : ℝ) * gridSincWeight m r : ℂ) *
        fourier r (((L : ℝ) * α / m : ℝ) : UnitAddCircle) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale (j : ℤ) : triangleFn (1 / (m : ℝ)) ((L : ℝ) * α / m + j) =
      triangleFn 1 ((L : ℝ) * α + (m : ℝ) * j) := by
    have he : (L : ℝ) * α / m + j = ((L : ℝ) * α + (m : ℝ) * j) / m := by
      field_simp
    have habs : |(L : ℝ) * α / m + j| / (1 / (m : ℝ)) =
        |(L : ℝ) * α + (m : ℝ) * j| := by
      rw [he, abs_div, abs_of_pos hmR]
      field_simp
    simp only [triangleFn, habs, div_one]
  have h := tsum_triangleFn_eq (one_div_pos.mpr hmR) ((L : ℝ) * α / m)
  simp only [hscale] at h
  calc
    (gridPeriodicTriangle L m α : ℂ) =
        (L : ℂ) * ∑' j : ℤ, (triangleFn 1 ((L : ℝ) * α + (m : ℝ) * j) : ℂ) := by
      simp only [gridPeriodicTriangle, Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_natCast]
    _ = _ := by
      rw [h, ← tsum_mul_left]
      apply tsum_congr
      intro r
      simp only [gridSincWeight, Complex.ofReal_mul, Complex.ofReal_natCast]
      ring

/-- The sinc-square coefficients have total mass one. -/
theorem tsum_gridSincWeight {m : ℕ} (hm : 0 < m) : ∑' r : ℤ, gridSincWeight m r = 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < 1 / (m : ℝ) := one_div_pos.mpr hmR
  have ha1 : 1 / (m : ℝ) ≤ 1 := (div_le_one hmR).mpr hm1
  have hzero (j : ℤ) (hj : j ≠ 0) : triangleFn (1 / (m : ℝ)) (j : ℝ) = 0 := by
    have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      have hnat : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hj
      have habs : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
        rw [← Int.cast_natCast j.natAbs, Int.natCast_natAbs]
        push_cast
        rfl
      rw [← habs]
      exact_mod_cast hnat
    exact triangleFn_eq_zero ha (ha1.trans hj1)
  have hsum : (∑' j : ℤ, (triangleFn (1 / (m : ℝ)) (j : ℝ) : ℂ)) = 1 := by
    rw [tsum_eq_sum (s := {0}) (fun j hj => by
      rw [hzero j (by simpa only [Finset.mem_singleton] using hj), Complex.ofReal_zero])]
    simp only [Finset.sum_singleton, Int.cast_zero, triangleFn, abs_zero, zero_div,
      sub_zero, max_eq_left zero_le_one, Complex.ofReal_one]
  have h := tsum_triangleFn_eq ha 0
  simp only [zero_add, fourier_coe_apply, Complex.ofReal_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h
  rw [hsum] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  exact h.symm

theorem summable_gridSincWeight {m : ℕ} (hm : 0 < m) : Summable (gridSincWeight m) := by
  by_contra hs
  have hzero := tsum_eq_zero_of_not_summable hs
  rw [tsum_gridSincWeight hm] at hzero
  exact one_ne_zero hzero

end GaloisForLFunctions.TransThresholdPairCorrelation
