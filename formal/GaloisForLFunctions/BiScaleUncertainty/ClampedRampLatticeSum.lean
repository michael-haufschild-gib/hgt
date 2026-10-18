import GaloisForLFunctions.BiScaleUncertainty.ClampedExponentialRamp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Exact lattice summation of the literal clamp, including its endpoint half
and a bounded fractional-part remainder. Every infinite sum here has finite support. -/

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def clampedLatticeRemainder (y : ℝ) : ℝ :=
  (y-(⌊y⌋₊ : ℝ))*(1-(y-(⌊y⌋₊ : ℝ)))/2

theorem clampedLatticeRemainder_bounds {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ clampedLatticeRemainder y ∧ clampedLatticeRemainder y ≤ 1/8 := by
  have h0 := Nat.floor_le hy
  have h1 := Nat.lt_floor_add_one y
  unfold clampedLatticeRemainder
  constructor
  · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  · nlinarith [sq_nonneg (y-(⌊y⌋₊ : ℝ)-(1/2 : ℝ))]

private def positiveLatticeSum (y : ℝ) : ℝ :=
  ∑' k : ℕ, max (y-((k : ℝ)+1)) 0

private theorem positiveLatticeTerm_zero (y : ℝ) {k : ℕ} (hk : ⌊y⌋₊ ≤ k) :
    max (y-((k : ℝ)+1)) 0 = 0 := by
  have hfloor := Nat.lt_floor_add_one y
  have hcast : (⌊y⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  exact max_eq_right (by linarith)

private theorem positiveLattice_summable (y : ℝ) :
    Summable (fun k : ℕ => max (y-((k : ℝ)+1)) 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range ⌊y⌋₊)
  intro k hk
  exact positiveLatticeTerm_zero y (by simpa only [Finset.mem_range, not_lt] using hk)

private theorem sum_successors (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ)+1)) = (m : ℝ)*((m : ℝ)+1)/2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem positiveLatticeSum_eq {y : ℝ} (hy : 0 ≤ y) :
    positiveLatticeSum y = (y^2-y)/2+clampedLatticeRemainder y := by
  have hfinite : positiveLatticeSum y =
      (∑ k ∈ Finset.range ⌊y⌋₊, (y-((k : ℝ)+1))) := by
    unfold positiveLatticeSum
    rw [tsum_eq_sum (s := Finset.range ⌊y⌋₊) (fun k hk =>
      positiveLatticeTerm_zero y (by simpa only [Finset.mem_range, not_lt] using hk))]
    apply Finset.sum_congr rfl
    intro k hk
    have hcast : (k : ℝ)+1 ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast (show k+1 ≤ ⌊y⌋₊ by have := Finset.mem_range.mp hk; omega)
    exact max_eq_left (by linarith [Nat.floor_le hy])
  rw [hfinite, Finset.sum_sub_distrib, sum_successors, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  unfold clampedLatticeRemainder
  ring

private theorem clampedRamp_eq_positiveParts {ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    clampedRamp ε v = (max (1+ε-v) 0-max (1-v) 0)/ε := by
  by_cases hlow : v ≤ 1
  · rw [clampedRamp_eq_one hε hlow, max_eq_left (by linarith : 0 ≤ 1+ε-v),
      max_eq_left (by linarith : 0 ≤ 1-v)]
    rw [show 1+ε-v-(1-v) = ε by ring, div_self hε.ne']
  · by_cases hhigh : 1+ε ≤ v
    · rw [clampedRamp_eq_zero hε hhigh,
        max_eq_right (by linarith : 1+ε-v ≤ 0),
        max_eq_right (by linarith : 1-v ≤ 0)]
      simp
    · rw [clampedRamp_eq_linear hε (by linarith) (by linarith),
        max_eq_left (by linarith : 0 ≤ 1+ε-v),
        max_eq_right (by linarith : 1-v ≤ 0), sub_zero]

private theorem clampedRamp_dilate_positiveParts {ε a t : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (ht : 0 < t) (k : ℕ) :
    clampedRamp ε (((k : ℝ)+1)*t/a) =
      (t/(a*ε))*(max (a*(1+ε)/t-((k : ℝ)+1)) 0-
        max (a/t-((k : ℝ)+1)) 0) := by
  have hscale : 0 < t/a := div_pos ht ha
  have hmax (v : ℝ) : max ((t/a)*v) 0 = (t/a)*max v 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg v 0 hscale.le).symm
  have h1 : 1+ε-((k : ℝ)+1)*t/a = (t/a)*(a*(1+ε)/t-((k : ℝ)+1)) := by
    field_simp
  have h0 : 1-((k : ℝ)+1)*t/a = (t/a)*(a/t-((k : ℝ)+1)) := by
    field_simp
  rw [clampedRamp_eq_positiveParts hε, h1, h0, hmax, hmax]
  field_simp

theorem summable_clampedRamp_dilate {ε a t : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (ht : 0 < t) :
    Summable (fun k : ℕ => clampedRamp ε (((k : ℝ)+1)*t/a)) := by
  have h := ((positiveLattice_summable (a*(1+ε)/t)).sub
    (positiveLattice_summable (a/t))).mul_left (t/(a*ε))
  exact h.congr (fun k => (clampedRamp_dilate_positiveParts hε ha ht k).symm)

def clampedLatticeSum (ε a t : ℝ) : ℝ :=
  ∑' k : ℕ, clampedRamp ε (((k : ℝ)+1)*t/a)

/-- The endpoint half is exact, including when either scaled endpoint is integral. -/
theorem clampedLatticeSum_eq {ε a t : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (ht : 0 < t) :
    clampedLatticeSum ε a t = a*(1+ε/2)/t-1/2+
      (t/(a*ε))*(clampedLatticeRemainder (a*(1+ε)/t)-clampedLatticeRemainder (a/t)) := by
  have he : clampedLatticeSum ε a t =
      (t/(a*ε))*(positiveLatticeSum (a*(1+ε)/t)-positiveLatticeSum (a/t)) := by
    unfold clampedLatticeSum positiveLatticeSum
    simp_rw [clampedRamp_dilate_positiveParts hε ha ht]
    rw [tsum_mul_left, (positiveLattice_summable (a*(1+ε)/t)).tsum_sub
      (positiveLattice_summable (a/t))]
  rw [he, positiveLatticeSum_eq (by positivity), positiveLatticeSum_eq (by positivity)]
  field_simp; ring

theorem clampedLatticeSum_error_le {ε a t : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (ht : 0 < t) :
    |clampedLatticeSum ε a t-(a*(1+ε/2)/t-1/2)| ≤ t/(8*a*ε) := by
  have hb := clampedLatticeRemainder_bounds (y := a*(1+ε)/t) (by positivity)
  have hc := clampedLatticeRemainder_bounds (y := a/t) (by positivity)
  have hd : |clampedLatticeRemainder (a*(1+ε)/t)-clampedLatticeRemainder (a/t)| ≤ 1/8 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [clampedLatticeSum_eq hε ha ht, add_sub_cancel_left, abs_mul,
    abs_of_pos (show 0 < t/(a*ε) by positivity)]
  calc
    _ ≤ (t/(a*ε))*(1/8) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by field_simp

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
