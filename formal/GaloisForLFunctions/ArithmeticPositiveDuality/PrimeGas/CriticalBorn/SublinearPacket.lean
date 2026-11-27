import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Window
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Elementary mass at a moving lower cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real
open scoped Topology

/-- Repeated halving removes a geometric fraction of elementary mass at
every positive power index, with the threshold allowed to depend on the depth. -/
private theorem halving {a : ℝ} (ha : 0<a) : ∃ r : ℝ, 0≤r ∧ r<1 ∧ ∀ j : ℕ,
    ∀ᶠ x : ℝ in atTop, powerMass a ((1/2:ℝ)^j*x) ≤ r^j * powerMass a x := by
  obtain ⟨d,hd,share⟩ := positive_window_share ha (by norm_num : (0:ℝ)<1/2) (by norm_num)
  let e := min d (1/2)
  have he : 0<e := lt_min hd (by norm_num)
  have er : e≤1/2 := min_le_right _ _
  have ed : e≤d := min_le_left _ _
  have hr : 0≤1-e := by linarith only [er]
  have half : ∀ᶠ x : ℝ in atTop, powerMass a (1/2*x) ≤ (1-e)*powerMass a x := by
    filter_upwards [share,eventually_ge_atTop (0:ℝ)] with x hs hx
    rw [windowMass_sub (by linarith only [hx] : 1/2*x≤x)] at hs
    have low := mul_le_mul_of_nonneg_right ed (powerMass_pos a x).le
    linarith only [hs,low]
  refine ⟨1-e,hr,by linarith only [he],?_⟩
  intro j
  induction j with
  | zero => exact Eventually.of_forall (fun x => by simp)
  | succ j ih =>
    have scaled := _root_.RHTower.tendsto_const_mul_atTop_of_pos (pow_pos (by norm_num : (0:ℝ)<1/2) j)
    filter_upwards [scaled.eventually half,ih] with x hs hj
    calc
      powerMass a ((1/2:ℝ)^(j+1)*x) = powerMass a (1/2*((1/2:ℝ)^j*x)) := by rw [pow_succ',mul_assoc]
      _ ≤ (1-e)*powerMass a ((1/2:ℝ)^j*x) := hs
      _ ≤ (1-e)*((1-e)^j*powerMass a x) := mul_le_mul_of_nonneg_left hj hr
      _ = _ := by rw [pow_succ',mul_assoc]

/-- Below the critical line every sublinear moving label cutoff loses
all its mass, even if it tends to infinity. -/
theorem subcritical_sublinear {ι : Type*} {l : Filter ι} {a : ℝ} (ha : 0<a) {x y : ι → ℝ}
    (hx : Tendsto x l atTop) (hy : Tendsto (fun i => y i/x i) l (𝓝 0)) :
    Tendsto (fun i => powerMass a (y i)/powerMass a (x i)) l (𝓝 0) := by
  obtain ⟨r,hr,hr',bound⟩ := halving ha
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr').eventually_lt_const hε).exists
  have cpos := pow_pos (by norm_num : (0:ℝ)<1/2) j
  filter_upwards [hx.eventually (bound j),hx.eventually_gt_atTop 0,hy.eventually_lt_const cpos]
    with i hi xi yi
  have hmass := powerMass_mono a ((div_lt_iff₀ xi).mp yi).le
  rw [Real.dist_eq,sub_zero,abs_of_pos (div_pos (powerMass_pos a _) (powerMass_pos a _))]
  exact ((div_le_iff₀ (powerMass_pos a _)).mpr (hmass.trans hi)).trans_lt hj

/-- Above the critical line any two cutoffs tending to infinity
exhaust the same positive finite elementary mass. -/
theorem supercritical_exhaustion {ι : Type*} {l : Filter ι} {a : ℝ} (ha : a<0)
    {x y : ι → ℝ} (hx : Tendsto x l atTop) (hy : Tendsto y l atTop) :
    Tendsto (fun i => powerMass a (y i)/powerMass a (x i)) l (𝓝 1) := by
  let f := fun n : ℕ => (n:ℝ)^(a-1)
  have hs : Summable f := Real.summable_nat_rpow.mpr (by linarith only [ha])
  have bound : BddAbove (Set.range (powerMass a)) :=
    ⟨∑' n, f n,by
      rintro _ ⟨z,rfl⟩
      exact hs.sum_le_tsum _ (fun n _ => rpow_nonneg (Nat.cast_nonneg n) _)⟩
  have lim := tendsto_atTop_ciSup (powerMass_mono a) bound
  have pos := (powerMass_pos a 2).trans_le (le_ciSup bound 2)
  have h := (lim.comp hy).div (lim.comp hx) pos.ne'
  rw [div_self pos.ne'] at h
  exact h.congr (fun i => rfl)

#print axioms subcritical_sublinear
#print axioms supercritical_exhaustion

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
