import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Increasing window measurements control ordinary means

Abel summation has a one-sided inverse when the weights of each row
increase toward its endpoint. A nonpositive row can never create a new
positive maximum of the unweighted partial sum. Applying this to the
two constant translates of a sequence recovers its ordinary Cesàro
limit from one possibly different weighted observation at each length.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology _root_.RHTower
noncomputable section

/-- The weighted observation of the prefix ending at N. -/
def weightedPrefix (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (N : ℕ) :=
  ∑ j ∈ range (N+1), x j*w N j

/-- Every row is nonnegative and nondecreasing on its own prefix and
places positive weight on its last coefficient. -/
def increasingRowAt (w : ℕ → ℕ → ℝ) (N : ℕ) : Prop :=
  0 ≤ w N 0 ∧ 0 < w N N ∧ ∀ j < N, w N j ≤ w N (j+1)

private theorem next_prefix_le (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) {N : ℕ}
    (hw : increasingRowAt w N) (hx : weightedPrefix x w N ≤ 0) {C : ℝ} (hC : 0 ≤ C)
    (hprev : ∀ j<N, deningerPartialSum x j ≤ C) : deningerPartialSum x N ≤ C := by
  let Δ (j : ℕ) := w N (j+1)-w N j
  have hflip : (∑ j ∈ range N, deningerPartialSum x j*(w N j-w N (j+1))) =
      -(∑ j ∈ range N, deningerPartialSum x j*Δ j) := by
    rw [←sum_neg_distrib]
    exact sum_congr rfl fun j _ => by dsimp only [Δ]; ring
  have he := deningerAbelSummation x (w N) N
  rw [hflip] at he
  apply (mul_le_mul_iff_left₀ hw.2.1).mp
  calc
    _ = weightedPrefix x w N + ∑ j ∈ range N, deningerPartialSum x j*Δ j := by
      unfold weightedPrefix
      linarith only [he]
    _ ≤ 0 + ∑ j ∈ range N, C*Δ j := add_le_add hx (sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hprev j (mem_range.mp hj)) (sub_nonneg.mpr (hw.2.2 j (mem_range.mp hj))))
    _ ≤ C*w N N := by
      rw [zero_add,←mul_sum]
      change C*(∑ j ∈ range N, (w N (j+1)-w N j)) ≤ _
      rw [sum_range_sub]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hw.1) hC

/-- Once increasing rows have nonpositive observations, all later
unweighted prefixes lie below a common finite bound. -/
theorem bounded_prefix_of_nonpositive_increasing_rows (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ᶠ N : ℕ in atTop, increasingRowAt w N)
    (hx : ∀ᶠ N : ℕ in atTop, weightedPrefix x w N ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, deningerPartialSum x N ≤ C := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hw.and hx)
  let C := ∑ j ∈ range K, |x j|
  have hC : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C,hC,fun N => ?_⟩
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : K ≤ N
    · exact next_prefix_le x w (hK N hN).1 (hK N hN).2 hC ih
    · exact (sum_le_sum (fun j (_ : j ∈ range (N+1)) => le_abs_self (x j))).trans
        (sum_le_sum_of_subset_of_nonneg (range_mono (by omega : N+1 ≤ K)) (fun j _ _ => abs_nonneg (x j)))

private theorem prefix_drift (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (hrow : ∀ᶠ N : ℕ in atTop, increasingRowAt w N ∧ m ≤ ∑ j ∈ range (N+1), w N j)
    (hx : Tendsto (weightedPrefix x w) atTop (𝓝 0)) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, deningerPartialSum x N ≤ C+b*((N:ℝ)+1) := by
  have hs : ∀ᶠ N : ℕ in atTop, weightedPrefix (fun j => x j-b) w N ≤ 0 := by
    filter_upwards [hrow,hx.eventually_lt_const (mul_pos hb hm)] with N hr hh
    dsimp only [weightedPrefix] at hh ⊢
    simp_rw [sub_mul]
    rw [sum_sub_distrib,←mul_sum,sub_nonpos]
    exact hh.le.trans (mul_le_mul_of_nonneg_left hr.2 hb.le)
  obtain ⟨C,hC,h⟩ := bounded_prefix_of_nonpositive_increasing_rows _ w (hrow.mono fun _ h => h.1) hs
  refine ⟨C,hC,fun N => ?_⟩
  have hh := h N
  simp only [deningerPartialSum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,Nat.cast_succ] at hh
  unfold deningerPartialSum
  linarith only [hh]

/-- A positive uniform lower bound on the row mass suffices for
vanishing observations to force ordinary Cesàro cancellation. No
upper bound on the row masses or on the input sequence is needed. -/
theorem cesaro_zero_of_increasing_window_readings (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) {m : ℝ}
    (hm : 0 < m) (hrow : ∀ᶠ N : ℕ in atTop, increasingRowAt w N ∧
      m ≤ ∑ j ∈ range (N+1), w N j)
    (hx : Tendsto (weightedPrefix x w) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => deningerPartialSum x N/((N:ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (weightedPrefix (fun i => -x i) w) atTop (𝓝 0) := by
    change Tendsto (fun N : ℕ => ∑ j ∈ range (N+1), (-x j)*w N j) atTop (𝓝 0)
    simpa only [weightedPrefix,neg_mul,sum_neg_distrib,neg_zero] using hx.neg
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C,hC,hp⟩ := prefix_drift x w hm hrow hx (half_pos hε)
  obtain ⟨D,hD,hn⟩ := prefix_drift (fun i => -x i) w hm hrow hn (half_pos hε)
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (2*(C+D+1)/ε)] with N hN
  have hh := hn N
  simp only [deningerPartialSum,sum_neg_distrib] at hh
  change -deningerPartialSum x N ≤ _ at hh
  have hn' := (div_le_iff₀ hε).mp hN
  have hpos : 0<(N:ℝ)+1 := by positivity
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos,div_lt_iff₀ hpos]
  exact abs_lt.mpr ⟨by nlinarith only [hh,hn',hC,hε],by nlinarith only [hp N,hn',hD,hε]⟩

#print axioms bounded_prefix_of_nonpositive_increasing_rows
#print axioms cesaro_zero_of_increasing_window_readings
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
