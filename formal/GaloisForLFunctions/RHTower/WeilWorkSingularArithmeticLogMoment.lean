import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The decreasing primitive of the exact forward log-moment bound

The moment inequality controls a decreasing normalized primitive, not only
an upper growth envelope. All arithmetic sums here are finite.
-/

open Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic.LogMoment

def mass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, w n

def moment (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Real.log n * w n

def primitive (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.log N * mass w N - moment w N

theorem primitive_eq_sum (w : ℕ → ℝ) (N : ℕ) :
    primitive w N = ∑ n ∈ Finset.Icc 1 N, (Real.log N - Real.log n) * w n := by
  simp only [primitive, mass, moment, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul]

theorem mass_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ mass w N := Finset.sum_nonneg fun n _ => hw n

theorem primitive_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ primitive w N := by
  rw [primitive_eq_sum]
  apply Finset.sum_nonneg
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
    (by exact_mod_cast hn'.2))) (hw n)

theorem primitive_succ (w : ℕ → ℝ) (N : ℕ) :
    primitive w (N + 1) = primitive w N +
      (Real.log (N + 1) - Real.log N) * mass w N := by
  simp only [primitive, mass, moment, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
    Nat.cast_add, Nat.cast_one]
  ring

theorem primitive_sub_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    primitive w N - primitive w M ≤ (Real.log N - Real.log M) * mass w N := by
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N :=
    fun n hn => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hMN⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ =>
      (Real.log n - Real.log M) * w n) hsub (fun n hn hnM => by
    have hn' := Finset.mem_Icc.mp hn
    have hMn : M < n := by
      by_contra h
      exact hnM (Finset.mem_Icc.mpr ⟨hn'.1, by omega⟩)
    exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMn.le))) (hw n))
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  dsimp only [primitive, mass, moment]
  linarith

theorem normalized_primitive_succ_le {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hbound : ∀ N : ℕ, 1 ≤ N → 2 * moment w N ≤ (Real.log N + C) * mass w N)
    {N : ℕ} (hN : 1 ≤ N) (hNC : C < Real.log N) :
    primitive w (N + 1) / (Real.log (N + 1) - C) ^ 2 ≤
      primitive w N / (Real.log N - C) ^ 2 := by
  let u := Real.log N - C
  let d := Real.log (N + 1) - Real.log N
  have hu : 0 < u := sub_pos.mpr hNC
  have hd : 0 ≤ d := sub_nonneg.mpr (Real.log_le_log
    (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast Nat.le_succ N))
  have hH := primitive_nonneg hw N
  have hE : u * mass w N ≤ 2 * primitive w N := by
    have h := hbound N hN
    dsimp [u, primitive]
    linarith
  have hU : Real.log (N + 1) - C = u + d := by dsimp [u, d]; ring
  rw [hU, primitive_succ]
  change (primitive w N + d * mass w N) / (u + d) ^ 2 ≤ primitive w N / u ^ 2
  apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity)) (sq_pos_of_pos hu)).mpr
  have hmul := mul_le_mul_of_nonneg_left hE (mul_nonneg hd hu.le)
  nlinarith [mul_nonneg hH (sq_nonneg d)]

/-- The normalized primitive has an actual finite nonnegative limit. -/
theorem exists_primitive_limit {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hbound : ∀ N : ℕ, 1 ≤ N → 2 * moment w N ≤ (Real.log N + C) * mass w N) :
    ∃ k : ℝ, 0 ≤ k ∧
      Tendsto (fun N : ℕ => primitive w N / (Real.log N - C) ^ 2) atTop (𝓝 k) ∧
      Tendsto (fun N : ℕ => primitive w N / (Real.log N) ^ 2) atTop (𝓝 k) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hlog.eventually_gt_atTop C).and (eventually_ge_atTop 1))
  let f : ℕ → ℝ := fun N => primitive w N / (Real.log N - C) ^ 2
  have ha : Antitone (fun n => f (n + N₀)) := antitone_nat_of_succ_le fun n => by
    have h := hN₀ (n + N₀) (by omega)
    simpa only [f, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.cast_add,
      Nat.cast_one, add_assoc] using
      normalized_primitive_succ_le hw hbound h.2 h.1
  have hf0 (N : ℕ) : 0 ≤ f N := div_nonneg (primitive_nonneg hw N) (sq_nonneg _)
  have hb : BddBelow (Set.range (fun n => f (n + N₀))) :=
    ⟨0, fun y ⟨n, hn⟩ => hn ▸ hf0 _⟩
  let k := ⨅ n, f (n + N₀)
  have hk := tendsto_atTop_ciInf ha hb
  have hk0 : 0 ≤ k := ge_of_tendsto hk (Eventually.of_forall fun n => hf0 _)
  have ht : Tendsto f atTop (𝓝 k) := (tendsto_add_atTop_iff_nat N₀).mp hk
  have hC : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hr : Tendsto (fun N : ℕ => (Real.log N - C) / Real.log N) atTop (𝓝 1) := by
    have hh : Tendsto (fun N : ℕ => 1 - C / Real.log N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hC
    apply hh.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    simp [sub_div, ne_of_gt hN]
  refine ⟨k, hk0, ht, ?_⟩
  have hlim := ht.mul (hr.pow 2)
  simp only [one_pow, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop C] with N hN
  dsimp [f]
  field_simp [ne_of_gt (sub_pos.mpr hN)]

end RHTower.WeilSingularArithmetic.LogMoment
