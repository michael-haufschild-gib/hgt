import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A positive configuration with non-attained top modulus and bounded power sums

A countable family of nodes `z_i` in the open unit disc with positive summable weights `w_i`,
whose moduli accumulate at `1` without attaining it, and whose power sums `Σ_i w_i z_i^m`
decay geometrically at any prescribed rate: `|Σ_i w_i z_i^m| ≤ e^{−λm}` for every `m ≥ 1`.
Scaling the nodes by `e^{λ}` gives a configuration with top modulus `e^{λ} > 1`, not attained,
and power sums of modulus at most `1`.  The nodes are arranged in rings: ring `N` consists of
the `N`-th roots of unity, possibly rotated by `π/N`, at radius `ρ_N = e^{−5/√N}`, with total
weight `c_N`.  The power sum of ring `N` at `m` is `c_N ρ_N^m (−1)^{s_N m/N}` when `N ∣ m` and
`0` otherwise, so ring `m` can be chosen, by recursion over the proper divisors of `m`, to cancel
the contribution of all earlier rings up to the positive seed `e^{−λm}`.  The weights stay
summable because a proper divisor `N ≤ m/2` gives `(ρ_N/ρ_m)^m ≤ e^{−2√m}`, while the seed
costs `e^{5√m − λm} ≤ e^{25/(4λ)}`.

This is the structural obstruction to single-base lag criteria: positivity of the weights,
absolute summability, and accumulation of the moduli at a non-attained supremum do not force
the single-base power sums to be unbounded.
-/

open Complex Real Finset

namespace RHTower

noncomputable section

/-- Radius of the ring `N`. -/
def ringRadius (N : ℕ) : ℝ := Real.exp (-(5 / Real.sqrt N))

/-- The positive seed at exponent `m` with rate `l`: `e^{−lm}`. -/
def ringSeed (l : ℝ) (m : ℕ) : ℝ := Real.exp (-(l * m))

theorem ringRadius_pos (N : ℕ) : 0 < ringRadius N := Real.exp_pos _

theorem ringSeed_pos (l : ℝ) (m : ℕ) : 0 < ringSeed l m := Real.exp_pos _

theorem ringSeed_le_one {l : ℝ} (hl : 0 ≤ l) (m : ℕ) : ringSeed l m ≤ 1 := by
  rw [ringSeed]
  exact Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)

theorem ringRadius_le_one (N : ℕ) : ringRadius N ≤ 1 := by
  rw [ringRadius]
  exact Real.exp_le_one_iff.mpr (by
    have : 0 ≤ 5 / Real.sqrt N := by positivity
    linarith)

theorem ringRadius_lt_one {N : ℕ} (hN : 1 ≤ N) : ringRadius N < 1 := by
  rw [ringRadius, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have : 0 < 5 / Real.sqrt N := by positivity
  linarith

theorem ringRadius_pow (N m : ℕ) :
    ringRadius N ^ m = Real.exp (-(5 * m / Real.sqrt N)) := by
  rw [ringRadius, ← Real.exp_nat_mul]
  congr 1
  ring

/-- `ρ_m^m = e^{−5√m}`. -/
theorem ringRadius_pow_self (m : ℕ) :
    ringRadius m ^ m = Real.exp (-(5 * Real.sqrt m)) := by
  rw [ringRadius_pow]
  congr 1
  have h : (m : ℝ) / Real.sqrt m = Real.sqrt m := Real.div_sqrt
  rw [mul_div_assoc, h]

/-- The sign of the rotated ring `N` at exponent `m`: `(−1)^{m/N}` if rotated, else `1`. -/
def ringSign (flag : Bool) (N m : ℕ) : ℝ := if flag then (-1 : ℝ) ^ (m / N) else 1

theorem abs_ringSign (flag : Bool) (N m : ℕ) : |ringSign flag N m| = 1 := by
  unfold ringSign; split_ifs <;> simp

/-- One recursion step: the ring data at `m` from the data of all proper divisors. -/
def ringStep (l : ℝ) (f : ℕ → ℝ × Bool) (m : ℕ) : ℝ × Bool :=
  ((|∑ N ∈ Nat.properDivisors m, (f N).1 * ringRadius N ^ m * ringSign (f N).2 N m| + ringSeed l m)
      / ringRadius m ^ m,
    decide (0 ≤ ∑ N ∈ Nat.properDivisors m, (f N).1 * ringRadius N ^ m * ringSign (f N).2 N m))

/-- The data of the rings below `m`. -/
def ringPrefix (l : ℝ) : ℕ → (ℕ → ℝ × Bool)
  | 0 => fun _ => (0, false)
  | m + 1 => fun N => if N = m then ringStep l (ringPrefix l m) m else ringPrefix l m N

/-- The ring data: total weight and rotation flag. -/
def ringData (l : ℝ) (N : ℕ) : ℝ × Bool := ringPrefix l (N + 1) N

/-- The total weight of ring `N`. -/
def ringWeight (l : ℝ) (N : ℕ) : ℝ := (ringData l N).1

/-- The rotation flag of ring `N`. -/
def ringFlag (l : ℝ) (N : ℕ) : Bool := (ringData l N).2

variable {l : ℝ}

theorem ringPrefix_eq_of_lt {m N : ℕ} (h : N < m) : ringPrefix l m N = ringData l N := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
      · simp only [ringPrefix]
        rw [if_neg (by omega)]
        exact ih h'
      · rfl

theorem ringStep_congr {f g : ℕ → ℝ × Bool} {m : ℕ} (h : ∀ N < m, f N = g N) :
    ringStep l f m = ringStep l g m := by
  unfold ringStep
  have e : ∑ N ∈ Nat.properDivisors m, (f N).1 * ringRadius N ^ m * ringSign (f N).2 N m
      = ∑ N ∈ Nat.properDivisors m, (g N).1 * ringRadius N ^ m * ringSign (g N).2 N m := by
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [h N (Nat.mem_properDivisors.mp hN).2]
  rw [e]

/-- The recursive sum `S_m` over the proper divisors. -/
def ringS (l : ℝ) (m : ℕ) : ℝ :=
  ∑ N ∈ Nat.properDivisors m, ringWeight l N * ringRadius N ^ m * ringSign (ringFlag l N) N m

theorem ringData_eq (m : ℕ) : ringData l m = ringStep l (ringData l) m := by
  have : ringData l m = ringStep l (ringPrefix l m) m := by
    simp [ringData, ringPrefix]
  rw [this]
  exact ringStep_congr fun N hN => ringPrefix_eq_of_lt hN

theorem ringWeight_eq (m : ℕ) :
    ringWeight l m = (|ringS l m| + ringSeed l m) / ringRadius m ^ m := by
  unfold ringWeight
  rw [ringData_eq]
  rfl

theorem ringFlag_eq (m : ℕ) : ringFlag l m = decide (0 ≤ ringS l m) := by
  unfold ringFlag
  rw [ringData_eq]
  rfl

theorem ringWeight_pos (m : ℕ) : 0 < ringWeight l m := by
  rw [ringWeight_eq]
  exact div_pos (by have := abs_nonneg (ringS l m); have := ringSeed_pos l m; linarith)
    (pow_pos (ringRadius_pos m) m)

/-- The ring `m` cancels the earlier rings up to the seed:
`S_m + c_m ρ_m^m σ_m(m) = −sign(S_m)·seed_m`. -/
theorem ringS_add_self (m : ℕ) (hm : 1 ≤ m) :
    ringS l m + ringWeight l m * ringRadius m ^ m * ringSign (ringFlag l m) m m
      = -(if 0 ≤ ringS l m then (1 : ℝ) else -1) * ringSeed l m := by
  rw [ringWeight_eq, ringFlag_eq, div_mul_cancel₀ _ (pow_pos (ringRadius_pos m) m).ne']
  unfold ringSign
  rw [Nat.div_self (by omega), pow_one]
  simp only [decide_eq_true_eq]
  by_cases h : 0 ≤ ringS l m
  · rw [if_pos h, if_pos h, abs_of_nonneg h]
    ring
  · rw [if_neg h, if_neg h, abs_of_neg (not_le.mp h)]
    ring

/-- The full power sum over all rings dividing `m`. -/
def ringTotal (l : ℝ) (m : ℕ) : ℝ :=
  ∑ N ∈ Nat.divisors m, ringWeight l N * ringRadius N ^ m * ringSign (ringFlag l N) N m

theorem ringTotal_eq (m : ℕ) (hm : 1 ≤ m) :
    ringTotal l m = -(if 0 ≤ ringS l m then (1 : ℝ) else -1) * ringSeed l m := by
  rw [← ringS_add_self m hm, ringTotal, ringS, ← Nat.insert_self_properDivisors (by omega),
    Finset.sum_insert Nat.self_notMem_properDivisors, add_comm]

theorem abs_ringTotal_le (m : ℕ) (hm : 1 ≤ m) : |ringTotal l m| ≤ ringSeed l m := by
  rw [ringTotal_eq m hm, abs_mul, abs_neg, abs_of_pos (ringSeed_pos l m)]
  split_ifs <;> simp

/-! ## Bounds on the weights -/

theorem two_mul_le_of_mem_properDivisors {N m : ℕ} (h : N ∈ Nat.properDivisors m) : 2 * N ≤ m := by
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp h
  obtain ⟨k, rfl⟩ := hdvd
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h; · simp at hlt
    exact h
  have hk : 2 ≤ k := by
    by_contra hk
    push Not at hk
    interval_cases k <;> simp at hlt
  nlinarith

/-- For a proper divisor `N` of `m`, `(ρ_N/ρ_m)^m ≤ e^{−2√m}`. -/
theorem ringRadius_ratio_le {N m : ℕ} (h : N ∈ Nat.properDivisors m) :
    ringRadius N ^ m / ringRadius m ^ m ≤ Real.exp (-(2 * Real.sqrt m)) := by
  have h2N := two_mul_le_of_mem_properDivisors h
  have hN : 1 ≤ N := Nat.pos_of_mem_properDivisors h
  rw [ringRadius_pow, ringRadius_pow_self m, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have key : 7 * Real.sqrt m * Real.sqrt N ≤ 5 * m := by
    have h1 : (7 * Real.sqrt m * Real.sqrt N) ^ (2 : ℕ) ≤ (5 * m) ^ (2 : ℕ) := by
      have e1 : (7 * Real.sqrt m * Real.sqrt N) ^ (2 : ℕ) = 49 * m * N := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hm0, Real.sq_sqrt (Nat.cast_nonneg N)]; ring
      rw [e1]
      have : (2 * N : ℝ) ≤ m := by exact_mod_cast h2N
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have h3 : 7 * Real.sqrt m ≤ 5 * m / Real.sqrt N := by
    rw [le_div_iff₀ hsN]; exact key
  linarith

theorem card_properDivisors_le (m : ℕ) : (Nat.properDivisors m).card ≤ m := by
  calc (Nat.properDivisors m).card ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro N hN
        exact Finset.mem_range.mpr (Nat.mem_properDivisors.mp hN).2
    _ = m := Finset.card_range m

theorem abs_ringS_le (m : ℕ) :
    |ringS l m| ≤ ∑ N ∈ Nat.properDivisors m, ringWeight l N * ringRadius N ^ m := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun N _ => ?_)
  rw [abs_mul, abs_ringSign, mul_one, abs_mul, abs_of_pos (ringWeight_pos N),
    abs_of_pos (pow_pos (ringRadius_pos N) m)]

/-- `seed_m/ρ_m^m = e^{5√m − lm}`. -/
theorem ringSeed_div_ringRadius_pow (m : ℕ) :
    ringSeed l m / ringRadius m ^ m = Real.exp (5 * Real.sqrt m - l * m) := by
  rw [ringSeed, ringRadius_pow_self m, ← Real.exp_sub]
  congr 1
  ring

/-- `e^{2√m} ≥ 2m`. -/
theorem two_mul_le_exp_two_sqrt (m : ℕ) : (2 * m : ℝ) ≤ Real.exp (2 * Real.sqrt m) := by
  have h := Real.pow_div_factorial_le_exp (2 * Real.sqrt m) (by positivity) 2
  have e : (2 * Real.sqrt m) ^ (2 : ℕ) / (Nat.factorial 2 : ℝ) = 2 * m := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    norm_num [Nat.factorial]
    ring
  rw [e] at h
  exact h

/-- `e^{2√m} ≥ 64 m³/720`. -/
theorem cube_le_exp_two_sqrt (m : ℕ) :
    64 * (m : ℝ) ^ (3 : ℕ) / 720 ≤ Real.exp (2 * Real.sqrt m) := by
  have h := Real.pow_div_factorial_le_exp (2 * Real.sqrt m) (by positivity) 6
  have e : (2 * Real.sqrt m) ^ (6 : ℕ) / (Nat.factorial 6 : ℝ) = 64 * (m : ℝ) ^ (3 : ℕ) / 720 := by
    rw [mul_pow, show (Real.sqrt m) ^ (6 : ℕ) = ((Real.sqrt m) ^ (2 : ℕ)) ^ (3 : ℕ) by ring,
      Real.sq_sqrt (Nat.cast_nonneg m)]
    norm_num [Nat.factorial]
  rw [e] at h
  exact h

/-- `m e^{−2√m} ≤ 1/2`. -/
theorem mul_exp_neg_two_sqrt_le_half (m : ℕ) :
    (m : ℝ) * Real.exp (-(2 * Real.sqrt m)) ≤ 1 / 2 := by
  have hE := two_mul_le_exp_two_sqrt m
  have hEpos := Real.exp_pos (2 * Real.sqrt m)
  rw [Real.exp_neg, mul_inv_le_iff₀ hEpos]
  linarith

/-- The seed cost is bounded: `e^{5√m − lm} ≤ e^{25/(4l)}`. -/
theorem exp_seed_cost_le {l : ℝ} (hl : 0 < l) (m : ℕ) :
    Real.exp (5 * Real.sqrt m - l * m) ≤ Real.exp (25 / (4 * l)) := by
  apply Real.exp_le_exp.mpr
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  have hs2 : l ^ (2 : ℕ) * Real.sqrt m ^ (2 : ℕ) = l ^ (2 : ℕ) * m := by rw [hs]
  have h := sq_nonneg (5 - 2 * l * Real.sqrt m)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h, hs2]

/-- The seed cost decays geometrically: `e^{5√m − lm} ≤ e^{25/(2l)} e^{−lm/2}`. -/
theorem exp_seed_cost_le_geom {l : ℝ} (hl : 0 < l) (m : ℕ) :
    Real.exp (5 * Real.sqrt m - l * m) ≤ Real.exp (25 / (2 * l)) * Real.exp (-(l / 2)) ^ m := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  have hs2 : l ^ (2 : ℕ) * Real.sqrt m ^ (2 : ℕ) = l ^ (2 : ℕ) * m := by rw [hs]
  have h := sq_nonneg (5 - l * Real.sqrt m)
  have h2 : 5 * Real.sqrt m - l * m / 2 ≤ 25 / (2 * l) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h, hs2]
  linarith

/-- The uniform weight bound `K = 2 e^{25/(4l)}`. -/
def ringWeightBound (l : ℝ) : ℝ := 2 * Real.exp (25 / (4 * l))

theorem one_le_ringWeightBound {l : ℝ} (hl : 0 < l) : 1 ≤ ringWeightBound l := by
  unfold ringWeightBound
  have : 1 ≤ Real.exp (25 / (4 * l)) := Real.one_le_exp (by positivity)
  linarith

/-- The recursive weight estimate: `c_m ≤ K m e^{−2√m} + e^{5√m − lm}` for `m ≥ 1`, given
`c_N ≤ K` on the proper divisors. -/
theorem ringWeight_step_le {m : ℕ} {K : ℝ}
    (hK : ∀ N ∈ Nat.properDivisors m, ringWeight l N ≤ K) (hK0 : 0 ≤ K) :
    ringWeight l m ≤ K * m * Real.exp (-(2 * Real.sqrt m)) + Real.exp (5 * Real.sqrt m - l * m) := by
  have hρpos := pow_pos (ringRadius_pos m) m
  have hEneg := Real.exp_pos (-(2 * Real.sqrt m))
  have hsum : ∑ N ∈ Nat.properDivisors m, ringWeight l N * ringRadius N ^ m
      ≤ (Nat.properDivisors m).card * (K * (ringRadius m ^ m * Real.exp (-(2 * Real.sqrt m)))) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun N hN => ?_
    have hr := ringRadius_ratio_le hN
    have hw := hK N hN
    rw [div_le_iff₀ hρpos] at hr
    calc ringWeight l N * ringRadius N ^ m ≤ K * ringRadius N ^ m :=
          mul_le_mul_of_nonneg_right hw (pow_pos (ringRadius_pos N) m).le
      _ ≤ K * (Real.exp (-(2 * Real.sqrt m)) * ringRadius m ^ m) :=
          mul_le_mul_of_nonneg_left hr hK0
      _ = K * (ringRadius m ^ m * Real.exp (-(2 * Real.sqrt m))) := by ring
  have hcard : ((Nat.properDivisors m).card : ℝ) ≤ m := by exact_mod_cast card_properDivisors_le m
  have h1 := abs_ringS_le (l := l) m
  have h2 : ringSeed l m = Real.exp (5 * Real.sqrt m - l * m) * ringRadius m ^ m := by
    rw [← ringSeed_div_ringRadius_pow m, div_mul_cancel₀ _ hρpos.ne']
  rw [ringWeight_eq, div_le_iff₀ hρpos]
  calc |ringS l m| + ringSeed l m
      ≤ (Nat.properDivisors m).card * (K * (ringRadius m ^ m * Real.exp (-(2 * Real.sqrt m))))
        + Real.exp (5 * Real.sqrt m - l * m) * ringRadius m ^ m := by rw [h2]; linarith
    _ ≤ m * (K * (ringRadius m ^ m * Real.exp (-(2 * Real.sqrt m))))
        + Real.exp (5 * Real.sqrt m - l * m) * ringRadius m ^ m := by
        gcongr
    _ = (K * m * Real.exp (-(2 * Real.sqrt m)) + Real.exp (5 * Real.sqrt m - l * m))
        * ringRadius m ^ m := by ring

theorem ringWeight_zero : ringWeight l 0 = 1 := by
  rw [ringWeight_eq]
  simp [ringS, ringSeed]

theorem ringWeight_le_bound {l : ℝ} (hl : 0 < l) (m : ℕ) : ringWeight l m ≤ ringWeightBound l := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ringWeight_zero]; exact one_le_ringWeightBound hl
    · have hK0 : 0 ≤ ringWeightBound l := by linarith [one_le_ringWeightBound hl]
      have h := ringWeight_step_le (l := l)
        (fun N hN => ih N (Nat.mem_properDivisors.mp hN).2) hK0
      have h1 := mul_exp_neg_two_sqrt_le_half m
      have h2 := exp_seed_cost_le hl m
      have e : ringWeightBound l * m * Real.exp (-(2 * Real.sqrt m))
          = ringWeightBound l * (m * Real.exp (-(2 * Real.sqrt m))) := by ring
      rw [e] at h
      have h3 : ringWeightBound l * (m * Real.exp (-(2 * Real.sqrt m))) ≤ ringWeightBound l * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 hK0
      unfold ringWeightBound at *
      linarith

/-- The summable majorant of the weights. -/
theorem ringWeight_le_majorant {l : ℝ} (hl : 0 < l) (m : ℕ) :
    ringWeight l m ≤ ringWeightBound l * (45 / 4) / (m : ℝ) ^ (2 : ℕ)
      + Real.exp (25 / (2 * l)) * Real.exp (-(l / 2)) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ringWeight_zero]
    have h1 : (0 : ℝ) ≤ ringWeightBound l * (45 / 4) / ((0 : ℕ) : ℝ) ^ (2 : ℕ) := by
      have := one_le_ringWeightBound hl; positivity
    have h2 : 1 ≤ Real.exp (25 / (2 * l)) := Real.one_le_exp (by positivity)
    simp only [pow_zero, mul_one]
    linarith
  · have hK0 : 0 ≤ ringWeightBound l := by linarith [one_le_ringWeightBound hl]
    have h := ringWeight_step_le (l := l) (m := m)
      (fun N _ => ringWeight_le_bound hl N) hK0
    have hgeom := exp_seed_cost_le_geom hl m
    have hE := cube_le_exp_two_sqrt m
    have hEpos := Real.exp_pos (2 * Real.sqrt m)
    have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h4 : Real.exp (-(2 * Real.sqrt m)) ≤ 720 / (64 * (m : ℝ) ^ (3 : ℕ)) := by
      rw [Real.exp_neg, inv_le_comm₀ hEpos (by positivity), inv_div]
      exact hE
    have h5 : ringWeightBound l * m * Real.exp (-(2 * Real.sqrt m))
        ≤ ringWeightBound l * (45 / 4) / (m : ℝ) ^ (2 : ℕ) := by
      calc ringWeightBound l * m * Real.exp (-(2 * Real.sqrt m))
          ≤ ringWeightBound l * m * (720 / (64 * (m : ℝ) ^ (3 : ℕ))) := by gcongr
        _ = ringWeightBound l * (45 / 4) / (m : ℝ) ^ (2 : ℕ) := by
            have hm' : (m : ℝ) ≠ 0 := by positivity
            field_simp
            ring
    linarith

theorem summable_ringWeight {l : ℝ} (hl : 0 < l) : Summable (ringWeight l) := by
  have h1 : Summable fun m : ℕ => ringWeightBound l * (45 / 4) / (m : ℝ) ^ (2 : ℕ) := by
    have := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left
      (ringWeightBound l * (45 / 4))
    refine this.congr fun m => ?_
    rw [mul_one_div]
  have h2 : Summable fun m : ℕ => Real.exp (25 / (2 * l)) * Real.exp (-(l / 2)) ^ m := by
    refine (summable_geometric_of_lt_one (Real.exp_pos _).le ?_).mul_left _
    rw [Real.exp_lt_one_iff]  -- placeholder
    linarith
  exact Summable.of_nonneg_of_le (fun m => (ringWeight_pos m).le)
    (fun m => ringWeight_le_majorant hl m) (h1.add h2)

/-! ## The nodes -/

/-- The rotation offset of ring `N`: `1` if rotated, `0` otherwise. -/
def ringOffset (l : ℝ) (N : ℕ) : ℝ := if ringFlag l N then 1 else 0

/-- The node `j` of ring `N`: `ρ_N e^{iπ(s_N + 2j)/N}`. -/
def ringNode (l : ℝ) (i : Σ N : ℕ, Fin N) : ℂ :=
  (ringRadius i.1 : ℂ)
    * Complex.exp (((Real.pi * (ringOffset l i.1 + 2 * (i.2 : ℕ)) / i.1 : ℝ) : ℂ) * I)

/-- The weight of a node of ring `N`: `c_N / N`. -/
def ringNodeWeight (l : ℝ) (i : Σ N : ℕ, Fin N) : ℝ := ringWeight l i.1 / i.1

theorem norm_ringNode (i : Σ N : ℕ, Fin N) : ‖ringNode l i‖ = ringRadius i.1 := by
  rw [ringNode, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (ringRadius_pos _)]

theorem norm_ringNode_lt_one (i : Σ N : ℕ, Fin N) : ‖ringNode l i‖ < 1 := by
  rw [norm_ringNode]
  exact ringRadius_lt_one (Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h => by
    have := i.2; rw [h] at this; exact this.elim0))

theorem ringNodeWeight_pos (i : Σ N : ℕ, Fin N) : 0 < ringNodeWeight l i := by
  have hN : 0 < i.1 := Nat.pos_of_ne_zero fun h => by
    have := i.2; rw [h] at this; exact this.elim0
  exact div_pos (ringWeight_pos _) (by exact_mod_cast hN)

/-- The phase factor of ring `N` at exponent `m` equals the sign when `N ∣ m`. -/
theorem ringPhase_eq {N m : ℕ} (hN : 0 < N) (hdvd : N ∣ m) :
    Complex.exp (((Real.pi * ringOffset l N * m / N : ℝ) : ℂ) * I)
      = (ringSign (ringFlag l N) N m : ℂ) := by
  obtain ⟨k, rfl⟩ := hdvd
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold ringOffset ringSign
  rw [Nat.mul_div_cancel_left k hN]
  by_cases hf : ringFlag l N
  · rw [if_pos hf, if_pos hf]
    have e : ((Real.pi * 1 * ((N * k : ℕ) : ℝ) / N : ℝ) : ℂ) * I = (k : ℂ) * (Real.pi * I) := by
      push_cast
      field_simp
      try ring
    rw [e, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    push_cast
    ring
  · rw [if_neg hf, if_neg hf]
    simp

/-- The geometric sum over the `N`-th roots of unity. -/
theorem sum_rootsOfUnity_pow {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ∑ j ∈ Finset.range N, Complex.exp (((2 * Real.pi * m * j / N : ℝ) : ℂ) * I)
      = if N ∣ m then (N : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * I / N) with hζ
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hterm : ∀ j : ℕ, Complex.exp (((2 * Real.pi * m * j / N : ℝ) : ℂ) * I) = (ζ ^ m) ^ j := by
    intro j
    rw [hζ, ← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    try ring
  simp_rw [hterm]
  by_cases hdvd : N ∣ m
  · have h1 : ζ ^ m = 1 := (hprim.pow_eq_one_iff_dvd m).mpr hdvd
    rw [if_pos hdvd]
    simp [h1]
  · have h1 : ζ ^ m ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd m).mp h)
    rw [if_neg hdvd, geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow,
      sub_self, zero_div]

/-- The power sum of ring `N` at exponent `m`. -/
theorem ring_powerSum {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ∑ j : Fin N, (ringNodeWeight l ⟨N, j⟩ : ℂ) * ringNode l ⟨N, j⟩ ^ m
      = if N ∣ m then ((ringWeight l N * ringRadius N ^ m * ringSign (ringFlag l N) N m : ℝ) : ℂ)
        else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsplit : ∀ j : Fin N, (ringNodeWeight l ⟨N, j⟩ : ℂ) * ringNode l ⟨N, j⟩ ^ m
      = (ringWeight l N / N : ℂ) * (ringRadius N : ℂ) ^ m
        * Complex.exp (((Real.pi * ringOffset l N * m / N : ℝ) : ℂ) * I)
        * Complex.exp (((2 * Real.pi * m * (j : ℕ) / N : ℝ) : ℂ) * I) := by
    intro j
    have e1 : Complex.exp ((m : ℂ) * ((((Real.pi * (ringOffset l N + 2 * (j : ℕ)) / N : ℝ)) : ℂ) * I))
        = Complex.exp (((Real.pi * ringOffset l N * m / N : ℝ) : ℂ) * I)
          * Complex.exp (((2 * Real.pi * m * (j : ℕ) / N : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      try ring
    simp only [ringNodeWeight, ringNode]
    rw [mul_pow, ← Complex.exp_nat_mul, e1]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => Complex.exp (((2 * Real.pi * m * j / N : ℝ) : ℂ) * I)) N,
    sum_rootsOfUnity_pow hN m]
  by_cases hdvd : N ∣ m
  · rw [if_pos hdvd, if_pos hdvd, ringPhase_eq hN hdvd]
    push_cast
    field_simp
    try ring
  · rw [if_neg hdvd, if_neg hdvd, mul_zero]

/-! ## The total power sum -/

theorem summable_ringNodeWeight {l : ℝ} (hl : 0 < l) : Summable (ringNodeWeight l) := by
  refine (summable_sigma_of_nonneg fun i => (ringNodeWeight_pos i).le).mpr
    ⟨fun N => Summable.of_finite, ?_⟩
  have h : ∀ N : ℕ, ∑' j : Fin N, ringNodeWeight l ⟨N, j⟩ ≤ ringWeight l N := by
    intro N
    rw [tsum_fintype]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact (ringWeight_pos 0).le
    · simp only [ringNodeWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hN.ne')]
  exact Summable.of_nonneg_of_le (fun N => tsum_nonneg fun j => (ringNodeWeight_pos _).le) h
    (summable_ringWeight hl)

theorem summable_powerSum {l : ℝ} (hl : 0 < l) (m : ℕ) :
    Summable fun i : (Σ N : ℕ, Fin N) => (ringNodeWeight l i : ℂ) * ringNode l i ^ m := by
  refine Summable.of_norm_bounded (summable_ringNodeWeight hl) fun i => ?_
  rw [norm_mul, norm_pow, norm_ringNode, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ringNodeWeight_pos i)]
  exact mul_le_of_le_one_right (ringNodeWeight_pos i).le
    (pow_le_one₀ (ringRadius_pos _).le (ringRadius_le_one _))

/-- The total power sum equals the real ring total. -/
theorem tsum_powerSum {l : ℝ} (hl : 0 < l) (m : ℕ) (hm : 1 ≤ m) :
    ∑' i : (Σ N : ℕ, Fin N), (ringNodeWeight l i : ℂ) * ringNode l i ^ m = (ringTotal l m : ℂ) := by
  have hs := summable_powerSum hl m
  have hsig := hs.hasSum.sigma
    (fun N => hasSum_fintype fun j : Fin N => (ringNodeWeight l ⟨N, j⟩ : ℂ) * ringNode l ⟨N, j⟩ ^ m)
  rw [← hsig.tsum_eq]
  rw [tsum_eq_sum (s := Nat.divisors m) fun N hN => ?_]
  · rw [ringTotal, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun N hN => ?_
    have hN0 : 0 < N := Nat.pos_of_mem_divisors hN
    rw [ring_powerSum hN0 m, if_pos (Nat.dvd_of_mem_divisors hN)]
  · rcases Nat.eq_zero_or_pos N with rfl | hN0
    · simp
    · rw [ring_powerSum hN0 m, if_neg]
      intro hdvd
      exact hN (Nat.mem_divisors.mpr ⟨hdvd, by omega⟩)

/-- **A positive configuration with non-attained top modulus and geometrically small power
sums.**  For every rate `l > 0`: positive summable weights on nodes inside the unit disc, moduli
accumulating at `1` without attaining it, and power sums of modulus at most `e^{−lm}` for every
`m ≥ 1`. -/
theorem exists_positive_configuration_powerSums_le {l : ℝ} (hl : 0 < l) :
    ∃ (w : (Σ N : ℕ, Fin N) → ℝ) (z : (Σ N : ℕ, Fin N) → ℂ),
      (∀ i, 0 < w i) ∧ Summable w ∧ (∀ i, ‖z i‖ < 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ i, 1 - ε < ‖z i‖) ∧
      ∀ m : ℕ, 1 ≤ m → ‖∑' i, (w i : ℂ) * z i ^ m‖ ≤ Real.exp (-(l * m)) := by
  refine ⟨ringNodeWeight l, ringNode l, ringNodeWeight_pos, summable_ringNodeWeight hl,
    norm_ringNode_lt_one, ?_, ?_⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (25 / ε ^ (2 : ℕ))
    have h25 : (0 : ℝ) < 25 / ε ^ (2 : ℕ) := by positivity
    have hN0 : 0 < N := by exact_mod_cast (lt_trans h25 hN)
    refine ⟨⟨N, ⟨0, hN0⟩⟩, ?_⟩
    rw [norm_ringNode]
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN0)
    have h1 : 1 - 5 / Real.sqrt N ≤ ringRadius N := Real.one_sub_le_exp_neg _
    have h2 : 5 / Real.sqrt N < ε := by
      rw [div_lt_iff₀ hsN]
      have h3 : 25 < ε ^ (2 : ℕ) * N := by
        rw [div_lt_iff₀ (by positivity)] at hN; linarith
      have h4 : (5 : ℝ) ^ (2 : ℕ) < (ε * Real.sqrt N) ^ (2 : ℕ) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; linarith
      exact (pow_lt_pow_iff_left₀ (by norm_num) (by positivity) two_ne_zero).mp h4
    linarith
  · intro m hm
    rw [tsum_powerSum hl m hm, Complex.norm_real, Real.norm_eq_abs]
    exact abs_ringTotal_le m hm

/-- **Scaled form.**  For every `R > 1` there is a positive configuration with all moduli below
`R`, moduli accumulating at `R`, and all power sums of modulus at most `1`. -/
theorem exists_positive_configuration_bounded_powerSums {R : ℝ} (hR : 1 < R) :
    ∃ (w : (Σ N : ℕ, Fin N) → ℝ) (z : (Σ N : ℕ, Fin N) → ℂ),
      (∀ i, 0 < w i) ∧ Summable w ∧ (∀ i, ‖z i‖ < R) ∧
      (∀ ε : ℝ, 0 < ε → ∃ i, R - ε < ‖z i‖) ∧
      ∀ m : ℕ, 1 ≤ m → ‖∑' i, (w i : ℂ) * z i ^ m‖ ≤ 1 := by
  have hl : 0 < Real.log R := Real.log_pos hR
  obtain ⟨w, z, hw, hws, hz, hacc, hsum⟩ := exists_positive_configuration_powerSums_le hl
  have hR0 : 0 < R := by linarith
  refine ⟨w, fun i => (R : ℂ) * z i, hw, hws, fun i => ?_, fun ε hε => ?_, fun m hm => ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have := hz i
    nlinarith
  · obtain ⟨i, hi⟩ := hacc (ε / R) (by positivity)
    refine ⟨i, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have : R * (1 - ε / R) = R - ε := by field_simp
    nlinarith
  · have e : ∑' i, (w i : ℂ) * ((R : ℂ) * z i) ^ m = (R : ℂ) ^ m * ∑' i, (w i : ℂ) * z i ^ m := by
      rw [← tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have h := hsum m hm
    have hRm : R ^ m * Real.exp (-(Real.log R * m)) = 1 := by
      rw [mul_comm (Real.log R), Real.exp_neg, Real.exp_nat_mul, Real.exp_log hR0]
      exact mul_inv_cancel₀ (pow_pos hR0 m).ne'
    calc R ^ m * ‖∑' i, (w i : ℂ) * z i ^ m‖ ≤ R ^ m * Real.exp (-(Real.log R * m)) :=
          mul_le_mul_of_nonneg_left h (pow_pos hR0 m).le
      _ = 1 := hRm

end

end RHTower
