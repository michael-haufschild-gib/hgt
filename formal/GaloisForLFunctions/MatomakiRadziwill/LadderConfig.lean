import GaloisForLFunctions.MatomakiRadziwill.LadderSequence

/-!
# The ladder configuration for given `L = log h` and `X`

The top scale is `exp((log X)^{0.93}) < p ≤ exp((log X)^{0.96})` (`topScale`).  The ladder scales are
`e^{a_j} < p ≤ e^{b_j}` for the `j` below `J = min{j : b_j > (log X)^{0.93}}` (`ladderJ`), and empty
beyond (`ladderScale`); they are pairwise disjoint and disjoint from the top scale because
`b_i < a_{i+1} ≤ a_j` for `i < j` and `b_j ≤ (log X)^{0.93}` for `j < J` (`ladderConfig`).
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem seqA_mono {L : ℝ} (hL : 2 ^ 20 ≤ L) {i j : ℕ} (hij : i ≤ j) : seqA L i ≤ seqA L j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have h1 := seqA_add_one_le_seqB hL j
    have h2 := seqB_lt_seqA_succ (by linarith : (2 : ℝ) ≤ L) j
    linarith

theorem seqB_lt_seqA {L : ℝ} (hL : 2 ^ 20 ≤ L) {i j : ℕ} (hij : i < j) : seqB L i < seqA L j :=
  lt_of_lt_of_le (seqB_lt_seqA_succ (by linarith) i) (seqA_mono hL hij)

theorem seqB_mono {L : ℝ} (hL : 2 ^ 20 ≤ L) {i j : ℕ} (hij : i ≤ j) : seqB L i ≤ seqB L j := by
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · have h1 := seqB_lt_seqA hL h
    have h2 := seqA_add_one_le_seqB hL j
    linarith

/-- The exponent bounding the ladder: `(log X)^{0.93}`. -/
def ladderTopLow (X : ℝ) : ℝ := Real.log X ^ (93 / 100 : ℝ)

/-- The top of the top scale: `(log X)^{0.96}`. -/
def ladderTopHigh (X : ℝ) : ℝ := Real.log X ^ (96 / 100 : ℝ)

theorem exists_seqB_gt {L : ℝ} (hL : 2 ^ 20 ≤ L) (y : ℝ) : ∃ j, y < seqB L j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (max y 0 / (L / 2) + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_⟩
  have hb := seqB_ge (by linarith : (2 : ℝ) ≤ L) j
  have hL2 : 0 < L / 2 := by linarith
  have h1 : max y 0 < 2 ^ j * (L / 2) := by
    have : max y 0 / (L / 2) < 2 ^ j := by linarith
    rwa [div_lt_iff₀ hL2] at this
  linarith [le_max_left y 0]

/-- The number of ladder scales: the least `J` with `b_J > (log X)^{0.93}`. -/
def ladderJ {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) : ℕ :=
  Nat.find (exists_seqB_gt hL (ladderTopLow X))

theorem seqB_le_of_lt_ladderJ {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) {j : ℕ} (hj : j < ladderJ hL X) :
    seqB L j ≤ ladderTopLow X :=
  le_of_not_gt (Nat.find_min (exists_seqB_gt hL (ladderTopLow X)) hj)

theorem lt_seqB_ladderJ {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) :
    ladderTopLow X < seqB L (ladderJ hL X) :=
  Nat.find_spec (exists_seqB_gt hL (ladderTopLow X))

/-- The ladder scale `j` (empty from `J` on). -/
def ladderScale {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) (j : ℕ) : Finset ℕ :=
  if j < ladderJ hL X then primesIoc ⌊Real.exp (seqA L j)⌋₊ ⌊Real.exp (seqB L j)⌋₊ else ∅

/-- The top scale. -/
def topScale (X : ℝ) : Finset ℕ :=
  primesIoc ⌊Real.exp (ladderTopLow X)⌋₊ ⌊Real.exp (ladderTopHigh X)⌋₊

theorem mem_primesIoc {M N p : ℕ} : p ∈ primesIoc M N ↔ M < p ∧ p ≤ N ∧ p.Prime := by
  rw [primesIoc, mem_filter, mem_Ioc, and_assoc]

/-- Primes of two intervals separated by `y ≤ z` are distinct. -/
theorem disjoint_primesIoc_exp {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint (primesIoc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊) (primesIoc ⌊Real.exp c⌋₊ ⌊Real.exp d⌋₊) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_primesIoc] at hp hp'
  have : ⌊Real.exp b⌋₊ ≤ ⌊Real.exp c⌋₊ := Nat.floor_le_floor (Real.exp_le_exp.mpr hbc)
  omega

/-- **The ladder configuration.** -/
def ladderConfig {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) : LadderScales where
  scale := ladderScale hL X
  top := topScale X
  J := ladderJ hL X
  prime_scale := by
    intro j p hp
    unfold ladderScale at hp
    split_ifs at hp
    · exact (mem_primesIoc.mp hp).2.2
    · simp at hp
  prime_top := fun p hp => (mem_primesIoc.mp hp).2.2
  disjoint_scale := by
    intro i j hij
    unfold ladderScale
    split_ifs with hi hj
    · rcases lt_or_gt_of_ne hij with h | h
      · exact disjoint_primesIoc_exp (seqB_lt_seqA hL h).le
      · exact (disjoint_primesIoc_exp (seqB_lt_seqA hL h).le).symm
    · exact Finset.disjoint_empty_right _
    · exact Finset.disjoint_empty_left _
    · exact Finset.disjoint_empty_left _
  disjoint_top := by
    intro j
    unfold ladderScale topScale
    split_ifs with hj
    · exact disjoint_primesIoc_exp (seqB_le_of_lt_ladderJ hL X hj)
    · exact Finset.disjoint_empty_left _

/-- The primes of scale `j < J` lie in `(e^{a_j}, e^{b_j}]`. -/
theorem mem_ladderScale_bounds {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) {j p : ℕ}
    (hp : p ∈ ladderScale hL X j) :
    Real.exp (seqA L j) ≤ p ∧ (p : ℝ) ≤ Real.exp (seqB L j) := by
  unfold ladderScale at hp
  split_ifs at hp
  · obtain ⟨h1, h2, -⟩ := mem_primesIoc.mp hp
    exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h1 |>.le,
      le_trans (Nat.cast_le.mpr h2) (Nat.floor_le (Real.exp_pos _).le)⟩
  · simp at hp

theorem mem_topScale_bounds {X : ℝ} {p : ℕ} (hp : p ∈ topScale X) :
    Real.exp (ladderTopLow X) ≤ p ∧ (p : ℝ) ≤ Real.exp (ladderTopHigh X) := by
  obtain ⟨h1, h2, -⟩ := mem_primesIoc.mp hp
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h1 |>.le,
    le_trans (Nat.cast_le.mpr h2) (Nat.floor_le (Real.exp_pos _).le)⟩

end

end GaloisForLFunctions.MatomakiRadziwill
