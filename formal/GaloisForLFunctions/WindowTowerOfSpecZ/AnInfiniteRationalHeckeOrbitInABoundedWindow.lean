import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Infinite rational Hecke orbits in a bounded interval

Doubling below three and dividing by three above it preserves `[1,6)`.
The two-adic valuation rules out every finite invariant set: maximize the
valuation and then minimize the vertex. The orbit of one is therefore infinite.
-/

namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- A Hecke step that stays in the interval from one to six. -/
def heckeSixStep (q : ℚ) : ℚ := if q < 3 then 2 * q else q / 3

theorem heckeSixStep_bounds {q : ℚ} (hq : 1 ≤ q ∧ q < 6) :
    1 ≤ heckeSixStep q ∧ heckeSixStep q < 6 := by
  unfold heckeSixStep
  split_ifs with h
  · constructor <;> linarith only [hq.1, h]
  · constructor <;> linarith only [hq.1, hq.2, le_of_not_gt h]

/-- Every finite nonempty set in `[1,6)` has an outgoing Hecke edge. -/
theorem exists_heckeSixStep_not_mem (S : Finset ℚ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, 1 ≤ q ∧ q < 6) :
    ∃ q ∈ S, heckeSixStep q ∉ S := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hthree : padicValRat 2 (3 : ℚ) = 0 := by
    change padicValRat 2 ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 3)]
    rfl
  obtain ⟨r, hr, hmax⟩ := S.exists_max_image (padicValRat 2) hne
  let T := S.filter fun q => padicValRat 2 q = padicValRat 2 r
  have hT : T.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  let q := T.min' hT
  have hqT : q ∈ T := T.min'_mem hT
  obtain ⟨hqS, hval⟩ := Finset.mem_filter.mp hqT
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (hS q hqS).1
  refine ⟨q, hqS, ?_⟩
  intro hm
  by_cases hq3 : q < 3
  · rw [heckeSixStep, if_pos hq3] at hm
    have hh := hmax (2 * q) hm
    rw [padicValRat.mul (by norm_num) hq0.ne', htwo, hval] at hh
    omega
  · rw [heckeSixStep, if_neg hq3] at hm
    have hdiv : padicValRat 2 (q / 3) = padicValRat 2 r := by
      rw [padicValRat.div hq0.ne' (by norm_num), hthree, sub_zero, hval]
    have hmT : q / 3 ∈ T := Finset.mem_filter.mpr ⟨hm, hdiv⟩
    have hh : q ≤ q / 3 := T.min'_le _ hmT
    linarith only [hh, hq0]

/-- The bounded Hecke orbit of a rational starting point. -/
def heckeSixOrbit (start : ℚ) : ℕ → ℚ
  | 0 => start
  | n + 1 => heckeSixStep (heckeSixOrbit start n)

theorem heckeSixOrbit_bounds {start : ℚ} (hstart : 1 ≤ start ∧ start < 6) (n : ℕ) :
    1 ≤ heckeSixOrbit start n ∧ heckeSixOrbit start n < 6 := by
  induction n with
  | zero => exact hstart
  | succ n ih => exact heckeSixStep_bounds ih

theorem heckeSixOrbit_edge (start : ℚ) (n : ℕ) :
    heckeSixOrbit start (n + 1) = 2 * heckeSixOrbit start n ∨
      heckeSixOrbit start n = 3 * heckeSixOrbit start (n + 1) := by
  rw [heckeSixOrbit, heckeSixStep]
  split_ifs
  · exact Or.inl rfl
  · right
    ring

/-- Every starting point in the interval has infinitely many rational vertices
connected to it by allowed Hecke edges inside that same interval. -/
theorem heckeSixOrbit_infinite {start : ℚ} (hstart : 1 ≤ start ∧ start < 6) :
    (Set.range (heckeSixOrbit start)).Infinite := by
  intro hfin
  let S := hfin.toFinset
  have hne : S.Nonempty := ⟨heckeSixOrbit start 0, hfin.mem_toFinset.mpr ⟨0, rfl⟩⟩
  have hS : ∀ q ∈ S, 1 ≤ q ∧ q < 6 := by
    intro q hq
    obtain ⟨n, rfl⟩ := hfin.mem_toFinset.mp hq
    exact heckeSixOrbit_bounds hstart n
  obtain ⟨q, hq, hout⟩ := exists_heckeSixStep_not_mem S hne hS
  obtain ⟨n, rfl⟩ := hfin.mem_toFinset.mp hq
  exact hout (hfin.mem_toFinset.mpr ⟨n + 1, rfl⟩)

/-- A finite graph cannot contain one and be closed under the active Hecke
neighbours throughout `[1,6)`. Only ratios two and three are needed. -/
theorem no_finite_hecke_template_at_six :
    ¬ ∃ T : Finset ℚ, 1 ∈ T ∧ ∀ q ∈ T, ∀ s : ℚ,
      1 ≤ s → s < 6 → s = 2 * q ∨ q = 3 * s → s ∈ T := by
  rintro ⟨T, h1, hclosed⟩
  have hstart : (1 : ℚ) ≤ 1 ∧ (1 : ℚ) < 6 := by norm_num
  have hmem : ∀ n, heckeSixOrbit 1 n ∈ T := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      exact hclosed _ ih _ (heckeSixOrbit_bounds hstart (n + 1)).1
        (heckeSixOrbit_bounds hstart (n + 1)).2 (heckeSixOrbit_edge 1 n)
  apply heckeSixOrbit_infinite hstart
  exact T.finite_toSet.subset (by rintro q ⟨n, rfl⟩; exact hmem n)

#print axioms exists_heckeSixStep_not_mem
#print axioms heckeSixOrbit_infinite
#print axioms no_finite_hecke_template_at_six

end GaloisForLFunctions.WindowTowerOfSpecZ
