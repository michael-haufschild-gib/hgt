import GaloisForLFunctions.RHTower.EulerDeletionDiscreteDevelopment
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondShadow
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# One infinite carrier for all chronological arithmetic words

Two genuinely noncommuting prefix operators act on bounded real functions of finite Boolean
words. Their real/imaginary linear combination retains each complex jump injectively. Products
of the literal discrete factors recover every strict iterated word coefficient exactly; the
last-in-time letter is first in the stored word.

For each fixed deletion modulus and each `Re s > 1/2`, one operator-norm limit simultaneously
completes all word lengths. The error is uniform over every finite word, not just each fixed
length. Actual zeta zeros close the first level of this same history by the previously proved
arithmetic zero-landing theorem. Neither higher-level vanishing, cross-modulus coherence, nor
critical-line selection is asserted. No diagonalization or spectral argument is used.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.ArithmeticWordHistory
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel
open scoped BoundedContinuousFunction

abbrev Word := List Bool
local instance : TopologicalSpace Word := ⊥
local instance : DiscreteTopology Word := ⟨rfl⟩
abbrev Carrier := Word →ᵇ ℝ
abbrev End := Carrier →L[ℝ] Carrier

local instance : Nontrivial Carrier := ⟨⟨0, 1, by
  intro h
  have he := congrArg (fun f : Carrier => f ([] : Word)) h
  simp at he⟩⟩
local instance : NormedRing End := inferInstance
local instance : NormedAlgebra ℝ End := inferInstance

def prefixMap (b : Bool) : C(Word, Word) :=
  ⟨fun w => b :: w, continuous_of_discreteTopology⟩

def letter (b : Bool) : End where
  toFun f := f.compContinuous (prefixMap b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := BoundedContinuousFunction.continuous_compContinuous _

theorem letter_apply (b : Bool) (f : Carrier) (w : Word) :
    letter b f w = f (b :: w) := rfl

def phaseLetters : ℂ →L[ℝ] End :=
  Complex.reCLM.smulRight (letter false) + Complex.imCLM.smulRight (letter true)

theorem phaseLetters_apply (z : ℂ) (f : Carrier) (w : Word) :
    phaseLetters z f w = z.re * f (false :: w) + z.im * f (true :: w) := rfl

def wordTest (w : Word) : Carrier :=
  BoundedContinuousFunction.mkOfDiscrete (fun v => if v = w then 1 else 0) 1 (by
    intro v u
    split_ifs <;> simp)

theorem wordTest_apply (w v : Word) : wordTest w v = if v = w then 1 else 0 := rfl

def component (z : ℂ) (b : Bool) : ℝ := if b then z.im else z.re

theorem phaseLetters_wordTest_nil (z : ℂ) : phaseLetters z (wordTest []) = 0 := by
  ext w
  simp [phaseLetters_apply, wordTest_apply]

theorem phaseLetters_wordTest_cons (z : ℂ) (b : Bool) (w : Word) :
    phaseLetters z (wordTest (b :: w)) = component z b • wordTest w := by
  ext v
  cases b <;> simp [phaseLetters_apply, wordTest_apply, component, List.cons.injEq]

theorem phaseLetters_injective : Function.Injective phaseLetters := by
  intro z t h
  have hx := congrArg (fun T : End => T (wordTest [false]) []) h
  have hy := congrArg (fun T : End => T (wordTest [true]) []) h
  apply Complex.ext
  · simpa [phaseLetters_apply, wordTest_apply] using hx
  · simpa [phaseLetters_apply, wordTest_apply] using hy

theorem letters_do_not_commute : letter false * letter true ≠ letter true * letter false := by
  intro h
  have he := congrArg (fun T : End => T (wordTest [true, false]) []) h
  simp only [mul_apply_eq_comp, letter_apply, wordTest_apply] at he
  simp at he

/-- The last-in-time letter is first in the word. -/
def iteratedWordPrefix (z : ℕ → ℂ) : ℕ → Word → ℝ
  | 0, w => if w = [] then 1 else 0
  | _+1, [] => 1
  | N+1, b :: w => iteratedWordPrefix z N (b :: w) +
      component (z N) b * iteratedWordPrefix z N w

theorem iteratedWordPrefix_nil (z : ℕ → ℂ) (N : ℕ) : iteratedWordPrefix z N [] = 1 := by
  cases N <;> rfl

theorem iteratedWordPrefix_singleton (z : ℕ → ℂ) (N : ℕ) (b : Bool) :
    iteratedWordPrefix z N [b] = ∑ n ∈ Finset.range N, component (z n) b := by
  induction N with
  | zero => simp [iteratedWordPrefix]
  | succ N ih => simp only [iteratedWordPrefix, iteratedWordPrefix_nil, mul_one,
      Finset.sum_range_succ, ih]

theorem orderedProduct_wordTest (z : ℕ → ℂ) (N : ℕ) (w : Word) :
    orderedProduct (fun n => (1 : End) + phaseLetters (z n)) N (wordTest w) [] =
      iteratedWordPrefix z N w := by
  induction N generalizing w with
  | zero => simp [orderedProduct, iteratedWordPrefix, wordTest_apply, eq_comm]
  | succ N ih =>
    cases w with
    | nil =>
      simp only [orderedProduct, mul_apply_eq_comp, add_apply,
        one_apply_eq_self, phaseLetters_wordTest_nil, add_zero, ih]
      cases N <;> rfl
    | cons b w =>
      simp only [orderedProduct, mul_apply_eq_comp, add_apply,
        one_apply_eq_self, phaseLetters_wordTest_cons, map_add, map_smul,
        BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
        ih, iteratedWordPrefix]

def literalJump (q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  realDeletionCoefficient q n • arithmeticDirichletWeight s n

theorem literalJump_eq_weightedJump (q : ℕ) (s : ℂ) (n : ℕ) :
    literalJump q s n = eulerDeletionWeightedJump q s n := by
  simp [literalJump, realDeletionCoefficient, arithmeticDirichletWeight,
    eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient, Algebra.smul_def]

def historyPrefix (q : ℕ) (s : ℂ) : ℕ → End :=
  eulerDeletionDiscreteDevelopment q s phaseLetters

def historyLimit (q : ℕ) (s : {z : ℂ // 1/2 < z.re}) : End :=
  Classical.choose (eulerDeletionDiscreteDevelopment_converges q s.property phaseLetters)

theorem historyPrefix_tendsto (q : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    Tendsto (historyPrefix q s.val) atTop (nhds (historyLimit q s)) :=
  Classical.choose_spec (eulerDeletionDiscreteDevelopment_converges q s.property phaseLetters)

def wordResponse (T : End) (w : Word) : ℝ := T (wordTest w) []

theorem norm_wordTest_le_one (w : Word) : ‖wordTest w‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro v
  simp only [wordTest_apply]
  split_ifs <;> simp

theorem wordResponse_sub_le (T U : End) (w : Word) :
    |wordResponse T w - wordResponse U w| ≤ ‖T - U‖ := by
  change ‖((T - U) (wordTest w)) ([] : Word)‖ ≤ _
  exact (((T - U) (wordTest w)).norm_coe_le_norm []).trans
    (((T - U).le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_left (norm_wordTest_le_one w) (norm_nonneg (T-U))))

theorem historyPrefix_wordResponse (q : ℕ) (s : ℂ) (N : ℕ) (w : Word) :
    wordResponse (historyPrefix q s N) w = iteratedWordPrefix (literalJump q s) N w := by
  simpa only [wordResponse, historyPrefix, eulerDeletionDiscreteDevelopment, literalJump,
    map_smul] using orderedProduct_wordTest (literalJump q s) N w

theorem wordResponse_continuous (w : Word) : Continuous (fun T : End => wordResponse T w) := by
  exact (BoundedContinuousFunction.evalCLM ℝ ([] : Word)).continuous.comp
    (ContinuousLinearMap.apply ℝ Carrier (wordTest w)).continuous

theorem every_wordResponse_tendsto (q : ℕ) (s : {z : ℂ // 1/2 < z.re}) (w : Word) :
    Tendsto (fun N => wordResponse (historyPrefix q s.val N) w) atTop
      (nhds (wordResponse (historyLimit q s) w)) :=
  (wordResponse_continuous w).tendsto _ |>.comp (historyPrefix_tendsto q s)

theorem every_iteratedWordPrefix_tendsto (q : ℕ) (s : {z : ℂ // 1/2 < z.re}) (w : Word) :
    Tendsto (fun N => iteratedWordPrefix (literalJump q s.val) N w) atTop
      (nhds (wordResponse (historyLimit q s) w)) := by
  simpa only [historyPrefix_wordResponse] using every_wordResponse_tendsto q s w

/-- One cutoff controls every word, without restricting its length. -/
theorem all_word_lengths_uniform (q : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ w : Word,
      |iteratedWordPrefix (literalJump q s.val) N w - wordResponse (historyLimit q s) w| < ε := by
  intro ε hε
  have ht : Tendsto (fun N => ‖historyPrefix q s.val N - historyLimit q s‖) atTop (nhds 0) := by
    simpa using ((historyPrefix_tendsto q s).sub_const (historyLimit q s)).norm
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨N₀, fun N hN w => ?_⟩
  rw [← historyPrefix_wordResponse]
  exact (wordResponse_sub_le _ _ _).trans_lt (hN₀ N hN)

/-- Actual arithmetic zeros close the first level of the same completed word history.
No higher-level vanishing follows from this statement. -/
theorem zeta_zero_closes_first_level (q : ℕ) (s : {z : ℂ // 1/2 < z.re})
    (hs1 : s.val ≠ 1) (hz : riemannZeta s.val = 0) (b : Bool) :
    wordResponse (historyLimit q s) [b] = 0 := by
  have ht := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero q
    (show 0 < s.val.re by linarith [s.property]) hs1 hz
  have hw := every_iteratedWordPrefix_tendsto q s [b]
  apply tendsto_nhds_unique hw
  simp only [iteratedWordPrefix_singleton, literalJump_eq_weightedJump]
  cases b
  · simpa [Function.comp_def, map_sum, component, Complex.reCLM_apply] using
      Complex.reCLM.continuous.tendsto (0 : ℂ) |>.comp ht
  · simpa [Function.comp_def, map_sum, component, Complex.imCLM_apply] using
      Complex.imCLM.continuous.tendsto (0 : ℂ) |>.comp ht

end RHTower.ArithmeticWordHistory

