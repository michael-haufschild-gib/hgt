import GaloisForLFunctions.HTGeometry.WeightedHistoryCompletionBoundaryLaw

/-!
# Relative weighted-history completion

Product completion admits infinite source histories even when their relaxed absolute action is
infinite.  The correct two-history object is relative: each completed history may have arbitrary
common infinite ancestry, while their transverse difference must come from a finite-action
finite-support history.

This file proves the first abstract rigidity law for that carrier.  Finite relative relaxed action
is exactly finite-support admission.  If the admitted transverse difference is invariant under
successor renewal, it vanishes.  No divisor, zero set, spectral operator, or target charge occurs in
the definitions.
-/

open scoped DirectSum ENNReal NNReal
open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [AddCommGroup K] [UniformSpace K] [T0Space K]
variable (Gamma : AddSubgroup K)

local instance relativeWeightedHistoryCompletionLocalInst1 : UniformSpace (⨁ _j : ℕ, Gamma) :=
  weightedHistoryUniformSpace (fun _ : ℕ => Gamma)

/-- A pair of completed histories is relatively restricted when its transverse difference comes
from one finite-support source history.  Each history separately may have infinite support. -/
def IsRelativeRestrictedHistory (x y : ℕ → K) : Prop :=
  x - y ∈ Set.range (weightedHistoryInclusion (fun _ : ℕ => Gamma))

/-- Relaxed source action of the transverse difference of two completed histories. -/
def WeightedHistoryDatum.relativeHistoryRelaxation
    [DecidableEq K]
    (D : WeightedHistoryDatum (fun _ : ℕ => Gamma)) (x y : ℕ → K) : ℝ≥0∞ :=
  D.weightedHistoryRelaxation (x - y)

omit [UniformSpace K] [T0Space K] in
@[simp]
theorem isRelativeRestrictedHistory_self (x : ℕ → K) :
    IsRelativeRestrictedHistory Gamma x x := by
  refine ⟨0, ?_⟩
  funext n
  change (((0 : ⨁ _j : ℕ, Gamma) n : Gamma) : K) = x n - x n
  simp

@[simp]
theorem WeightedHistoryDatum.relativeHistoryRelaxation_self
    [DecidableEq K]
    (D : WeightedHistoryDatum (fun _ : ℕ => Gamma)) (x : ℕ → K) :
    D.relativeHistoryRelaxation Gamma x x = 0 := by
  rw [relativeHistoryRelaxation]
  have hzero : x - x = weightedHistoryInclusion (fun _ : ℕ => Gamma) 0 := by
    funext n
    simp [weightedHistoryInclusion]
  rw [hzero, D.weightedHistoryRelaxation_eq_action]
  exact_mod_cast D.weightedHistoryAction_zero

/-- Finite relative relaxed action is exactly admission to the relative restricted completion. -/
theorem WeightedHistoryDatum.relativeHistoryRelaxation_ne_top_iff
    [DecidableEq K]
    (D : WeightedHistoryDatum (fun _ : ℕ => Gamma)) (x y : ℕ → K) :
    D.relativeHistoryRelaxation Gamma x y ≠ ⊤ ↔
      IsRelativeRestrictedHistory Gamma x y := by
  constructor
  · intro hfinite
    by_contra hnot
    exact hfinite (D.weightedHistoryRelaxation_eq_top_of_not_mem_range hnot)
  · rintro ⟨h, hh⟩
    rw [relativeHistoryRelaxation, ← hh, D.weightedHistoryRelaxation_eq_action]
    exact ENNReal.coe_ne_top

omit [UniformSpace K] [T0Space K] in
/-- A finite-support successor-invariant history is zero. -/
theorem directSum_eq_zero_of_successor_invariant
    (h : ⨁ _j : ℕ, Gamma)
    (hinv : ∀ n : ℕ,
      ((h (n + 1) : Gamma) : K) = ((h n : Gamma) : K)) :
    h = 0 := by
  classical
  obtain ⟨N, hsupport⟩ := h.support.exists_nat_subset_range
  have hN : N ∉ h.support := by
    intro hmem
    exact (Nat.lt_irrefl N) (Finset.mem_range.mp (hsupport hmem))
  have hzero : ((h N : Gamma) : K) = 0 := by
    have hz : h N = 0 := DFinsupp.notMem_support_iff.mp hN
    simp [hz]
  have hconst : ∀ n : ℕ, ((h n : Gamma) : K) = ((h 0 : Gamma) : K) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (hinv n).trans ih
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  rw [hconst n, ← hconst N, hzero]
  rfl

/-- **Relative renewal rigidity.**  Finite relative source action admits only a finite-support
transverse mismatch.  If literal successor renewal repeats that mismatch cofinally, it vanishes.
Common infinite history and every internal kernel coordinate remain unrestricted. -/
theorem WeightedHistoryDatum.eq_of_relativeHistoryRelaxation_ne_top_of_successor_invariant
    [DecidableEq K]
    (D : WeightedHistoryDatum (fun _ : ℕ => Gamma)) (x y : ℕ → K)
    (hfinite : D.relativeHistoryRelaxation Gamma x y ≠ ⊤)
    (hrenew : ∀ n : ℕ, (x - y) (n + 1) = (x - y) n) :
    x = y := by
  have hadmit :=
    (D.relativeHistoryRelaxation_ne_top_iff Gamma x y).mp hfinite
  rcases hadmit with ⟨h, hh⟩
  have hinv : ∀ n : ℕ,
      ((h (n + 1) : Gamma) : K) = ((h n : Gamma) : K) := by
    intro n
    have hs := congrFun hh (n + 1)
    have ht := congrFun hh n
    simpa [weightedHistoryInclusion] using hs.trans ((hrenew n).trans ht.symm)
  have hz := directSum_eq_zero_of_successor_invariant Gamma h hinv
  funext n
  have hn := congrFun hh n
  rw [hz] at hn
  simpa [weightedHistoryInclusion] using sub_eq_zero.mp hn.symm

end

end GaloisForLFunctions.HTGeometry
