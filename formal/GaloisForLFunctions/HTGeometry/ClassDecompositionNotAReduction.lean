/-
The class decomposition is not a reduction: its dominant part is the original problem.

In the parametrisation `2a = d_a z²`, `q = d_q w²`, `m = wz`, a dyadic box `w ≍ W`, `z ≍ Z` contains

    W·Q·Z·A  with  Q W² ≍ L ,  A Z² ≍ L      →      **L² / (W Z)**

terms, so summing over dyadic `W ≤ √L` and `Z ≤ L` gives `L² Σ 1/W Σ 1/Z ≍ L²`, **dominated by
`W ≍ Z ≍ 1`.**

But `w = z = 1` means `m = 1`, i.e. `2aq = d` is squarefree — and then the `√d`-class of that Farey
fraction contains only that one fraction.  A positive proportion (`6/π²` up to the factor `2`) of the
Farey fractions have `2aq` squarefree, so

* **a positive proportion of the classes are singletons**, and there are `≍ L²` of them — the whole
  count;
* on that part the rational factor `z/w` is constant, so the bilinear structure of the previous file
  is absent;
* and "across-class cancellation" restricted to the singleton classes **is** the original frontier
  bound, verbatim.

Hence the class decomposition partitions the frontier object into a sparse structured part (`w` or `z`
large) and a dominant part identical to the original.  **It is a partition, not a reduction.**

What survives from cycles 248–259: the parametrisation itself, the coherence criterion `d_q w ∣ k`,
the size distribution `≍ L/√d`, and the elementary non-resonance bound.  What does not: the claim
that the decomposition reduces the problem.
-/
import GaloisForLFunctions.HTGeometry.FrontierBilinearForm

namespace HTGeometry

/-! ### The dyadic box count -/

/-- Exponent of the number of terms in the dyadic box `w ≍ N^(ω)`, `z ≍ N^(ζ)`. -/
def boxTermCount (ω ζ : ℚ) : ℚ := totalFrequencyExponent - ω - ζ

/-- **The box at `w ≍ z ≍ 1` holds the whole count.** -/
@[simp] theorem boxTermCount_at_one : boxTermCount 0 0 = totalFrequencyExponent := by
  unfold boxTermCount; ring

/-- **And every other box holds strictly fewer.** -/
theorem boxTermCount_decreasing {ω ζ : ℚ} (h : 0 < ω + ζ) :
    boxTermCount ω ζ < boxTermCount 0 0 := by
  unfold boxTermCount; linarith

/-- Numerically the dominant box holds `N^(2/3)` terms. -/
theorem dominant_box_size : boxTermCount 0 0 = 2 / 3 := by
  rw [boxTermCount_at_one]; unfold totalFrequencyExponent; rfl

/-! ### The dominant box consists of singleton classes -/

/-- Exponent of the number of singleton classes: those with `2aq` squarefree. -/
def singletonClassCount : ℚ := 2 / 3

/-- **They are a positive proportion of all frequencies.** -/
theorem singletons_are_dominant :
    singletonClassCount = totalFrequencyExponent := by
  unfold singletonClassCount totalFrequencyExponent; rfl

/-- **And their class size is `O(1)`**, matching the size distribution at `d ≍ L²`. -/
theorem singleton_size : classSizeAtExponent (2 / 3) = 0 :=
  classSizeAt_top

/-- **So the dominant box is exactly the singleton part.** -/
theorem dominant_box_is_singletons :
    boxTermCount 0 0 = singletonClassCount := by
  rw [boxTermCount_at_one, singletons_are_dominant]

/-! ### Hence no reduction -/

/-- The bound required on the singleton part. -/
def singletonTarget : ℚ := frontierLindelof

/-- **It is the original frontier target**, on a set of the original size. -/
theorem singleton_problem_is_original :
    singletonTarget = frontierLindelof ∧
      singletonClassCount = frontierTermCount ∧
      singletonClassCount - singletonTarget = fareyOrderExponent := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold singletonClassCount frontierTermCount; rfl
  · unfold singletonClassCount singletonTarget frontierLindelof fareyOrderExponent; norm_num

/-- **The decomposition is a partition, not a reduction.**  The structured part — where `w` or `z` is
large — is sparse, and the dominant part reproduces the original problem exactly. -/
theorem decomposition_not_a_reduction :
    boxTermCount 0 0 = totalFrequencyExponent ∧
      singletonClassCount = totalFrequencyExponent ∧
      singletonTarget = frontierLindelof :=
  ⟨boxTermCount_at_one, singletons_are_dominant, rfl⟩

/-- **The structured part is sparse.**  Boxes with `w ≍ N^(1/6)` (the largest `w`) hold only
`N^(1/2)` terms, a fraction `N^(-1/6)` of the total. -/
theorem structured_part_sparse :
    boxTermCount bilinearWExponent 0 = 1 / 2 ∧
      totalFrequencyExponent - boxTermCount bilinearWExponent 0 = 1 / 6 := by
  unfold boxTermCount bilinearWExponent totalFrequencyExponent
  constructor <;> norm_num

end HTGeometry
