/-
The exponents of the resonance counts, corrected.

The frontier object is evaluated at the single point `n = N`; the squarefree kernels run to
`D ≍ N^(2/3)`, so `√D ≍ N^(1/3)`; and a `√d`-class becomes coherent at resonance level
`ε ≍ N^(-1/3)`.  With these parameters the two counting bounds of the previous file evaluate as

    naive lattice count      `2εD + n√D`      →   `max(N^(1/3), N^(4/3))` = **N^(4/3)**
    refined count            `ε(D + n√D)`     →   `max(N^(1/3), N)`       = **N**

against a total of `N^(1/3)` classes.  **Both are vacuous**, the refined one by a factor `N^(2/3)`
less.  The dominant term in each case is the one involving `n√D`, not `εD`.

The refined count becomes non-vacuous only when `ε n √D ≤ N^(1/3)`, i.e. `ε ≤ N^(-1)`.  Since the
single-frequency bound gives `‖n√d‖ ≫ 1/(n√d) ≍ N^(-4/3)`, the counting has content only on
`ε ∈ [N^(-4/3), N^(-1)]`, while the class structure requires `ε ≍ N^(-1/3)` — **two full Farey orders
away**.

The structural reason is that the evaluation point `n ≍ N` vastly exceeds the frequency modulus
`√D ≍ N^(1/3)`: there is no averaging over `n` available, since the object is a single point of a
sequence whose mean is known.
-/
import GaloisForLFunctions.HTGeometry.SimultaneousResonanceCount

namespace HTGeometry

/-! ### The parameters -/

/-- Exponent of the evaluation point `n = N`. -/
def evalPointExponent : ℚ := 1

/-- Exponent of the range of squarefree kernels. -/
def kernelRangeExponent : ℚ := 2 / 3

/-- Exponent of `√D`. -/
def kernelRootExponent : ℚ := 1 / 3

/-- Exponent of the resonance level at which a class becomes coherent. -/
def classCoherenceLevel : ℚ := -(1 / 3)

theorem kernelRoot_is_half_range : kernelRootExponent = kernelRangeExponent / 2 := by
  unfold kernelRootExponent kernelRangeExponent; norm_num

/-! ### The two counts -/

/-- The naive lattice count's exponent: `max(ε D, n √D)`. -/
def naiveCountExponent : ℚ := evalPointExponent + kernelRootExponent

/-- **It is `4/3`.** -/
@[simp] theorem naiveCount_eq : naiveCountExponent = 4 / 3 := by
  unfold naiveCountExponent evalPointExponent kernelRootExponent; norm_num

/-- The refined count's exponent, with the square-root-modulo-`n²` input: `ε n √D`. -/
def refinedCountExponent : ℚ := classCoherenceLevel + evalPointExponent + kernelRootExponent

/-- **It is `1`.** -/
@[simp] theorem refinedCount_eq : refinedCountExponent = 1 := by
  unfold refinedCountExponent classCoherenceLevel evalPointExponent kernelRootExponent; norm_num

/-- **The refined count improves the naive one by a Farey order.** -/
theorem refined_beats_naive :
    naiveCountExponent - refinedCountExponent = fareyOrderExponent := by
  rw [naiveCount_eq, refinedCount_eq]
  unfold fareyOrderExponent; norm_num

/-! ### Both are vacuous -/

/-- **The naive count exceeds the number of classes by `1`.** -/
theorem naive_vacuous :
    classCountExponent < naiveCountExponent ∧
      naiveCountExponent - classCountExponent = 1 := by
  rw [naiveCount_eq]
  unfold classCountExponent
  constructor <;> norm_num

/-- **And the refined count exceeds it by `2/3`.** -/
theorem refined_vacuous :
    classCountExponent < refinedCountExponent ∧
      refinedCountExponent - classCountExponent = 2 / 3 := by
  rw [refinedCount_eq]
  unfold classCountExponent
  constructor <;> norm_num

/-! ### Where the counting would have content -/

/-- The resonance level at which the refined count becomes non-vacuous. -/
def nonVacuousResonanceLevel : ℚ := -1

/-- **It is exactly where `ε n √D = N^(1/3)`.** -/
theorem nonVacuous_level_eq :
    nonVacuousResonanceLevel + evalPointExponent + kernelRootExponent = classCountExponent := by
  unfold nonVacuousResonanceLevel evalPointExponent kernelRootExponent classCountExponent
  norm_num

/-- The floor imposed by the single-frequency bound `‖n√d‖ ≫ 1/(n√d)`. -/
def singleFrequencyFloor : ℚ := -(4 / 3)

/-- **The counting has content only on the window `[N^(-4/3), N^(-1)]`.** -/
theorem counting_window :
    singleFrequencyFloor < nonVacuousResonanceLevel ∧
      nonVacuousResonanceLevel - singleFrequencyFloor = fareyOrderExponent := by
  unfold singleFrequencyFloor nonVacuousResonanceLevel fareyOrderExponent
  constructor <;> norm_num

/-- **And the class structure needs a level two Farey orders above that window.** -/
theorem class_level_far_above :
    nonVacuousResonanceLevel < classCoherenceLevel ∧
      classCoherenceLevel - nonVacuousResonanceLevel = 2 * fareyOrderExponent := by
  unfold nonVacuousResonanceLevel classCoherenceLevel fareyOrderExponent
  constructor <;> norm_num

/-! ### The structural reason -/

/-- **The evaluation point exceeds the frequency modulus by two Farey orders.** -/
theorem evalPoint_exceeds_modulus :
    evalPointExponent - kernelRootExponent = 2 * fareyOrderExponent := by
  unfold evalPointExponent kernelRootExponent fareyOrderExponent; norm_num

/-- **Summary.**  Both elementary counts are vacuous; the refined one is better by one Farey order;
the counting window is `[N^(-4/3), N^(-1)]`; and the class structure needs `N^(-1/3)`, two Farey
orders above it. -/
theorem resonance_count_summary :
    naiveCountExponent = 4 / 3 ∧ refinedCountExponent = 1 ∧
      classCountExponent = 1 / 3 ∧
      classCoherenceLevel - nonVacuousResonanceLevel = 2 * fareyOrderExponent := by
  refine ⟨naiveCount_eq, refinedCount_eq, rfl, class_level_far_above.2⟩

end HTGeometry
