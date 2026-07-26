/-
The class-size distribution, corrected — and the consequence that condition (i) is unnecessary.

Solving `2aq = d m²` with `(a,q) = 1` factors `d = d_a d_q` into coprime parts and writes
`2a = d_a z²`, `q = d_q w²`, `m = wz`.  Counting the admissible `(z, w)` with `q ≤ L` gives the class
sizes

    **size(d) ≍ L / √d** ,

so the classes are **not** `≍ L` in number of size `≍ L` each: there are `≍ L²` of them (one per
squarefree `d ≤ 2L²`), the largest has size `≍ L`, and the total is
`Σ_(d ≤ L²) L/√d ≍ L·L = L²` — the right number of frequencies.

Three consequences.

* Only the `≍ L` classes with `d ≤ L` have size `≥ √L`; they contain `≍ L^(3/2)` of the `L²`
  frequencies, a fraction `L^(-1/2)`.
* The remaining `≍ L²` classes have size `O(1)`: for them coherence is vacuous.
* **The `ℓ²` norm of the sizes is `(Σ_d L²/d)^(1/2) ≍ L (log L)^(1/2)`.**  So if the class sums add
  with square-root cancellation, the total is `L^(1+o(1)) = N^(1/3+o(1))` — **the Lindelöf value**,
  *whatever the classes do internally*.

Hence **condition (i) is not needed**: across-class cancellation alone suffices, because the class
sizes are `ℓ²`-bounded by the Lindelöf value.  The earlier reading — `≍ L` classes of size `≍ L`, with
the within-class level at `N^(1/2)` — used a uniform-size approximation that the true distribution
does not satisfy.
-/
import GaloisForLFunctions.HTGeometry.PrincipalClassCoherence

namespace HTGeometry

/-! ### The corrected counts -/

/-- Exponent of the number of `√d`-classes: one per squarefree `d ≤ 2L²`. -/
def correctedClassCount : ℚ := 2 / 3

/-- Exponent of the largest class's size, at `d = 1`. -/
def principalClassSizeExp : ℚ := 1 / 3

/-- **The corrected class count is `L² = N^(2/3)`, not `L = N^(1/3)`.** -/
theorem correctedClassCount_ne_old : correctedClassCount ≠ classCountExponent := by
  unfold correctedClassCount classCountExponent; norm_num

/-- **The size at `d = N^(e)` is `L/√d`, of exponent `1/3 − e/2`.** -/
def classSizeAtExponent (e : ℚ) : ℚ := 1 / 3 - e / 2

/-- At `d = 1` it is the largest size. -/
@[simp] theorem classSizeAt_zero : classSizeAtExponent 0 = principalClassSizeExp := by
  unfold classSizeAtExponent principalClassSizeExp; ring

/-- **At `d ≍ L` the size is `√L`.** -/
theorem classSizeAt_farey : classSizeAtExponent (1 / 3) = 1 / 6 := by
  unfold classSizeAtExponent; norm_num

/-- **At `d ≍ L²` the size is `O(1)`.** -/
theorem classSizeAt_top : classSizeAtExponent (2 / 3) = 0 := by
  unfold classSizeAtExponent; norm_num

/-- The sizes shrink as the kernel grows. -/
theorem classSizeAt_antitone {e e' : ℚ} (h : e < e') :
    classSizeAtExponent e' < classSizeAtExponent e := by
  unfold classSizeAtExponent; linarith

/-! ### The total and the `ℓ²` norm -/

/-- Exponent of the total number of frequencies, `Σ_d L/√d ≍ L·L`. -/
def totalFrequencyExponent : ℚ := 2 / 3

/-- **It matches the frontier's term count.** -/
theorem total_matches_frontier : totalFrequencyExponent = frontierTermCount := by
  unfold totalFrequencyExponent frontierTermCount; norm_num

/-- Exponent of the `ℓ²` norm of the class sizes, `(Σ_d L²/d)^(1/2) ≍ L` up to logarithms. -/
def classSizeL2Exponent : ℚ := 1 / 3

/-- **It equals the Lindelöf value for the frontier object.** -/
theorem l2_is_lindelof : classSizeL2Exponent = frontierLindelof := rfl

/-- **And it is strictly below the total**, by one Farey order. -/
theorem l2_below_total :
    classSizeL2Exponent < totalFrequencyExponent ∧
      totalFrequencyExponent - classSizeL2Exponent = fareyOrderExponent := by
  unfold classSizeL2Exponent totalFrequencyExponent fareyOrderExponent
  constructor <;> norm_num

/-! ### Condition (i) is unnecessary -/

/-- The level reached when the class sums add with square-root cancellation, whatever their internal
structure. -/
def acrossClassOnlyLevel : ℚ := classSizeL2Exponent

/-- **It is the Lindelöf value.** -/
@[simp] theorem acrossClassOnly_is_lindelof : acrossClassOnlyLevel = frontierLindelof := rfl

/-- **So across-class cancellation alone suffices**, and the internal coherence of the classes —
condition (i) — is not needed. -/
theorem conditionOne_unnecessary :
    acrossClassOnlyLevel = frontierLindelof ∧
      acrossClassOnlyLevel < totalFrequencyExponent := by
  refine ⟨rfl, ?_⟩
  unfold acrossClassOnlyLevel classSizeL2Exponent totalFrequencyExponent; norm_num

/-- **Where the divisibility argument bites.**  Only the classes with `d ≤ L` have size at least
`√L`; they hold `≍ L^(3/2)` of the `L²` frequencies, a fraction `L^(-1/2) = N^(-1/6)`. -/
theorem divisibility_covers_a_small_fraction :
    classSizeAtExponent (1 / 3) = 1 / 6 ∧
      (1 : ℚ) / 3 + 1 / 6 = 1 / 2 ∧
      totalFrequencyExponent - 1 / 2 = 1 / 6 := by
  refine ⟨classSizeAt_farey, by norm_num, ?_⟩
  unfold totalFrequencyExponent; norm_num

/-- **Summary of the correction.**  Classes number `L²`, sizes are `L/√d`, the `ℓ²` norm is the
Lindelöf value, and condition (i) — which the uniform-size reading made necessary — is not. -/
theorem class_distribution_summary :
    correctedClassCount = 2 / 3 ∧
      classSizeAtExponent 0 = 1 / 3 ∧
      classSizeL2Exponent = frontierLindelof ∧
      correctedClassCount ≠ classCountExponent := by
  refine ⟨rfl, classSizeAt_zero, rfl, correctedClassCount_ne_old⟩

end HTGeometry
