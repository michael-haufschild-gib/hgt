import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheBatteryOfTheCount

/-!
# The successor enters the count only modulo the square-root class

The integers of `ℤ` are counted exactly: the **successor weight** `1` has partial sums `⌊x⌋`, within
`1` of `x` (`abs_partialSum_one_sub_le`), so its precision is `0`. The count is a comparison of the
prime weight with the successor:

* **The count compares with the successor** (`count_iff_sub_one_mem_sqrtClass`): `a` satisfies the
  count iff `a − 1 ∈ 𝒬`.
* **Successor models** (`count_iff_sub_mem_sqrtClass_of_successor`): for any weight `u` whose partial
  sums are within `𝒬` of the integer count, the count for `a` is `a − u ∈ 𝒬`. A model of the integers
  at square-root precision (an over-regular Beurling count) gives the same count statement.
* **Coarse successors change the question** (`not_count_and_sub_mem_of_successor_not_mem`): if
  `u − 1 ∉ 𝒬`, no weight satisfies the count and is within `𝒬` of `u`.

So the exactness of the successor is not what the count uses; the count uses only the class of the
integer count modulo `𝒬`. Over-regular Beurling systems share that class, which is why integer-count
precision does not decide the prime count: the deciding input must come from the prime side.
-/

noncomputable section

open Filter Asymptotics Real Finset

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The **successor weight** `1`: its partial sums count the integers. -/
def successorWeight : ℕ → ℝ := fun _ => 1

theorem partialSum_successorWeight (x : ℝ) : partialSum successorWeight x = ⌊x⌋₊ := by
  simp [partialSum, successorWeight]

/-- **The successor has precision `0`**: `|⌊x⌋ − x| ≤ 1` for `x ≥ 0`. -/
theorem abs_partialSum_one_sub_le {x : ℝ} (hx : 0 ≤ x) : |partialSum successorWeight x - x| ≤ 1 := by
  rw [partialSum_successorWeight, abs_le]
  constructor <;> linarith [Nat.floor_le hx, Nat.lt_floor_add_one x]

/-- The successor satisfies the count. -/
theorem count_successorWeight : Count successorWeight := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx0 : 0 ≤ x := le_trans (exp_pos 1).le hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (sqrtScale_nonneg x), one_mul]
  exact (abs_partialSum_one_sub_le hx0).trans (one_le_sqrtScale hx)

/-- **The count compares with the successor**: `Count a ↔ a − 1 ∈ 𝒬`. -/
theorem count_iff_sub_one_mem_sqrtClass (a : ℕ → ℝ) :
    Count a ↔ a - successorWeight ∈ sqrtClass := by
  constructor
  · intro h; exact sub_mem_sqrtClass_of_count count_successorWeight h
  · intro h
    have := (count_add_iff_mem_sqrtClass count_successorWeight (a - successorWeight)).mpr h
    simpa using this

/-- **Successor models**: if `u − 1 ∈ 𝒬`, the count for `a` is `a − u ∈ 𝒬`. -/
theorem count_iff_sub_mem_sqrtClass_of_successor {u : ℕ → ℝ} (hu : u - successorWeight ∈ sqrtClass)
    (a : ℕ → ℝ) : Count a ↔ a - u ∈ sqrtClass := by
  rw [count_iff_sub_one_mem_sqrtClass]
  constructor
  · intro h
    have := PrecisionClass.sub_mem h hu
    simpa using this
  · intro h
    have := PrecisionClass.add_mem h hu
    simpa using this

/-- **Coarse successors change the question**: if `u − 1 ∉ 𝒬`, no weight satisfies the count and is
within `𝒬` of `u`. -/
theorem not_count_and_sub_mem_of_successor_not_mem {u : ℕ → ℝ}
    (hu : u - successorWeight ∉ sqrtClass) (a : ℕ → ℝ) :
    ¬ (Count a ∧ a - u ∈ sqrtClass) := fun ⟨h, h'⟩ => by
  have h1 := (count_iff_sub_one_mem_sqrtClass a).mp h
  have := PrecisionClass.sub_mem h1 h'
  exact hu (by simpa using this)

/-- **RH is the comparison of `Λ` with the successor at square-root precision.** -/
theorem riemannHypothesis_iff_vonMangoldt_sub_one_mem_sqrtClass :
    RiemannHypothesis ↔ vonMangoldtWeight - successorWeight ∈ sqrtClass :=
  count_vonMangoldt_iff.symm.trans (count_iff_sub_one_mem_sqrtClass _)

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
