import GaloisForLFunctions.RHTower.WeilLogShiftMaxKernelDefect

/-! Exponential reweighting exposes the negative hyperplane of the Weil cost kernel. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCostPair {ι : Type*} [Fintype ι] (x u v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * v j * Real.exp (2 * |x j - x i|)

def finiteWeilCostMoment {ι : Type*} [Fintype ι] (x u : ι → ℝ) : ℝ :=
  ∑ i, u i * Real.exp (-2 * x i)

theorem finiteWeilCostPair_symm {ι : Type*} [Fintype ι] (x u v : ι → ℝ) :
    finiteWeilCostPair x u v = finiteWeilCostPair x v u := by
  unfold finiteWeilCostPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_sub_comm (x i) (x j)]
  ring

theorem finiteWeilCostMoment_linearCombination {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (a b : ℝ) :
    finiteWeilCostMoment x (fun i => a * u i + b * v i) =
      a * finiteWeilCostMoment x u + b * finiteWeilCostMoment x v := by
  simp only [finiteWeilCostMoment, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]

theorem finiteWeilCostPair_linearCombination {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (a b : ℝ) :
    finiteWeilCostPair x (fun i => a * u i + b * v i)
        (fun i => a * u i + b * v i) =
      a ^ 2 * finiteWeilCostPair x u u + 2 * a * b * finiteWeilCostPair x u v +
        b ^ 2 * finiteWeilCostPair x v v := by
  have hterm (i j : ι) :
      (a * u i + b * v i) * (a * u j + b * v j) * Real.exp (2 * |x j - x i|) =
        a ^ 2 * (u i * u j * Real.exp (2 * |x j - x i|)) +
        (a * b) * (u i * v j * Real.exp (2 * |x j - x i|)) +
        (a * b) * (v i * u j * Real.exp (2 * |x j - x i|)) +
        b ^ 2 * (v i * v j * Real.exp (2 * |x j - x i|)) := by ring
  unfold finiteWeilCostPair
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change a ^ 2 * finiteWeilCostPair x u u + a * b * finiteWeilCostPair x u v +
      a * b * finiteWeilCostPair x v u + b ^ 2 * finiteWeilCostPair x v v =
    a ^ 2 * finiteWeilCostPair x u u + 2 * a * b * finiteWeilCostPair x u v +
      b ^ 2 * finiteWeilCostPair x v v
  rw [finiteWeilCostPair_symm x v u]
  ring

theorem finiteWeilCostKernel_eq_max (x y : ℝ) :
    Real.exp (2 * |y - x|) = Real.exp (-2 * x) * Real.exp (-2 * y) *
      max (Real.exp (4 * x)) (Real.exp (4 * y)) := by
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),
      max_eq_right (Real.exp_le_exp.mpr (by linarith)), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr h),
      max_eq_left (Real.exp_le_exp.mpr (by linarith)), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

theorem finiteWeilCostPair_self_max {ι : Type*} [Fintype ι] (x u : ι → ℝ) :
    finiteWeilCostPair x u u = finiteMaxKernelForm Finset.univ
      (fun i => Real.exp (4 * x i)) (fun i => u i * Real.exp (-2 * x i)) := by
  unfold finiteWeilCostPair finiteMaxKernelForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteWeilCostKernel_eq_max]
  ring

/-- A single explicit moment dominates the signed cost, with positive definite defect. -/
theorem exists_finiteWeilCostPair_strict_defect {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ι → ℝ,
      0 ≤ R * finiteWeilCostMoment x u ^ 2 - finiteWeilCostPair x u u ∧
        (R * finiteWeilCostMoment x u ^ 2 - finiteWeilCostPair x u u = 0 ↔ u = 0) := by
  let R := (∑ i, Real.exp (4 * x i)) + 1
  have hR : ∀ i ∈ (Finset.univ : Finset ι), Real.exp (4 * x i) < R := by
    intro i hi
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (Real.exp_pos (4 * x j)).le) hi
    dsimp [R]
    linarith
  have hp : Function.Injective (fun i => Real.exp (4 * x i)) := by
    intro i j he
    apply hx
    have he' := Real.exp_injective he
    linarith
  refine ⟨R, ?_, fun u => ?_⟩
  · dsimp [R]
    have := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      (Real.exp_pos (4 * x i)).le)
    linarith
  · rw [finiteWeilCostPair_self_max]
    have hd := finiteMaxKernel_defect Finset.univ (fun i => Real.exp (4 * x i))
      (fun i => u i * Real.exp (-2 * x i)) hp R hR
    refine ⟨hd.1, hd.2.trans ?_⟩
    constructor
    · intro hu
      funext i
      exact (mul_eq_zero.mp (hu i (Finset.mem_univ i))).resolve_right (Real.exp_ne_zero _)
    · rintro rfl
      simp

theorem finiteWeilCostPair_moment_zero {ι : Type*} [Fintype ι]
    (x u : ι → ℝ) (hx : Function.Injective x) (hu : finiteWeilCostMoment x u = 0) :
    finiteWeilCostPair x u u ≤ 0 ∧ (finiteWeilCostPair x u u = 0 ↔ u = 0) := by
  obtain ⟨R, _, hR⟩ := exists_finiteWeilCostPair_strict_defect x hx
  have h := hR u
  simpa [hu] using h

end RHTower
