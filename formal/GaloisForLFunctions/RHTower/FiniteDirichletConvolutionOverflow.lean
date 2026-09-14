import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The complete boundary of a finite Dirichlet convolution

Multiplying two heads truncated at `N` sums over a rectangle. Summing their Dirichlet convolution
through `N` retains only the hyperbola region `d * m ≤ N`. The difference is the full overflow
`d, m ≤ N < d * m`, with all original coefficients retained.

For Möbius and constant-one coefficients, the hyperbola part is exactly the unit. The resulting
identity is valid for every complex parameter and includes the empty-cutoff endpoint. It does not
assert that the overflow vanishes, construct a reciprocal to continued zeta, or constrain zeros.
-/

open scoped BigOperators

noncomputable section
namespace RHTower

/-- The part of a rectangular product lying beyond its Dirichlet-convolution cutoff. -/
def dirichletRectangleOverflow {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (N : ℕ) : R :=
  ∑ d ∈ Finset.Icc 1 N, f d *
    ∑ m ∈ Finset.Icc 1 N \ Finset.Icc 1 (N / d), g m

/-- The row difference is exactly the region beyond the multiplicative hyperbola. -/
theorem mem_dirichletOverflowRow {N d m : ℕ} (hd : 0 < d) :
    m ∈ Finset.Icc 1 N \ Finset.Icc 1 (N / d) ↔
      1 ≤ m ∧ m ≤ N ∧ N < d * m := by
  simp only [Finset.mem_sdiff, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, hmN⟩, hnot⟩
    refine ⟨hm1, hmN, Nat.lt_of_not_ge ?_⟩
    intro hmul
    apply hnot
    refine ⟨hm1, (Nat.le_div_iff_mul_le hd).2 ?_⟩
    exact (Nat.mul_comm m d).le.trans hmul
  · rintro ⟨hm1, hmN, hmul⟩
    refine ⟨⟨hm1, hmN⟩, ?_⟩
    rintro ⟨_, hmdiv⟩
    have hle := (Nat.le_div_iff_mul_le hd).1 hmdiv
    exact (Nat.not_le_of_gt hmul) ((Nat.mul_comm d m).le.trans hle)

/-- Exact finite convolution law, retaining every overflow term. -/
theorem sum_Icc_mul_sum_eq_convolution_add_overflow
    {R : Type*} [Semiring R] (f g : ArithmeticFunction R) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, f d) * (∑ m ∈ Finset.Icc 1 N, g m) =
      (∑ n ∈ Finset.Icc 1 N, (f * g) n) + dirichletRectangleOverflow f g N := by
  rw [Finset.sum_mul, sum_Icc_mul_apply, dirichletRectangleOverflow,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← mul_add]
  congr 1
  have hsub : Finset.Icc 1 (N / d) ⊆ Finset.Icc 1 N := by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans (Nat.div_le_self N d)⟩
  exact (Finset.sum_sdiff (f := fun m => g m) hsub).symm.trans (add_comm _ _)

private def dirichletTermAF (f : ArithmeticFunction ℂ) (s : ℂ) :
    ArithmeticFunction ℂ where
  toFun := LSeries.term f s
  map_zero' := LSeries.term_zero f s

private theorem dirichletTermAF_mul (f g : ArithmeticFunction ℂ) (s : ℂ) :
    dirichletTermAF (f * g) s = dirichletTermAF f s * dirichletTermAF g s := by
  ext n
  change LSeries.term (⇑(f * g)) s n =
    ∑ p ∈ n.divisorsAntidiagonal, LSeries.term f s p.1 * LSeries.term g s p.2
  rw [← ArithmeticFunction.coe_mul]
  exact LSeries.term_convolution f g s n

/-- The literal finite Dirichlet head of an arithmetic coefficient family. -/
def finiteDirichletHead (f : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, LSeries.term f s n

/-- The head retains the original coefficients and complex-power weights. -/
theorem finiteDirichletHead_eq_sum_mul_cpow
    (f : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) :
    finiteDirichletHead f N s =
      ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s) := by
  apply Finset.sum_congr rfl
  intro n _
  exact LSeries.term_def₀ f.map_zero s n

/-- The complete complex-weighted overflow, with no analytic continuation or inverse inserted. -/
def finiteDirichletOverflow (f g : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, LSeries.term f s d *
    ∑ m ∈ Finset.Icc 1 N \ Finset.Icc 1 (N / d), LSeries.term g s m

/-- Complex Dirichlet weighting preserves the exact finite boundary decomposition. -/
theorem finiteDirichletHead_mul (f g : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) :
    finiteDirichletHead f N s * finiteDirichletHead g N s =
      finiteDirichletHead (f * g) N s + finiteDirichletOverflow f g N s := by
  have h := sum_Icc_mul_sum_eq_convolution_add_overflow
    (dirichletTermAF f s) (dirichletTermAF g s) N
  rw [← dirichletTermAF_mul] at h
  exact h

/-- The complete boundary agrees under both parenthesizations of three products.
This is forced by associativity at every parameter, not a zero-dependent obstruction. -/
theorem finiteDirichletOverflow_assoc
    (f g h : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) :
    finiteDirichletOverflow (f * g) h N s +
        finiteDirichletOverflow f g N s * finiteDirichletHead h N s =
      finiteDirichletOverflow f (g * h) N s +
        finiteDirichletHead f N s * finiteDirichletOverflow g h N s := by
  apply add_left_cancel (a := finiteDirichletHead ((f * g) * h) N s)
  calc
    _ = (finiteDirichletHead (f * g) N s + finiteDirichletOverflow f g N s) *
        finiteDirichletHead h N s := by
      rw [← add_assoc, ← finiteDirichletHead_mul, add_mul]
    _ = (finiteDirichletHead f N s * finiteDirichletHead g N s) *
        finiteDirichletHead h N s := by
      rw [finiteDirichletHead_mul f g]
    _ = finiteDirichletHead f N s *
        (finiteDirichletHead (g * h) N s + finiteDirichletOverflow g h N s) := by
      rw [← finiteDirichletHead_mul, mul_assoc]
    _ = _ := by
      rw [mul_add, finiteDirichletHead_mul, mul_assoc, add_assoc]

/-- Swapping both arithmetic coefficient families preserves the complete scalar boundary. -/
theorem finiteDirichletOverflow_comm
    (f g : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) :
    finiteDirichletOverflow f g N s = finiteDirichletOverflow g f N s := by
  apply add_left_cancel (a := finiteDirichletHead (f * g) N s)
  calc
    _ = finiteDirichletHead f N s * finiteDirichletHead g N s :=
      (finiteDirichletHead_mul f g N s).symm
    _ = finiteDirichletHead g N s * finiteDirichletHead f N s := mul_comm _ _
    _ = _ := by rw [finiteDirichletHead_mul, mul_comm g f]

/-- The unit contributes once exactly when the cutoff includes the integer one. -/
theorem finiteDirichletHead_one (N : ℕ) (s : ℂ) :
    finiteDirichletHead 1 N s = if 1 ≤ N then 1 else 0 := by
  rw [finiteDirichletHead_eq_sum_mul_cpow]
  simp [ArithmeticFunction.one_apply, ite_mul]

/-- Möbius recovery on a rectangle retains the full hyperbola overflow. -/
theorem finiteMobiusHead_mul_zetaHead (N : ℕ) (s : ℂ) :
    finiteDirichletHead ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℂ) N s *
      finiteDirichletHead ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
        ArithmeticFunction ℂ) N s =
    (if 1 ≤ N then 1 else 0) +
      finiteDirichletOverflow
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) N s := by
  rw [finiteDirichletHead_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    finiteDirichletHead_one]

end RHTower
