import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Classical Fredholm determinant of a continuous kernel

This module supplies the analytic infrastructure used by Suzuki's equation (4.19).  Unlike the
Hilbert--Carleman determinant of an abstract Hilbert--Schmidt matrix, the classical Fredholm
determinant of a continuous kernel is defined by its integral series.  Its convergence rests on
Hadamard's determinant bound; the factorial permutation bound is too weak.

The construction here is deliberately independent of any resolvent or differential equation:
`ContinuousKernelFredholm.determinant K a z` is the literal Fredholm series of kernel `K` on cube
`[0,a]^n`.  This prevents a determinant identity from being obtained circularly by defining the
determinant to solve the desired ODE.
-/

open scoped BigOperators

noncomputable section

open Module Set

namespace ContinuousKernelFredholm

/-- Complex Hadamard inequality in column-norm form. -/
theorem complex_hadamard_column_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ j : Fin n,
      ‖(WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℂ (Fin n))‖ := by
  classical
  let e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  let v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => WithLp.toLp 2 (fun i : Fin n => A i j)
  have hdim : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim v
  have heA : e.toBasis.toMatrix v = A := by
    ext i j
    change (e.repr (v j)) i = A i j
    simp [e, v]
  have hchange : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    have hmul := e.toBasis.toMatrix_mul_toMatrix b.toBasis v
    have hdet := congrArg Matrix.det hmul
    rw [Matrix.det_mul] at hdet
    change e.toBasis.det b * b.toBasis.det v = e.toBasis.det v at hdet
    calc
      ‖e.toBasis.det v‖ = ‖e.toBasis.det b * b.toBasis.det v‖ := by rw [hdet]
      _ = ‖e.toBasis.det b‖ * ‖b.toBasis.det v‖ := norm_mul _ _
      _ = ‖b.toBasis.det v‖ := by
        rw [OrthonormalBasis.det_to_matrix_orthonormalBasis]
        simp
  have hb : b.toBasis.det v = ∏ i, inner ℂ (b i) (v i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim v
  rw [← heA, ← Basis.det_apply, hchange, hb, norm_prod]
  apply Finset.prod_le_prod
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    calc
      ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
      _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

/-- Complex Hadamard inequality when every matrix entry has norm at most `M`. -/
theorem complex_hadamard_entry_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {M : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ (Real.sqrt n * M) ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  refine (complex_hadamard_column_bound A).trans ?_
  calc
    (∏ j : Fin n,
      ‖(WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℂ (Fin n))‖)
        ≤ ∏ _j : Fin n, Real.sqrt n * M := by
          apply Finset.prod_le_prod
          · intro j hj
            exact norm_nonneg _
          · intro j hj
            let e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
              EuclideanSpace.basisFun (Fin n) ℂ
            let x : EuclideanSpace ℂ (Fin n) :=
              WithLp.toLp 2 (fun i : Fin n => A i j)
            refine (e.norm_le_card_mul_iSup_norm_inner x).trans ?_
            have hsup : (⨆ i, ‖inner ℂ (e i) x‖) ≤ M := by
              apply ciSup_le
              intro i
              change ‖inner ℂ (EuclideanSpace.basisFun (Fin n) ℂ i) x‖ ≤ M
              rw [EuclideanSpace.basisFun_inner]
              exact hA i j
            simpa using mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg n)
    _ = (Real.sqrt n * M) ^ n := by simp

/-- The Hadamard majorant `((sqrt n)c)^n/n!` is summable for every nonnegative `c`.

Stirling's lower bound reduces its tail to a geometric series. -/
theorem summable_hadamard_majorant (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun n : ℕ => (Real.sqrt n * c) ^ n / (n.factorial : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 * Real.exp 1 * c) ^ (2 : ℕ))
  refine (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)).of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨max N 1, fun n hnmax => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hnmax
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hnmax)
  have hncast : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hec : 0 ≤ Real.exp 1 * c := mul_nonneg (Real.exp_pos 1).le hc
  have htwoec : 0 ≤ 2 * Real.exp 1 * c := by positivity
  have hsqrtLower : 2 * Real.exp 1 * c ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq htwoec]
    exact Real.sqrt_le_sqrt (hN.trans hncast)
  have hratio : Real.exp 1 * c / Real.sqrt n ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrtn]
    nlinarith
  have hbase : 0 < (n : ℝ) / Real.exp 1 := div_pos hnreal (Real.exp_pos 1)
  have hsqrtFactor : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi := Real.pi_gt_three
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * n := by gcongr
  have hfacLower : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n ≤
          Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n := by
            exact le_mul_of_one_le_left (pow_nonneg hbase.le n) hsqrtFactor
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hquotient :
      (Real.sqrt n * c) ^ n / (n.factorial : ℝ) ≤
        (Real.sqrt n * c) ^ n / (((n : ℝ) / Real.exp 1) ^ n) := by
    exact div_le_div_of_nonneg_left (pow_nonneg (mul_nonneg hsqrtn.le hc) n)
      (pow_pos hbase n) hfacLower
  have hrewrite :
      (Real.sqrt n * c) ^ n / (((n : ℝ) / Real.exp 1) ^ n) =
        (Real.exp 1 * c / Real.sqrt n) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp [hsqrtn.ne', (Real.exp_pos 1).ne']
    rw [Real.sq_sqrt hnreal.le]
    ring
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (mul_nonneg hsqrtn.le hc) n)
    (Nat.cast_nonneg n.factorial))]
  calc
    (Real.sqrt n * c) ^ n / (n.factorial : ℝ)
        ≤ (Real.exp 1 * c / Real.sqrt n) ^ n := hquotient.trans_eq hrewrite
    _ ≤ ((1 : ℝ) / 2) ^ n := by
      exact pow_le_pow_left₀ (div_nonneg hec hsqrtn.le) hratio n

/-- Iterated Lebesgue integral over the cube `[0,a]^n`.

The recursive presentation is definitionally suited to later moving-endpoint differentiation. -/
noncomputable def cubeIntervalIntegral :
    ∀ n : ℕ, ℝ → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, _a, f => f (fun i => Fin.elim0 i)
  | n + 1, a, f => ∫ x in (0 : ℝ)..a,
      cubeIntervalIntegral n a (fun v => f (Fin.cons x v))

/-- A pointwise bound `C` on `[0,a]^n` bounds the cube integral by `a^n C`. -/
theorem norm_cubeIntervalIntegral_le
    (n : ℕ) {a C : ℝ} (ha : 0 ≤ a)
    (f : (Fin n → ℝ) → ℂ)
    (hf : ∀ x, (∀ i, x i ∈ Icc (0 : ℝ) a) → ‖f x‖ ≤ C) :
    ‖cubeIntervalIntegral n a f‖ ≤ a ^ n * C := by
  induction n with
  | zero =>
      simpa [cubeIntervalIntegral] using hf (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      rw [cubeIntervalIntegral]
      calc
        ‖∫ x in (0 : ℝ)..a,
            cubeIntervalIntegral n a (fun v => f (Fin.cons x v))‖
            ≤ (a ^ n * C) * |a - 0| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro x hx
              apply ih (fun v => f (Fin.cons x v))
              intro v hv
              apply hf (Fin.cons x v)
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · rw [uIoc_of_le ha] at hx
                exact ⟨hx.1.le, hx.2⟩
              · simpa using hv j
        _ = a ^ (n + 1) * C := by
          simp only [sub_zero, abs_of_nonneg ha]
          ring

/-- Determinant integrand in the `n`-th classical Fredholm coefficient. -/
noncomputable def fredholmIntegrand
    (K : ℝ → ℝ → ℂ) (n : ℕ) (x : Fin n → ℝ) : ℂ :=
  Matrix.det (fun i j : Fin n => K (x i) (x j))

/-- The `n`-th classical Fredholm coefficient on `[0,a]`. -/
noncomputable def fredholmCoefficient
    (K : ℝ → ℝ → ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  cubeIntervalIntegral n a (fredholmIntegrand K n) / (n.factorial : ℂ)

/-- Classical Fredholm series `det(I + z K_[0,a])`. -/
noncomputable def determinant
    (K : ℝ → ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * fredholmCoefficient K a n

/-- Hadamard bound for one Fredholm coefficient. -/
theorem fredholmCoefficient_norm_le
    (K : ℝ → ℝ → ℂ) {a M : ℝ} (ha : 0 ≤ a)
    (hK : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ M)
    (n : ℕ) :
    ‖fredholmCoefficient K a n‖ ≤
      (Real.sqrt n * (a * M)) ^ n / (n.factorial : ℝ) := by
  rw [fredholmCoefficient, norm_div, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n.factorial)
  refine (norm_cubeIntervalIntegral_le n (C := (Real.sqrt n * M) ^ n) ha _ ?_).trans_eq ?_
  · intro x hx
    exact complex_hadamard_entry_bound _ (fun i j => hK _ (hx i) _ (hx j))
  · rw [mul_pow]
    ring

/-- Absolute convergence of the classical continuous-kernel Fredholm series for every `z`. -/
theorem determinant_summable
    (K : ℝ → ℝ → ℂ) {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hK : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ M)
    (z : ℂ) :
    Summable (fun n : ℕ => z ^ n * fredholmCoefficient K a n) := by
  apply Summable.of_norm_bounded
    (summable_hadamard_majorant (‖z‖ * (a * M))
      (mul_nonneg (norm_nonneg z) (mul_nonneg ha hM)))
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖z‖ ^ n * ‖fredholmCoefficient K a n‖
        ≤ ‖z‖ ^ n * ((Real.sqrt n * (a * M)) ^ n / (n.factorial : ℝ)) := by
          gcongr
          exact fredholmCoefficient_norm_le K ha hK n
    _ = (Real.sqrt n * (‖z‖ * (a * M))) ^ n / (n.factorial : ℝ) := by
      ring

end ContinuousKernelFredholm
