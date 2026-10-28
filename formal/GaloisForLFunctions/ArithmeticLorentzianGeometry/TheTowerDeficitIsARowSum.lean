import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerDichotomy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSignOfTheTowerFinitePart

/-!
# The tower deficit is a row sum

The renormalized prime place enters Weil's form on the `p`-adic classes through the tower finite
part `F_p(b) = 2γ_p |b|² + log p (|b|² − K_q(b))`, `q = p^{−1/2}`
(RenormalizedArithmeticPotentialTheory). Its matrix (`towerMatrix`) has `2γ_p` on the diagonal
and `−log p · q^{|i−j|}` off it, so `−F_p` is a **Metzler** form (`isMetzler_neg_towerMatrix`).

* **Its row sums are bounded by the tower deficit** (`rowSum_neg_towerMatrix_le`): the row of `−F_p`
  at the class `i` is `−2γ_p − log p + log p Σ_j q^{|i−j|} ≤ −2γ_p + 2 log p q/(1 − q) = 2d_p`, with
  `d_p = √p log p/(p − 1) − γ`. The Kac–Murdock–Szegő row is at most `(1 + q)/(1 − q)`.
* **The sign law is the row-sum law** (`towerFinitePart_add_nonneg_iff_rowSum`): `F_p + c|·|² ≥ 0` on
  every depth iff `c` dominates every row sum of `−F_p` on every depth. One direction is the
  stability regime of `TheMetzlerDichotomy` with weight `π = 1`; the other is the sharp sign law
  `c ≥ 2d_p` of RAPT.

So the local data of the renormalized prime place are Metzler forms whose only obstruction to
positivity is their row sums; the deficit `2d_p > 0` at the small primes (`d_2 > 0`) is a positive
row sum that another place must cancel. In a link decomposition of the atomic intersection form
the prime-place links are these Metzler forms, and the accounting of who pays `2d_p` is an
accounting of row sums.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory GaloisForLFunctions.ArithmeticIntersectionTheory

/-- The matrix of the tower finite part on the classes `0, …, N − 1`. -/
def towerMatrix (p N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (if i = j then 2 * localEuler p + Real.log p else 0) -
    Real.log p * kmsEntry (1 / Real.sqrt p) i j

/-- The quadratic form of `towerMatrix` is the tower finite part. -/
theorem qf_towerMatrix (p N : ℕ) (b : ℕ → ℝ) :
    qf (towerMatrix p N) (fun i => b i) = towerFinitePart p N b := by
  rw [qf_eq_sum, towerFinitePart, kmsForm]
  simp only [towerMatrix, Matrix.of_apply, mul_sub, sub_mul, sum_sub_distrib, mul_ite, mul_zero,
    ite_mul, zero_mul]
  have e1 : ∀ i : Fin N, ∑ j : Fin N, (if i = j then b i * (2 * localEuler p + Real.log p) * b j
      else 0) = (2 * localEuler p + Real.log p) * b i ^ 2 := fun i => by
    rw [Finset.sum_ite_eq]; simp only [mem_univ, if_true]; ring
  have e2 : ∑ i : Fin N, ∑ j : Fin N, b i * (Real.log p * kmsEntry (1 / Real.sqrt p) i j) * b j =
      Real.log p * ∑ i ∈ range N, ∑ j ∈ range N, b i * b j * kmsEntry (1 / Real.sqrt p) i j := by
    rw [mul_sum, Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N,
      b i * (Real.log p * kmsEntry (1 / Real.sqrt p) i j) * b j) N]
    refine sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun j => b i * (Real.log p * kmsEntry (1 / Real.sqrt p) i j) *
      b j) N, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp only [e1]
  rw [e2, ← mul_sum, Fin.sum_univ_eq_sum_range (fun i => b i ^ 2) N]
  ring

theorem towerMatrix_isSymm (p N : ℕ) : (towerMatrix p N).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    simp only [towerMatrix, Matrix.of_apply, kmsEntry, eq_comm (a := i), max_comm, min_comm]

/-- **`−F_p` is Metzler.** -/
theorem isMetzler_neg_towerMatrix {p : ℕ} (hp : p.Prime) (N : ℕ) :
    IsMetzler (-towerMatrix p N) := fun i j hij => by
  simp only [Matrix.neg_apply, towerMatrix, Matrix.of_apply, if_neg hij, zero_sub, neg_neg]
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    (pow_nonneg (inv_sqrt_prime_nonneg p) _)

/-- The Kac–Murdock–Szegő row: `Σ_{j < N} q^{|i−j|} ≤ (1 + q)/(1 − q)`. -/
theorem sum_kmsEntry_row_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N i : ℕ) :
    ∑ j ∈ range N, kmsEntry q i j ≤ (1 + q) / (1 - q) := by
  have hgeom : ∀ n, ∑ k ∈ range n, q ^ k ≤ (1 - q)⁻¹ := fun n => by
    rw [← tsum_geometric_of_lt_one hq0 hq1]
    exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ fun k _ => pow_nonneg hq0 k
  rw [← sum_filter_add_sum_filter_not (range N) (fun j => j ≤ i)]
  have hlow : ∑ j ∈ range N with j ≤ i, kmsEntry q i j ≤ (1 - q)⁻¹ := by
    calc ∑ j ∈ range N with j ≤ i, kmsEntry q i j
        = ∑ j ∈ range N with j ≤ i, q ^ (i - j) := sum_congr rfl fun j hj => by
          simp only [mem_filter] at hj
          simp [kmsEntry, max_eq_left hj.2, min_eq_right hj.2]
      _ ≤ ∑ j ∈ range (i + 1), q ^ (i - j) :=
          sum_le_sum_of_subset_of_nonneg (fun j hj => by
            simp only [mem_filter, mem_range] at hj ⊢; omega) (fun j _ _ => pow_nonneg hq0 _)
      _ = ∑ k ∈ range (i + 1), q ^ k := by
          rw [← sum_range_reflect]; exact sum_congr rfl fun j hj => by
            simp only [mem_range] at hj; congr 1; omega
      _ ≤ (1 - q)⁻¹ := hgeom _
  have hhigh : ∑ j ∈ range N with ¬ j ≤ i, kmsEntry q i j ≤ q * (1 - q)⁻¹ := by
    calc ∑ j ∈ range N with ¬ j ≤ i, kmsEntry q i j
        = ∑ j ∈ range N with ¬ j ≤ i, q ^ (j - i) := sum_congr rfl fun j hj => by
          simp only [mem_filter, not_le] at hj
          simp [kmsEntry, max_eq_right hj.2.le, min_eq_left hj.2.le]
      _ ≤ ∑ j ∈ Ico (i + 1) (i + 1 + N), q ^ (j - i) :=
          sum_le_sum_of_subset_of_nonneg (fun j hj => by
            simp only [mem_filter, mem_range, mem_Ico] at hj ⊢; omega) (fun j _ _ => pow_nonneg hq0 _)
      _ = q * ∑ k ∈ range N, q ^ k := by
          rw [sum_Ico_eq_sum_range, mul_sum]
          refine (sum_congr (by congr 1; omega) fun k _ => ?_)
          rw [show i + 1 + k - i = k + 1 by omega, pow_succ, mul_comm]
      _ ≤ q * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left (hgeom _) hq0
  have : (1 - q)⁻¹ + q * (1 - q)⁻¹ = (1 + q) / (1 - q) := by
    field_simp [(by linarith : (1 : ℝ) - q ≠ 0)]
  linarith

/-- **The row sums of `−F_p` are at most `2d_p`.** -/
theorem rowSum_neg_towerMatrix_le {p : ℕ} (hp : p.Prime) (N : ℕ) (i : Fin N) :
    rowSum (-towerMatrix p N) i ≤ 2 * towerDeficit p := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hrow : rowSum (-towerMatrix p N) i =
      -(2 * localEuler p + Real.log p) + Real.log p * ∑ j ∈ range N, kmsEntry q i j := by
    simp only [rowSum, mulVec, dotProduct, Pi.one_apply, mul_one, Matrix.neg_apply, towerMatrix,
      Matrix.of_apply, neg_sub, sum_sub_distrib]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, if_true]
    rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun j => kmsEntry q i j) N]
    ring
  have hK := sum_kmsEntry_row_le hq0 hq1 N i
  have hE := localEuler_sub_eq hp
  rw [hrow]
  have h1 : Real.log p * ∑ j ∈ range N, kmsEntry q i j ≤ Real.log p * ((1 + q) / (1 - q)) :=
    mul_le_mul_of_nonneg_left hK hL
  have h2 : (1 + q) / (1 - q) = 1 + 2 * (q / (1 - q)) := by
    field_simp [(by linarith : (1 : ℝ) - q ≠ 0)]; ring
  have h3 : q / (1 - q) = 1 / Real.sqrt p / (1 - 1 / Real.sqrt p) := rfl
  rw [h2] at h1
  nlinarith

/-- **The sign law is the row-sum law**: `F_p + c|·|² ≥ 0` on every depth iff `c` dominates every row
sum of the Metzler form `−F_p` on every depth. -/
theorem towerFinitePart_add_nonneg_iff_rowSum {p : ℕ} (hp : p.Prime) (c : ℝ) :
    (∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b + c * ∑ j ∈ range N, b j ^ 2) ↔
      ∀ (N : ℕ) (i : Fin N), rowSum (-towerMatrix p N) i ≤ c := by
  constructor
  · intro h N i
    exact (rowSum_neg_towerMatrix_le hp N i).trans ((towerFinitePart_add_nonneg_iff hp c).mp h)
  · intro h N b
    -- stability regime: `−F_p − c` is Metzler with nonpositive row sums
    set Q : Matrix (Fin N) (Fin N) ℝ := -towerMatrix p N - c • (1 : Matrix (Fin N) (Fin N) ℝ)
    have hQs : Q.IsSymm := ((towerMatrix_isSymm p N).neg).sub (Matrix.isSymm_one.smul c)
    have hQM : IsMetzler Q := fun i j hij => by
      simp only [Q, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero,
        sub_zero]
      exact isMetzler_neg_towerMatrix hp N i j hij
    have hQrow : ∀ i, (Q *ᵥ fun _ => (1 : ℝ)) i ≤ 0 := fun i => by
      have : (Q *ᵥ fun _ => (1 : ℝ)) i = rowSum (-towerMatrix p N) i - c := by
        simp only [Q, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, mul_one, rowSum]
        rfl
      rw [this]; linarith [h N i]
    have hneg := qf_nonpos_of_mulVec_nonpos hQs hQM (π := fun _ => 1) (fun _ => one_pos) hQrow
      (fun i => b i)
    have e : qf Q (fun i => b i) = -(towerFinitePart p N b + c * ∑ j ∈ range N, b j ^ 2) := by
      have h1 : qf Q (fun i => b i) = -qf (towerMatrix p N) (fun i => b i) -
          c * ∑ i : Fin N, b i ^ 2 := by
        simp only [Q, qf, bil, sub_mulVec, neg_mulVec, smul_mulVec, one_mulVec]
        rw [dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul]
        simp only [dotProduct, sq]
      rw [h1, qf_towerMatrix, Fin.sum_univ_eq_sum_range (fun i => b i ^ 2) N]
      ring
    linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
