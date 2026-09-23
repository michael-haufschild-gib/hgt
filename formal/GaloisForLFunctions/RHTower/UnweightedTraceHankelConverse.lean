import GaloisForLFunctions.RHTower.TraceHankelConverse
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant

/-!
# Unweighted finite trace--Hankel reality detector

The usual positive-root trace--Hankel criterion inserts a spectral weight.  For a finite
characteristic packet no weight is necessary: positivity of the unweighted Hermite form

`Re sum_z w_z p(z)^(2 : ℕ)`

for every real polynomial already forces every packet point to be real.  The proof is local and
coefficient-faithful.  A real polynomial isolates one nonreal conjugacy orbit and takes the values
`i` and `-i` there, making every surviving contribution strictly negative.
-/

open Complex Polynomial
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- **Unweighted finite Hermite converse.**  A finite complex packet with positive
multiplicities is real whenever its unweighted real-polynomial trace--Hankel form is
nonnegative.  No conjugation-closure premise and no positive translation of the packet are
needed. -/
theorem finite_unweightedTraceHankel_nonneg_implies_real
    (F : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ F, 0 < w z)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (∑ z ∈ F, (((w z : ℝ) : ℂ) * evalRealPolynomial p z ^ (2 : ℕ))).re) :
    ∀ z ∈ F, z.im = 0 := by
  intro α hα
  by_contra him
  let sep : Polynomial ℝ := realOrbitSeparator F α
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  let d : ℂ := Complex.I / evalRealPolynomial sep α
  let p : Polynomial ℝ := sep * realLinearInterpolator α d
  have hpα : evalRealPolynomial p α = Complex.I := by
    simp only [p, evalRealPolynomial_mul, evalRealLinearInterpolator him]
    dsimp only [d]
    field_simp
  have hpconj : evalRealPolynomial p ((starRingEnd ℂ) α) = -Complex.I := by
    rw [evalRealPolynomial_conj, hpα]
    simp
  let term : ℂ → ℂ := fun z => ((w z : ℝ) : ℂ) * evalRealPolynomial p z ^ (2 : ℕ)
  have htermα : (term α).re = -w α := by
    simp only [term, hpα, pow_two, Complex.I_mul_I, mul_neg, mul_one,
      Complex.neg_re, Complex.ofReal_re]
  have hterm_nonpos : ∀ z ∈ F.erase α, (term z).re ≤ 0 := by
    intro z hz
    have hzF : z ∈ F := (Finset.mem_erase.mp hz).2
    have hzα : z ≠ α := (Finset.mem_erase.mp hz).1
    by_cases hzc : z = (starRingEnd ℂ) α
    · subst z
      have hsquare : (-Complex.I) ^ (2 : ℕ) = (-1 : ℂ) := by
        rw [pow_two, neg_mul_neg, Complex.I_mul_I]
      dsimp only [term]
      rw [hpconj, hsquare]
      simp
      exact (hw ((starRingEnd ℂ) α) hzF).le
    · have hsepz : evalRealPolynomial sep z = 0 := by
        exact evalRealOrbitSeparator_eq_zero hzF hzα hzc
      have hpz : evalRealPolynomial p z = 0 := by
        simp [p, hsepz]
      simp [term, hpz]
  have hrest : (∑ z ∈ F.erase α, term z).re ≤ 0 := by
    calc
      (∑ z ∈ F.erase α, term z).re =
          ∑ z ∈ F.erase α, (term z).re := by simp
      _ ≤ 0 := Finset.sum_nonpos hterm_nonpos
  have hnonneg := hpos p
  change 0 ≤ (∑ z ∈ F, term z).re at hnonneg
  rw [← Finset.sum_erase_add F term hα, Complex.add_re, htermα] at hnonneg
  have hwα : 0 < w α := hw α hα
  linarith

/-- Family form of the unweighted converse.  Repeated packet points are retained with their
literal positive multiplicity, so no deduplication or root enumeration is required downstream. -/
theorem finiteFamily_unweightedTraceHankel_nonneg_implies_real
    {ι : Type*} [Fintype ι] (lam : ι → ℂ)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (∑ i : ι, evalRealPolynomial p (lam i) ^ (2 : ℕ)).re) :
    ∀ i : ι, (lam i).im = 0 := by
  classical
  intro i
  by_contra him
  let α : ℂ := lam i
  have himα : α.im ≠ 0 := by simpa [α] using him
  let F : Finset ℂ := Finset.univ.image lam
  have hα : α ∈ F := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let sep : Polynomial ℝ := realOrbitSeparator F α
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  let d : ℂ := Complex.I / evalRealPolynomial sep α
  let p : Polynomial ℝ := sep * realLinearInterpolator α d
  have hpα : evalRealPolynomial p α = Complex.I := by
    simp only [p, evalRealPolynomial_mul, evalRealLinearInterpolator himα]
    dsimp only [d]
    field_simp
  have hpconj : evalRealPolynomial p ((starRingEnd ℂ) α) = -Complex.I := by
    rw [evalRealPolynomial_conj, hpα]
    simp
  let term : ι → ℂ := fun j => evalRealPolynomial p (lam j) ^ (2 : ℕ)
  have htermi : (term i).re = -1 := by
    simp only [term, α] at hpα ⊢
    rw [hpα, pow_two, Complex.I_mul_I]
    norm_num
  have hterm_nonpos : ∀ j ∈ (Finset.univ.erase i), (term j).re ≤ 0 := by
    intro j hj
    have hlamF : lam j ∈ F := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    by_cases hja : lam j = α
    · dsimp only [term]
      rw [hja, hpα, pow_two, Complex.I_mul_I]
      norm_num
    · by_cases hjc : lam j = (starRingEnd ℂ) α
      · dsimp only [term]
        rw [hjc, hpconj]
        have hsquare : (-Complex.I) ^ (2 : ℕ) = (-1 : ℂ) := by
          rw [pow_two, neg_mul_neg, Complex.I_mul_I]
        rw [hsquare]
        norm_num
      · have hsepz : evalRealPolynomial sep (lam j) = 0 :=
          evalRealOrbitSeparator_eq_zero hlamF hja hjc
        have hpz : evalRealPolynomial p (lam j) = 0 := by
          simp [p, hsepz]
        simp [term, hpz]
  have hrest : (∑ j ∈ Finset.univ.erase i, term j).re ≤ 0 := by
    calc
      (∑ j ∈ Finset.univ.erase i, term j).re =
          ∑ j ∈ Finset.univ.erase i, (term j).re := by simp
      _ ≤ 0 := Finset.sum_nonpos hterm_nonpos
  have hnonneg := hpos p
  change 0 ≤ (∑ j : ι, term j).re at hnonneg
  rw [show (∑ j : ι, term j) =
      (∑ j ∈ Finset.univ.erase i, term j) + term i by
        exact (Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)).symm,
    Complex.add_re, htermi] at hnonneg
  linarith

private theorem natDegree_C_mul_X_le_one (a : ℝ) :
    (C a * X).natDegree ≤ 1 := by
  calc
    (C a * X).natDegree ≤ (C a).natDegree + X.natDegree :=
      Polynomial.natDegree_mul_le
    _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]

theorem natDegree_realConjQuadratic_le_two (β : ℂ) :
    (realConjQuadratic β).natDegree ≤ 2 := by
  rw [realConjQuadratic]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  apply max_le
  · refine (Polynomial.natDegree_sub_le _ _).trans ?_
    apply max_le
    · simp
    · exact (natDegree_C_mul_X_le_one (2 * β.re)).trans (by omega)
  · simp

theorem natDegree_realLinearInterpolator_le_one (α c : ℂ) :
    (realLinearInterpolator α c).natDegree ≤ 1 := by
  rw [realLinearInterpolator]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  apply max_le
  · rw [Polynomial.natDegree_C]
    omega
  · exact natDegree_C_mul_X_le_one (c.im / α.im)

theorem natDegree_realOrbitSeparator_le_twice_card (F : Finset ℂ) (α : ℂ) :
    (realOrbitSeparator F α).natDegree ≤ 2 * F.card := by
  rw [realOrbitSeparator]
  calc
    (∏ β ∈ F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α),
        realConjQuadratic β).natDegree
        ≤ ∑ β ∈ F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α),
          (realConjQuadratic β).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _β ∈ F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α), 2 := by
      exact Finset.sum_le_sum fun β _ => natDegree_realConjQuadratic_le_two β
    _ = 2 * (F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α)).card := by
      simp [Nat.mul_comm]
    _ ≤ 2 * F.card := Nat.mul_le_mul_left 2 (Finset.card_filter_le _ _)

/-- **Finite-window unweighted Hermite converse.**  For an `n`-point family it is enough to
test real polynomials through degree `2n+1`.  Thus reality is detected by a finite Hankel block,
not an unbounded family of trace moments. -/
theorem finiteFamily_unweightedTraceHankel_nonneg_degree_le_implies_real
    {ι : Type*} [Fintype ι] (lam : ι → ℂ)
    (hpos : ∀ p : Polynomial ℝ,
      p.natDegree ≤ 2 * Fintype.card ι + 1 →
      0 ≤ (∑ i : ι, evalRealPolynomial p (lam i) ^ (2 : ℕ)).re) :
    ∀ i : ι, (lam i).im = 0 := by
  classical
  intro i
  by_contra him
  let α : ℂ := lam i
  have himα : α.im ≠ 0 := by simpa [α] using him
  let F : Finset ℂ := Finset.univ.image lam
  have hα : α ∈ F := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let sep : Polynomial ℝ := realOrbitSeparator F α
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  let d : ℂ := Complex.I / evalRealPolynomial sep α
  let p : Polynomial ℝ := sep * realLinearInterpolator α d
  have hFcard : F.card ≤ Fintype.card ι := by
    dsimp only [F]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := lam))
  have hpdeg : p.natDegree ≤ 2 * Fintype.card ι + 1 := by
    calc
      p.natDegree ≤ sep.natDegree + (realLinearInterpolator α d).natDegree := by
        exact Polynomial.natDegree_mul_le
      _ ≤ 2 * F.card + 1 := Nat.add_le_add
        (natDegree_realOrbitSeparator_le_twice_card F α)
        (natDegree_realLinearInterpolator_le_one α d)
      _ ≤ 2 * Fintype.card ι + 1 := Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 hFcard) 1
  have hpα : evalRealPolynomial p α = Complex.I := by
    simp only [p, evalRealPolynomial_mul, evalRealLinearInterpolator himα]
    dsimp only [d]
    field_simp
  have hpconj : evalRealPolynomial p ((starRingEnd ℂ) α) = -Complex.I := by
    rw [evalRealPolynomial_conj, hpα]
    simp
  let term : ι → ℂ := fun j => evalRealPolynomial p (lam j) ^ (2 : ℕ)
  have htermi : (term i).re = -1 := by
    simp only [term, α] at hpα ⊢
    rw [hpα, pow_two, Complex.I_mul_I]
    norm_num
  have hterm_nonpos : ∀ j ∈ (Finset.univ.erase i), (term j).re ≤ 0 := by
    intro j hj
    have hlamF : lam j ∈ F := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    by_cases hja : lam j = α
    · dsimp only [term]
      rw [hja, hpα, pow_two, Complex.I_mul_I]
      norm_num
    · by_cases hjc : lam j = (starRingEnd ℂ) α
      · dsimp only [term]
        rw [hjc, hpconj]
        have hsquare : (-Complex.I) ^ (2 : ℕ) = (-1 : ℂ) := by
          rw [pow_two, neg_mul_neg, Complex.I_mul_I]
        rw [hsquare]
        norm_num
      · have hsepz : evalRealPolynomial sep (lam j) = 0 :=
          evalRealOrbitSeparator_eq_zero hlamF hja hjc
        have hpz : evalRealPolynomial p (lam j) = 0 := by
          simp [p, hsepz]
        simp [term, hpz]
  have hrest : (∑ j ∈ Finset.univ.erase i, term j).re ≤ 0 := by
    calc
      (∑ j ∈ Finset.univ.erase i, term j).re =
          ∑ j ∈ Finset.univ.erase i, (term j).re := by simp
      _ ≤ 0 := Finset.sum_nonpos hterm_nonpos
  have hnonneg := hpos p hpdeg
  change 0 ≤ (∑ j : ι, term j).re at hnonneg
  rw [show (∑ j : ι, term j) =
      (∑ j ∈ Finset.univ.erase i, term j) + term i by
        exact (Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)).symm,
    Complex.add_re, htermi] at hnonneg
  linarith

/-! ## Root-free finite-matrix Hermite form -/

/-- Coefficient-faithful unweighted Hermite form of a finite matrix.  It is defined only from
real polynomial coefficients and matrix power traces; no eigenvalue, characteristic root, or
divisor point enters its construction. -/
def finiteMatrixUnweightedTraceHankel
    {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (p : Polynomial ℝ) : ℂ :=
  ∑ r ∈ p.support, ∑ s ∈ p.support,
    ((p.coeff r : ℝ) : ℂ) * ((p.coeff s : ℝ) : ℂ) * (M ^ (r + s)).trace

private theorem evalRealPolynomial_eq_sum_support (p : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial p z =
      ∑ n ∈ p.support, ((p.coeff n : ℝ) : ℂ) * z ^ n := by
  rw [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def]
  simp

/-- In Schur coordinates, the root-free matrix Hermite form is exactly the unweighted square
sum of diagonal characteristic nodes. -/
theorem finiteMatrixUnweightedTraceHankel_eq_schur
    {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
    {M U T : Matrix m m ℂ}
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T)
    (p : Polynomial ℝ) :
    finiteMatrixUnweightedTraceHankel M p =
      ∑ i : m, evalRealPolynomial p (T i i) ^ (2 : ℕ) := by
  classical
  rw [finiteMatrixUnweightedTraceHankel]
  simp_rw [GaloisForLFunctions.HTGeometry.trace_pow_eq_sum_diag
    hU1 hU2 hT hMT]
  simp_rw [Finset.mul_sum]
  calc
    ∑ r ∈ p.support, ∑ s ∈ p.support, ∑ i : m,
        ((p.coeff r : ℝ) : ℂ) * ((p.coeff s : ℝ) : ℂ) * (T i i) ^ (r + s) =
        ∑ r ∈ p.support, ∑ i : m, ∑ s ∈ p.support,
          ((p.coeff r : ℝ) : ℂ) * ((p.coeff s : ℝ) : ℂ) *
            (T i i) ^ (r + s) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = ∑ i : m, ∑ r ∈ p.support, ∑ s ∈ p.support,
          ((p.coeff r : ℝ) : ℂ) * ((p.coeff s : ℝ) : ℂ) *
            (T i i) ^ (r + s) := by
      exact Finset.sum_comm
    _ = ∑ i : m, evalRealPolynomial p (T i i) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [evalRealPolynomial_eq_sum_support, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [pow_add]
      ring

/-- **Root-free finite-matrix Hermite--Sylvester converse.**  Universal nonnegativity of the
literal power-trace form forces every Schur characteristic node to be real. -/
theorem finiteMatrix_unweightedTraceHankel_nonneg_implies_schur_real
    {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
    {M U T : Matrix m m ℂ}
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (finiteMatrixUnweightedTraceHankel M p).re) :
    ∀ i : m, (T i i).im = 0 := by
  apply finiteFamily_unweightedTraceHankel_nonneg_implies_real (fun i : m => T i i)
  intro p
  rw [← finiteMatrixUnweightedTraceHankel_eq_schur hU1 hU2 hT hMT]
  exact hpos p

/-- Finite-matrix Hermite--Sylvester converse with the explicit `2n+1` degree window. -/
theorem finiteMatrix_unweightedTraceHankel_nonneg_degree_le_implies_schur_real
    {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
    {M U T : Matrix m m ℂ}
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T)
    (hpos : ∀ p : Polynomial ℝ,
      p.natDegree ≤ 2 * Fintype.card m + 1 →
      0 ≤ (finiteMatrixUnweightedTraceHankel M p).re) :
    ∀ i : m, (T i i).im = 0 := by
  apply finiteFamily_unweightedTraceHankel_nonneg_degree_le_implies_real
    (fun i : m => T i i)
  intro p hp
  rw [← finiteMatrixUnweightedTraceHankel_eq_schur hU1 hU2 hT hMT]
  exact hpos p hp

end

end RHTower
