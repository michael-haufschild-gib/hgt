import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Strict disk location of finite OPUC zeros

This module starts the unconditional Bernstein--Szegő formalization.  It works directly with the
positive-definite Cayley--Toeplitz Gram section.  The head and tail embeddings of a coefficient
vector have the same Gram norm because the matrix is Toeplitz.  Combining this shift isometry
with orthogonality of the last Gram--Schmidt vector gives the strict unit-disk location of every
zero of the corresponding finite orthogonal polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexOrder InnerProductSpace ComplexConjugate

noncomputable section

/-- Embed a degree-at-most `N - 1` coefficient vector as the low coefficients of a vector of
length `N + 1`. -/
def opucHead {N : ℕ} (q : Fin N → ℂ) : Fin (N + 1) → ℂ :=
  Fin.snoc q 0

/-- Multiply a degree-at-most `N - 1` coefficient vector by the polynomial variable. -/
def opucTail {N : ℕ} (q : Fin N → ℂ) : Fin (N + 1) → ℂ :=
  Fin.cons 0 q

@[simp]
theorem opucHead_castSucc {N : ℕ} (q : Fin N → ℂ) (i : Fin N) :
    opucHead q i.castSucc = q i := by
  simp [opucHead]

@[simp]
theorem opucHead_last {N : ℕ} (q : Fin N → ℂ) :
    opucHead q (Fin.last N) = 0 := by
  simp [opucHead]

@[simp]
theorem opucTail_zero {N : ℕ} (q : Fin N → ℂ) :
    opucTail q 0 = 0 := by
  simp [opucTail]

@[simp]
theorem opucTail_succ {N : ℕ} (q : Fin N → ℂ) (i : Fin N) :
    opucTail q i.succ = q i := by
  simp [opucTail]

/-- Toeplitz shift isometry as an exact equality of the two Gram quadratic forms. -/
theorem opucTail_gram_eq_opucHead_gram
    {N : ℕ} (c : ℤ → ℂ) (q : Fin N → ℂ) :
    ((circleToeplitzGram N c) *ᵥ opucTail q) ⬝ᵥ star (opucTail q) =
      ((circleToeplitzGram N c) *ᵥ opucHead q) ⬝ᵥ star (opucHead q) := by
  let common : ℂ :=
    ∑ i : Fin N, (∑ j : Fin N, c ((i : ℤ) - (j : ℤ)) * q j) * star (q i)
  have htail : ((circleToeplitzGram N c) *ᵥ opucTail q) ⬝ᵥ star (opucTail q) =
      common := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    simp_rw [Fin.sum_univ_succ]
    simp [circleToeplitzGram, opucTail, common]
  have hhead : ((circleToeplitzGram N c) *ᵥ opucHead q) ⬝ᵥ star (opucHead q) =
      common := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    simp_rw [Fin.sum_univ_castSucc]
    simp [circleToeplitzGram, opucHead, common]
  exact htail.trans hhead.symm

/-- The explicit sesquilinear form associated to a finite Toeplitz section.  This definition keeps
the theorem statements independent of a locally installed normed-space instance. -/
def finiteToeplitzInner {N : ℕ} (c : ℤ → ℂ)
    (u v : Fin (N + 1) → ℂ) : ℂ :=
  ((circleToeplitzGram N c) *ᵥ v) ⬝ᵥ star u

/-- A normalized vector orthogonal to all low coefficients cannot factor through a root on or
outside the unit circle.  This is the Hilbert-geometric core of the OPUC root-location theorem. -/
theorem norm_lt_one_of_toeplitz_root_factor
    {N : ℕ} {c : ℤ → ℂ} (hG : (circleToeplitzGram N c).PosDef)
    {p : Fin (N + 1) → ℂ} {q : Fin N → ℂ} {a : ℂ}
    (hfactor : p = opucTail q - a • opucHead q)
    (horth : finiteToeplitzInner c p (opucHead q) = 0)
    (hnorm : finiteToeplitzInner c p p = 1) :
    ‖a‖ < 1 := by
  letI := Matrix.toSeminormedAddCommGroup
    (circleToeplitzGram N c) hG.posSemidef
  letI := Matrix.toInnerProductSpace (circleToeplitzGram N c) hG.posSemidef
  let u : Fin (N + 1) → ℂ := opucTail q
  let v : Fin (N + 1) → ℂ := opucHead q
  have hinnerShift : inner ℂ u u = inner ℂ v v := by
    change ((circleToeplitzGram N c) *ᵥ opucTail q) ⬝ᵥ star (opucTail q) =
      ((circleToeplitzGram N c) *ᵥ opucHead q) ⬝ᵥ star (opucHead q)
    exact opucTail_gram_eq_opucHead_gram c q
  have hinnerOrth : inner ℂ p v = 0 := by
    change finiteToeplitzInner c p (opucHead q) = 0
    exact horth
  have hinnerNorm : inner ℂ p p = 1 := by
    change finiteToeplitzInner c p p = 1
    exact hnorm
  have hu : u = p + a • v := by
    rw [hfactor]
    simp only [u, v]
    abel
  have hinnerOrth' : inner ℂ v p = 0 := by
    rw [← inner_conj_symm]
    simp [hinnerOrth]
  have hexpand : inner ℂ u u =
      inner ℂ p p + (Complex.normSq a : ℂ) * inner ℂ v v := by
    rw [hu]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hinnerOrth, hinnerOrth', mul_zero, add_zero, zero_add]
    rw [← mul_assoc, Complex.mul_conj]
  have hq : RCLike.re (inner ℂ v v) =
      1 + Complex.normSq a * RCLike.re (inner ℂ v v) := by
    calc
      RCLike.re (inner ℂ v v) = RCLike.re (inner ℂ u u) :=
        congrArg RCLike.re hinnerShift.symm
      _ = RCLike.re
          (inner ℂ p p + (Complex.normSq a : ℂ) * inner ℂ v v) :=
        congrArg RCLike.re hexpand
      _ = 1 + Complex.normSq a * RCLike.re (inner ℂ v v) := by
        rw [hinnerNorm]
        norm_num
  have hv0 : 0 ≤ RCLike.re (inner ℂ v v) := inner_self_nonneg
  by_contra! ha
  have hsq : 1 ≤ Complex.normSq a := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  nlinarith

/-- The normalized final Gram--Schmidt coefficient vector for the level-`N` Toeplitz section. -/
def finiteOPUCVector {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) : Fin (N + 1) → ℂ := by
  let normInst := Matrix.toNormedAddCommGroup (circleToeplitzGram N c) hG
  letI : NormedAddCommGroup (Fin (N + 1) → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin (N + 1) → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace (circleToeplitzGram N c) hG.posSemidef
  let b : Module.Basis (Fin (N + 1)) ℂ (Fin (N + 1) → ℂ) :=
    Pi.basisFun ℂ (Fin (N + 1))
  exact InnerProductSpace.gramSchmidtNormed ℂ b (Fin.last N)

/-- The degree-`N` orthonormal polynomial encoded by the last inverse-Cholesky row. -/
def finiteOPUCPolynomial {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) : Polynomial ℂ :=
  Polynomial.ofFn (N + 1) (finiteOPUCVector c hG)

theorem finiteOPUCVector_inner_self {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    finiteToeplitzInner c (finiteOPUCVector c hG) (finiteOPUCVector c hG) = 1 := by
  let normInst := Matrix.toNormedAddCommGroup (circleToeplitzGram N c) hG
  letI : NormedAddCommGroup (Fin (N + 1) → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin (N + 1) → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace (circleToeplitzGram N c) hG.posSemidef
  let b : Module.Basis (Fin (N + 1)) ℂ (Fin (N + 1) → ℂ) :=
    Pi.basisFun ℂ (Fin (N + 1))
  change inner ℂ (InnerProductSpace.gramSchmidtNormed ℂ b (Fin.last N))
      (InnerProductSpace.gramSchmidtNormed ℂ b (Fin.last N)) = 1
  have horth := InnerProductSpace.gramSchmidtNormed_orthonormal b.linearIndependent
  simpa using (orthonormal_iff_ite.mp horth (Fin.last N) (Fin.last N))

/-- The final orthogonal polynomial is orthogonal to every lower coefficient vector. -/
theorem finiteOPUCVector_inner_head {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (q : Fin N → ℂ) :
    finiteToeplitzInner c (finiteOPUCVector c hG) (opucHead q) = 0 := by
  let normInst := Matrix.toNormedAddCommGroup (circleToeplitzGram N c) hG
  letI : NormedAddCommGroup (Fin (N + 1) → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin (N + 1) → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace (circleToeplitzGram N c) hG.posSemidef
  let b : Module.Basis (Fin (N + 1)) ℂ (Fin (N + 1) → ℂ) :=
    Pi.basisFun ℂ (Fin (N + 1))
  have hhead : opucHead q = ∑ i : Fin N, q i • b i.castSucc := by
    ext j
    by_cases hj : j = Fin.last N
    · subst j
      simp [opucHead, b, Pi.basisFun_apply]
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      simp [opucHead, b, Pi.basisFun_apply, Pi.single_apply]
  change inner ℂ (InnerProductSpace.gramSchmidtNormed ℂ b (Fin.last N)) (opucHead q) = 0
  rw [hhead, inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  suffices inner ℂ (InnerProductSpace.gramSchmidtNormed ℂ b (Fin.last N))
      (b i.castSucc) = 0 by rw [this, mul_zero]
  simp only [InnerProductSpace.gramSchmidtNormed, inner_smul_left]
  rw [InnerProductSpace.gramSchmidt_inv_triangular ℂ b (Fin.castSucc_lt_last i), mul_zero]

/-- The leading coefficient of the finite OPUC vector is nonzero. -/
theorem finiteOPUCVector_last_ne_zero {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    finiteOPUCVector c hG (Fin.last N) ≠ 0 := by
  intro hzero
  have hpos := gramSchmidtInverseFrame_diag_pos
    (circleToeplitzGram N c) hG (Fin.last N)
  change 0 < (star (finiteOPUCVector c hG (Fin.last N))).re at hpos
  rw [hzero] at hpos
  norm_num at hpos

/-- The finite OPUC polynomial has exactly the expected degree. -/
theorem finiteOPUCPolynomial_natDegree {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    (finiteOPUCPolynomial c hG).natDegree = N := by
  apply le_antisymm
  · rw [finiteOPUCPolynomial]
    exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N)
      (finiteOPUCVector c hG))
  · apply Polynomial.le_natDegree_of_ne_zero
    simpa [finiteOPUCPolynomial] using finiteOPUCVector_last_ne_zero c hG

/-- Every zero of a positive-degree finite OPUC polynomial lies strictly inside the unit disk. -/
theorem finiteOPUCPolynomial_isRoot_norm_lt_one_succ
    {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram (N + 1) c).PosDef)
    {a : ℂ} (ha : (finiteOPUCPolynomial c hG).IsRoot a) :
    ‖a‖ < 1 := by
  let p : Polynomial ℂ := finiteOPUCPolynomial c hG
  let qpoly : Polynomial ℂ := p /ₘ (Polynomial.X - Polynomial.C a)
  have hpdeg : p.natDegree = N + 1 := finiteOPUCPolynomial_natDegree c hG
  have hqdeg : qpoly.natDegree < N + 1 := by
    change (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree < N + 1
    rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C a),
      Polynomial.natDegree_X_sub_C, hpdeg]
    omega
  let q : Fin (N + 1) → ℂ := Polynomial.toFn (N + 1) qpoly
  have hqpoly : Polynomial.ofFn (N + 1) q = qpoly := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hqdeg
  have hpoly : (Polynomial.X - Polynomial.C a) * qpoly = p := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
  have hfactor : finiteOPUCVector c hG = opucTail q - a • opucHead q := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · have hcoeff := congrArg (fun r : Polynomial ℂ => r.coeff 0) hpoly
      simp [p, finiteOPUCPolynomial, qpoly, q] at hcoeff ⊢
      exact hcoeff.symm
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · have hcoeff := congrArg (fun r : Polynomial ℂ => r.coeff (N + 1)) hpoly
        change ((Polynomial.X - Polynomial.C a) * qpoly).coeff (N + 1) =
          p.coeff (N + 1) at hcoeff
        rw [Polynomial.coeff_X_sub_C_mul] at hcoeff
        have hzero : qpoly.coeff (N + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hqdeg
        simp [p, finiteOPUCPolynomial, q, Polynomial.toFn, hzero] at hcoeff ⊢
        exact hcoeff.symm
      · have hcoeff := congrArg (fun r : Polynomial ℂ => r.coeff (i + 1)) hpoly
        change ((Polynomial.X - Polynomial.C a) * qpoly).coeff (i + 1) =
          p.coeff (i + 1) at hcoeff
        rw [Polynomial.coeff_X_sub_C_mul] at hcoeff
        change finiteOPUCVector c hG i.castSucc.succ =
          opucTail q i.castSucc.succ - a * opucHead q i.castSucc.succ
        rw [show opucHead q i.castSucc.succ = q i.succ by
          rw [Fin.succ_castSucc]
          exact opucHead_castSucc q i.succ]
        simp [p, finiteOPUCPolynomial, q, Polynomial.toFn] at hcoeff ⊢
        exact hcoeff.symm
  exact norm_lt_one_of_toeplitz_root_factor hG hfactor
    (finiteOPUCVector_inner_head c hG q)
    (finiteOPUCVector_inner_self c hG)

/-- **Strict OPUC root-location theorem.** For every positive-definite finite Toeplitz section,
all roots of its normalized final Gram--Schmidt polynomial lie in the open unit disk. -/
theorem finiteOPUCPolynomial_isRoot_norm_lt_one
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {a : ℂ} (ha : (finiteOPUCPolynomial c hG).IsRoot a) :
    ‖a‖ < 1 := by
  cases N with
  | zero =>
      have hpdeg := finiteOPUCPolynomial_natDegree c hG
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
      have hcoeff : (finiteOPUCPolynomial c hG).coeff 0 ≠ 0 := by
        simpa [finiteOPUCPolynomial] using finiteOPUCVector_last_ne_zero c hG
      rw [hpC] at ha
      simp [Polynomial.IsRoot, hcoeff] at ha
  | succ N =>
      exact finiteOPUCPolynomial_isRoot_norm_lt_one_succ c hG ha

end

end GaloisForLFunctions.HTGeometry
