import GaloisForLFunctions.HilbertMetric.GramCurvaturePersistence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Determinant curvature from an entrywise matrix 2-jet

This module differentiates the determinant through its finite Leibniz expansion.  It constructs
its first and second scalar jets from the value and first two entrywise derivative matrices and
then proves the literal second-derivative formula for `log det`.  Together with coherent
collision jets, this reduces Gaussian curvature persistence to identifying the limiting matrix
2-jet.
-/

open Filter

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- First derivative of a determinant as a polynomial in its value and entrywise derivative. -/
def detFirstJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : Matrix ι ι ℝ) : ℝ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : ι, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * A₁ (σ i) i

private def detFirstJetDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A dA B dB : Matrix ι ι ℝ) : ℝ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : ι,
      ((∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, A (σ k) k) * dA (σ j) j) *
        B (σ i) i +
        (∏ j ∈ Finset.univ.erase i, A (σ j) j) * dB (σ i) i)

/-- Second derivative of a determinant as a polynomial in its entrywise matrix 2-jet. -/
def detSecondJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℝ) : ℝ :=
  detFirstJetDerivative A A₁ A₁ A₂

/-- Entrywise derivatives determine the derivative of the matrix determinant. -/
theorem hasDerivAt_matrixDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (A₁ : Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ i j) x) :
    HasDerivAt (fun t => (A t).det) (detFirstJet (A x) A₁) x := by
  rw [show (fun t => (A t).det) = fun t =>
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, A t (σ i) i by
    funext t
    exact Matrix.det_apply' (A t)]
  unfold detFirstJet
  apply HasDerivAt.fun_sum
  intro σ hσ
  convert! ((HasDerivAt.fun_finsetProd fun i hi => hA (σ i) i).const_mul
    (((Equiv.Perm.sign σ : ℤ) : ℝ))) using 1

/-- Differentiating the first determinant jet produces the second determinant jet. -/
theorem hasDerivAt_matrixDetFirstJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : ℝ → Matrix ι ι ℝ) (A₂ : Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ x i j) x)
    (hA₁ : ∀ i j, HasDerivAt (fun t => A₁ t i j) (A₂ i j) x) :
    HasDerivAt (fun t => detFirstJet (A t) (A₁ t))
      (detSecondJet (A x) (A₁ x) A₂) x := by
  unfold detFirstJet detSecondJet detFirstJetDerivative
  apply HasDerivAt.fun_sum
  intro σ hσ
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i hi
  exact (HasDerivAt.fun_finsetProd fun j hj => hA (σ j) j).mul (hA₁ (σ i) i)

/-- The literal second derivative of a determinant is its algebraic second jet. -/
theorem det_secondDerivative_eq_jet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : ℝ → Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t) :
    deriv (deriv (fun t => (A t).det)) x = detSecondJet (A x) (A₁ x) (A₂ x) := by
  have hderiv :
      (fun t => deriv (fun s => (A s).det) t) =
        fun t => detFirstJet (A t) (A₁ t) := by
    funext t
    exact (hasDerivAt_matrixDet A (A₁ t) t (hA t)).deriv
  have hsecond := hasDerivAt_matrixDetFirstJet A A₁ (A₂ x) x (hA x) (hA₁ x)
  change deriv (fun t => deriv (fun s => (A s).det) t) x = _
  rw [hderiv]
  exact hsecond.deriv

/-- The literal second derivative of `log det` is the scalar curvature numerator divided by `det²`. -/
theorem logDet_secondDerivative_eq_jet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : ℝ → Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hdet : ∀ᶠ t in nhds x, (A t).det ≠ 0) :
    deriv (deriv (fun t => Real.log (A t).det)) x =
      ((A x).det * detSecondJet (A x) (A₁ x) (A₂ x) -
        detFirstJet (A x) (A₁ x) ^ 2) / (A x).det ^ 2 := by
  have hdetDeriv (t : ℝ) := hasDerivAt_matrixDet A (A₁ t) t (hA t)
  have hdetx : (A x).det ≠ 0 := mem_of_mem_nhds hdet
  have hlogDeriv :
      (fun t => deriv (fun s => Real.log (A s).det) t) =ᶠ[nhds x]
        fun t => detFirstJet (A t) (A₁ t) / (A t).det := by
    filter_upwards [hdet] with t ht
    exact ((hdetDeriv t).log ht).deriv
  have hfirstJet :=
    hasDerivAt_matrixDetFirstJet A A₁ (A₂ x) x (hA x) (hA₁ x)
  have hratio := hfirstJet.div (hdetDeriv x) hdetx
  have hactual := (hratio.congr_of_eventuallyEq hlogDeriv).deriv
  convert hactual using 1
  unfold detSecondJet
  ring

theorem hasDerivAt_det_one_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • B : Matrix ι ι ℝ).det) (Matrix.trace B) 0 := by
  let P : Polynomial ℝ := Matrix.det
    ((1 : Matrix ι ι (Polynomial ℝ)) + (Polynomial.X : Polynomial ℝ) •
      B.map (Polynomial.C : ℝ →+* Polynomial ℝ))
  have hpoly : HasDerivAt (fun t : ℝ => P.eval t) (Matrix.trace B) 0 := by
    convert! P.hasDerivAt 0 using 1
    simpa [P] using! (Matrix.derivative_det_one_add_X_smul B).symm
  convert hpoly using 1
  funext t
  simp [P, eval_det, ← Matrix.smul_eq_mul_diagonal]

theorem detFirstJet_eq_det_mul_trace_inv_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : Matrix ι ι ℝ) (hdet : A.det ≠ 0) :
    detFirstJet A A₁ = A.det * Matrix.trace (A⁻¹ * A₁) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hleft :
      HasDerivAt (fun t : ℝ => (A + t • A₁).det) (detFirstJet A A₁) 0 := by
    have hentry (i j : ι) :
        HasDerivAt (fun t : ℝ => (A + t • A₁) i j) (A₁ i j) 0 := by
      convert!
        (hasDerivAt_const (x := 0) (A i j)).add
          ((hasDerivAt_id (x := 0)).mul_const (A₁ i j)) using 1
      simp only [zero_add, one_mul]
    convert hasDerivAt_matrixDet
      (fun t : ℝ => A + t • A₁) A₁ 0 hentry using 1
    all_goals simp
  have hright := (hasDerivAt_det_one_add_smul (A⁻¹ * A₁)).const_mul A.det
  apply hleft.unique
  convert! hright using 1
  funext t
  calc
    (A + t • A₁).det = (A * (1 + t • (A⁻¹ * A₁))).det := by
      congr 1
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        Matrix.mul_nonsing_inv_cancel_left A A₁ hunit]
    _ = A.det * (1 + t • (A⁻¹ * A₁) : Matrix ι ι ℝ).det := Matrix.det_mul _ _

theorem hasDerivAt_matrix_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (A₁ : Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ i j) x)
    (hdet : (A x).det ≠ 0) :
    ∀ i j, HasDerivAt (fun t => (A t)⁻¹ i j)
      (-((A x)⁻¹ * A₁ * (A x)⁻¹) i j) x := by
  have hdetDeriv := hasDerivAt_matrixDet A A₁ x hA
  have hAdj (i j : ι) : DifferentiableAt ℝ (fun t => (A t).adjugate i j) x := by
    rw [show (fun t => (A t).adjugate i j) =
        fun t => ((A t).updateRow j (Pi.single i (1 : ℝ) : ι → ℝ)).det by
      funext t
      exact Matrix.adjugate_apply (A t) i j]
    exact (hasDerivAt_matrixDet
      (fun t => (A t).updateRow j (Pi.single i (1 : ℝ) : ι → ℝ))
      (A₁.updateRow j 0) x (by
        intro a b
        by_cases haj : a = j
        · subst a
          simpa [Matrix.updateRow_apply] using
            (hasDerivAt_const (x := x) ((Pi.single i (1 : ℝ) : ι → ℝ) b))
        · simpa [Matrix.updateRow_apply, haj] using
            hA a b)).differentiableAt
  let B₁ : Matrix ι ι ℝ := fun i j => deriv (fun t => (A t)⁻¹ i j) x
  have hB₁ (i j : ι) : HasDerivAt (fun t => (A t)⁻¹ i j) (B₁ i j) x := by
    apply DifferentiableAt.hasDerivAt
    rw [show (fun t => (A t)⁻¹ i j) =
        fun t => (A t).det⁻¹ * (A t).adjugate i j by
      funext t
      simp [Matrix.inv_def]]
    exact (hdetDeriv.differentiableAt.inv hdet).mul (hAdj i j)
  have hne : ∀ᶠ t in nhds x, (A t).det ≠ 0 :=
    (hdetDeriv.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hdet
  have hzero (i j : ι) : (A₁ * (A x)⁻¹ + A x * B₁) i j = 0 := by
    have hprod : HasDerivAt (fun t => (A t * (A t)⁻¹) i j)
        ((A₁ * (A x)⁻¹ + A x * B₁) i j) x := by
      simpa [Matrix.mul_apply, Finset.sum_add_distrib] using
        (HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB₁ k j))
    have heq :
        (fun t => (A t * (A t)⁻¹) i j) =ᶠ[nhds x]
          fun _ => (1 : Matrix ι ι ℝ) i j := by
      filter_upwards [hne] with t ht
      rw [Matrix.mul_nonsing_inv (A t) (isUnit_iff_ne_zero.mpr ht)]
    exact (hprod.congr_of_eventuallyEq heq.symm).unique
      (hasDerivAt_const (x := x) ((1 : Matrix ι ι ℝ) i j))
  have hmatrix : A₁ * (A x)⁻¹ + A x * B₁ = 0 := by
    ext i j
    simpa using hzero i j
  have hright : A x * B₁ = -(A₁ * (A x)⁻¹) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hmatrix
  have hunit : IsUnit (A x).det := isUnit_iff_ne_zero.mpr hdet
  have hB₁eq : B₁ = -((A x)⁻¹ * A₁ * (A x)⁻¹) := by
    calc
      B₁ = ((A x)⁻¹ * A x) * B₁ := by
        rw [Matrix.nonsing_inv_mul (A x) hunit, Matrix.one_mul]
      _ = (A x)⁻¹ * (A x * B₁) := Matrix.mul_assoc _ _ _
      _ = (A x)⁻¹ * (-(A₁ * (A x)⁻¹)) := by rw [hright]
      _ = -((A x)⁻¹ * A₁ * (A x)⁻¹) := by
        rw [Matrix.mul_neg, Matrix.mul_assoc]
  intro i j
  have h := hB₁ i j
  rw [hB₁eq] at h
  simpa using h

theorem detSecondJet_eq_det_mul_trace_sq_add_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℝ) (hdet : A.det ≠ 0) :
    detSecondJet A A₁ A₂ =
      A.det * (Matrix.trace (A⁻¹ * A₁) ^ 2 + gramLogCurvatureJet A A₁ A₂) := by
  let P : ℝ → Matrix ι ι ℝ := fun t => A + t • A₁
  let Q : ℝ → Matrix ι ι ℝ := fun t => A₁ + t • A₂
  have hP (i j : ι) : HasDerivAt (fun t => P t i j) (A₁ i j) 0 := by
    dsimp [P]
    convert!
      (hasDerivAt_const (x := 0) (A i j)).add
        ((hasDerivAt_id (x := 0)).mul_const (A₁ i j)) using 1
    simp only [zero_add, one_mul]
  have hQ (i j : ι) : HasDerivAt (fun t => Q t i j) (A₂ i j) 0 := by
    dsimp [Q]
    convert!
      (hasDerivAt_const (x := 0) (A₁ i j)).add
        ((hasDerivAt_id (x := 0)).mul_const (A₂ i j)) using 1
    simp only [zero_add, one_mul]
  have hleft : HasDerivAt (fun t => detFirstJet (P t) (Q t))
      (detSecondJet A A₁ A₂) 0 := by
    convert hasDerivAt_matrixDetFirstJet P Q A₂ 0
      (by simpa [Q] using hP) hQ using 1
    all_goals simp [P, Q]
  have hdetPath : HasDerivAt (fun t => (P t).det) (detFirstJet A A₁) 0 := by
    convert hasDerivAt_matrixDet P A₁ 0 hP using 1
    all_goals simp [P]
  have hinv := hasDerivAt_matrix_inv P A₁ 0 hP (by simpa [P] using hdet)
  have htraceRaw : HasDerivAt (fun t => Matrix.trace ((P t)⁻¹ * Q t))
      (Matrix.trace ((-(A⁻¹ * A₁ * A⁻¹)) * A₁ + A⁻¹ * A₂)) 0 := by
    unfold Matrix.trace
    convert! HasDerivAt.fun_sum (fun i _ =>
      (by
        simpa [Matrix.mul_apply, Finset.sum_add_distrib, P, Q] using!
          (HasDerivAt.fun_sum fun k _ => (hinv i k).mul (hQ k i)) :
        HasDerivAt (fun t => ((P t)⁻¹ * Q t) i i)
          (((-(A⁻¹ * A₁ * A⁻¹)) * A₁ + A⁻¹ * A₂) i i) 0)) using 1
  have htrace : HasDerivAt (fun t => Matrix.trace ((P t)⁻¹ * Q t))
      (gramLogCurvatureJet A A₁ A₂) 0 := by
    convert htraceRaw using 1
    unfold gramLogCurvatureJet
    congr 1
    simp [Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  have hright := hdetPath.mul htrace
  have hne : ∀ᶠ t in nhds (0 : ℝ), (P t).det ≠ 0 :=
    (hdetPath.continuousAt.ne_iff_eventually_ne continuousAt_const).mp
      (by simpa [P] using hdet)
  have heq :
      (fun t => detFirstJet (P t) (Q t)) =ᶠ[nhds (0 : ℝ)]
        fun t => (P t).det * Matrix.trace ((P t)⁻¹ * Q t) := by
    filter_upwards [hne] with t ht
    exact detFirstJet_eq_det_mul_trace_inv_mul (P t) (Q t) ht
  have hderivEq := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  rw [detFirstJet_eq_det_mul_trace_inv_mul A A₁ hdet] at hderivEq
  simp [P, Q] at hderivEq
  nlinarith

theorem determinantCurvatureNumerator_eq_det_sq_mul_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℝ) (hdet : A.det ≠ 0) :
    A.det * detSecondJet A A₁ A₂ - detFirstJet A A₁ ^ 2 =
      A.det ^ 2 * gramLogCurvatureJet A A₁ A₂ := by
  rw [detSecondJet_eq_det_mul_trace_sq_add_gram A A₁ A₂ hdet,
    detFirstJet_eq_det_mul_trace_inv_mul A A₁ hdet]
  ring

theorem logDet_secondDerivative_eq_gramLogCurvatureJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : ℝ → Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hdet : ∀ᶠ t in nhds x, (A t).det ≠ 0) :
    deriv (deriv (fun t => Real.log (A t).det)) x =
      gramLogCurvatureJet (A x) (A₁ x) (A₂ x) := by
  have hx : (A x).det ≠ 0 := mem_of_mem_nhds hdet
  rw [logDet_secondDerivative_eq_jet A A₁ A₂ x hA hA₁ hdet,
    determinantCurvatureNumerator_eq_det_sq_mul_gram _ _ _ hx]
  field_simp [hx]


end

end GaloisForLFunctions.HilbertMetric
