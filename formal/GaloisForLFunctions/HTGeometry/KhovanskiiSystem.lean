import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Nonsingular exponential-polynomial systems

A Khovanskii system in `n` variables is a square family of polynomials in the additive coordinates
`X_i` and multiplicative coordinates `Y_i`, evaluated on the exponential graph `Y_i = exp X_i`.
Its nonsingular zero locus is discrete, hence countable.  This is the analytic-countability engine
for exponential algebraic closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Additive and exponential coordinates of a complex tuple. -/
def complexExponentialGraph {n : ℕ} (z : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ
  | Sum.inl i => z i
  | Sum.inr i => Complex.exp (z i)

/-- Evaluation of one exponential polynomial. -/
def exponentialPolynomialEval {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin n) ℂ)
    (z : Fin n → ℂ) : ℂ :=
  MvPolynomial.eval (complexExponentialGraph z) P

/-- Evaluation of a square exponential-polynomial system. -/
def exponentialSystemEval {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => exponentialPolynomialEval (P i) z

theorem analyticAt_complexExponentialGraph {n : ℕ} (z : Fin n → ℂ) :
    AnalyticAt ℂ complexExponentialGraph z := by
  refine AnalyticAt.pi fun j => ?_
  cases j with
  | inl i =>
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z
  | inr i =>
      exact ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin n => ℂ) i).analyticAt z).cexp'

theorem analyticAt_exponentialPolynomialEval {n : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ) :
    AnalyticAt ℂ (exponentialPolynomialEval P) z := by
  unfold exponentialPolynomialEval
  induction P using MvPolynomial.induction_on with
  | C c =>
      simpa only [MvPolynomial.eval_C] using
        (analyticAt_const (𝕜 := ℂ) (x := z) :
          AnalyticAt ℂ (fun _ : Fin n → ℂ => c) z)
  | add P Q hP hQ =>
      simp only [map_add]
      change AnalyticAt ℂ
        ((fun w => MvPolynomial.eval (complexExponentialGraph w) P) +
          fun w => MvPolynomial.eval (complexExponentialGraph w) Q) z
      exact hP.add hQ
  | mul_X P i hP =>
      have hi : AnalyticAt ℂ (fun w : Fin n → ℂ => complexExponentialGraph w i) z := by
        cases i with
        | inl j =>
            exact (ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin n => ℂ) j).analyticAt z
        | inr j =>
            exact ((ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin n => ℂ) j).analyticAt z).cexp'
      simp only [map_mul, MvPolynomial.eval_X]
      change AnalyticAt ℂ
        ((fun w => MvPolynomial.eval (complexExponentialGraph w) P) *
          fun w => complexExponentialGraph w i) z
      exact hP.mul hi

theorem analyticAt_exponentialSystemEval {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ) :
    AnalyticAt ℂ (exponentialSystemEval P) z := by
  exact AnalyticAt.pi fun i => analyticAt_exponentialPolynomialEval (P i) z

/-- Jacobian after restricting a polynomial system to the exponential graph. -/
def exponentialJacobian {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    MvPolynomial.eval (complexExponentialGraph z) (MvPolynomial.pderiv (Sum.inl j) (P i)) +
      Complex.exp (z j) *
        MvPolynomial.eval (complexExponentialGraph z) (MvPolynomial.pderiv (Sum.inr j) (P i))

theorem fderiv_complexExponentialGraph_apply {n : ℕ} (z v : Fin n → ℂ)
    (i : Fin n ⊕ Fin n) :
    fderiv ℂ (fun w : Fin n → ℂ => complexExponentialGraph w i) z v =
      match i with
      | Sum.inl j => v j
      | Sum.inr j => Complex.exp (z j) * v j := by
  cases i with
  | inl j =>
      have hproj : HasFDerivAt (fun w : Fin n → ℂ => w j)
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) z :=
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin n => ℂ) j).hasFDerivAt
      rw [show (fun w : Fin n → ℂ => complexExponentialGraph w (Sum.inl j)) =
          fun w => w j by rfl, hproj.fderiv]
      rfl
  | inr j =>
      have hproj : HasFDerivAt (fun w : Fin n → ℂ => w j)
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) z :=
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin n => ℂ) j).hasFDerivAt
      have hcomp := (Complex.hasDerivAt_exp (z j)).hasFDerivAt.comp z hproj
      have hcomp' : HasFDerivAt (fun w : Fin n → ℂ => Complex.exp (w j))
          ((ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (z j))).comp
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j)) z := by
        simpa [Function.comp_def] using hcomp
      rw [show (fun w : Fin n → ℂ => complexExponentialGraph w (Sum.inr j)) =
          fun w => Complex.exp (w j) by rfl, hcomp'.fderiv]
      simp [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm]

/-- Chain rule for one polynomial restricted to the exponential graph. -/
theorem fderiv_exponentialPolynomialEval_apply {n : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin n) ℂ) (z v : Fin n → ℂ) :
    fderiv ℂ (exponentialPolynomialEval P) z v =
      ∑ j, (MvPolynomial.eval (complexExponentialGraph z)
          (MvPolynomial.pderiv (Sum.inl j) P) +
        Complex.exp (z j) * MvPolynomial.eval (complexExponentialGraph z)
          (MvPolynomial.pderiv (Sum.inr j) P)) * v j := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hconst : exponentialPolynomialEval (MvPolynomial.C c) =
          fun _ : Fin n → ℂ => c := by
        funext w
        simp [exponentialPolynomialEval]
      rw [hconst]
      change (fderiv ℂ (Function.const (Fin n → ℂ) c) z) v = _
      rw [fderiv_const]
      simp
  | add P Q hP hQ =>
      rw [show exponentialPolynomialEval (P + Q) =
          exponentialPolynomialEval P + exponentialPolynomialEval Q by
        funext w
        simp [exponentialPolynomialEval]]
      rw [fderiv_add (analyticAt_exponentialPolynomialEval P z).differentiableAt
        (analyticAt_exponentialPolynomialEval Q z).differentiableAt]
      simp only [add_apply, hP, hQ, map_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  | mul_X P i hP =>
      have hmul : exponentialPolynomialEval (P * MvPolynomial.X i) =
          exponentialPolynomialEval P *
            (fun w : Fin n → ℂ => complexExponentialGraph w i) := by
        funext w
        simp [exponentialPolynomialEval]
      have hcoord : DifferentiableAt ℂ
          (fun w : Fin n → ℂ => complexExponentialGraph w i) z := by
        cases i with
        | inl j => exact differentiableAt_apply j z
        | inr j =>
            exact Complex.differentiable_exp.differentiableAt.comp z
              (differentiableAt_apply j z)
      rw [hmul, fderiv_mul
        (analyticAt_exponentialPolynomialEval P z).differentiableAt
        hcoord]
      simp only [add_apply, smul_apply, hP, fderiv_complexExponentialGraph_apply]
      simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.pderiv_X,
        MvPolynomial.eval_X]
      cases i with
      | inl k =>
          simp [complexExponentialGraph, exponentialPolynomialEval, Pi.single_apply]
          simp_rw [add_mul, Finset.sum_add_distrib]
          simp
          ring_nf
          rw [Finset.mul_sum, Finset.mul_sum]
          simp [mul_assoc]
      | inr k =>
          simp [complexExponentialGraph, exponentialPolynomialEval, Pi.single_apply]
          simp_rw [add_mul, Finset.sum_add_distrib]
          try simp
          ring_nf
          simp_rw [mul_ite, ite_mul, Finset.sum_add_distrib]
          simp
          rw [Finset.mul_sum, Finset.mul_sum]
          simp [mul_assoc, mul_comm, mul_left_comm]
          abel

/-- The derivative of a square exponential-polynomial system is its exponential Jacobian. -/
theorem fderiv_exponentialSystemEval_apply {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z v : Fin n → ℂ) :
    fderiv ℂ (exponentialSystemEval P) z v =
      (exponentialJacobian P z).mulVec v := by
  funext i
  have hdiff : DifferentiableAt ℂ (exponentialSystemEval P) z :=
    (analyticAt_exponentialSystemEval P z).differentiableAt
  have hi := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v)
    (fderiv_apply hdiff i)
  change fderiv ℂ (exponentialPolynomialEval (P i)) z v =
    fderiv ℂ (exponentialSystemEval P) z v i at hi
  rw [fderiv_exponentialPolynomialEval_apply] at hi
  simpa [exponentialJacobian, Matrix.mulVec, dotProduct] using hi.symm

/-- A nonzero exponential-Jacobian determinant makes the analytic derivative bijective. -/
theorem bijective_fderiv_exponentialSystemEval_of_det_ne_zero {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ)
    (hdet : (exponentialJacobian P z).det ≠ 0) :
    Function.Bijective (fderiv ℂ (exponentialSystemEval P) z) := by
  let A := exponentialJacobian P z
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit hunit
  have hsub : A.submatrix id id = A := by
    ext i j
    rfl
  have hsurj : Function.Surjective A.mulVec :=
    matrix_mulVec_surjective_of_submatrix_det_ne_zero A id (by
      rw [hsub]
      exact hdet)
  constructor
  · intro u v huv
    apply hinj
    simpa [A, fderiv_exponentialSystemEval_apply] using huv
  · intro y
    obtain ⟨v, hv⟩ := hsurj y
    exact ⟨v, by simpa [A, fderiv_exponentialSystemEval_apply] using hv⟩

/-- Nonsingular zeros of one fixed square exponential-polynomial system. -/
def khovanskiiLocus {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) : Set (Fin n → ℂ) :=
  {z | exponentialSystemEval P z = 0 ∧
    Function.Bijective (fderiv ℂ (exponentialSystemEval P) z)}

theorem mem_khovanskiiLocus_of_eval_eq_zero_of_det_ne_zero {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) (z : Fin n → ℂ)
    (hzero : exponentialSystemEval P z = 0)
    (hdet : (exponentialJacobian P z).det ≠ 0) :
    z ∈ khovanskiiLocus P :=
  ⟨hzero, bijective_fderiv_exponentialSystemEval_of_det_ne_zero P z hdet⟩

/-- Every nonsingular exponential-polynomial zero is isolated. -/
theorem isDiscrete_khovanskiiLocus {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) :
    IsDiscrete (khovanskiiLocus P) := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  intro z
  let D := fderiv ℂ (exponentialSystemEval P) (z : Fin n → ℂ)
  have hbij : Function.Bijective D := z.2.2
  let e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.ofBijective D
      (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)
  have hstrict : HasStrictFDerivAt (exponentialSystemEval P)
      (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) z := by
    have hbase := (analyticAt_exponentialSystemEval P z).hasStrictFDerivAt
    have he : (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = D := rfl
    rw [he]
    exact hbase
  let phi := hstrict.toOpenPartialHomeomorph (exponentialSystemEval P)
  have hzsource : (z : Fin n → ℂ) ∈ phi.source :=
    hstrict.mem_toOpenPartialHomeomorph_source
  have hopen : IsOpen (Subtype.val ⁻¹' phi.source : Set (khovanskiiLocus P)) :=
    phi.open_source.preimage continuous_subtype_val
  convert hopen using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · rintro rfl
    exact hzsource
  · intro hw
    apply Subtype.ext
    apply phi.injOn hw hzsource
    change exponentialSystemEval P w = exponentialSystemEval P z
    rw [w.2.1, z.2.1]

/-- A fixed Khovanskii system has only countably many nonsingular complex zeros. -/
theorem countable_khovanskiiLocus {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) :
    (khovanskiiLocus P).Countable := by
  haveI : DiscreteTopology (khovanskiiLocus P) :=
    (isDiscrete_iff_discreteTopology.mp (isDiscrete_khovanskiiLocus P))
  exact Set.countable_coe_iff.mp
    (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- Coordinates occurring in the nonsingular zero locus of one fixed system. -/
def khovanskiiCoordinateSet {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) : Set ℂ :=
  ⋃ i : Fin n, (fun z : Fin n → ℂ => z i) '' khovanskiiLocus P

theorem countable_khovanskiiCoordinateSet {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ) :
    (khovanskiiCoordinateSet P).Countable := by
  exact Set.countable_iUnion fun i =>
    (countable_khovanskiiLocus P).image (fun z : Fin n → ℂ => z i)

end

end GaloisForLFunctions.HTGeometry
