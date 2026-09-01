import GaloisForLFunctions.HTGeometry.ComplexDeterminantSecondJet
import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicSkewAdjointAdditiveTwoPortNoGo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Arbitrary-rank trace-free skew-adjoint additive SC no-go

For every entire finite matrix curve `M` centered at zero, trace-free at every spectral point,
and tied to its negative Schwarz-reflected conjugate transpose, Jacobi's second-variation formula
gives

`(det (1 + M))''(0) = -tr(M'(0)^2) = ∑ᵢⱼ |M'ᵢⱼ(0)|² ≥ 0`.

The rank may vary with the cutoff. Cauchy convergence of jets therefore prevents these determinant
stages from converging compact-open to normalized Xi, whose central second jet is strictly negative.
This closes

`finite trace-free skew-adjoint additive SC stages -> Xi determinant landing
  -> SC divisor/orientation endpoint -> RH`

at its Xi-landing gate. The opposite Hermitian sign, non-trace-free completions, regularized
infinite-dimensional determinants, and nondeterminantal landings are not excluded.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasDerivAt_complexDet_one_add_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    HasDerivAt (fun z : ℂ => (1 + z • B : Matrix ι ι ℂ).det)
      (Matrix.trace B) 0 := by
  let P : Polynomial ℂ := Matrix.det
    ((1 : Matrix ι ι (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
      B.map (Polynomial.C : ℂ →+* Polynomial ℂ))
  have hpoly : HasDerivAt (fun z : ℂ => P.eval z) (Matrix.trace B) 0 := by
    convert! P.hasDerivAt 0 using 1
    simpa [P] using! (Matrix.derivative_det_one_add_X_smul B).symm
  convert hpoly using 1
  funext z
  simp [P, eval_det, ← Matrix.smul_eq_mul_diagonal]

theorem complexDetFirstJet_eq_det_mul_trace_inv_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : Matrix ι ι ℂ) (hdet : A.det ≠ 0) :
    complexDetFirstJet A A₁ = A.det * Matrix.trace (A⁻¹ * A₁) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hleft :
      HasDerivAt (fun t : ℂ => (A + t • A₁).det)
        (complexDetFirstJet A A₁) 0 := by
    have hentry (i j : ι) :
        HasDerivAt (fun t : ℂ => (A + t • A₁) i j) (A₁ i j) 0 := by
      convert!
        (hasDerivAt_const (x := 0) (A i j)).add
          ((hasDerivAt_id (x := 0)).mul_const (A₁ i j)) using 1
      simp only [zero_add, one_mul]
    convert hasDerivAt_complexMatrixDet
      (fun t : ℂ => A + t • A₁) A₁ 0 hentry using 1
    all_goals simp
  have hright := (hasDerivAt_complexDet_one_add_smul (A⁻¹ * A₁)).const_mul A.det
  apply hleft.unique
  convert! hright using 1
  funext t
  calc
    (A + t • A₁).det = (A * (1 + t • (A⁻¹ * A₁))).det := by
      congr 1
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        Matrix.mul_nonsing_inv_cancel_left A A₁ hunit]
    _ = A.det * (1 + t • (A⁻¹ * A₁) : Matrix ι ι ℂ).det := Matrix.det_mul _ _

theorem hasDerivAt_complexMatrix_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) (A₁ : Matrix ι ι ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ i j) x)
    (hdet : (A x).det ≠ 0) :
    ∀ i j, HasDerivAt (fun t => (A t)⁻¹ i j)
      (-((A x)⁻¹ * A₁ * (A x)⁻¹) i j) x := by
  have hdetDeriv := hasDerivAt_complexMatrixDet A A₁ x hA
  have hAdj (i j : ι) : DifferentiableAt ℂ (fun t => (A t).adjugate i j) x := by
    rw [show (fun t => (A t).adjugate i j) =
        fun t => ((A t).updateRow j (Pi.single i (1 : ℂ) : ι → ℂ)).det by
      funext t
      exact Matrix.adjugate_apply (A t) i j]
    exact (hasDerivAt_complexMatrixDet
      (fun t => (A t).updateRow j (Pi.single i (1 : ℂ) : ι → ℂ))
      (A₁.updateRow j 0) x (by
        intro a b
        by_cases haj : a = j
        · subst a
          simpa [Matrix.updateRow_apply] using
            (hasDerivAt_const (x := x) ((Pi.single i (1 : ℂ) : ι → ℂ) b))
        · simpa [Matrix.updateRow_apply, haj] using
            hA a b)).differentiableAt
  let B₁ : Matrix ι ι ℂ := fun i j => deriv (fun t => (A t)⁻¹ i j) x
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
          fun _ => (1 : Matrix ι ι ℂ) i j := by
      filter_upwards [hne] with t ht
      rw [Matrix.mul_nonsing_inv (A t) (isUnit_iff_ne_zero.mpr ht)]
    exact (hprod.congr_of_eventuallyEq heq.symm).unique
      (hasDerivAt_const (x := x) ((1 : Matrix ι ι ℂ) i j))
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

/-- Complex Jacobi second-variation formula. -/
theorem complexDetSecondJet_eq_det_mul_trace_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℂ) (hdet : A.det ≠ 0) :
    complexDetSecondJet A A₁ A₂ =
      A.det * (Matrix.trace (A⁻¹ * A₁) ^ 2 +
        Matrix.trace (A⁻¹ * A₂ - A⁻¹ * A₁ * A⁻¹ * A₁)) := by
  let P : ℂ → Matrix ι ι ℂ := fun t => A + t • A₁
  let Q : ℂ → Matrix ι ι ℂ := fun t => A₁ + t • A₂
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
  have hleft : HasDerivAt (fun t => complexDetFirstJet (P t) (Q t))
      (complexDetSecondJet A A₁ A₂) 0 := by
    convert hasDerivAt_complexDetFirstJet P Q A₂ 0
      (by simpa [Q] using hP) hQ using 1
    all_goals simp [P, Q]
  have hdetPath : HasDerivAt (fun t => (P t).det)
      (complexDetFirstJet A A₁) 0 := by
    convert hasDerivAt_complexMatrixDet P A₁ 0 hP using 1
    all_goals simp [P]
  have hinv := hasDerivAt_complexMatrix_inv P A₁ 0 hP (by simpa [P] using hdet)
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
      (Matrix.trace (A⁻¹ * A₂ - A⁻¹ * A₁ * A⁻¹ * A₁)) 0 := by
    convert htraceRaw using 1
    congr 1
    simp [Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  have hright := hdetPath.mul htrace
  have hne : ∀ᶠ t in nhds (0 : ℂ), (P t).det ≠ 0 :=
    (hdetPath.continuousAt.ne_iff_eventually_ne continuousAt_const).mp
      (by simpa [P] using hdet)
  have heq :
      (fun t => complexDetFirstJet (P t) (Q t)) =ᶠ[nhds (0 : ℂ)]
        fun t => (P t).det * Matrix.trace ((P t)⁻¹ * Q t) := by
    filter_upwards [hne] with t ht
    exact complexDetFirstJet_eq_det_mul_trace_inv_mul (P t) (Q t) ht
  have hderivEq := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  rw [complexDetFirstJet_eq_det_mul_trace_inv_mul A A₁ hdet] at hderivEq
  simp [P, Q] at hderivEq
  rw [Matrix.trace_sub]
  linear_combination hderivEq

theorem complexDetSecondJet_one_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₁ A₂ : Matrix ι ι ℂ) :
    complexDetSecondJet 1 A₁ A₂ =
      Matrix.trace A₁ ^ 2 + Matrix.trace (A₂ - A₁ * A₁) := by
  simpa using complexDetSecondJet_eq_det_mul_trace_formula
    (1 : Matrix ι ι ℂ) A₁ A₂ (by simp)

end

end GaloisForLFunctions.HTGeometry

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Entrywise first complex derivative of a finite matrix curve. -/
def additiveSCMatrixFirstJet {n : ℕ}
    (M : ℂ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => deriv (fun w => M w i j) z

/-- Entrywise central second complex derivative of a finite matrix curve. -/
def additiveSCMatrixSecondJet {n : ℕ}
    (M : ℂ → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => deriv (deriv (fun w => M w i j)) 0

/-- Identity-centered additive finite SC stage. -/
def finiteSkewAdjointAdditiveSCMatrix {n : ℕ}
    (M : ℂ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + M z

theorem additiveSCMatrixFirstJet_skew
    {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hskew : ∀ z i j,
      M z j i = -additiveSCSchwarzSharp (fun w => M w i j) z)
    (i j : Fin n) :
    additiveSCMatrixFirstJet M 0 j i =
      -(starRingEnd ℂ) (additiveSCMatrixFirstJet M 0 i j) := by
  have hfun : (fun z => M z j i) =
      fun z => -additiveSCSchwarzSharp (fun w => M w i j) z := by
    funext z
    exact hskew z i j
  have hleft := (hM j i 0).hasDerivAt
  have hleft' : HasDerivAt
      (fun z => -additiveSCSchwarzSharp (fun w => M w i j) z)
      (deriv (fun z => M z j i) 0) 0 :=
    hleft.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z => (congrFun hfun z).symm))
  have hright :=
    ((differentiable_additiveSCSchwarzSharp (hM i j)) 0).hasDerivAt.neg
  rw [deriv_additiveSCSchwarzSharp] at hright
  have heq := hleft'.unique hright
  simpa [additiveSCMatrixFirstJet, Function.comp_apply] using heq

/-- Exact arbitrary-rank central determinant curvature for trace-free skew-adjoint additive SC. -/
theorem iteratedDeriv_two_finiteSkewAdjointAdditiveSCMatrix_det_zero
    {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hM0 : M 0 = 0)
    (htrace : ∀ z, Matrix.trace (M z) = 0) :
    iteratedDeriv 2 (fun z => (finiteSkewAdjointAdditiveSCMatrix M z).det) 0 =
      -Matrix.trace (additiveSCMatrixFirstJet M 0 * additiveSCMatrixFirstJet M 0) := by
  have hfirstDiff (i j : Fin n) :
      Differentiable ℂ (fun z => additiveSCMatrixFirstJet M z i j) := by
    simpa [additiveSCMatrixFirstJet, iteratedDeriv_one] using
      GaloisForLFunctions.differentiable_iteratedDeriv_of_entire (hM i j) 1
  have hjet := complexDet_secondDerivative_eq_jet
    (finiteSkewAdjointAdditiveSCMatrix M)
    (additiveSCMatrixFirstJet M)
    (additiveSCMatrixSecondJet M) 0
    (Filter.Eventually.of_forall (fun z => by
      intro i j
      change HasDerivAt
        ((fun _ : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) i j) +
          fun s => M s i j)
        (deriv (fun w => M w i j) z) z
      simpa only [zero_add] using
        (hasDerivAt_const (x := z) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).add
          ((hM i j z).hasDerivAt)))
    (fun i j => by
      change HasDerivAt (fun t => deriv (fun w => M w i j) t)
        (deriv (deriv (fun w => M w i j)) 0) 0
      exact (hfirstDiff i j 0).hasDerivAt)
  have hbase : finiteSkewAdjointAdditiveSCMatrix M 0 = 1 := by
    simp [finiteSkewAdjointAdditiveSCMatrix, hM0]
  have htraceFun : (fun z => Matrix.trace (M z)) = fun _ => 0 := by
    funext z
    exact htrace z
  have htraceFirstAt (z : ℂ) :
      HasDerivAt (fun w => Matrix.trace (M w))
        (Matrix.trace (additiveSCMatrixFirstJet M z)) z := by
    unfold Matrix.trace
    convert! HasDerivAt.fun_sum
      (fun i _ => (hM i i z).hasDerivAt) using 1
  have htraceFirstAll (z : ℂ) :
      Matrix.trace (additiveSCMatrixFirstJet M z) = 0 := by
    have h := (htraceFirstAt z).deriv
    rw [htraceFun] at h
    simpa using h.symm
  have htraceFirst : Matrix.trace (additiveSCMatrixFirstJet M 0) = 0 :=
    htraceFirstAll 0
  have htraceFirstFun :
      (fun z => Matrix.trace (additiveSCMatrixFirstJet M z)) = fun _ => 0 := by
    funext z
    exact htraceFirstAll z
  have htraceSecondAt :
      HasDerivAt (fun z => Matrix.trace (additiveSCMatrixFirstJet M z))
        (Matrix.trace (additiveSCMatrixSecondJet M)) 0 := by
    unfold Matrix.trace
    convert! HasDerivAt.fun_sum
      (fun i _ => (hfirstDiff i i 0).hasDerivAt) using 1
  have htraceSecond : Matrix.trace (additiveSCMatrixSecondJet M) = 0 := by
    have h := htraceSecondAt.deriv
    rw [htraceFirstFun] at h
    simpa using h.symm
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hjet, hbase, complexDetSecondJet_one_formula]
  rw [Matrix.trace_sub, htraceFirst, htraceSecond]
  ring

theorem neg_re_trace_sq_eq_sum_normSq_of_skew
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ i j, K j i = -(starRingEnd ℂ) (K i j)) :
    (-Matrix.trace (K * K)).re =
      ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (K i j) := by
  have hterm (i j : Fin n) :
      (K i j * K j i).re = -Complex.normSq (K i j) := by
    rw [hK i j, mul_neg, Complex.mul_conj]
    simp
  rw [Matrix.trace]
  simp only [Complex.neg_re, Complex.re_sum, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [hterm]
  simp

theorem re_iteratedDeriv_two_finiteSkewAdjointAdditiveSCMatrix_det_zero_nonneg
    {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hM0 : M 0 = 0)
    (htrace : ∀ z, Matrix.trace (M z) = 0)
    (hskew : ∀ z i j,
      M z j i = -additiveSCSchwarzSharp (fun w => M w i j) z) :
    0 ≤ (iteratedDeriv 2
      (fun z => (finiteSkewAdjointAdditiveSCMatrix M z).det) 0).re := by
  rw [iteratedDeriv_two_finiteSkewAdjointAdditiveSCMatrix_det_zero hM hM0 htrace]
  rw [neg_re_trace_sq_eq_sum_normSq_of_skew
    (additiveSCMatrixFirstJet M 0)
    (additiveSCMatrixFirstJet_skew hM hskew)]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem differentiable_finiteSkewAdjointAdditiveSCMatrix_det
    {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j)) :
    Differentiable ℂ (fun z => (finiteSkewAdjointAdditiveSCMatrix M z).det) := by
  intro z
  refine (hasDerivAt_complexMatrixDet
    (finiteSkewAdjointAdditiveSCMatrix M)
    (additiveSCMatrixFirstJet M z) z ?_).differentiableAt
  intro i j
  change HasDerivAt
    ((fun _ : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) i j) +
      fun s => M s i j)
    (deriv (fun w => M w i j) z) z
  simpa only [zero_add] using
    (hasDerivAt_const (x := z) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).add
      ((hM i j z).hasDerivAt)

/-- No varying finite rank, trace-free, skew-adjoint additive SC determinant stages land Xi. -/
theorem not_tendstoLocallyUniformly_finiteSkewAdjointAdditiveSCMatrix_normalizedXiC
    (d : ℕ → ℕ)
    (M : (k : ℕ) → ℂ → Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hM : ∀ k i j, Differentiable ℂ (fun z => M k z i j))
    (hM0 : ∀ k, M k 0 = 0)
    (htrace : ∀ k z, Matrix.trace (M k z) = 0)
    (hskew : ∀ k z i j,
      M k z j i = -additiveSCSchwarzSharp (fun w => M k w i j) z) :
    ¬ TendstoLocallyUniformly
      (fun k z => (finiteSkewAdjointAdditiveSCMatrix (M k) z).det)
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hjet : Tendsto
      (fun k => iteratedDeriv 2
        (fun z => (finiteSkewAdjointAdditiveSCMatrix (M k) z).det) 0) atTop
      (𝓝 (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0)) := by
    exact GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
      hconv.tendstoLocallyUniformlyOn
      (Filter.Eventually.of_forall fun k =>
        (differentiable_finiteSkewAdjointAdditiveSCMatrix_det
          (fun i j => hM k i j)).differentiableOn)
      2 (Set.mem_univ 0)
  have hjetRe : Tendsto
      (fun k => (iteratedDeriv 2
        (fun z => (finiteSkewAdjointAdditiveSCMatrix (M k) z).det) 0).re) atTop
      (𝓝 (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hjet
  have hnonneg : 0 ≤ (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0).re := by
    exact isClosed_Ici.mem_of_tendsto hjetRe
      (Filter.Eventually.of_forall fun k =>
        re_iteratedDeriv_two_finiteSkewAdjointAdditiveSCMatrix_det_zero_nonneg
          (fun i j => hM k i j) (hM0 k) (fun z => htrace k z)
          (fun z i j => hskew k z i j))
  rw [iteratedDeriv_two_normalizedXiC_zero] at hnonneg
  exact (not_lt_of_ge hnonneg) XiC_secondDeriv_div_center_re_neg

end


end RHTower
