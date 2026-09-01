import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicScalarExtension
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialSemilinearEval
import GaloisForLFunctions.HTGeometry.SigmaDeltaOrbitIdeal

/-!
# Relation-adapted Bessel parameterized Picard--Vessiot quotients

Any scalar differential relation satisfied by the actual meromorphic Bessel solution generates,
together with the normalized determinant relation, a proper sigma--delta orbit ideal in the
universal Bessel PPV coordinate ring.  Extending it to a maximal proper sigma--delta ideal produces
a genuine Bessel PPV datum in which that relation holds.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic besselScalarComplexDifferential
  besselScalarRatFuncComplexDifferential besselScalarRatFuncConstantsDifferential
  constantsDifferentialAlgebra besselScalarRatFuncAlgebra besselScalarMeroAlgebra
  ratFuncConstantsDifferentialAlgebra meromorphicDifferentialAlgebra
  besselScalarTensorDifferential besselScalarTensorDifferentialAlgebra

theorem ringEquiv_iterate_add {R : Type*} [Semiring R]
    (sigma : R ≃+* R) (m : ℕ) (x y : R) :
    ((sigma : R → R)^[m]) (x + y) =
      ((sigma : R → R)^[m]) x + ((sigma : R → R)^[m]) y := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', hm, map_add]

theorem ringEquiv_iterate_mul {R : Type*} [Semiring R]
    (sigma : R ≃+* R) (m : ℕ) (x y : R) :
    ((sigma : R → R)^[m]) (x * y) =
      ((sigma : R → R)^[m]) x * ((sigma : R → R)^[m]) y := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', hm, map_mul]

theorem ringEquiv_iterate_zero {R : Type*} [Semiring R]
    (sigma : R ≃+* R) (m : ℕ) :
    ((sigma : R → R)^[m]) 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m hm => rw [Function.iterate_succ_apply', hm, map_zero]

/-- Evaluate a scalar differential polynomial at the upper entry of the generic first column. -/
def besselScalarPPVRelation
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    ppvLocalization (RatFunc Constants) 2 :=
  differentialPolynomialEvalOver
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P

theorem besselOrderPPVSigma_commutesDeriv
    (s : ℝ) (x : ppvLocalization (RatFunc Constants) 2) :
    besselOrderPPVSigma s (Differential.deriv x) =
      Differential.deriv (besselOrderPPVSigma s x) := by
  unfold besselOrderPPVSigma
  exact ppvSigma_commutes (K := RatFunc Constants) (n := 2)
    FieldShift.ratShiftEquiv besselRatShift_commutes
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s) x

theorem besselOrderPPVSigma_fundamental_zero_zero (s : ℝ) :
    besselOrderPPVSigma s (ppvFundamental (RatFunc Constants) 2 0 0) =
      ppvFundamental (RatFunc Constants) 2 1 0 := by
  unfold besselOrderPPVSigma
  rw [ppvSigma_ppvFundamental]
  simp [FieldShift.besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two]

theorem besselOrderPPVSigma_fundamental_one_zero (s : ℝ) :
    besselOrderPPVSigma s (ppvFundamental (RatFunc Constants) 2 1 0) =
      ppvFundamental (RatFunc Constants) 2 0 0 +
        ppvBaseMap (RatFunc Constants) 2
            (FieldShift.orderShiftCoeff (slope s)) *
          ppvFundamental (RatFunc Constants) 2 1 0 := by
  unfold besselOrderPPVSigma
  rw [ppvSigma_ppvFundamental]
  simp [FieldShift.besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two]

theorem besselMeromorphicPPVEval_iterate_base
    (s : ℝ) (hs : 0 < s) (m : ℕ) (r : RatFunc Constants) :
    besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (ppvBaseMap (RatFunc Constants) 2 r)) =
      ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
        (algebraMap (RatFunc Constants) BesselScalarTensor r) := by
  induction m generalizing r with
  | zero => exact besselMeromorphicPPVEval_base s hs r
  | succ m hm =>
      rw [Function.iterate_succ_apply, besselOrderPPVSigma_base, hm]
      rw [Function.iterate_succ_apply, besselScalarTensorShift_algebraMap]

theorem besselMeromorphicPPVEval_iterate_firstColumn
    (s : ℝ) (hs : 0 < s) (m : ℕ) :
    besselMeromorphicPPVEval s hs
          (((besselOrderPPVSigma s : _ → _)^[m])
            (ppvFundamental (RatFunc Constants) 2 0 0)) =
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY0 s hs) ∧
      besselMeromorphicPPVEval s hs
          (((besselOrderPPVSigma s : _ → _)^[m])
            (ppvFundamental (RatFunc Constants) 2 1 0)) =
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY1 s hs) := by
  induction m with
  | zero =>
      constructor <;>
        simp [besselMeromorphicPPVEval_ppvFundamental,
          besselMeromorphicPPVMatrix, besselScalarY0, besselScalarY1]
  | succ m hm =>
      constructor
      · rw [Function.iterate_succ_apply, besselOrderPPVSigma_fundamental_zero_zero,
          hm.2, Function.iterate_succ_apply, besselScalarTensorShift_y0]
      · rw [Function.iterate_succ_apply,
          besselOrderPPVSigma_fundamental_one_zero,
          ringEquiv_iterate_add, ringEquiv_iterate_mul, map_add, map_mul,
          hm.1, hm.2,
          besselMeromorphicPPVEval_iterate_base,
          Function.iterate_succ_apply, besselScalarTensorShift_y1,
          ringEquiv_iterate_add, ringEquiv_iterate_mul]

theorem besselMeromorphicPPVEval_scalarRelation
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    besselMeromorphicPPVEval s hs (besselScalarPPVRelation P) =
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => besselScalarY0 s hs) P := by
  have hmap := map_differentialPolynomialEvalOver
    (besselMeromorphicPPVEval s hs)
    (besselMeromorphicPPVEval_commutesDeriv s hs)
    (besselMeromorphicPPVEval_base s hs)
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P
  have hzerozero : besselMeromorphicPPVEval s hs
      (ppvFundamental (RatFunc Constants) 2 0 0) = besselScalarY0 s hs := by
    simpa [besselMeromorphicPPVMatrix] using
      (besselMeromorphicPPVEval_ppvFundamental s hs 0 0)
  rw [show (fun i : Unit => besselMeromorphicPPVEval s hs
      (ppvFundamental (RatFunc Constants) 2 0 0)) =
      (fun _ : Unit => besselScalarY0 s hs) by
    funext i
    exact hzerozero] at hmap
  exact hmap

theorem besselMeromorphicPPVEval_iterate_scalarRelation
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) (m : ℕ) :
    besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (besselScalarPPVRelation P)) =
      ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
        (differentialPolynomialEvalOver (K := RatFunc Constants)
          (fun _ : Unit => besselScalarY0 s hs) P) := by
  let Pm :=
    (((differentialPolynomialSigma FieldShift.ratShiftEquiv :
      DifferentialPolynomial Unit (RatFunc Constants) →
        DifferentialPolynomial Unit (RatFunc Constants))^[m]) P)
  have hsource := differentialPolynomialEvalOver_sigma_point_iterate
    (iota := Unit) FieldShift.ratShiftEquiv (besselOrderPPVSigma s)
    (besselOrderPPVSigma_base s) (besselOrderPPVSigma_commutesDeriv s)
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P m
  have heval := map_differentialPolynomialEvalOver
    (besselMeromorphicPPVEval s hs)
    (besselMeromorphicPPVEval_commutesDeriv s hs)
    (besselMeromorphicPPVEval_base s hs)
    (fun _ : Unit =>
      ((besselOrderPPVSigma s : _ → _)^[m])
        (ppvFundamental (RatFunc Constants) 2 0 0)) Pm
  have htarget := differentialPolynomialEvalOver_sigma_point_iterate
    (iota := Unit) FieldShift.ratShiftEquiv besselScalarTensorShift
    besselScalarTensorShift_algebraMap besselScalarTensorShift_deriv
    (fun _ : Unit => besselScalarY0 s hs) P m
  rw [besselScalarPPVRelation]
  rw [← hsource]
  rw [heval]
  rw [show (fun _ : Unit => besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (ppvFundamental (RatFunc Constants) 2 0 0))) =
      (fun _ : Unit =>
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY0 s hs)) by
    funext u
    exact (besselMeromorphicPPVEval_iterate_firstColumn s hs m).1]
  exact htarget

theorem besselOrderPPVSigma_fundamentalDetSqRelation_fixed (s : ℝ) :
    besselOrderPPVSigma s
        (ppvFundamentalDetSqRelation (RatFunc Constants) 2) =
      ppvFundamentalDetSqRelation (RatFunc Constants) 2 := by
  unfold besselOrderPPVSigma
  exact ppvSigma_fundamentalDetSqRelation_fixed_of_det_sq
    (K := RatFunc Constants) (n := 2)
    FieldShift.ratShiftEquiv besselRatShift_commutes
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s)
    (besselOrderCompanion_det_sq s)

theorem besselOrderPPVSigma_iterate_fundamentalDetSqRelation
    (s : ℝ) (m : ℕ) :
    ((besselOrderPPVSigma s : _ → _)^[m])
        (ppvFundamentalDetSqRelation (RatFunc Constants) 2) =
      ppvFundamentalDetSqRelation (RatFunc Constants) 2 := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', hm,
        besselOrderPPVSigma_fundamentalDetSqRelation_fixed]

theorem besselMeromorphicPPVEval_fundamentalDetSqRelation
    (s : ℝ) (hs : 0 < s) :
    besselMeromorphicPPVEval s hs
        (ppvFundamentalDetSqRelation (RatFunc Constants) 2) = 0 := by
  have hmatrix :
      (ppvFundamental (RatFunc Constants) 2).map
          (besselMeromorphicPPVEval s hs) =
        besselMeromorphicPPVMatrix s hs := by
    ext i j
    exact besselMeromorphicPPVEval_ppvFundamental s hs i j
  rw [ppvFundamentalDetSqRelation, map_sub, map_pow, map_one]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmatrix,
    besselMeromorphicPPVMatrix_det]
  simp

def besselRelationGenerators
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    Set (ppvLocalization (RatFunc Constants) 2) :=
  {ppvFundamentalDetSqRelation (RatFunc Constants) 2, besselScalarPPVRelation P}

theorem besselRelationOrbitIdeal_ne_top
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants))
    (hP : differentialPolynomialEvalOver (K := RatFunc Constants)
      (fun _ : Unit => besselScalarY0 s hs) P = 0) :
    sigmaDeltaOrbitIdeal (besselOrderPPVSigma s) (besselRelationGenerators P) ≠ ⊤ := by
  apply sigmaDeltaOrbitIdeal_ne_top_of_ringHom
    (besselMeromorphicPPVEval s hs)
    (besselMeromorphicPPVEval_commutesDeriv s hs)
  intro p hp m
  rw [besselRelationGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · rw [besselOrderPPVSigma_iterate_fundamentalDetSqRelation]
    exact besselMeromorphicPPVEval_fundamentalDetSqRelation s hs
  · rw [besselMeromorphicPPVEval_iterate_scalarRelation, hP]
    exact ringEquiv_iterate_zero besselScalarTensorShift m

/-- Every actual scalar Bessel relation can be imposed in a genuine normalized Bessel PPV datum. -/
theorem exists_besselOrderParameterizedPVData_containing_relation
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants))
    (hP : differentialPolynomialEvalOver (K := RatFunc Constants)
      (fun _ : Unit => besselScalarY0 s hs) P = 0) :
    ∃ data : BesselOrderParameterizedPVData s,
      besselScalarPPVRelation P ∈ data.M := by
  let I := sigmaDeltaOrbitIdeal (besselOrderPPVSigma s) (besselRelationGenerators P)
  have hI : IsSigmaDeltaIdeal (besselOrderPPVSigma s) I :=
    isSigmaDeltaIdeal_sigmaDeltaOrbitIdeal
      (besselOrderPPVSigma_commutesDeriv s) (besselRelationGenerators P)
  have hIne : I ≠ ⊤ := besselRelationOrbitIdeal_ne_top s hs P hP
  obtain ⟨M, hM, hMne, hM', hIM, hsimple, hcomm⟩ :=
    exists_sigmaDeltaSimple_quotient (besselOrderPPVSigma s)
      (besselOrderPPVSigma_commutesDeriv s) I hI hIne
  have hbase : ∀ x : RatFunc Constants,
      sigmaQuotientEquiv (besselOrderPPVSigma s) M hM.1 hM'
          (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
        Ideal.Quotient.mk M
          (ppvBaseMap (RatFunc Constants) 2 (FieldShift.ratShiftEquiv x)) := by
    intro x
    rw [sigmaQuotientEquiv_mk, besselOrderPPVSigma_base]
  have hbaseDeriv : ∀ x : RatFunc Constants,
      letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ M) :=
        quotientDifferential M hM.2
      Differential.deriv
          (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
        Ideal.Quotient.mk M
          (ppvBaseMap (RatFunc Constants) 2 (Differential.deriv x)) := by
    intro x
    exact quotientDifferential_ppvBaseMap_deriv M hM.2 x
  have hfund : ∀ i j,
      sigmaQuotientEquiv (besselOrderPPVSigma s) M hM.1 hM'
          (Ideal.Quotient.mk M (ppvFundamental (RatFunc Constants) 2 i j)) =
        (((((FieldShift.besselOrderCompanion (slope s)).map
          (ppvBaseMap (RatFunc Constants) 2)).map (Ideal.Quotient.mk M)) *
          ((ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M))) i j) := by
    intro i j
    rw [sigmaQuotientEquiv_mk]
    unfold besselOrderPPVSigma
    rw [ppvSigma_ppvFundamental]
    simp [Matrix.mul_apply]
  have hdet : IsUnit
      ((ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M)).det := by
    have hu := isUnit_det_ppvFundamental.map (Ideal.Quotient.mk M)
    rw [RingHom.map_det (Ideal.Quotient.mk M)
      (ppvFundamental (RatFunc Constants) 2), RingHom.mapMatrix_apply] at hu
    exact hu
  have hdetMem : ppvFundamentalDetSqRelation (RatFunc Constants) 2 ∈ M :=
    hIM (mem_sigmaDeltaOrbitIdeal (show
      ppvFundamentalDetSqRelation (RatFunc Constants) 2 ∈
        besselRelationGenerators P by simp [besselRelationGenerators]))
  have hdetZero := Ideal.Quotient.eq_zero_iff_mem.mpr hdetMem
  have hdetSq :
      ((ppvFundamental (RatFunc Constants) 2).map
        (Ideal.Quotient.mk M)).det ^ 2 = 1 := by
    rw [ppvFundamentalDetSqRelation, map_sub, map_pow, map_one] at hdetZero
    rw [RingHom.map_det (Ideal.Quotient.mk M)
      (ppvFundamental (RatFunc Constants) 2), RingHom.mapMatrix_apply] at hdetZero
    exact sub_eq_zero.mp hdetZero
  let data : BesselOrderParameterizedPVData s := {
    M := M
    isSigmaDeltaIdeal := hM
    ne_top := hMne
    isSigmaIdeal_symm := hM'
    isSigmaDeltaSimple := hsimple
    commutesDeriv := hcomm
    baseCompatible := hbase
    baseDerivCompatible := hbaseDeriv
    fundamental := hfund
    fundamental_det_isUnit := hdet
    fundamental_det_sq_eq_one := hdetSq
    detInverse := Ideal.Quotient.mk M
      (IsLocalization.Away.invSelf
        ((jetFundamentalMatrix (RatFunc Constants) 2).det))
    fundamental_det_mul_inverse := ppvQuotient_det_mul_inverse M
    generatedJets := ppvQuotient_adjoin_jetVariables M
    jets_are_iteratedDeriv := iterate_deriv_ppvQuotientFundamental M hM.2
  }
  refine ⟨data, ?_⟩
  change besselScalarPPVRelation P ∈ M
  exact hIM (mem_sigmaDeltaOrbitIdeal (show besselScalarPPVRelation P ∈
    besselRelationGenerators P by simp [besselRelationGenerators]))

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
