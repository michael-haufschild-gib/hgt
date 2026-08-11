import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionEvenContactSource

/-!
# Bilinear arithmetic producer for every Padé contact above order one

Diagonal adaptive shear has even top degree.  Polarizing before arithmetic formation removes that
restriction: two admitted null-ideal lifts whose lift degrees sum to `d-2` produce the Padé defect
of contact order `d`.  The output is the literal rational-Gamma-minus-von-Mangoldt completed
packet, not a posterior orientation report.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Coefficient packet of a bilinear crossing amplitude. -/
def xiShiftedBilinearCrossingCoefficientPacket (A B : Polynomial ℝ) :
    Fin ((A * B).natDegree + 1) → ℝ :=
  Polynomial.toFn ((A * B).natDegree + 1) (A * B)

/-- Symmetric Euler shear selected by differentiating the bilinear crossing `L(A X B)`. -/
def xiShiftedBoundaryAdaptiveBilinearShearPolynomial
    (A B : Polynomial ℝ) : Polynomial ℝ :=
  (X * A) * (X * xiShiftedBoundaryShiftedEuler 1 B) +
    (X * B) * (X * xiShiftedBoundaryShiftedEuler 1 A)

/-- Bilinear shear is the Euler derivative of the product of the two odd amplitudes. -/
theorem xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_X_derivative
    (A B : Polynomial ℝ) :
    xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B =
      X * ((X * A) * (X * B)).derivative := by
  simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
    xiShiftedBoundaryShiftedEuler, Polynomial.derivative_mul,
    Polynomial.derivative_X, one_mul, C_1]
  ring

/-- Degree bound for the bilinear adaptive source. -/
theorem natDegree_xiShiftedBoundaryAdaptiveBilinearShearPolynomial_le
    {A B : Polynomial ℝ} {a b : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = a)
    (hB : B.Monic) (hBdeg : B.natDegree = b) :
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B).natDegree ≤ a + b + 2 := by
  let C : Polynomial ℝ := (X * A) * (X * B)
  have hXA : (X * A).Monic := Polynomial.monic_X.mul hA
  have hXB : (X * B).Monic := Polynomial.monic_X.mul hB
  have hC : C.Monic := hXA.mul hXB
  have hCdeg : C.natDegree = a + b + 2 := by
    dsimp only [C]
    rw [hXA.natDegree_mul hXB, Polynomial.monic_X.natDegree_mul hA,
      Polynomial.monic_X.natDegree_mul hB, hAdeg, hBdeg, Polynomial.natDegree_X]
    omega
  rw [xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_X_derivative]
  change (X * C.derivative).natDegree ≤ a + b + 2
  calc
    (X * C.derivative).natDegree ≤ X.natDegree + C.derivative.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + (C.natDegree - 1) := by
      simpa only [Polynomial.natDegree_X] using
        Nat.add_le_add_left (Polynomial.natDegree_derivative_le C) 1
    _ = a + b + 2 := by rw [hCdeg]; omega

/-- Top coefficient of bilinear shear is total source degree. -/
theorem coeff_xiShiftedBoundaryAdaptiveBilinearShearPolynomial_top
    {A B : Polynomial ℝ} {a b : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = a)
    (hB : B.Monic) (hBdeg : B.natDegree = b) :
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B).coeff (a + b + 2) =
      ((a + b + 2 : ℕ) : ℝ) := by
  let C : Polynomial ℝ := (X * A) * (X * B)
  have hC : C.Monic := (Polynomial.monic_X.mul hA).mul (Polynomial.monic_X.mul hB)
  have hCdeg : C.natDegree = a + b + 2 := by
    dsimp only [C]
    rw [(Polynomial.monic_X.mul hA).natDegree_mul (Polynomial.monic_X.mul hB),
      Polynomial.monic_X.natDegree_mul hA, Polynomial.monic_X.natDegree_mul hB,
      hAdeg, hBdeg, Polynomial.natDegree_X]
    omega
  have hcoeffC : C.coeff (a + b + 2) = 1 := by
    rw [← hCdeg]
    exact hC.coeff_natDegree
  rw [xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_X_derivative]
  change (X * C.derivative).coeff (a + b + 2) = _
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    show a + b + 1 + 1 = a + b + 2 by omega, hcoeffC]
  push_cast
  ring

/-- A sequence vanishing below `K` sees only coefficient `K` of a polynomial of degree at most
`K`. -/
theorem momentFunctional_eq_top_of_sequence_eq_zero_below
    {a : ℕ → ℝ} {K : ℕ} (hzero : ∀ k < K, a k = 0)
    {Q : Polynomial ℝ} (hQdeg : Q.natDegree ≤ K) :
    HTGeometry.momentFunctional a Q = Q.coeff K * a K := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  rw [Finset.sum_eq_single K]
  · intro k hk hkne
    have hkcoeff : Q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    have hkle : k ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero hkcoeff
    rw [hzero k (by omega), mul_zero]
  · intro hK
    have hKcoeff : Q.coeff K = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hK
    rw [hKcoeff, zero_mul]

/-- The base-one completed packet of a cross coefficient packet is the bilinear odd crossing. -/
theorem xiShiftedCompletedMomentAggregate_bilinearPacket_eq_momentInner
    (y : ℝ) (A B : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate y 1
        (xiShiftedBilinearCrossingCoefficientPacket A B) =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) A (X * B) := by
  let N := (A * B).natDegree + 1
  let c : Fin N → ℝ := xiShiftedBilinearCrossingCoefficientPacket A B
  have hc : Polynomial.ofFn N c = A * B :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hprod : X * Polynomial.ofFn N c = A * (X * B) := by
    rw [hc]
    ring
  change xiShiftedCompletedMomentAggregate y 1 c = _
  rw [HTGeometry.momentInner_def, ← hprod]
  have hsum :
      HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * Polynomial.ofFn N c) =
        ∑ j : Fin N, c j * (xiShiftedReciprocalMoment y ((j : ℕ) + 1)).re := by
    rw [Polynomial.ofFn_eq_sum_monomial, Finset.mul_sum]
    rw [HTGeometry.momentFunctional_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [X_mul_monomial, HTGeometry.momentFunctional_monomial]
  rw [hsum]
  simp only [xiShiftedCompletedMomentAggregate]
  apply Finset.sum_congr rfl
  intro j _
  rw [show 1 + (j : ℕ) = (j : ℕ) + 1 by omega]

/-- Source connection for a bilinear odd crossing. -/
theorem hasDerivAt_xiShiftedMomentInner_bilinearCrossing_eq_adaptiveShear
    {y : ℝ} (hy : 0 < y) (A B : Polynomial ℝ) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re) A (X * B))
      (-HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B)) y := by
  have h := hasDerivAt_xiShiftedMomentFunctional_sourceConnection hy (A * (X * B))
  have hpoly : X * xiShiftedBoundaryShiftedEuler 1 (A * (X * B)) =
      xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B := by
    simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
      xiShiftedBoundaryShiftedEuler, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, C_1]
    ring
  rw [hpoly] at h
  simpa only [HTGeometry.momentInner_def] using h

/-- One adaptive midpoint step turns the cross packet into the bilinear Euler shear. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveBilinearPacket_eq_shear
    {y : ℝ} (hy : 0 < y) (A B : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedBilinearCrossingCoefficientPacket A B)) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B) := by
  let c := xiShiftedBilinearCrossingCoefficientPacket A B
  have haggregate := hasDerivAt_xiShiftedCompletedMomentAggregate hy 1 c
  have hfun :
      (fun v => xiShiftedCompletedMomentAggregate v 1 c) =
        (fun v => HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment v k).re) A (X * B)) := by
    funext v
    exact xiShiftedCompletedMomentAggregate_bilinearPacket_eq_momentInner v A B
  rw [hfun] at haggregate
  have hshear :=
    hasDerivAt_xiShiftedMomentInner_bilinearCrossing_eq_adaptiveShear hy A B
  have hderiv := haggregate.unique hshear
  change -xiShiftedCompletedMomentAggregate y 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1 c) =
    -HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B) at hderiv
  linarith

/-- Literal arithmetic formation selected by a bilinear amplitude pair before aggregation. -/
def xiShiftedAdaptiveBilinearCompletedArithmeticSource
    (w : ℝ) (A B : Polynomial ℝ) : ℝ :=
  let c := xiShiftedBoundaryAdaptiveMidpointCoefficients 1
    (xiShiftedBilinearCrossingCoefficientPacket A B)
  xiShiftedBoundaryRationalGammaAggregate w 2 c -
    xiShiftedBoundaryVonMangoldtAggregate w 2 c

/-- Completed cross packet equals its rational-Gamma-minus-von-Mangoldt formation. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveBilinearPacket_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) (A B : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedBilinearCrossingCoefficientPacket A B)) =
      xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B := by
  rw [xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw]
  rfl

/-- Source-first bilinear shear equals the literal completed arithmetic formation. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear
    {w : ℝ} (hw : 1 / 2 < w) (A B : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B) := by
  rw [← xiShiftedCompletedMomentAggregate_adaptiveBilinearPacket_eq_arithmeticSource hw]
  exact xiShiftedCompletedMomentAggregate_adaptiveBilinearPacket_eq_shear
    (sq_pos_of_pos (by linarith : 0 < w)) A B

/-- **All-contact bilinear arithmetic producer.**  For contact order `d ≥ 2`, any two null-ideal
lifts whose degrees sum to `d-2` make the literal completed source equal `(2n+d) delta_(2n+d)`.
This covers both even and odd contacts without a fixed observer. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
    {w : ℝ} (hw : 1 / 2 < w) {n d i j : ℕ} (_hd : 2 ≤ d)
    (hij : i + j + 2 = d) (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ i
    let B := P * X ^ j
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      ((2 * n + d : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ i
  let B := P * X ^ j
  let Q := xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow i)
  have hB : B.Monic := hP.mul (Polynomial.monic_X_pow j)
  have hAdeg : A.natDegree = n + i := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow i), hPdeg,
      Polynomial.natDegree_X_pow]
  have hBdeg : B.natDegree = n + j := by
    dsimp only [B]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow j), hPdeg,
      Polynomial.natDegree_X_pow]
  have hQdeg : Q.natDegree ≤ 2 * n + d := by
    apply (natDegree_xiShiftedBoundaryAdaptiveBilinearShearPolynomial_le
      hA hAdeg hB hBdeg).trans
    omega
  have hQcoeff : Q.coeff (2 * n + d) = ((2 * n + d : ℕ) : ℝ) := by
    have htop := coeff_xiShiftedBoundaryAdaptiveBilinearShearPolynomial_top
      hA hAdeg hB hBdeg
    have hindex : (n + i) + (n + j) + 2 = 2 * n + d := by omega
    dsimp only [Q]
    simpa only [hindex] using htop
  have hfactor : ∃ R : Polynomial ℝ, Q = P * R := by
    refine ⟨(X * X ^ i) * (X * xiShiftedBoundaryShiftedEuler 1 B) +
      (X * X ^ j) * (X * xiShiftedBoundaryShiftedEuler 1 A), ?_⟩
    dsimp only [Q, xiShiftedBoundaryAdaptiveBilinearShearPolynomial, A, B]
    ring
  obtain ⟨R, hQR⟩ := hfactor
  have hdefect : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) Q =
      HTGeometry.momentFunctional
        (xiShiftedHankelBoundaryPadeDefect (w ^ 2) c) Q := by
    rw [hQR]
    exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) c R).symm
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw]
  change HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) Q = _
  rw [hdefect,
    momentFunctional_eq_top_of_sequence_eq_zero_below hzero hQdeg, hQcoeff]

/-- Canonical inverse-Hankel specialization: admission selects `P^sharp` before both lifts and
before arithmetic source formation. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_canonicalAdmission_eq_firstPadeDefect
    {w : ℝ} (hw : 1 / 2 < w) {n d i j : ℕ} (hd : 2 ≤ d)
    (hij : i + j + 2 = d)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2)
        (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) k = 0) :
    let P := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w (P * X ^ i) (P * X ^ j) =
      ((2 * n + d : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2)
          (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n)
          (2 * n + d) := by
  dsimp only
  let c := HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have hsource :=
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
      hw hd hij c hlast hzero
  rw [finiteHankelNullMonicPolynomial_monicMomentAdmissionVector] at hsource
  exact hsource

/-! ### Polarized source matrix at higher contact -/

/-- The literal bilinear arithmetic source is symmetric in its two amplitudes. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm
    (w : ℝ) (A B : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      xiShiftedAdaptiveBilinearCompletedArithmeticSource w B A := by
  unfold xiShiftedAdaptiveBilinearCompletedArithmeticSource
  unfold xiShiftedBilinearCrossingCoefficientPacket
  rw [show B * A = A * B by ring]

/-- Two-amplitude compression of the adaptive bilinear arithmetic source. -/
def xiShiftedAdaptiveBilinearSourcePairMatrix
    (w : ℝ) (A B : Polynomial ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => xiShiftedAdaptiveBilinearCompletedArithmeticSource w (![A, B] i) (![A, B] j)

theorem xiShiftedAdaptiveBilinearSourcePairMatrix_isHermitian
    (w : ℝ) (A B : Polynomial ℝ) :
    (xiShiftedAdaptiveBilinearSourcePairMatrix w A B).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiShiftedAdaptiveBilinearSourcePairMatrix,
      xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm]

/-- **Null-diagonal/live-polarization law.**  At every first contact of order at least three,
the source matrix on the base null amplitude and the order-`d-2` lift is neither positive nor
negative semidefinite.  Its base diagonal is zero because order two has not yet contacted, while
its polarized entry is the nonzero literal arithmetic source `(2n+d) delta_(2n+d)`. -/
theorem xiShiftedAdaptiveBilinearSourcePairMatrix_neither_posSemidef_of_first_contact
    {w : ℝ} (hw : 1 / 2 < w) {n d : ℕ} (hd : 3 ≤ d)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0)
    (hcontact : xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let B := P * X ^ (d - 2)
    ¬ (xiShiftedAdaptiveBilinearSourcePairMatrix w P B).PosSemidef ∧
      ¬ (-xiShiftedAdaptiveBilinearSourcePairMatrix w P B).PosSemidef := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let B := P * X ^ (d - 2)
  let M := xiShiftedAdaptiveBilinearSourcePairMatrix w P B
  let e : Fin 2 → ℝ := ![1, 0]
  have hzeroTwo : ∀ k < 2 * n + 2,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0 := by
    intro k hk
    exact hzero k (by omega)
  have hdiag : xiShiftedAdaptiveBilinearCompletedArithmeticSource w P P = 0 := by
    have h := xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
      (i := 0) (j := 0) hw (by omega : 2 ≤ 2)
        (by omega : 0 + 0 + 2 = 2) c hlast hzeroTwo
    have h' : xiShiftedAdaptiveBilinearCompletedArithmeticSource w P P =
        ((2 * n + 2 : ℕ) : ℝ) *
          xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + 2) := by
      simpa [P] using h
    rw [h', hzero _ (by omega), mul_zero]
  have hoff : xiShiftedAdaptiveBilinearCompletedArithmeticSource w B P ≠ 0 := by
    have h := xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
      (i := d - 2) (j := 0) hw (by omega : 2 ≤ d)
        (by omega : (d - 2) + 0 + 2 = d) c hlast hzero
    have h' : xiShiftedAdaptiveBilinearCompletedArithmeticSource w B P =
        ((2 * n + d : ℕ) : ℝ) *
          xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) := by
      simpa [P, B] using h
    rw [h']
    exact mul_ne_zero (by positivity) hcontact
  constructor
  · intro hpsd
    have hquad : e ⬝ᵥ M.mulVec e = 0 := by
      simp [e, M, xiShiftedAdaptiveBilinearSourcePairMatrix, hdiag,
        dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hkernel : M *ᵥ e = 0 :=
      (hpsd.dotProduct_mulVec_zero_iff e).mp hquad
    have hcoord := congrFun hkernel (1 : Fin 2)
    simp [e, M, xiShiftedAdaptiveBilinearSourcePairMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord
    exact hoff hcoord
  · intro hpsd
    have hquad : e ⬝ᵥ (-M).mulVec e = 0 := by
      simp [e, M, xiShiftedAdaptiveBilinearSourcePairMatrix, hdiag,
        dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hkernel : (-M) *ᵥ e = 0 :=
      (hpsd.dotProduct_mulVec_zero_iff e).mp hquad
    have hcoord := congrFun hkernel (1 : Fin 2)
    simp [e, M, xiShiftedAdaptiveBilinearSourcePairMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord
    exact hoff hcoord

end

end RHTower
