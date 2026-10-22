import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopeCore
import GaloisForLFunctions.HTGeometry.PairRelationSimplePartial
import GaloisForLFunctions.HTGeometry.KhovanskiiSystem
import GaloisForLFunctions.HTGeometry.ComplexExponentialAlgebraicClosure
import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect
import GaloisForLFunctions.HTGeometry.LinearIndependenceMinorTransfer

/-!
# Essentiality and exponential algebraicity of a stage-two Schanuel counterexample

This module closes clause 4 of the canonical stage-two defect-slope normal form.  It constructs
three pair-supported algebraic relations, proves their conormal rows span the Kähler kernel, and
uses the nonzero intrinsic defect to obtain a nonsingular two-equation Khovanskii subsystem.
Consequently both exponents enter finite ecl stage two, the generated value field lies in the
countable complex exponential-algebraic closure, and so does the canonical defect slope.

The final essentiality predicate is Kirby's exact cancellation-free predimension comparison over
every rationally independent basis of a subspace of the original rational span.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def stageTwoCoordinateDifferential (x : Fin 2 → ℂ) :
    (Fin 4 → stageTwoValueField (x 0) (x 1)) →ₗ[stageTwoValueField (x 0) (x 1)]
      KaehlerDifferential AlgNum (stageTwoValueField (x 0) (x 1)) :=
  ∑ k : Fin 4, (LinearMap.proj k).smulRight
    (KaehlerDifferential.D AlgNum (stageTwoValueField (x 0) (x 1))
      (stageTwoGeneratorIn x k))

def stageTwoRelationGradientMatrix (x : Fin 2 → ℂ)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum) :
    Matrix (Fin 3) (Fin 4) (stageTwoValueField (x 0) (x 1)) :=
  fun r k => MvPolynomial.aeval (stageTwoGeneratorIn x)
    (MvPolynomial.pderiv k (Q r))

def stageTwoAdditiveIndex (i : Fin 2) : Fin 4 :=
  ⟨i.1, by omega⟩

def stageTwoMultiplicativeIndex (i : Fin 2) : Fin 4 :=
  ⟨i.1 + 2, by omega⟩

@[simp] theorem stageTwoGeneratorIn_additiveIndex (x : Fin 2 → ℂ) (i : Fin 2) :
    stageTwoGeneratorIn x (stageTwoAdditiveIndex i) = stageTwoExponentIn x i := by
  apply Subtype.ext
  fin_cases i <;> rfl

@[simp] theorem stageTwoGeneratorIn_multiplicativeIndex (x : Fin 2 → ℂ) (i : Fin 2) :
    stageTwoGeneratorIn x (stageTwoMultiplicativeIndex i) = stageTwoExponentialIn x i := by
  apply Subtype.ext
  fin_cases i <;> rfl

def stageTwoExponentialTangent (x : Fin 2 → ℂ)
    (u : Fin 2 → stageTwoValueField (x 0) (x 1)) :
    Fin 4 → stageTwoValueField (x 0) (x 1) :=
  ![u 0, u 1, stageTwoExponentialIn x 0 * u 0,
    stageTwoExponentialIn x 1 * u 1]

@[simp] theorem stageTwoExponentialTangent_additiveIndex (x : Fin 2 → ℂ)
    (u : Fin 2 → stageTwoValueField (x 0) (x 1)) (i : Fin 2) :
    stageTwoExponentialTangent x u (stageTwoAdditiveIndex i) = u i := by
  fin_cases i <;> rfl

@[simp] theorem stageTwoExponentialTangent_multiplicativeIndex (x : Fin 2 → ℂ)
    (u : Fin 2 → stageTwoValueField (x 0) (x 1)) (i : Fin 2) :
    stageTwoExponentialTangent x u (stageTwoMultiplicativeIndex i) =
      stageTwoExponentialIn x i * u i := by
  fin_cases i <;> rfl

def stageTwoInternalExponentialJacobian (x : Fin 2 → ℂ)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum) :
    Matrix (Fin 3) (Fin 2) (stageTwoValueField (x 0) (x 1)) :=
  fun r i => stageTwoRelationGradientMatrix x Q r (stageTwoAdditiveIndex i) +
    stageTwoExponentialIn x i *
      stageTwoRelationGradientMatrix x Q r (stageTwoMultiplicativeIndex i)

theorem stageTwoInternalExponentialJacobian_mulVec (x : Fin 2 → ℂ)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (u : Fin 2 → stageTwoValueField (x 0) (x 1)) :
    (stageTwoInternalExponentialJacobian x Q).mulVec u =
      (stageTwoRelationGradientMatrix x Q).mulVec
        (stageTwoExponentialTangent x u) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, stageTwoInternalExponentialJacobian,
    stageTwoRelationGradientMatrix]
  rw [Fin.sum_univ_two, Fin.sum_univ_four]
  simp [stageTwoAdditiveIndex, stageTwoMultiplicativeIndex,
    stageTwoExponentialTangent]
  ring

theorem exists_stageTwo_relationTriplet
    (x : Fin 2 → ℂ)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (j : Fin 4) (hj : Transcendental AlgNum (stageTwoGeneratorIn x j))
    (ks : Fin 3 → Fin 4) (hkj : ∀ r, ks r ≠ j) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) AlgNum,
      (∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0) ∧
      (∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
        (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0) ∧
      (∀ r l, l ≠ ks r → l ≠ j → MvPolynomial.pderiv l (Q r) = 0) := by
  have hdep (r : Fin 3) : ¬ AlgebraicIndependent AlgNum
      ![stageTwoGeneratorIn x (ks r), stageTwoGeneratorIn x j] := by
    intro hAI
    have hle := hAI.cardinalMk_le_trdeg
    rw [htrdeg] at hle
    norm_num [Cardinal.mk_fin] at hle
  choose Q hQzero hQpivot hQsupport using fun r =>
    exists_relation_supported_pair_pivot (stageTwoGeneratorIn x)
      (hkj r) hj (hdep r)
  exact ⟨Q, hQzero, hQpivot, hQsupport⟩

theorem stageTwoRelationGradientMatrix_row_mem_ker
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0)
    (r : Fin 3) :
    (stageTwoRelationGradientMatrix x Q).row r ∈
      LinearMap.ker (stageTwoCoordinateDifferential x) := by
  rw [LinearMap.mem_ker]
  have hdiff := derivation_aeval_eq_gradient
    (KaehlerDifferential.D AlgNum (stageTwoValueField (x 0) (x 1)))
    (stageTwoGeneratorIn x) (Q r)
  rw [hQzero r, map_zero] at hdiff
  simpa [stageTwoCoordinateDifferential, stageTwoRelationGradientMatrix,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype] using hdiff.symm

theorem linearIndependent_stageTwoRelationGradientMatrix_rows
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (ks : Fin 3 → Fin 4) (hks : Function.Injective ks)
    (j : Fin 4) (hkj : ∀ r, ks r ≠ j)
    (hQpivot : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0)
    (hQsupport : ∀ r l, l ≠ ks r → l ≠ j →
      MvPolynomial.pderiv l (Q r) = 0) :
    LinearIndependent (stageTwoValueField (x 0) (x 1))
      (stageTwoRelationGradientMatrix x Q).row := by
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  have hcol := congrFun hc (ks r)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
  rw [Finset.sum_eq_single r] at hcol
  · exact (mul_eq_zero.mp hcol).resolve_right (hQpivot r)
  · intro s hs hsr
    have hne : ks r ≠ ks s := fun h => hsr (hks h.symm)
    change c s * MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q s)) = 0
    rw [hQsupport s (ks r) hne (hkj r), map_zero, mul_zero]
  · intro hr
    exact absurd (Finset.mem_univ r) hr

theorem stageTwoCoordinateDifferential_surjective
    (x : Fin 2 → ℂ) (j : Fin 4)
    (hrank : Module.finrank (stageTwoValueField (x 0) (x 1))
      (KaehlerDifferential AlgNum (stageTwoValueField (x 0) (x 1))) = 1)
    (hj : KaehlerDifferential.D AlgNum (stageTwoValueField (x 0) (x 1))
      (stageTwoGeneratorIn x j) ≠ 0) :
    Function.Surjective (stageTwoCoordinateDifferential x) := by
  intro omega
  obtain ⟨c, hc, -⟩ := existsUnique_defectSlope hrank hj omega
  refine ⟨Pi.single j c, ?_⟩
  rw [hc]
  simp [stageTwoCoordinateDifferential, Pi.single_apply]

theorem span_stageTwoRelationGradientMatrix_rows_eq_ker
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0)
    (ks : Fin 3 → Fin 4) (hks : Function.Injective ks)
    (j : Fin 4) (hkj : ∀ r, ks r ≠ j)
    (hQpivot : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0)
    (hQsupport : ∀ r l, l ≠ ks r → l ≠ j →
      MvPolynomial.pderiv l (Q r) = 0)
    (hrank : Module.finrank (stageTwoValueField (x 0) (x 1))
      (KaehlerDifferential AlgNum (stageTwoValueField (x 0) (x 1))) = 1)
    (hj : KaehlerDifferential.D AlgNum (stageTwoValueField (x 0) (x 1))
      (stageTwoGeneratorIn x j) ≠ 0) :
    Submodule.span (stageTwoValueField (x 0) (x 1))
      (Set.range (stageTwoRelationGradientMatrix x Q).row) =
      LinearMap.ker (stageTwoCoordinateDifferential x) := by
  let K := stageTwoValueField (x 0) (x 1)
  let A := stageTwoRelationGradientMatrix x Q
  have hLI : LinearIndependent K A.row :=
    linearIndependent_stageTwoRelationGradientMatrix_rows x Q ks hks j hkj
      hQpivot hQsupport
  have hle : Submodule.span K (Set.range A.row) ≤
      LinearMap.ker (stageTwoCoordinateDifferential x) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact stageTwoRelationGradientMatrix_row_mem_ker x Q hQzero r
  have hsurj : Function.Surjective (stageTwoCoordinateDifferential x) :=
    stageTwoCoordinateDifferential_surjective x j hrank hj
  have hkerdim : Module.finrank K
      (LinearMap.ker (stageTwoCoordinateDifferential x)) = 3 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker
      (stageTwoCoordinateDifferential x)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hrank] at hdim
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hdim
    change Module.finrank (stageTwoValueField (x 0) (x 1))
      (LinearMap.ker (stageTwoCoordinateDifferential x)) = 3
    omega
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hLI, hkerdim]
  simp

theorem stageTwoInternalExponentialJacobian_kernel_eq_zero
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0)
    (ks : Fin 3 → Fin 4) (hks : Function.Injective ks)
    (j : Fin 4) (hkj : ∀ r, ks r ≠ j)
    (hj : Transcendental AlgNum (stageTwoGeneratorIn x j))
    (hQpivot : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0)
    (hQsupport : ∀ r l, l ≠ ks r → l ≠ j →
      MvPolynomial.pderiv l (Q r) = 0)
    (u : Fin 2 → stageTwoValueField (x 0) (x 1))
    (hu : (stageTwoInternalExponentialJacobian x Q).mulVec u = 0) :
    u = 0 := by
  let K := stageTwoValueField (x 0) (x 1)
  let Omega := KaehlerDifferential AlgNum K
  let A := stageTwoRelationGradientMatrix x Q
  let tangent := stageTwoExponentialTangent x u
  have hrank : Module.finrank K Omega = 1 :=
    finrank_kaehlerDifferential_eq_one_of_trdeg_eq_one htrdeg
  have hDj : KaehlerDifferential.D AlgNum K (stageTwoGeneratorIn x j) ≠ 0 := by
    intro hzero
    exact hj ((GaloisForLFunctions.kaehlerD_eq_zero_iff_isAlgebraic).mp hzero)
  have hspan := span_stageTwoRelationGradientMatrix_rows_eq_ker
    x Q hQzero ks hks j hkj hQpivot hQsupport hrank hDj
  have hAtangent : A.mulVec tangent = 0 := by
    rw [← stageTwoInternalExponentialJacobian_mulVec x Q u]
    exact hu
  let ell : (Fin 4 → K) →ₗ[K] K :=
    ∑ k : Fin 4, (tangent k) • LinearMap.proj k
  have hell_apply (c : Fin 4 → K) : ell c = dotProduct c tangent := by
    simp only [ell, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, dotProduct]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hker_le : LinearMap.ker (stageTwoCoordinateDifferential x) ≤
      LinearMap.ker ell := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    change ell ((stageTwoRelationGradientMatrix x Q).row r) = 0
    rw [hell_apply]
    exact congrFun hAtangent r
  choose mu hmu hmu_unique using fun k =>
    existsUnique_defectSlope hrank hDj
      (KaehlerDifferential.D AlgNum K (stageTwoGeneratorIn x k))
  have hcoord_single (k : Fin 4) (a : K) :
      stageTwoCoordinateDifferential x (Pi.single k a) =
        a • KaehlerDifferential.D AlgNum
          (stageTwoValueField (x 0) (x 1)) (stageTwoGeneratorIn x k) := by
    simp [stageTwoCoordinateDifferential, Pi.single_apply]
  have hell_single (k : Fin 4) (a : K) :
      ell (Pi.single k a) = a * tangent k := by
    rw [hell_apply]
    simp [dotProduct, Pi.single_apply]
  have htangent (k : Fin 4) : tangent k = mu k * tangent j := by
    have hc : (Pi.single k 1 - Pi.single j (mu k) : Fin 4 → K) ∈
        LinearMap.ker (stageTwoCoordinateDifferential x) := by
      rw [LinearMap.mem_ker]
      rw [map_sub, hcoord_single, hcoord_single, one_smul, hmu k,
        sub_self]
    have hellzero : ell (Pi.single k 1 - Pi.single j (mu k)) = 0 :=
      LinearMap.mem_ker.mp (hker_le hc)
    rw [map_sub, hell_single, hell_single, one_mul, sub_eq_zero] at hellzero
    exact hellzero
  let ia := stageTwoAdditiveIndex (0 : Fin 2)
  let im := stageTwoMultiplicativeIndex (0 : Fin 2)
  let y := stageTwoExponentialIn x 0
  let delta := y⁻¹ * mu im - mu ia
  have hdefect : stageTwoDefect x 0 =
      delta • KaehlerDifferential.D AlgNum K (stageTwoGeneratorIn x j) := by
    change (stageTwoExponentialIn x 0)⁻¹ •
          KaehlerDifferential.D AlgNum K (stageTwoExponentialIn x 0) -
        KaehlerDifferential.D AlgNum K (stageTwoExponentIn x 0) = _
    rw [← stageTwoGeneratorIn_multiplicativeIndex,
      ← stageTwoGeneratorIn_additiveIndex, hmu im, hmu ia, smul_smul, sub_smul]
    rfl
  have hdelta : delta ≠ 0 := by
    intro hzero
    apply stageTwoDefect_ne_zero x hx 0
    rw [hdefect, hzero, zero_smul]
  have hy : y ≠ 0 := by
    intro hzero
    have hval := congrArg Subtype.val hzero
    exact Complex.exp_ne_zero (x 0) (by simp [y, stageTwoExponentialIn] at hval)
  have hnum : mu im - y * mu ia ≠ 0 := by
    intro hzero
    apply hdelta
    have heq : mu im = y * mu ia := sub_eq_zero.mp hzero
    simp [delta, heq, hy]
  have hadd := htangent ia
  have hmul := htangent im
  have hnumzero : (mu im - y * mu ia) * tangent j = 0 := by
    calc
      (mu im - y * mu ia) * tangent j =
          mu im * tangent j - y * (mu ia * tangent j) := by ring
      _ = y * u 0 - y * u 0 := by
        rw [← hmul, ← hadd]
        rfl
      _ = 0 := sub_self _
  have htj : tangent j = 0 := (mul_eq_zero.mp hnumzero).resolve_left hnum
  funext i
  have hi := htangent (stageTwoAdditiveIndex i)
  rw [htj, mul_zero] at hi
  simpa [tangent] using hi

theorem stageTwoInternalExponentialJacobian_injective
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0)
    (ks : Fin 3 → Fin 4) (hks : Function.Injective ks)
    (j : Fin 4) (hkj : ∀ r, ks r ≠ j)
    (hj : Transcendental AlgNum (stageTwoGeneratorIn x j))
    (hQpivot : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0)
    (hQsupport : ∀ r l, l ≠ ks r → l ≠ j →
      MvPolynomial.pderiv l (Q r) = 0) :
    Function.Injective (stageTwoInternalExponentialJacobian x Q).mulVec := by
  intro u v huv
  apply sub_eq_zero.mp
  apply stageTwoInternalExponentialJacobian_kernel_eq_zero x hx htrdeg Q hQzero
    ks hks j hkj hj hQpivot hQsupport
  funext r
  have hr := congrFun huv r
  simpa [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib] using
    sub_eq_zero.mpr hr

theorem exists_stageTwoInternalExponentialJacobian_minor
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0)
    (ks : Fin 3 → Fin 4) (hks : Function.Injective ks)
    (j : Fin 4) (hkj : ∀ r, ks r ≠ j)
    (hj : Transcendental AlgNum (stageTwoGeneratorIn x j))
    (hQpivot : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x)
      (MvPolynomial.pderiv (ks r) (Q r)) ≠ 0)
    (hQsupport : ∀ r l, l ≠ ks r → l ≠ j →
      MvPolynomial.pderiv l (Q r) = 0) :
    ∃ rows : Fin 2 → Fin 3,
      ((stageTwoInternalExponentialJacobian x Q).submatrix rows id).det ≠ 0 := by
  let B := stageTwoInternalExponentialJacobian x Q
  have hinj : Function.Injective B.mulVec :=
    stageTwoInternalExponentialJacobian_injective x hx htrdeg Q hQzero
      ks hks j hkj hj hQpivot hQsupport
  have hcols : LinearIndependent (stageTwoValueField (x 0) (x 1)) B.col :=
    Matrix.mulVec_injective_iff.mp hinj
  have hrows : LinearIndependent (stageTwoValueField (x 0) (x 1)) B.transpose.row := by
    simpa [Matrix.row, Matrix.col] using hcols
  obtain ⟨rows, -, hdet⟩ :=
    exists_injective_det_submatrix_ne_zero (M := B.transpose) hrows
  refine ⟨rows, ?_⟩
  have heq : B.transpose.submatrix id rows =
      (B.submatrix rows id).transpose := by
    ext i k
    rfl
  rw [heq, Matrix.det_transpose] at hdet
  exact hdet

def stageTwoComplementZero : Fin 3 → Fin 4 := ![1, 2, 3]

def stageTwoComplementTwo : Fin 3 → Fin 4 := ![0, 1, 3]

theorem stageTwoComplementZero_injective :
    Function.Injective stageTwoComplementZero := by
  intro i k hik
  fin_cases i <;> fin_cases k <;>
    simp_all [stageTwoComplementZero]

theorem stageTwoComplementTwo_injective :
    Function.Injective stageTwoComplementTwo := by
  intro i k hik
  fin_cases i <;> fin_cases k <;>
    simp_all [stageTwoComplementTwo]

theorem stageTwoComplementZero_ne_zero (r : Fin 3) :
    stageTwoComplementZero r ≠ 0 := by
  fin_cases r <;> simp [stageTwoComplementZero]

theorem stageTwoComplementTwo_ne_two (r : Fin 3) :
    stageTwoComplementTwo r ≠ 2 := by
  fin_cases r <;> simp [stageTwoComplementTwo]

theorem exists_transcendental_stageTwoGeneratorIn
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x) :
    (Transcendental AlgNum (stageTwoGeneratorIn x 0) ∧
        Function.Injective stageTwoComplementZero ∧
        ∀ r, stageTwoComplementZero r ≠ 0) ∨
      (Transcendental AlgNum (stageTwoGeneratorIn x 2) ∧
        Function.Injective stageTwoComplementTwo ∧
        ∀ r, stageTwoComplementTwo r ≠ 2) := by
  rcases transcendental_or_transcendental_exp (hx.ne_zero 0) with h | h
  · left
    refine ⟨transcendental_base_of_transcendental_rat
      (transcendental_mk (stageTwoGeneratorIn x 0).property h),
      stageTwoComplementZero_injective, stageTwoComplementZero_ne_zero⟩
  · right
    refine ⟨transcendental_base_of_transcendental_rat
      (transcendental_mk (stageTwoGeneratorIn x 2).property h),
      stageTwoComplementTwo_injective, stageTwoComplementTwo_ne_two⟩

theorem exists_stageTwo_relationTriplet_minor
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) AlgNum,
      (∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0) ∧
      ∃ rows : Fin 2 → Fin 3,
        ((stageTwoInternalExponentialJacobian x Q).submatrix rows id).det ≠ 0 := by
  rcases exists_transcendental_stageTwoGeneratorIn x hx with h | h
  · rcases h with ⟨hj, hks, hkj⟩
    obtain ⟨Q, hQzero, hQpivot, hQsupport⟩ :=
      exists_stageTwo_relationTriplet x htrdeg 0 hj stageTwoComplementZero hkj
    refine ⟨Q, hQzero, ?_⟩
    exact exists_stageTwoInternalExponentialJacobian_minor x hx htrdeg Q hQzero
      stageTwoComplementZero hks 0 hkj hj hQpivot hQsupport
  · rcases h with ⟨hj, hks, hkj⟩
    obtain ⟨Q, hQzero, hQpivot, hQsupport⟩ :=
      exists_stageTwo_relationTriplet x htrdeg 2 hj stageTwoComplementTwo hkj
    refine ⟨Q, hQzero, ?_⟩
    exact exists_stageTwoInternalExponentialJacobian_minor x hx htrdeg Q hQzero
      stageTwoComplementTwo hks 2 hkj hj hQpivot hQsupport

/-- Canonical ordering of the two additive and two multiplicative exponential-graph coordinates. -/
def stageTwoExponentialIndexEquiv : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]
  invFun
    | Sum.inl i => stageTwoAdditiveIndex i
    | Sum.inr i => stageTwoMultiplicativeIndex i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by rcases i with i | i <;> fin_cases i <;> rfl

@[simp] theorem stageTwoExponentialIndexEquiv_additiveIndex (i : Fin 2) :
    stageTwoExponentialIndexEquiv (stageTwoAdditiveIndex i) = Sum.inl i := by
  fin_cases i <;> rfl

@[simp] theorem stageTwoExponentialIndexEquiv_multiplicativeIndex (i : Fin 2) :
    stageTwoExponentialIndexEquiv (stageTwoMultiplicativeIndex i) = Sum.inr i := by
  fin_cases i <;> rfl

@[simp] theorem complexExponentialGraph_stageTwoExponentialIndexEquiv
    (x : Fin 2 → ℂ) (j : Fin 4) :
    complexExponentialGraph x (stageTwoExponentialIndexEquiv j) =
      stageTwoGenerator x j := by
  fin_cases j <;> rfl

/-- The algebraic numbers embed into the first finite exponential-algebraic-closure stage. -/
theorem isAlgebraic_coe_algNum (z : AlgNum) : IsAlgebraic ℚ (z : ℂ) := by
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  exact (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom ℚ AlgNum ℂ) (algebraMap AlgNum ℂ).injective).mpr hz

def algNumToComplexEclStageOne : AlgNum →+* complexEclStage 1 where
  toFun z := ⟨z, isAlgebraic_mem_complexEclStage_one (isAlgebraic_coe_algNum z)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_algNumToComplexEclStageOne (z : AlgNum) :
    ((algNumToComplexEclStageOne z : complexEclStage 1) : ℂ) = z := rfl

/-- The selected two-equation exponential-polynomial system over the algebraic numbers. -/
def stageTwoComplexKhovanskiiSystem
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum) (rows : Fin 2 → Fin 3) :
    Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  fun i => MvPolynomial.map (algebraMap AlgNum ℂ)
    (MvPolynomial.rename stageTwoExponentialIndexEquiv (Q (rows i)))

/-- The same selected system, with coefficients admitted to the first ecl stage. -/
def stageTwoEclKhovanskiiSystem
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum) (rows : Fin 2 → Fin 3) :
    Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 2) (complexEclStage 1) :=
  fun i => MvPolynomial.map algNumToComplexEclStageOne
    (MvPolynomial.rename stageTwoExponentialIndexEquiv (Q (rows i)))

theorem map_stageTwoEclKhovanskiiSystem
    (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum) (rows : Fin 2 → Fin 3) :
    mapKhovanskiiSystem (complexEclStage 1) (stageTwoEclKhovanskiiSystem Q rows) =
      stageTwoComplexKhovanskiiSystem Q rows := by
  have hcomp : (complexEclStage 1).subtype.comp algNumToComplexEclStageOne =
      algebraMap AlgNum ℂ := by
    ext z
    rfl
  funext i
  simp [mapKhovanskiiSystem, stageTwoEclKhovanskiiSystem,
    stageTwoComplexKhovanskiiSystem, MvPolynomial.map_map, hcomp]

theorem eval₂_stageTwoGenerator_eq_coe_aeval
    (x : Fin 2 → ℂ) (P : MvPolynomial (Fin 4) AlgNum) :
    MvPolynomial.eval₂ (algebraMap AlgNum ℂ) (stageTwoGenerator x) P =
      algebraMap (stageTwoValueField (x 0) (x 1)) ℂ
        (MvPolynomial.aeval (stageTwoGeneratorIn x) P) := by
  rw [MvPolynomial.aeval_def]
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply AlgNum
        (stageTwoValueField (x 0) (x 1)) ℂ c).symm
  | add P Q hP hQ =>
      simp only [MvPolynomial.eval₂_add, map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]
      rw [hP]
      rfl

theorem exponentialSystemEval_stageTwoComplexKhovanskiiSystem_eq_zero
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (rows : Fin 2 → Fin 3)
    (hQzero : ∀ r, MvPolynomial.aeval (stageTwoGeneratorIn x) (Q r) = 0) :
    exponentialSystemEval (stageTwoComplexKhovanskiiSystem Q rows) x = 0 := by
  funext i
  change exponentialPolynomialEval (stageTwoComplexKhovanskiiSystem Q rows i) x = 0
  rw [show exponentialPolynomialEval (stageTwoComplexKhovanskiiSystem Q rows i) x =
      MvPolynomial.eval₂ (algebraMap AlgNum ℂ) (stageTwoGenerator x)
        (Q (rows i)) by
    simp [exponentialPolynomialEval, stageTwoComplexKhovanskiiSystem,
      MvPolynomial.eval_map, MvPolynomial.eval₂_rename, Function.comp_def]]
  rw [eval₂_stageTwoGenerator_eq_coe_aeval, hQzero, map_zero]

theorem eval_pderiv_stageTwoComplexKhovanskiiSystem
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (rows : Fin 2 → Fin 3) (i : Fin 2) (j : Fin 4) :
    MvPolynomial.eval (complexExponentialGraph x)
        (MvPolynomial.pderiv (stageTwoExponentialIndexEquiv j)
          (stageTwoComplexKhovanskiiSystem Q rows i)) =
      algebraMap (stageTwoValueField (x 0) (x 1)) ℂ
        (MvPolynomial.aeval (stageTwoGeneratorIn x)
          (MvPolynomial.pderiv j (Q (rows i)))) := by
  rw [show MvPolynomial.eval (complexExponentialGraph x)
      (MvPolynomial.pderiv (stageTwoExponentialIndexEquiv j)
        (stageTwoComplexKhovanskiiSystem Q rows i)) =
      MvPolynomial.eval₂ (algebraMap AlgNum ℂ) (stageTwoGenerator x)
        (MvPolynomial.pderiv j (Q (rows i))) by
    simp [stageTwoComplexKhovanskiiSystem, MvPolynomial.pderiv_map,
    MvPolynomial.pderiv_rename stageTwoExponentialIndexEquiv.injective,
    MvPolynomial.eval_map, MvPolynomial.eval₂_rename, Function.comp_def]]
  exact eval₂_stageTwoGenerator_eq_coe_aeval x _

theorem exponentialJacobian_stageTwoComplexKhovanskiiSystem
    (x : Fin 2 → ℂ) (Q : Fin 3 → MvPolynomial (Fin 4) AlgNum)
    (rows : Fin 2 → Fin 3) :
    exponentialJacobian (stageTwoComplexKhovanskiiSystem Q rows) x =
      ((stageTwoInternalExponentialJacobian x Q).submatrix rows id).map
        (algebraMap (stageTwoValueField (x 0) (x 1)) ℂ) := by
  ext i j
  simp only [exponentialJacobian, Matrix.map_apply, Matrix.submatrix_apply,
    id_eq]
  rw [show Sum.inl j = stageTwoExponentialIndexEquiv (stageTwoAdditiveIndex j) by simp,
    show Sum.inr j = stageTwoExponentialIndexEquiv (stageTwoMultiplicativeIndex j) by simp,
    eval_pderiv_stageTwoComplexKhovanskiiSystem,
    eval_pderiv_stageTwoComplexKhovanskiiSystem]
  change
    algebraMap (stageTwoValueField (x 0) (x 1)) ℂ
        (MvPolynomial.aeval (stageTwoGeneratorIn x)
          (MvPolynomial.pderiv (stageTwoAdditiveIndex j) (Q (rows i)))) +
      Complex.exp (x j) *
        algebraMap (stageTwoValueField (x 0) (x 1)) ℂ
          (MvPolynomial.aeval (stageTwoGeneratorIn x)
            (MvPolynomial.pderiv (stageTwoMultiplicativeIndex j) (Q (rows i)))) =
      algebraMap (stageTwoValueField (x 0) (x 1)) ℂ
        (MvPolynomial.aeval (stageTwoGeneratorIn x)
            (MvPolynomial.pderiv (stageTwoAdditiveIndex j) (Q (rows i))) +
          stageTwoExponentialIn x j *
            MvPolynomial.aeval (stageTwoGeneratorIn x)
              (MvPolynomial.pderiv (stageTwoMultiplicativeIndex j) (Q (rows i))))
  rw [map_add, map_mul]
  rfl

theorem stageTwoExponent_mem_complexEclStage_two_of_trdeg_one
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (i : Fin 2) : x i ∈ complexEclStage 2 := by
  obtain ⟨Q, hQzero, rows, hminor⟩ :=
    exists_stageTwo_relationTriplet_minor x hx htrdeg
  let K := stageTwoValueField (x 0) (x 1)
  let A := (stageTwoInternalExponentialJacobian x Q).submatrix rows id
  have hdet : (exponentialJacobian (stageTwoComplexKhovanskiiSystem Q rows) x).det ≠ 0 := by
    rw [exponentialJacobian_stageTwoComplexKhovanskiiSystem]
    have hmapdet := (algebraMap K ℂ).map_det A
    simp only [RingHom.mapMatrix_apply] at hmapdet
    rw [← hmapdet]
    intro hz
    apply hminor
    apply (algebraMap K ℂ).injective
    simpa using hz
  have hzero := exponentialSystemEval_stageTwoComplexKhovanskiiSystem_eq_zero
    x Q rows hQzero
  have hxComplex : x ∈ khovanskiiLocus (stageTwoComplexKhovanskiiSystem Q rows) :=
    mem_khovanskiiLocus_of_eval_eq_zero_of_det_ne_zero _ _ hzero hdet
  have hxStage : x ∈ khovanskiiLocus
      (mapKhovanskiiSystem (complexEclStage 1) (stageTwoEclKhovanskiiSystem Q rows)) := by
    rw [map_stageTwoEclKhovanskiiSystem]
    exact hxComplex
  exact khovanskiiCoordinate_mem_complexEclStage_succ
    (stageTwoEclKhovanskiiSystem Q rows) hxStage i

theorem stageTwoGenerator_mem_complexExponentialAlgebraicClosure_of_trdeg_one
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (j : Fin 4) :
    stageTwoGenerator x j ∈ complexExponentialAlgebraicClosure := by
  have hxi (i : Fin 2) : x i ∈ complexExponentialAlgebraicClosure :=
    complexEclStage_le_complexExponentialAlgebraicClosure 2
      (stageTwoExponent_mem_complexEclStage_two_of_trdeg_one x hx htrdeg i)
  fin_cases j
  · exact hxi 0
  · exact hxi 1
  · exact exp_mem_complexExponentialAlgebraicClosure (hxi 0)
  · exact exp_mem_complexExponentialAlgebraicClosure (hxi 1)

/-- The countable ecl subfield, regarded as an intermediate field over the algebraic numbers. -/
def complexEclAsIntermediateField : IntermediateField AlgNum ℂ :=
  complexExponentialAlgebraicClosure.toIntermediateField fun z =>
    isAlgebraic_mem_complexExponentialAlgebraicClosure (isAlgebraic_coe_algNum z)

theorem stageTwoValueField_le_complexEclAsIntermediateField_of_trdeg_one
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1) :
    stageTwoValueField (x 0) (x 1) ≤ complexEclAsIntermediateField := by
  rw [stageTwoValueField_eq_adjoin_range, IntermediateField.adjoin_le_iff]
  rintro z ⟨j, rfl⟩
  exact stageTwoGenerator_mem_complexExponentialAlgebraicClosure_of_trdeg_one
    x hx htrdeg j

theorem coe_mem_complexExponentialAlgebraicClosure_of_mem_stageTwoValueField
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1)
    (z : stageTwoValueField (x 0) (x 1)) :
    (z : ℂ) ∈ complexExponentialAlgebraicClosure :=
  stageTwoValueField_le_complexEclAsIntermediateField_of_trdeg_one x hx htrdeg z.property

/-- Kirby's essential-counterexample condition in its cancellation-free basis form.

For linearly independent tuples `x` and `c`, the displayed inequality is exactly
`δ(x) ≤ δ(c)` after moving the two finite rational linear dimensions to opposite sides.  It is
quantified over every rationally independent basis `c` in the rational span of `x`; predimension
depends only on that rational span. -/
def IsEssentialSchanuelCounterexample {n : ℕ} (x : Fin n → ℂ) : Prop :=
  ¬ SchanuelExtractionFor x ∧
    ∀ {m : ℕ} (c : Fin m → ℂ), LinearIndependent ℚ c →
      Set.range c ⊆ Submodule.span ℚ (Set.range x) →
      Algebra.trdeg AlgNum (schanuelExponentialValueField x) + (m : Cardinal) ≤
        Algebra.trdeg AlgNum (schanuelExponentialValueField c) + (n : Cardinal)

theorem one_le_trdeg_schanuelExponentialValueField_of_ne
    {n : ℕ} (x : Fin n → ℂ) (i : Fin n) (hi : x i ≠ 0) :
    1 ≤ Algebra.trdeg AlgNum (schanuelExponentialValueField x) := by
  let K := schanuelExponentialValueField x
  rcases transcendental_or_transcendental_exp hi with h | h
  · let z : K := ⟨x i, IntermediateField.subset_adjoin AlgNum _
      ⟨Sum.inl i, rfl⟩⟩
    have hzQ : Transcendental ℚ z := transcendental_mk z.property h
    have hz : Transcendental AlgNum z :=
      transcendental_base_of_transcendental_rat hzQ
    have hAI : AlgebraicIndependent AlgNum (fun _ : Fin 1 => z) :=
      algebraicIndependent_unique_type_iff.mpr hz
    simpa [Cardinal.mk_fin] using hAI.cardinalMk_le_trdeg
  · let z : K := ⟨Complex.exp (x i), IntermediateField.subset_adjoin AlgNum _
      ⟨Sum.inr i, rfl⟩⟩
    have hzQ : Transcendental ℚ z := transcendental_mk z.property h
    have hz : Transcendental AlgNum z :=
      transcendental_base_of_transcendental_rat hzQ
    have hAI : AlgebraicIndependent AlgNum (fun _ : Fin 1 => z) :=
      algebraicIndependent_unique_type_iff.mpr hz
    simpa [Cardinal.mk_fin] using hAI.cardinalMk_le_trdeg

theorem isEssentialSchanuelCounterexample_stageTwo_of_trdeg_one
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (htrdeg : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1) :
    IsEssentialSchanuelCounterexample x := by
  constructor
  · exact (not_schanuelExtractionFor_two_iff_stageTwoValueField_trdeg_lt x).mpr (by
      rw [htrdeg]
      norm_num)
  · intro m c hc hspan
    have hspanle : Submodule.span ℚ (Set.range c) ≤
        Submodule.span ℚ (Set.range x) :=
      Submodule.span_le.mpr hspan
    letI : Module.Finite ℚ (Submodule.span ℚ (Set.range x)) :=
      Module.Finite.of_fg (Submodule.fg_span (Set.finite_range x))
    have hm' := Submodule.finrank_mono hspanle
    have hm : m ≤ 2 := by
      rw [finrank_span_eq_card hc, finrank_span_eq_card hx] at hm'
      simpa using hm'
    have htrdeg' : Algebra.trdeg AlgNum (schanuelExponentialValueField x) = 1 := by
      rw [← stageTwoValueField_eq_schanuelExponentialValueField]
      exact htrdeg
    rw [htrdeg']
    interval_cases m
    · calc
        (1 : Cardinal) + 0 ≤ 2 := by norm_num
        _ = 0 + 2 := by simp
        _ ≤ Algebra.trdeg AlgNum (schanuelExponentialValueField c) + 2 :=
          by simp [add_comm]
    · calc
        (1 : Cardinal) + 1 = 2 + 0 := by norm_num
        _ ≤ 2 + Algebra.trdeg AlgNum (schanuelExponentialValueField c) :=
          add_le_add_right bot_le 2
        _ = Algebra.trdeg AlgNum (schanuelExponentialValueField c) + 2 :=
          add_comm _ _
    · have hpos : 1 ≤ Algebra.trdeg AlgNum (schanuelExponentialValueField c) :=
        one_le_trdeg_schanuelExponentialValueField_of_ne c 0 (hc.ne_zero 0)
      calc
        (1 : Cardinal) + 2 = 2 + 1 := by norm_num
        _ ≤ 2 + Algebra.trdeg AlgNum (schanuelExponentialValueField c) :=
          add_le_add_right hpos 2
        _ = Algebra.trdeg AlgNum (schanuelExponentialValueField c) + 2 :=
          add_comm _ _

/-- Clause 4, combined with the already closed clauses 1--3: the actual canonical slope belongs to
the countable complex exponential-algebraic closure, and the tuple is essential in Kirby's exact
predimension sense. -/
theorem exists_stageTwoDefectSlopeCore_essential_ecl
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) < 2) :
    ∃ core : StageTwoDefectSlopeCore x,
      IsEssentialSchanuelCounterexample x ∧
        (core.rho : ℂ) ∈ complexExponentialAlgebraicClosure := by
  obtain ⟨core⟩ := exists_stageTwoDefectSlopeCore x hx hlt
  exact ⟨core,
    isEssentialSchanuelCounterexample_stageTwo_of_trdeg_one x hx core.trdeg_eq_one,
    coe_mem_complexExponentialAlgebraicClosure_of_mem_stageTwoValueField
      x hx core.trdeg_eq_one core.rho⟩

end

end GaloisForLFunctions.RHTower
