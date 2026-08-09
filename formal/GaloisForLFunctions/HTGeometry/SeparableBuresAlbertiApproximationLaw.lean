import GaloisForLFunctions.HTGeometry.FiniteDimensionalOperatorAlbertiLaw
import GaloisForLFunctions.HTGeometry.SeparableBuresPositiveReporterLaw
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Separable Bures Alberti approximation law

Finite-subspace block extension and Hilbert–Schmidt tail control lift exact
finite-dimensional Alberti reporters to positive trace-class operators on a
separable Hilbert space.
-/

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open RHTower
open scoped ComplexOrder InnerProductSpace

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteSubspaceReporterExtension (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (c : ℂ) : H →L[ℂ] H :=
  S.subtypeL ∘L A ∘L S.orthogonalProjectionOnto +
    c • (1 - S.starProjection)

omit [CompleteSpace H] in
theorem projection_subtype (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    S.orthogonalProjectionOnto ∘L S.subtypeL = 1 := by
  ext x
  simp

omit [CompleteSpace H] in
theorem projection_complement (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    S.orthogonalProjectionOnto ∘L (1 - S.starProjection) = 0 := by
  ext x
  change S.starProjection (x - S.starProjection x) = 0
  rw [map_sub]
  rw [S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)]
  exact sub_self _

omit [CompleteSpace H] in
theorem complement_subtype (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    (1 - S.starProjection) ∘L S.subtypeL = 0 := by
  ext x
  change (x : H) - S.starProjection x = 0
  rw [S.starProjection_eq_self_iff.mpr x.property]
  exact sub_self _

omit [CompleteSpace H] in
theorem projection_sq (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    S.starProjection ∘L S.starProjection = S.starProjection := by
  ext x
  exact S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)

omit [CompleteSpace H] in
theorem complement_sq (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    (1 - S.starProjection) ∘L (1 - S.starProjection) =
      1 - S.starProjection := by
  ext x
  change (x - S.starProjection x) -
      S.starProjection (x - S.starProjection x) = x - S.starProjection x
  rw [map_sub, S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)]
  abel

theorem finiteSubspaceReporterExtension_mul (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A B : S →L[ℂ] S) (c d : ℂ) :
    finiteSubspaceReporterExtension S A c ∘L finiteSubspaceReporterExtension S B d = finiteSubspaceReporterExtension S (A ∘L B) (c * d) := by
  let i := S.subtypeL
  let p := S.orthogonalProjectionOnto
  let Q := 1 - S.starProjection
  have hmain : (i ∘L A ∘L p) ∘L (i ∘L B ∘L p) =
      i ∘L (A ∘L B) ∘L p := by
    ext x
    change i (A (p (i (B (p x))))) = i (A (B (p x)))
    have hpi := congrArg (fun T => T (B (p x))) (projection_subtype S)
    change p (i (B (p x))) = B (p x) at hpi
    rw [hpi]
  have hcross₁ : (i ∘L A ∘L p) ∘L Q = 0 := by
    ext x
    change i (A (p (Q x))) = 0
    have hpq := congrArg (fun T => T x) (projection_complement S)
    change p (Q x) = 0 at hpq
    rw [hpq]
    simp
  have hcross₂ : Q ∘L (i ∘L B ∘L p) = 0 := by
    ext x
    change Q (i (B (p x))) = 0
    have hqi := congrArg (fun T => T (B (p x))) (complement_subtype S)
    change Q (i (B (p x))) = 0 at hqi
    exact hqi
  have htail : Q ∘L Q = Q := complement_sq S
  simp only [finiteSubspaceReporterExtension, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [hmain, hcross₁, hcross₂, htail]
  module

omit [CompleteSpace H] in
theorem complement_eq_orthogonalProjection
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    1 - S.starProjection = Sᗮ.starProjection := by
  ext x
  change x - S.starProjection x = Sᗮ.starProjection x
  have h := S.starProjection_add_starProjection_orthogonal x
  calc
    x - S.starProjection x =
        (S.starProjection x + Sᗮ.starProjection x) - S.starProjection x :=
      congrArg (fun y => y - S.starProjection x) h.symm
    _ = Sᗮ.starProjection x := by abel

omit [CompleteSpace H] in
theorem finiteSubspaceReporterExtension_one (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    finiteSubspaceReporterExtension S 1 1 = 1 := by
  ext x
  simp only [finiteSubspaceReporterExtension, add_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self,
    one_smul, sub_apply]
  change (S.orthogonalProjectionOnto x : H) +
      (x - S.starProjection x) = x
  rw [show (S.orthogonalProjectionOnto x : H) = S.starProjection x by rfl]
  abel

theorem finiteSubspaceReporterExtension_isPositive (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (hA : A.IsPositive) (c : ℝ) (hc : 0 ≤ c) :
    (finiteSubspaceReporterExtension S A (c : ℂ)).IsPositive := by
  have hblock : (S.subtypeL ∘L A ∘L S.orthogonalProjectionOnto).IsPositive := by
    have h := hA.conj_adjoint S.subtypeL
    rwa [S.adjoint_subtypeL] at h
  have hQ : (1 - S.starProjection).IsPositive := by
    rw [complement_eq_orthogonalProjection]
    exact IsPositive.of_isStarProjection isStarProjection_starProjection
  exact hblock.add (hQ.smul_of_nonneg (by exact_mod_cast hc))

theorem finiteSubspaceReporterExtension_isUnit (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (hA : IsUnit A) (c : ℂ) (hc : c ≠ 0) :
    IsUnit (finiteSubspaceReporterExtension S A c) := by
  let B := finiteSubspaceReporterExtension S (Ring.inverse A) c⁻¹
  have hinv : A ∘L Ring.inverse A = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel A hA
  have hinv' : Ring.inverse A ∘L A = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.inverse_mul_cancel A hA
  have hAB : finiteSubspaceReporterExtension S A c ∘L B = 1 := by
    rw [finiteSubspaceReporterExtension_mul, hinv, mul_inv_cancel₀ hc,
      finiteSubspaceReporterExtension_one]
  have hBA : B ∘L finiteSubspaceReporterExtension S A c = 1 := by
    rw [finiteSubspaceReporterExtension_mul, hinv', inv_mul_cancel₀ hc,
      finiteSubspaceReporterExtension_one]
  refine ⟨⟨finiteSubspaceReporterExtension S A c, B, ?_, ?_⟩, rfl⟩
  · simpa only [ContinuousLinearMap.mul_def] using hAB
  · simpa only [ContinuousLinearMap.mul_def] using hBA

theorem finiteSubspaceReporterExtension_ringInverse (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (hA : IsUnit A) (c : ℂ) (hc : c ≠ 0) :
    Ring.inverse (finiteSubspaceReporterExtension S A c) =
      finiteSubspaceReporterExtension S (Ring.inverse A) c⁻¹ := by
  have hE := finiteSubspaceReporterExtension_isUnit S A hA c hc
  have hinv : A ∘L Ring.inverse A = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel A hA
  apply hE.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ hE]
  symm
  simpa only [ContinuousLinearMap.mul_def] using
    (show finiteSubspaceReporterExtension S A c ∘L finiteSubspaceReporterExtension S (Ring.inverse A) c⁻¹ = 1 by
      rw [finiteSubspaceReporterExtension_mul, hinv, mul_inv_cancel₀ hc,
        finiteSubspaceReporterExtension_one])

theorem finiteSubspaceReporterExtension_isStrictlyPositive
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (hA : IsStrictlyPositive A) (c : ℝ) (hc : 0 < c) :
    IsStrictlyPositive (finiteSubspaceReporterExtension S A (c : ℂ)) := by
  refine IsStrictlyPositive.iff_of_unital.mpr ⟨?_, ?_⟩
  · exact (nonneg_iff_isPositive _).2 (finiteSubspaceReporterExtension_isPositive S A
      ((nonneg_iff_isPositive _).1 hA.nonneg) c hc.le)
  · exact finiteSubspaceReporterExtension_isUnit S A hA.isUnit (c : ℂ) (by exact_mod_cast hc.ne')

theorem finiteDomain_isHilbertSchmidt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [FiniteDimensional ℂ E] (T : E →L[ℂ] F) :
    T.IsHilbertSchmidt := by
  rw [isHilbertSchmidt_iff_summable
    (stdOrthonormalBasis ℂ E).toHilbertBasis]
  exact (hasSum_fintype _).summable

def finiteSubspaceCompression (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (M : H →L[ℂ] H) : S →L[ℂ] S :=
  S.orthogonalProjectionOnto ∘L M ∘L S.subtypeL

theorem finiteSubspaceCompression_isPositive
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (M : H →L[ℂ] H) (hM : M.IsPositive) :
    (finiteSubspaceCompression S M).IsPositive := by
  have h := hM.conj_adjoint S.orthogonalProjectionOnto
  rwa [S.adjoint_orthogonalProjectionOnto] at h

theorem trace_block
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (A : S →L[ℂ] S) :
    separableBuresTracePairing C
        (S.subtypeL ∘L A ∘L S.orthogonalProjectionOnto) =
      Complex.re (opTrace (finiteSubspaceCompression S (C : H →L[ℂ] H) ∘L A)) := by
  let i := S.subtypeL
  let p := S.orthogonalProjectionOnto
  let Y : H →L[ℂ] S := A ∘L p ∘L (C : H →L[ℂ] H)
  have hi : i.IsHilbertSchmidt := finiteDomain_isHilbertSchmidt i
  have hroot := positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hroot2 : CFC.sqrt (C : H →L[ℂ] H) ∘L
      CFC.sqrt (C : H →L[ℂ] H) = (C : H →L[ℂ] H) :=
    CFC.sqrt_mul_sqrt_self _ ((nonneg_iff_isPositive _).2 hC)
  have hCHS : (C : H →L[ℂ] H).IsHilbertSchmidt := by
    rw [← hroot2]
    exact hroot.comp_left _
  have hY : Y.IsHilbertSchmidt := hCHS.comp_left (A ∘L p)
  have hcyc : opTrace (i ∘L Y) = opTrace (Y ∘L i) :=
    opTrace_comp_comm hi hY
  have hA : A.IsHilbertSchmidt := finiteDimensional_isHilbertSchmidt A
  have hcomp : (finiteSubspaceCompression S (C : H →L[ℂ] H)).IsHilbertSchmidt :=
    finiteDimensional_isHilbertSchmidt _
  have hcycS : opTrace (A ∘L finiteSubspaceCompression S (C : H →L[ℂ] H)) =
      opTrace (finiteSubspaceCompression S (C : H →L[ℂ] H) ∘L A) :=
    opTrace_comp_comm hA hcomp
  unfold separableBuresTracePairing
  congr 1
  calc
    opTrace ((C : H →L[ℂ] H) ∘L
        (S.subtypeL ∘L A ∘L S.orthogonalProjectionOnto)) =
        opTrace ((S.subtypeL ∘L A ∘L S.orthogonalProjectionOnto) ∘L
          (C : H →L[ℂ] H)) :=
      C.property.one_opTrace_comp_comm _ |>.symm
    _ = opTrace (i ∘L Y) := by
      congr 1
    _ = opTrace (Y ∘L i) := hcyc
    _ = opTrace (A ∘L finiteSubspaceCompression S (C : H →L[ℂ] H)) := by
      congr 1
    _ = opTrace (finiteSubspaceCompression S (C : H →L[ℂ] H) ∘L A) := hcycS

def finiteHilbertBasisSubspace {ι : Type*} (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    Submodule ℂ H := Submodule.span ℂ (b '' (s : Set ι))

noncomputable instance finiteHilbertBasisSubspace_finiteDimensional {ι : Type*}
    (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    FiniteDimensional ℂ (finiteHilbertBasisSubspace b s) := by
  unfold finiteHilbertBasisSubspace
  exact FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet s |>.image b)

omit [CompleteSpace H] in
theorem basis_mem {ι : Type*} (b : HilbertBasis ι ℂ H)
    (s : Finset ι) {i : ι} (hi : i ∈ s) : b i ∈ finiteHilbertBasisSubspace b s := by
  apply Submodule.subset_span
  exact ⟨i, hi, rfl⟩

omit [CompleteSpace H] in
theorem basis_mem_orthogonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (s : Finset ι) {i : ι} (hi : i ∉ s) : b i ∈ (finiteHilbertBasisSubspace b s)ᗮ := by
  classical
  refine (Submodule.mem_orthogonal' _ _).2 fun y hy => ?_
  refine Submodule.span_induction
    (p := fun y _ => inner ℂ (b i) y = (0 : ℂ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨j, hj, rfl⟩
    have hortho := orthonormal_iff_ite.mp b.orthonormal i j
    rw [hortho, if_neg]
    rintro rfl
    exact hi hj
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

theorem basis_projection {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (s : Finset ι) (i : ι) :
    (finiteHilbertBasisSubspace b s).starProjection (b i) =
      if i ∈ s then b i else 0 := by
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    exact Submodule.starProjection_eq_self_iff.mpr (basis_mem b s hi)
  · rw [if_neg hi]
    exact Submodule.eq_starProjection_of_mem_orthogonal
      (finiteHilbertBasisSubspace b s).zero_mem
      (by simpa using basis_mem_orthogonal b s hi)

theorem basis_complement_projection {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (s : Finset ι) (i : ι) :
    (1 - (finiteHilbertBasisSubspace b s).starProjection) (b i) =
      if i ∈ s then 0 else b i := by
  rw [sub_apply, one_apply_eq_self,
    basis_projection]
  split_ifs <;> simp

theorem hsNormSq_comp_basisComplement
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : T.IsHilbertSchmidt) (s : Finset ι) :
    hsNormSq (T ∘L (1 - (finiteHilbertBasisSubspace b s).starProjection)) =
      ∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2 := by
  let Q := 1 - (finiteHilbertBasisSubspace b s).starProjection
  have hQ : (T ∘L Q).IsHilbertSchmidt := hT.comp_right Q
  rw [hsNormSq_eq hQ b]
  have htail :
      (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) =
        ∑' i, ({i | i ∉ s} : Set ι).indicator
          (fun j => ‖T (b j)‖ ^ 2) i :=
    tsum_subtype ({i | i ∉ s} : Set ι) (fun j => ‖T (b j)‖ ^ 2)
  rw [htail]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_notMem]
    · rw [ContinuousLinearMap.comp_apply,
        basis_complement_projection b s i, if_pos hi]
      simp
    · simpa using hi
  · rw [Set.indicator_of_mem]
    · rw [ContinuousLinearMap.comp_apply,
        basis_complement_projection b s i, if_neg hi]
    · simpa using hi

theorem exists_common_hilbertSchmidt_tail_lt
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    {T U : H →L[ℂ] H} (hT : T.IsHilbertSchmidt) (hU : U.IsHilbertSchmidt)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι,
      (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) < ε ∧
      (∑' i : {i // i ∉ s}, ‖U (b i)‖ ^ 2) < ε := by
  classical
  let f : ι → ℝ := fun i => ‖T (b i)‖ ^ 2
  let g : ι → ℝ := fun i => ‖U (b i)‖ ^ 2
  have hf : Summable f := hT.summable b
  have hg : Summable g := hU.summable b
  have hsum : Summable (fun i => f i + g i) := hf.add hg
  have htend : Filter.Tendsto
      (fun s : Finset ι => ∑ i ∈ s, (f i + g i))
      Filter.atTop (nhds (∑' i, (f i + g i))) := hsum.hasSum
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp htend ε hε).exists
  have hdecomp := hsum.sum_add_tsum_subtype_compl s
  rw [Real.dist_eq, abs_lt] at hs
  have htailSum : (∑' i : {i // i ∉ s}, (f i + g i)) < ε := by
    linarith [hs.1]
  have hfsub : Summable (fun i : {i // i ∉ s} => f i) :=
    hf.subtype _
  have hgsub : Summable (fun i : {i // i ∉ s} => g i) :=
    hg.subtype _
  rw [hfsub.tsum_add hgsub] at htailSum
  have hfnonneg : 0 ≤ ∑' i : {i // i ∉ s}, f i :=
    tsum_nonneg fun _ => sq_nonneg _
  have hgnonneg : 0 ≤ ∑' i : {i // i ∉ s}, g i :=
    tsum_nonneg fun _ => sq_nonneg _
  have hftail : (∑' i : {i // i ∉ s}, f i) < ε :=
    lt_of_le_of_lt (le_add_of_nonneg_right hgnonneg) htailSum
  have hgtail : (∑' i : {i // i ∉ s}, g i) < ε :=
    lt_of_le_of_lt (le_add_of_nonneg_left hfnonneg) htailSum
  refine ⟨s, ?_, ?_⟩
  · simpa only [f] using hftail
  · simpa only [g] using hgtail

theorem tracePairing_basisComplement
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    (s : Finset ι) :
    separableBuresTracePairing C
        (1 - (finiteHilbertBasisSubspace b s).starProjection) =
      ∑' i : {i // i ∉ s},
        ‖CFC.sqrt (C : H →L[ℂ] H) (b i)‖ ^ 2 := by
  let Q := 1 - (finiteHilbertBasisSubspace b s).starProjection
  let R := CFC.sqrt (C : H →L[ℂ] H)
  have hQpos : Q.IsPositive := by
    dsimp [Q]
    rw [complement_eq_orthogonalProjection]
    exact IsPositive.of_isStarProjection isStarProjection_starProjection
  have hQnonneg : 0 ≤ Q := (nonneg_iff_isPositive _).2 hQpos
  have hQsq : Q ∘L Q = Q := complement_sq _
  have hsqrtQ : CFC.sqrt Q = Q := by
    apply CFC.sqrt_unique
    · exact hQsq
    · exact hQnonneg
  have hR : R.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hRQ : (R ∘L Q).IsHilbertSchmidt := hR.comp_right Q
  have hadj : adjoint (R ∘L Q) = Q ∘L R := by
    simp only [ContinuousLinearMap.adjoint_comp]
    rw [IsSelfAdjoint.of_nonneg hQnonneg |>.adjoint_eq,
      IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (C : H →L[ℂ] H)) |>.adjoint_eq]
  rw [separableBuresTracePairing_eq_hsNormSq C hC Q hQnonneg, hsqrtQ]
  change hsNormSq (Q ∘L R) = _
  rw [← hadj, hRQ.hsNormSq_adjoint]
  exact hsNormSq_comp_basisComplement b hR s

theorem tracePairing_extend_one
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (A : S →L[ℂ] S) :
    separableBuresTracePairing C (finiteSubspaceReporterExtension S A 1) =
      Complex.re (opTrace (finiteSubspaceCompression S (C : H →L[ℂ] H) ∘L A)) +
        separableBuresTracePairing C (1 - S.starProjection) := by
  rw [finiteSubspaceReporterExtension, one_smul, separableBuresTracePairing_add_right,
    trace_block C hC S A]

theorem rangeCovariance_projectedRoot
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (R X : H →L[ℂ] H) (hRstar : adjoint R = R) (hR2 : R ∘L R = X) :
    rangeCovariance (S.orthogonalProjectionOnto ∘L R) =
      finiteSubspaceCompression S X := by
  unfold rangeCovariance finiteSubspaceCompression
  rw [ContinuousLinearMap.adjoint_comp, hRstar,
    S.adjoint_orthogonalProjectionOnto, ← hR2]
  ext x
  rfl

theorem sheetTargetIncidence_projected
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (R T : H →L[ℂ] H) (hRstar : adjoint R = R) :
    sheetTargetIncidence
        (S.orthogonalProjectionOnto ∘L R)
        (S.orthogonalProjectionOnto ∘L T) =
      R ∘L S.starProjection ∘L T := by
  unfold sheetTargetIncidence
  rw [ContinuousLinearMap.adjoint_comp, hRstar,
    S.adjoint_orthogonalProjectionOnto]
  ext x
  rfl

theorem traceNorm_add_neg_le {A B : H →L[ℂ] H}
    (hA : MemSchattenClass 1 A) (hB : MemSchattenClass 1 B) :
    traceNorm H (A + (-B)) ≤ traceNorm H A + traceNorm H B := by
  have h := traceNorm_add_le
    (hA.isCompactOperator one_pos)
    (hB.one_neg.isCompactOperator one_pos)
    hA.one_summable hB.one_neg.one_summable
  have hneg : traceNorm H (-B) = traceNorm H B := by
    rw [show -B = (-1 : ℂ) • B by simp, traceNorm_smul]
    simp
  rwa [hneg] at h

omit [CompleteSpace H] in
theorem projected_comp_decomp
    (P R T : H →L[ℂ] H) :
    R ∘L P ∘L T = R ∘L T + (-(R ∘L (1 - P) ∘L T)) := by
  ext x
  change R (P (T x)) = R (T x) + -R (T x - P (T x))
  rw [map_sub]
  abel

theorem traceNorm_projected_comp_le
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (R T : H →L[ℂ] H) (hR : R.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) :
    traceNorm H (R ∘L S.starProjection ∘L T) ≤
      traceNorm H (R ∘L T) +
        hsNorm (R ∘L (1 - S.starProjection)) * hsNorm T := by
  have hRQ : (R ∘L (1 - S.starProjection)).IsHilbertSchmidt :=
    hR.comp_right _
  have hRTmem : MemSchattenClass 1 (R ∘L T) :=
    memSchattenClass_one_comp hR hT
  have hEmem : MemSchattenClass 1
      ((R ∘L (1 - S.starProjection)) ∘L T) :=
    memSchattenClass_one_comp hRQ hT
  rw [projected_comp_decomp]
  have htri := traceNorm_add_neg_le hRTmem hEmem
  have hbound : traceNorm H ((R ∘L (1 - S.starProjection)) ∘L T) ≤
      hsNorm (R ∘L (1 - S.starProjection)) * hsNorm T := by
    unfold traceNorm
    exact tsum_approxNumber_comp_le hRQ hT
  exact htri.trans
    (add_le_add (le_refl (traceNorm H (R ∘L T))) hbound)

theorem compressedFidelity_le
    (C M : SchattenOneOperator H)
    (hC : (C : H →L[ℂ] H).IsPositive)
    (hM : (M : H →L[ℂ] H).IsPositive)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    operatorBuresRootFidelity
        (finiteSubspaceCompression S (C : H →L[ℂ] H))
        (finiteSubspaceCompression S (M : H →L[ℂ] H)) ≤
      operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) +
        hsNorm (CFC.sqrt (C : H →L[ℂ] H) ∘L (1 - S.starProjection)) *
          hsNorm (CFC.sqrt (M : H →L[ℂ] H)) := by
  let RC := CFC.sqrt (C : H →L[ℂ] H)
  let RM := CFC.sqrt (M : H →L[ℂ] H)
  have hRC : RC.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hRM : RM.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt M hM
  have hRCstar : adjoint RC = RC :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (C : H →L[ℂ] H)) |>.adjoint_eq
  have hRMstar : adjoint RM = RM :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (M : H →L[ℂ] H)) |>.adjoint_eq
  have hRC2 : RC ∘L RC = (C : H →L[ℂ] H) :=
    CFC.sqrt_mul_sqrt_self _ ((nonneg_iff_isPositive _).2 hC)
  have hRM2 : RM ∘L RM = (M : H →L[ℂ] H) :=
    CFC.sqrt_mul_sqrt_self _ ((nonneg_iff_isPositive _).2 hM)
  let U : H →L[ℂ] S := S.orthogonalProjectionOnto ∘L RC
  let V : H →L[ℂ] S := S.orthogonalProjectionOnto ∘L RM
  have hfid : operatorBuresRootFidelity
      (finiteSubspaceCompression S (C : H →L[ℂ] H))
      (finiteSubspaceCompression S (M : H →L[ℂ] H)) =
        traceNorm H (RC ∘L S.starProjection ∘L RM) := by
    rw [← rangeCovariance_projectedRoot S RC _ hRCstar hRC2,
      ← rangeCovariance_projectedRoot S RM _ hRMstar hRM2,
      ← rectTraceNorm_sheetTargetIncidence_eq_operatorBuresRootFidelity U V,
      show sheetTargetIncidence U V = RC ∘L S.starProjection ∘L RM from
        sheetTargetIncidence_projected S RC RM hRCstar,
      rectTraceNorm_eq_traceNorm]
  rw [hfid]
  exact traceNorm_projected_comp_le S RC RM hRC hRM

theorem exists_separableReporterHalfSum_lt
    (C M : SchattenOneOperator H)
    (hC : (C : H →L[ℂ] H).IsPositive)
    (hM : (M : H →L[ℂ] H).IsPositive)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
      separableBuresReporterHalfSum C M A <
        operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) + ε := by
  classical
  let b := hsBasis ℂ H
  let RC := CFC.sqrt (C : H →L[ℂ] H)
  let RM := CFC.sqrt (M : H →L[ℂ] H)
  let B := hsNorm RM
  let α := min 1 (ε / (8 * (B + 1)))
  have hRC : RC.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hRM : RM.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt M hM
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact ContinuousLinearMap.hsNorm_nonneg _
  have hden : 0 < 8 * (B + 1) := by positivity
  have hαpos : 0 < α := lt_min one_pos (div_pos hε hden)
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαfrac : α ≤ ε / (8 * (B + 1)) := min_le_right _ _
  have hαbudget : α * (B + 1) ≤ ε / 8 := by
    calc
      α * (B + 1) ≤ (ε / (8 * (B + 1))) * (B + 1) :=
        mul_le_mul_of_nonneg_right hαfrac (by linarith)
      _ = ε / 8 := by field_simp
  have hαB : α * B ≤ ε / 8 := by
    calc
      α * B ≤ α * (B + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hαpos.le
      _ ≤ ε / 8 := hαbudget
  have hαsq : α ^ 2 ≤ ε / 8 := by
    calc
      α ^ 2 ≤ α := by nlinarith
      _ ≤ α * (B + 1) := by
        nlinarith [mul_nonneg hαpos.le hB0]
      _ ≤ ε / 8 := hαbudget
  obtain ⟨s, hsC, hsM⟩ := exists_common_hilbertSchmidt_tail_lt
    b hRC hRM (sq_pos_of_pos hαpos)
  let S := finiteHilbertBasisSubspace b s
  have htailC : separableBuresTracePairing C (1 - S.starProjection) < α ^ 2 := by
    rw [tracePairing_basisComplement b C hC s]
    exact hsC
  have htailM : separableBuresTracePairing M (1 - S.starProjection) < α ^ 2 := by
    rw [tracePairing_basisComplement b M hM s]
    exact hsM
  have hRCQ : hsNorm (RC ∘L (1 - S.starProjection)) < α := by
    rw [hsNorm, hsNormSq_comp_basisComplement b hRC s]
    exact (Real.sqrt_lt' hαpos).2 hsC
  have hcompC : 0 ≤ finiteSubspaceCompression S (C : H →L[ℂ] H) :=
    (nonneg_iff_isPositive _).2 (finiteSubspaceCompression_isPositive S _ hC)
  have hcompM : 0 ≤ finiteSubspaceCompression S (M : H →L[ℂ] H) :=
    (nonneg_iff_isPositive _).2 (finiteSubspaceCompression_isPositive S _ hM)
  obtain ⟨AS, hAS, hASobj⟩ := exists_finiteOperatorReporterHalfSum_lt
    (finiteSubspaceCompression S (C : H →L[ℂ] H))
    (finiteSubspaceCompression S (M : H →L[ℂ] H))
    hcompC hcompM (show 0 < ε / 4 by positivity)
  let A := finiteSubspaceReporterExtension S AS 1
  have hA : IsStrictlyPositive A := by
    exact finiteSubspaceReporterExtension_isStrictlyPositive S AS hAS 1 one_pos
  have hinv : Ring.inverse A = finiteSubspaceReporterExtension S (Ring.inverse AS) 1 := by
    simpa only [A, inv_one] using
      finiteSubspaceReporterExtension_ringInverse S AS hAS.isUnit 1 one_ne_zero
  have hobj : separableBuresReporterHalfSum C M A =
      finiteOperatorReporterHalfSum
          (finiteSubspaceCompression S (C : H →L[ℂ] H))
          (finiteSubspaceCompression S (M : H →L[ℂ] H)) AS +
        (separableBuresTracePairing C (1 - S.starProjection) +
          separableBuresTracePairing M (1 - S.starProjection)) / 2 := by
    unfold separableBuresReporterHalfSum finiteOperatorReporterHalfSum
    rw [show A = finiteSubspaceReporterExtension S AS 1 by rfl,
      tracePairing_extend_one C hC S AS, hinv,
      tracePairing_extend_one M hM S (Ring.inverse AS)]
    ring
  have hfid := compressedFidelity_le C M hC hM S
  have herror : hsNorm (RC ∘L (1 - S.starProjection)) * hsNorm RM ≤ ε / 8 :=
    calc
      hsNorm (RC ∘L (1 - S.starProjection)) * hsNorm RM ≤ α * B :=
        mul_le_mul_of_nonneg_right hRCQ.le
          (ContinuousLinearMap.hsNorm_nonneg _)
      _ ≤ ε / 8 := hαB
  refine ⟨A, hA, ?_⟩
  rw [hobj]
  linarith

def separableReporterValueSet
    (C M : SchattenOneOperator H) : Set ℝ :=
  {q | ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
    q = separableBuresReporterHalfSum C M A}

theorem separableReporterValueSet_nonempty
    (C M : SchattenOneOperator H) :
    (separableReporterValueSet C M).Nonempty := by
  refine ⟨separableBuresReporterHalfSum C M 1, 1, isStrictlyPositive_one, rfl⟩

theorem separableReporterValueSet_bddBelow
    (C M : SchattenOneOperator H)
    (hC : (C : H →L[ℂ] H).IsPositive)
    (hM : (M : H →L[ℂ] H).IsPositive) :
    BddBelow (separableReporterValueSet C M) := by
  refine ⟨operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H), ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact operatorBuresRootFidelity_le_separableReporterHalfSum C M hC hM A hA

theorem separableReporter_sInf_eq_operatorBuresRootFidelity
    (C M : SchattenOneOperator H)
    (hC : (C : H →L[ℂ] H).IsPositive)
    (hM : (M : H →L[ℂ] H).IsPositive) :
    sInf (separableReporterValueSet C M) =
      operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : operatorBuresRootFidelity (C : H →L[ℂ] H)
        (M : H →L[ℂ] H) < sInf (separableReporterValueSet C M) :=
      lt_of_not_ge hnot
    let ε := (sInf (separableReporterValueSet C M) -
      operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H)) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨A, hA, hobj⟩ := exists_separableReporterHalfSum_lt C M hC hM hε
    have hmem : separableBuresReporterHalfSum C M A ∈
        separableReporterValueSet C M := ⟨A, hA, rfl⟩
    have hle := csInf_le (separableReporterValueSet_bddBelow C M hC hM) hmem
    dsimp [ε] at hobj
    linarith
  · apply le_csInf (separableReporterValueSet_nonempty C M)
    rintro q ⟨A, hA, rfl⟩
    exact operatorBuresRootFidelity_le_separableReporterHalfSum C M hC hM A hA

theorem separableBuresTracePairing_mono_right
    (M : SchattenOneOperator H) (hM : (M : H →L[ℂ] H).IsPositive)
    {A B : H →L[ℂ] H} (hAB : A ≤ B) :
    separableBuresTracePairing M A ≤ separableBuresTracePairing M B := by
  have hdiff : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hnonneg := separableBuresTracePairing_nonneg M hM (B - A) hdiff
  have hB : B = A + (B - A) := by abel
  rw [hB, separableBuresTracePairing_add_right]
  linarith

theorem continuousOn_separableBuresReporterHalfSum_right
    (C M : SchattenOneOperator H) :
    ContinuousOn (separableBuresReporterHalfSum C M)
      {A : H →L[ℂ] H | IsStrictlyPositive A} := by
  intro A hA
  have hinv : ContinuousAt Ring.inverse A := by
    have h := NormedRing.inverse_continuousAt hA.isUnit.unit
    rw [hA.isUnit.unit_spec] at h
    exact h
  exact (((continuous_separableBuresTracePairing_right C).continuousAt.add
    ((continuous_separableBuresTracePairing_right M).continuousAt.comp hinv)).div_const 2).continuousWithinAt

theorem affine_separableBuresReporterHalfSum_left
    (C : SchattenOneOperator H) (A : H →L[ℂ] H) :
    ∀ M N : SchattenOneOperator H, ∀ a b : ℝ, a + b = 1 →
      separableBuresReporterHalfSum C (a • M + b • N) A =
        a * separableBuresReporterHalfSum C M A +
          b * separableBuresReporterHalfSum C N A := by
  intro M N a b hab
  unfold separableBuresReporterHalfSum
  rw [separableBuresTracePairing_add_left,
    separableBuresTracePairing_real_smul_left,
    separableBuresTracePairing_real_smul_left]
  have hsource : separableBuresTracePairing C A =
      a * separableBuresTracePairing C A + b * separableBuresTracePairing C A := by
    calc
      separableBuresTracePairing C A =
          (a + b) * separableBuresTracePairing C A := by rw [hab, one_mul]
      _ = _ := by ring
  linear_combination hsource / 2

theorem concaveOn_separableBuresReporterHalfSum_left
    {K : Set (SchattenOneOperator H)} (hK : Convex ℝ K)
    (C : SchattenOneOperator H) (A : H →L[ℂ] H) :
    ConcaveOn ℝ K (fun M => separableBuresReporterHalfSum C M A) := by
  refine ⟨hK, ?_⟩
  intro M hM N hN a b ha hb hab
  simpa [smul_eq_mul] using
    (affine_separableBuresReporterHalfSum_left C A M N a b hab).ge

theorem convexOn_separableBuresReporterHalfSum_right
    (C M : SchattenOneOperator H)
    (hM : (M : H →L[ℂ] H).IsPositive) :
    ConvexOn ℝ {A : H →L[ℂ] H | IsStrictlyPositive A}
      (separableBuresReporterHalfSum C M) := by
  refine ⟨convex_strictlyPositiveReporters, ?_⟩
  intro A hA B hB a b ha hb hab
  have hinv := CStarAlgebra.convexOn_ringInverse.2 hA hB ha hb hab
  have hmono := separableBuresTracePairing_mono_right M hM hinv
  rw [separableBuresTracePairing_add_right,
    separableBuresTracePairing_real_smul_right,
    separableBuresTracePairing_real_smul_right] at hmono
  unfold separableBuresReporterHalfSum
  rw [separableBuresTracePairing_add_right,
    separableBuresTracePairing_real_smul_right,
    separableBuresTracePairing_real_smul_right]
  have hsource := separableBuresTracePairing_add_right C (a • A) (b • B)
  rw [separableBuresTracePairing_real_smul_right,
    separableBuresTracePairing_real_smul_right] at hsource
  simp only [smul_eq_mul]
  linarith

theorem continuous_separableBuresReporterHalfSum_left
    (C : SchattenOneOperator H) (A : H →L[ℂ] H) :
    Continuous (fun M : SchattenOneOperator H =>
      separableBuresReporterHalfSum C M A) := by
  unfold separableBuresReporterHalfSum
  exact (continuous_const.add
    (continuous_separableBuresTracePairing_left (Ring.inverse A))).div_const 2



end RHTower
