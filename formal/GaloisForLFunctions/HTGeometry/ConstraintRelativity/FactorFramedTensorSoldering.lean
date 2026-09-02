import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorJacobian

/-!
# Exact factor-framed tensor soldering

This leaf constructs the literal factor-incidence cotangent source, its coefficient-weighted
soldering map into the trace-dual quotient, and the induced Smith-bar cokernel.  It proves exact
range/kernel identification, equality of kernel and cokernel lengths, and the nonzero homogeneous
defect in every factor count at least two.
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators
open IsLocalRing

theorem factorSourceExponent_add_two_mul
    {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d)
    (hi : i ∈ missingFace T) :
    factorSourceExponent r T i + 2 * r i = factorTraceTargetDepth r T := by
  rw [factorSourceExponent, factorTraceTargetDepth]
  have hsum := Finset.sum_erase_add (s := missingFace T) r hi
  omega

theorem factorTraceTargetIdeal_le_faceBarIdeal
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    factorTraceTargetIdeal a r T ≤ faceBarIdeal a r T := by
  rw [factorTraceTargetIdeal, faceBarIdeal, Ideal.span_le]
  rintro x rfl
  apply Ideal.mem_span_singleton.mpr
  apply pow_dvd_pow
  exact (weightedFaceDepth_le_factorSourceExponent r T
    (Classical.choice (inferInstance : Nonempty (Fin d)))).trans (by
      simp only [factorSourceExponent, factorTraceTargetDepth]
      exact Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset
        (f := r) (Finset.erase_subset _ _)))

def factorMulLinear {R : Type*} [CommRing R] (c : R) : R →ₗ[R] R where
  toFun x := c * x
  map_add' x y := mul_add c x y
  map_smul' x y := by
    change c * (x * y) = x * (c * y)
    ac_rfl

def factorGradientBarMap
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d)
    (hi : i ∈ missingFace T) :
    R ⧸ factorSourceBarIdeal a r i →ₗ[R]
      R ⧸ factorTraceTargetIdeal a r T :=
  Submodule.mapQ (factorSourceBarIdeal a r i) (factorTraceTargetIdeal a r T)
    (factorMulLinear (a ^ factorSourceExponent r T i)) (by
      intro x hx
      rw [factorSourceBarIdeal, Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      change a ^ factorSourceExponent r T i * (a ^ (2 * r i) * c) ∈
        factorTraceTargetIdeal a r T
      rw [factorTraceTargetIdeal, Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← mul_assoc, ← pow_add, factorSourceExponent_add_two_mul r T i hi])

@[simp] theorem factorGradientBarMap_mk
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d)
    (hi : i ∈ missingFace T) (x : R) :
    factorGradientBarMap a r T i hi
        (Submodule.Quotient.mk x : R ⧸ factorSourceBarIdeal a r i) =
      (Submodule.Quotient.mk (a ^ factorSourceExponent r T i * x) :
        R ⧸ factorTraceTargetIdeal a r T) := rfl

def factorSourceFaceForTarget {d : ℕ} (T : TensorFace d) (i : Fin d) :
    FactorSourceFace d i :=
  ⟨(Finset.univ.erase i) \ T, by simp⟩

def factorTargetFaceForSource {d : ℕ} (i : Fin d) (S : FactorSourceFace d i) :
    TensorFace d :=
  (Finset.univ.erase i) \ S.1

theorem factorTargetFaceForSource_missing
    {d : ℕ} (i : Fin d) (S : FactorSourceFace d i) :
    i ∈ missingFace (factorTargetFaceForSource i S) := by
  simp [missingFace, factorTargetFaceForSource]

theorem factorTargetFaceForSource_sourceFaceForTarget
    {d : ℕ} (T : TensorFace d) (i : Fin d) (hi : i ∈ missingFace T) :
    factorTargetFaceForSource i (factorSourceFaceForTarget T i) = T := by
  classical
  ext j
  simp [factorTargetFaceForSource, factorSourceFaceForTarget, missingFace] at hi ⊢
  aesop

theorem factorSourceFaceForTarget_targetFaceForSource
    {d : ℕ} (i : Fin d) (S : FactorSourceFace d i) :
    factorSourceFaceForTarget (factorTargetFaceForSource i S) i = S := by
  classical
  apply Subtype.ext
  ext j
  simp [factorSourceFaceForTarget, factorTargetFaceForSource] at S ⊢
  aesop

abbrev FactorMissingIndex {d : ℕ} (T : TensorFace d) :=
  {i : Fin d // i ∈ missingFace T}

abbrev FactorIncidenceSourceModel
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  ∀ T : TensorFace d, (i : FactorMissingIndex T) →
    R ⧸ factorSourceBarIdeal a r i.1

def factorCotangentCoordinate
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) (S : FactorSourceFace d i) :
    FactorCotangentModel a r →ₗ[R] R ⧸ factorSourceBarIdeal a r i where
  toFun x := x i S
  map_add' x y := rfl
  map_smul' c x := rfl

def factorFramedSolderingComponent
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    FactorCotangentModel a r →ₗ[R] R ⧸ factorTraceTargetIdeal a r T :=
  ∑ i : Fin d, if hi : i ∈ missingFace T then
    (factorGradientBarMap a r T i hi).comp
      (factorCotangentCoordinate a r i (factorSourceFaceForTarget T i))
  else 0

def factorFramedSoldering
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorCotangentModel a r →ₗ[R] FactorTraceQuotientModel a r :=
  LinearMap.pi (factorFramedSolderingComponent a r)

theorem factorFramedSoldering_apply
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (x : FactorCotangentModel a r)
    (T : TensorFace d) :
    factorFramedSoldering a r x T =
      ∑ i : Fin d, if hi : i ∈ missingFace T then
        factorGradientBarMap a r T i hi (x i (factorSourceFaceForTarget T i))
      else 0 := by
  rw [factorFramedSoldering, LinearMap.pi_apply,
    factorFramedSolderingComponent, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ missingFace T <;>
    simp [hi, factorCotangentCoordinate]

def factorIncidenceCoordinate
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) (i : FactorMissingIndex T) :
    FactorIncidenceSourceModel a r →ₗ[R] R ⧸ factorSourceBarIdeal a r i.1 where
  toFun x := x T i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def factorIncidenceSolderingComponent
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    FactorIncidenceSourceModel a r →ₗ[R] R ⧸ factorTraceTargetIdeal a r T :=
  ∑ i : FactorMissingIndex T,
    (factorGradientBarMap a r T i.1 i.2).comp (factorIncidenceCoordinate a r T i)

def factorIncidenceSoldering
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorIncidenceSourceModel a r →ₗ[R] FactorTraceQuotientModel a r :=
  LinearMap.pi (factorIncidenceSolderingComponent a r)

def factorTraceToFaceBarComponent
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    (R ⧸ factorTraceTargetIdeal a r T) →ₗ[R]
      R ⧸ faceBarIdeal a r T :=
  Submodule.mapQ (factorTraceTargetIdeal a r T) (faceBarIdeal a r T)
    LinearMap.id (by simpa using factorTraceTargetIdeal_le_faceBarIdeal a r T)

def factorTraceToFaceBars
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorTraceQuotientModel a r →ₗ[R]
      (∀ T : TensorFace d, R ⧸ faceBarIdeal a r T) :=
  LinearMap.pi fun T =>
    (factorTraceToFaceBarComponent a r T).comp (LinearMap.proj T)

theorem factorTraceToFaceBarComponent_surjective
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    Function.Surjective (factorTraceToFaceBarComponent a r T) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

theorem factorTraceToFaceBars_surjective
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    Function.Surjective (factorTraceToFaceBars a r) := by
  intro y
  choose x hx using fun T => factorTraceToFaceBarComponent_surjective a r T (y T)
  exact ⟨x, funext hx⟩

theorem factorTraceToFaceBarComponent_comp_gradientBarMap
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d)
    (hi : i ∈ missingFace T) :
    (factorTraceToFaceBarComponent a r T).comp
        (factorGradientBarMap a r T i hi) = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ z =>
    change (Submodule.Quotient.mk
      (a ^ factorSourceExponent r T i * z) : R ⧸ faceBarIdeal a r T) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [smul_eq_mul, mul_comm] using
      (faceBarIdeal a r T).smul_mem z (factorSourcePower_mem_faceBarIdeal a r T i)

theorem factorIncidenceSolderingComponent_range_eq_ker
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    LinearMap.range (factorIncidenceSolderingComponent a r T) =
      LinearMap.ker (factorTraceToFaceBarComponent a r T) := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    rw [factorIncidenceSolderingComponent, LinearMap.sum_apply, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change ((factorTraceToFaceBarComponent a r T).comp
      (factorGradientBarMap a r T i.1 i.2)) (x T i) = 0
    rw [factorTraceToFaceBarComponent_comp_gradientBarMap]
    rfl
  · intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hz : z ∈ faceBarIdeal a r T := by
      rw [LinearMap.mem_ker] at hy
      change (Submodule.Quotient.mk z : R ⧸ faceBarIdeal a r T) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      exact hy
    by_cases hM : (missingFace T).Nonempty
    · obtain ⟨i, hi, hdepth⟩ :=
        exists_mem_factorSourceExponent_eq_weightedFaceDepth r T hM
      rw [faceBarIdeal, Ideal.mem_span_singleton] at hz
      obtain ⟨c, hc⟩ := hz
      let ii : FactorMissingIndex T := ⟨i, hi⟩
      let x : FactorIncidenceSourceModel a r := fun U j =>
        if hU : U = T then
          if hj : j.1 = i then
            hj ▸ (Submodule.Quotient.mk c : R ⧸ factorSourceBarIdeal a r i)
          else 0
        else 0
      refine ⟨x, ?_⟩
      rw [factorIncidenceSolderingComponent, LinearMap.sum_apply]
      rw [Finset.sum_eq_single ii]
      · have hxii : x T ii =
            (Submodule.Quotient.mk c : R ⧸ factorSourceBarIdeal a r i) := by
          simp [x, ii]
        change factorGradientBarMap a r T ii.1 ii.2 (x T ii) = _
        rw [hxii]
        dsimp [ii]
        change (Submodule.Quotient.mk
          (a ^ factorSourceExponent r T i * c) :
            R ⧸ factorTraceTargetIdeal a r T) = Submodule.Quotient.mk z
        rw [hdepth, hc]
      · intro j _ hji
        have hj : j.1 ≠ i := by
          intro hj
          apply hji
          exact Subtype.ext hj
        simp [x, factorIncidenceCoordinate, hj]
      · intro hii
        exact (hii (Finset.mem_univ ii)).elim
    · have hEmpty : missingFace T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      rw [Submodule.Quotient.mk_eq_zero, factorTraceTargetIdeal,
        factorTraceTargetDepth, hEmpty]
      simp

theorem factorIncidenceSoldering_range_eq_traceToFaceBars_ker
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    LinearMap.range (factorIncidenceSoldering a r) =
      LinearMap.ker (factorTraceToFaceBars a r) := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    funext T
    exact LinearMap.mem_ker.mp
      ((factorIncidenceSolderingComponent_range_eq_ker a r T).le
        ⟨x, rfl⟩)
  · intro y hy
    have hyT : ∀ T, y T ∈ LinearMap.range
        (factorIncidenceSolderingComponent a r T) := by
      intro T
      rw [factorIncidenceSolderingComponent_range_eq_ker]
      exact LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp hy) T)
    choose x hx using hyT
    let z : FactorIncidenceSourceModel a r := fun T i => x T T i
    refine ⟨z, ?_⟩
    funext T
    simpa [factorIncidenceSoldering, factorIncidenceSolderingComponent,
      factorIncidenceCoordinate, z, LinearMap.pi_apply, LinearMap.sum_apply] using hx T

abbrev FactorFramedSolderingCokernel
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  FactorTraceQuotientModel a r ⧸ LinearMap.range (factorIncidenceSoldering a r)

def factorFramedSolderingCokernelMap
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorFramedSolderingCokernel a r →ₗ[R]
      (∀ T : TensorFace d, R ⧸ faceBarIdeal a r T) :=
  (LinearMap.range (factorIncidenceSoldering a r)).liftQ
    (factorTraceToFaceBars a r) (by
      rw [factorIncidenceSoldering_range_eq_traceToFaceBars_ker])

theorem factorFramedSolderingCokernelMap_bijective
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    Function.Bijective (factorFramedSolderingCokernelMap a r) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        apply (Submodule.Quotient.eq
          (LinearMap.range (factorIncidenceSoldering a r))).2
        rw [factorIncidenceSoldering_range_eq_traceToFaceBars_ker]
        apply LinearMap.mem_ker.mpr
        change factorTraceToFaceBars a r x = factorTraceToFaceBars a r y at hxy
        rw [map_sub, hxy, sub_self]
  · intro y
    obtain ⟨x, hx⟩ := factorTraceToFaceBars_surjective a r y
    exact ⟨Submodule.Quotient.mk x, hx⟩

noncomputable def factorFramedSolderingCokernelEquivFaceBars
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorFramedSolderingCokernel a r ≃ₗ[R]
      (∀ T : TensorFace d, R ⧸ faceBarIdeal a r T) :=
  LinearEquiv.ofBijective (factorFramedSolderingCokernelMap a r)
    (factorFramedSolderingCokernelMap_bijective a r)

noncomputable def factorFramedSolderingCokernelEquivGradientCokernel
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorFramedSolderingCokernel a r ≃ₗ[R] FactorGradientCokernel a r :=
  (factorFramedSolderingCokernelEquivFaceBars a r).trans
    (factorGradientCokernelEquivFaceBars a r).symm

theorem sum_factorMissingIndex_sourceDepth
    {d : ℕ} (r : Fin d → ℕ) :
    (∑ T : TensorFace d, ∑ i : FactorMissingIndex T, 2 * r i.1) =
      ∑ T : TensorFace d, factorTraceTargetDepth r T := by
  apply Finset.sum_congr rfl
  intro T _
  rw [factorTraceTargetDepth, Finset.mul_sum]
  simpa only [FactorMissingIndex, Finset.univ_eq_attach] using
    Finset.sum_attach (missingFace T) (fun i => 2 * r i)

theorem factorIncidenceSourceModel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) (r : Fin d → ℕ) :
    Module.length R (FactorIncidenceSourceModel a r) =
      ((2 ^ d * ∑ i, r i : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype]
  simp_rw [Module.length_pi_of_fintype]
  simp_rw [factorSourceBar_length a ha r]
  norm_cast
  rw [sum_factorMissingIndex_sourceDepth, sum_factorTraceTargetDepth]

theorem factorFramedSolderingCokernel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) (r : Fin d → ℕ) :
    Module.length R (FactorFramedSolderingCokernel a r) =
      ((∑ T : TensorFace d, weightedFaceDepth r T : ℕ) : ℕ∞) := by
  rw [(factorFramedSolderingCokernelEquivGradientCokernel a r).length_eq,
    factorGradientCokernel_length_eq_sum_weightedFaceDepth a ha]

abbrev FactorFramedSolderingKernel
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  LinearMap.ker (factorIncidenceSoldering a r)

theorem factorIncidenceSoldering_source_length_eq_kernel_add_range
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Module.length R (FactorIncidenceSourceModel a r) =
      Module.length R (FactorFramedSolderingKernel a r) +
        Module.length R (LinearMap.range (factorIncidenceSoldering a r)) := by
  let f := factorIncidenceSoldering a r
  apply Module.length_eq_add_of_exact f.ker.subtype f.rangeRestrict
  · exact Submodule.subtype_injective _
  · rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  · rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      Submodule.range_subtype]

theorem factorTraceQuotient_length_eq_range_add_cokernel
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Module.length R (FactorTraceQuotientModel a r) =
      Module.length R (LinearMap.range (factorIncidenceSoldering a r)) +
        Module.length R (FactorFramedSolderingCokernel a r) := by
  let f := factorIncidenceSoldering a r
  apply Module.length_eq_add_of_exact f.range.subtype f.range.mkQ
  · exact Submodule.subtype_injective _
  · exact Submodule.Quotient.mk_surjective _
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]

/-- Card `(10)`: self-duality of the framed square presentation gives equal kernel and cokernel
lengths, without an injectivity or flatness assumption. -/
theorem factorFramedSolderingKernel_length_eq_cokernel
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) (r : Fin d → ℕ) :
    Module.length R (FactorFramedSolderingKernel a r) =
      Module.length R (FactorFramedSolderingCokernel a r) := by
  have hsource := factorIncidenceSoldering_source_length_eq_kernel_add_range a r
  have htarget := factorTraceQuotient_length_eq_range_add_cokernel a r
  rw [factorIncidenceSourceModel_length a ha r] at hsource
  rw [factorTraceQuotientModel_length a ha r] at htarget
  have hrange : Module.length R (LinearMap.range (factorIncidenceSoldering a r)) ≠ ⊤ := by
    intro htop
    have hbad : (((2 ^ d * ∑ i, r i : ℕ) : ℕ∞)) = ⊤ := by
      simpa [htop] using hsource
    exact ENat.coe_ne_top _ hbad
  apply WithTop.add_left_cancel hrange
  calc
    Module.length R (LinearMap.range (factorIncidenceSoldering a r)) +
        Module.length R (FactorFramedSolderingKernel a r) =
        ((2 ^ d * ∑ i, r i : ℕ) : ℕ∞) := by
      rw [add_comm]
      exact hsource.symm
    _ = Module.length R (LinearMap.range (factorIncidenceSoldering a r)) +
        Module.length R (FactorFramedSolderingCokernel a r) := htarget

theorem factorFramedSolderingKernel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) (r : Fin d → ℕ) :
    Module.length R (FactorFramedSolderingKernel a r) =
      ((∑ T : TensorFace d, weightedFaceDepth r T : ℕ) : ℕ∞) := by
  rw [factorFramedSolderingKernel_length_eq_cokernel a ha r,
    factorFramedSolderingCokernel_length a ha r]

/-- Card `(10)`: in every factor count `d ≥ 2`, the homogeneous framed soldering map has a
nonzero kernel. -/
theorem homogeneous_factorFramedSolderingKernel_nontrivial
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (hd : 2 ≤ d) (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) :
    Nontrivial (FactorFramedSolderingKernel a (fun _ : Fin d => 1)) := by
  apply (Module.length_pos_iff (R := R)).mp
  letI : NeZero d := ⟨by omega⟩
  rw [factorFramedSolderingKernel_length a ha,
    sum_weightedFaceDepth_const_one hd]
  norm_cast
  omega

/-- Card `(10)`: in every factor count `d ≥ 2`, the homogeneous framed soldering map has a
nonzero cokernel. -/
theorem homogeneous_factorFramedSolderingCokernel_nontrivial
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (hd : 2 ≤ d) (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) :
    Nontrivial (FactorFramedSolderingCokernel a (fun _ : Fin d => 1)) := by
  apply (Module.length_pos_iff (R := R)).mp
  letI : NeZero d := ⟨by omega⟩
  rw [factorFramedSolderingCokernel_length a ha,
    sum_weightedFaceDepth_const_one hd]
  norm_cast
  omega

end HTGeometry.ConstraintRelativity
