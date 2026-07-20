import GaloisForLFunctions.HTGeometry.DifferentialAutomorphismDefectEscape
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.WickContractedMatroidPersistence

/-!
# Differential semilinear automorphisms

A differential automorphism may preserve a coefficient field setwise without fixing it
pointwise.  This module proves that normalization is enough to transport algebraic and
differential independence, generated differential fields and their closures, differential
algebraicity, and hypertranscendence, including relative DA/HT over arbitrary generated fields.
It then supplies additive-defect and multiplicative-quotient escape laws over such normalized
bases.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- A differential automorphism of an ambient field together with the induced differential
automorphism of a normalized coefficient field. -/
structure DifferentialSemilinearEquiv (F E : Type*)
    [Field F] [Field E] [Algebra F E] [Differential F] [Differential E] where
  baseEquiv : F ≃+* F
  ambientEquiv : E ≃+* E
  map_algebraMap' : ∀ c,
    ambientEquiv (algebraMap F E c) = algebraMap F E (baseEquiv c)
  map_base_deriv' : ∀ c,
    baseEquiv (Differential.deriv c) = Differential.deriv (baseEquiv c)
  map_ambient_deriv' : ∀ x,
    ambientEquiv (Differential.deriv x) = Differential.deriv (ambientEquiv x)

/-- Every coefficient-fixing differential automorphism is a differential semilinear
automorphism with trivial action on the base. -/
def DifferentialAlgEquiv.toDifferentialSemilinearEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialAlgEquiv F E) : DifferentialSemilinearEquiv F E where
  baseEquiv := RingEquiv.refl F
  ambientEquiv := sigma.toAlgEquiv.toRingEquiv
  map_algebraMap' c := sigma.toAlgEquiv.commutes c
  map_base_deriv' _ := rfl
  map_ambient_deriv' x := sigma.map_deriv' x

namespace DifferentialSemilinearEquiv

/-- A differential semilinear automorphism commutes with every ambient jet. -/
theorem map_differentialJet
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) (n : ℕ) (x : E) :
    sigma.ambientEquiv (differentialJet n x) =
      differentialJet n (sigma.ambientEquiv x) := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [differentialJet_succ, sigma.map_ambient_deriv', ih,
        differentialJet_succ]

/-- The image of an intermediate field under a normalized-base automorphism. Unlike
`IntermediateField.map`, this permits a nontrivial automorphism of the coefficient field while
retaining the same embedded base. -/
def mapIntermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E)
    (L : IntermediateField F E) : IntermediateField F E :=
  (L.toSubfield.map sigma.ambientEquiv.toRingHom).toIntermediateField (by
    intro c
    refine ⟨algebraMap F E (sigma.baseEquiv.symm c), L.algebraMap_mem _, ?_⟩
    change sigma.ambientEquiv (algebraMap F E (sigma.baseEquiv.symm c)) = _
    rw [sigma.map_algebraMap', sigma.baseEquiv.apply_symm_apply])

/-- Membership in the semilinear image is detected before applying the ambient automorphism. -/
@[simp]
theorem mem_mapIntermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E)
    (L : IntermediateField F E) (x : E) :
    sigma.ambientEquiv x ∈ sigma.mapIntermediateField L ↔ x ∈ L := by
  change sigma.ambientEquiv.toRingHom x ∈
      L.toSubfield.map sigma.ambientEquiv.toRingHom ↔ x ∈ L
  exact Subfield.map_mem_map sigma.ambientEquiv.toRingHom

/-- The inverse semilinear automorphism normalizes the same coefficient field. -/
def symm
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) :
    DifferentialSemilinearEquiv F E where
  baseEquiv := sigma.baseEquiv.symm
  ambientEquiv := sigma.ambientEquiv.symm
  map_algebraMap' c := by
    apply sigma.ambientEquiv.injective
    rw [sigma.ambientEquiv.apply_symm_apply, sigma.map_algebraMap',
      sigma.baseEquiv.apply_symm_apply]
  map_base_deriv' c := by
    apply sigma.baseEquiv.injective
    rw [sigma.baseEquiv.apply_symm_apply, sigma.map_base_deriv',
      sigma.baseEquiv.apply_symm_apply]
  map_ambient_deriv' x := by
    apply sigma.ambientEquiv.injective
    rw [sigma.ambientEquiv.apply_symm_apply, sigma.map_ambient_deriv',
      sigma.ambientEquiv.apply_symm_apply]

/-- Mapping an intermediate field and then mapping back by the inverse normalized-base
automorphism recovers the field exactly. -/
@[simp]
theorem mapIntermediateField_symm_mapIntermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E)
    (L : IntermediateField F E) :
    sigma.symm.mapIntermediateField (sigma.mapIntermediateField L) = L := by
  ext x
  simpa [DifferentialSemilinearEquiv.symm] using
    ((sigma.symm.mem_mapIntermediateField (sigma.mapIntermediateField L)
      (sigma.ambientEquiv x)).trans (sigma.mem_mapIntermediateField L x))

/-- Mapping first by the inverse and then by the original normalized-base automorphism also
recovers the intermediate field exactly. -/
@[simp]
theorem mapIntermediateField_mapIntermediateField_symm
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E)
    (L : IntermediateField F E) :
    sigma.mapIntermediateField (sigma.symm.mapIntermediateField L) = L := by
  simpa [DifferentialSemilinearEquiv.symm] using
    sigma.symm.mapIntermediateField_symm_mapIntermediateField L

/-- Semilinear images preserve derivation-closed intermediate fields. -/
theorem derivationClosed_mapIntermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E)
    {L : IntermediateField F E} (hL : DerivationClosed L) :
    DerivationClosed (sigma.mapIntermediateField L) := by
  intro y hy
  rw [← sigma.ambientEquiv.apply_symm_apply y] at hy ⊢
  rw [← sigma.map_ambient_deriv']
  exact (sigma.mem_mapIntermediateField L _).mpr
    (hL ((sigma.mem_mapIntermediateField L _).mp hy))

/-- **Normalized-base differential-field covariance.** A differential semilinear automorphism
sends the differential field generated by a value set exactly to the differential field generated
by its transformed values. Thus normalization of the coefficient field, rather than pointwise
fixing, is the precise hypothesis needed for generated differential fields to be equivariant. -/
theorem mapIntermediateField_differentialAdjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (sigma : DifferentialSemilinearEquiv F E) (s : Set E) :
    sigma.mapIntermediateField (differentialAdjoin F s) =
      differentialAdjoin F (sigma.ambientEquiv '' s) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst y
    have hx' : x ∈ sigma.symm.mapIntermediateField
        (differentialAdjoin F (sigma.ambientEquiv '' s)) := by
      apply differentialAdjoin_le F _
        (sigma.symm.derivationClosed_mapIntermediateField
          (derivationClosed_differentialAdjoin F _)) hx
      intro z hz
      rw [← sigma.ambientEquiv.symm_apply_apply z]
      apply (sigma.symm.mem_mapIntermediateField _ _).mpr
      exact subset_differentialAdjoin F _ ⟨z, hz, rfl⟩
    have hx'' := (sigma.symm.mem_mapIntermediateField
      (differentialAdjoin F (sigma.ambientEquiv '' s))
      (sigma.ambientEquiv x)).mp (by
        simpa [DifferentialSemilinearEquiv.symm] using hx')
    simpa [DifferentialSemilinearEquiv.symm] using hx''
  · apply differentialAdjoin_le F
    · rintro y ⟨x, hx, rfl⟩
      exact (sigma.mem_mapIntermediateField _ _).mpr
        (subset_differentialAdjoin F s hx)
    · exact sigma.derivationClosed_mapIntermediateField
        (derivationClosed_differentialAdjoin F s)

/-- Algebraic independence is invariant under a semilinear automorphism which normalizes the
coefficient field. -/
theorem algebraicIndependent_map
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) {x : ι → E}
    (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent F (fun i => sigma.ambientEquiv (x i)) := by
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  let q := MvPolynomial.map sigma.baseEquiv.symm.toRingHom p
  have hqeval : MvPolynomial.aeval x q = 0 := by
    apply sigma.ambientEquiv.injective
    rw [map_zero]
    have hcoeff :
        sigma.ambientEquiv.toRingHom.comp (algebraMap F E) =
          (algebraMap F E).comp sigma.baseEquiv.toRingHom := by
      ext c
      exact sigma.map_algebraMap' c
    calc
      sigma.ambientEquiv (MvPolynomial.aeval x q) =
          MvPolynomial.eval₂Hom
              (sigma.ambientEquiv.toRingHom.comp (algebraMap F E))
              (fun i => sigma.ambientEquiv (x i)) q :=
        MvPolynomial.map_eval₂Hom
          (algebraMap F E) x sigma.ambientEquiv.toRingHom q
      _ = MvPolynomial.aeval (fun i => sigma.ambientEquiv (x i)) p := by
        rw [hcoeff]
        change MvPolynomial.eval₂Hom
            ((algebraMap F E).comp sigma.baseEquiv.toRingHom)
            (fun i => sigma.ambientEquiv (x i))
            (MvPolynomial.map sigma.baseEquiv.symm.toRingHom p) = _
        rw [MvPolynomial.eval₂Hom_map_hom]
        rw [MvPolynomial.aeval_eq_eval₂Hom]
        have hcomp :
            ((algebraMap F E).comp sigma.baseEquiv.toRingHom).comp
                sigma.baseEquiv.symm.toRingHom =
              algebraMap F E := by
          ext c
          simp
        rw [hcomp]
      _ = 0 := hp
  have hq : q = 0 := hx q hqeval
  apply (MvPolynomial.mapEquiv ι sigma.baseEquiv.symm).injective
  simpa [q] using hq

/-- Differential independence is transported by a differential semilinear automorphism. -/
theorem differentialIndependent_map
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) {x : ι → E}
    (hx : DifferentialIndependent F x) :
    DifferentialIndependent F (fun i => sigma.ambientEquiv (x i)) := by
  unfold DifferentialIndependent at hx ⊢
  have hmap := sigma.algebraicIndependent_map hx
  convert hmap using 1
  funext p
  exact (sigma.map_differentialJet p.2 (x p.1)).symm

/-- Differential independence is exactly invariant under a normalized-base differential
automorphism. -/
theorem differentialIndependent_map_iff
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) (x : ι → E) :
    DifferentialIndependent F (fun i => sigma.ambientEquiv (x i)) ↔
      DifferentialIndependent F x := by
  constructor
  · intro h
    have hback := sigma.symm.differentialIndependent_map h
    simpa [DifferentialSemilinearEquiv.symm] using hback
  · exact sigma.differentialIndependent_map

/-- Applying one normalized-base differential automorphism to every entry preserves the complete
represented differential matroid, not merely whole-family independence. -/
theorem differentialFamilyMatroid_map_eq
    {F E : Type u} {ι : Type v} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) (x : ι → E) :
    differentialFamilyMatroid (F := F) (fun i => sigma.ambientEquiv (x i)) =
      differentialFamilyMatroid (F := F) x := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      differentialFamilyMatroid_indep_iff]
    exact sigma.differentialIndependent_map_iff (fun i : I => x i)

/-- A normalized-base differential automorphism transports arbitrary differential-matroid
closures exactly. The generating set may be dependent. -/
theorem mem_differentialMatroid_closure_image_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) (s : Set E) (x : E) :
    sigma.ambientEquiv x ∈
        (differentialMatroid F E).closure (sigma.ambientEquiv '' s) ↔
      x ∈ (differentialMatroid F E).closure s := by
  have hmat := sigma.differentialFamilyMatroid_map_eq (fun y : E ↦ y)
  change (differentialMatroid F E).comap sigma.ambientEquiv =
      (differentialMatroid F E).comap id at hmat
  have hclosure := congrArg (fun M : Matroid E ↦ M.closure s) hmat
  change ((differentialMatroid F E).comap sigma.ambientEquiv).closure s =
      ((differentialMatroid F E).comap id).closure s at hclosure
  rw [Matroid.comap_closure_eq, Matroid.comap_closure_eq] at hclosure
  have hx := Set.ext_iff.mp hclosure x
  simpa using hx

/-- **Relative normalized-base HT covariance.** A differential semilinear automorphism preserves
hypertranscendence over every generated differential field while transporting both the source set
and the tested value. No independence hypothesis on the source set is required. -/
theorem hypertranscendentalOver_differentialAdjoin_image_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) (s : Set E) (x : E) :
    HypertranscendentalOver
        (differentialAdjoin F (sigma.ambientEquiv '' s)) (sigma.ambientEquiv x) ↔
      HypertranscendentalOver (differentialAdjoin F s) x := by
  rw [← differentialMatroid_contract_isNonloop_iff_hypertranscendentalOver,
    ← differentialMatroid_contract_isNonloop_iff_hypertranscendentalOver,
    Matroid.contract_isNonloop_iff, Matroid.contract_isNonloop_iff]
  simp only [differentialMatroid_ground, Set.mem_diff, Set.mem_univ, true_and]
  exact not_congr (sigma.mem_differentialMatroid_closure_image_iff s x)

/-- Relative differential algebraicity is transported by the same normalized-base semilinear
action, with no independence assumption on the generated coefficient field. -/
theorem differentialAlgebraicOver_differentialAdjoin_image_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) (s : Set E) (x : E) :
    DifferentialAlgebraicOver
        (differentialAdjoin F (sigma.ambientEquiv '' s)) (sigma.ambientEquiv x) ↔
      DifferentialAlgebraicOver (differentialAdjoin F s) x := by
  simpa only [HypertranscendentalOver, not_not] using not_congr
    (sigma.hypertranscendentalOver_differentialAdjoin_image_iff s x)

/-- Differential algebraicity is exactly invariant under a normalized-base differential
automorphism. -/
theorem differentialAlgebraicOver_map_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) (x : E) :
    DifferentialAlgebraicOver F (sigma.ambientEquiv x) ↔
      DifferentialAlgebraicOver F x := by
  simp only [DifferentialAlgebraicOver]
  exact not_congr (sigma.differentialIndependent_map_iff (fun _ : Unit => x))

/-- Hypertranscendence is exactly invariant under a normalized-base differential automorphism. -/
theorem hypertranscendentalOver_map_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E]
    (sigma : DifferentialSemilinearEquiv F E) (x : E) :
    HypertranscendentalOver F (sigma.ambientEquiv x) ↔
      HypertranscendentalOver F x :=
  not_congr (sigma.differentialAlgebraicOver_map_iff x)

/-- A DA source has a DA additive defect under every normalized-base differential automorphism. -/
theorem differentialAlgebraicOver_sub_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) {x : E}
    (hx : DifferentialAlgebraicOver F x) :
    DifferentialAlgebraicOver F (sigma.ambientEquiv x - x) :=
  differentialAlgebraicOver_sub
    ((sigma.differentialAlgebraicOver_map_iff x).mpr hx) hx

/-- A DA source has a DA multiplicative quotient under every normalized-base differential
automorphism. -/
theorem differentialAlgebraicOver_div_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) {x : E}
    (hx : DifferentialAlgebraicOver F x) :
    DifferentialAlgebraicOver F (sigma.ambientEquiv x / x) :=
  differentialAlgebraicOver_div
    ((sigma.differentialAlgebraicOver_map_iff x).mpr hx) hx

/-- **Semilinear additive-defect escape.** A hypertranscendental additive defect forces its
source to be hypertranscendental even when the automorphism acts nontrivially on the normalized
coefficient field. -/
theorem hypertranscendentalOver_of_sub_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) {x : E}
    (hdefect : HypertranscendentalOver F (sigma.ambientEquiv x - x)) :
    HypertranscendentalOver F x := by
  intro hx
  exact hdefect (sigma.differentialAlgebraicOver_sub_self hx)

/-- **Semilinear quotient escape.** A hypertranscendental multiplicative quotient forces its
source to be hypertranscendental even when the automorphism acts nontrivially on the normalized
coefficient field. -/
theorem hypertranscendentalOver_of_div_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E]
    (sigma : DifferentialSemilinearEquiv F E) {x : E}
    (hquotient : HypertranscendentalOver F (sigma.ambientEquiv x / x)) :
    HypertranscendentalOver F x := by
  intro hx
  exact hquotient (sigma.differentialAlgebraicOver_div_self hx)

end DifferentialSemilinearEquiv

end


end GaloisForLFunctions.HTGeometry
