import GaloisForLFunctions.HTGeometry.HomogenizedMonoidProjCover

/-!
# The full blowup of a pinched monoid algebra

The native Rees Proj is covered by its homogenizer chart. This module identifies that
homogeneous localization with the previously constructed affine chart and hence with
`R[M][T]`. A homogeneous fraction `c*U^n/(t*U)^n` maps to `c/t^n` in the common
localization. Regularity of `t` proves injectivity, while the exact vertex-ideal power
law proves that every such fraction belongs to the polynomial chart.

The resulting scheme isomorphism retains the source map and every monoid coordinate.
No finite-generation, Noetherian, domain, or properness hypothesis is used.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.HomogenizedMonoidAlgebra
variable (R M : Type*) [CommRing R] [AddCommMonoid M]

/-- The native degree-zero homogeneous localization at the marked homogenizer. -/
abbrev NativeChart := HomogeneousLocalization.Away (reesGrade R M) (reesGenerator R M 0)

local instance : CommRing (Overring R M) := inferInstance
local instance : CommRing (NativeChart R M) := inferInstance

/-- The inverse homogenizer in the faithful common localization. -/
def inverseParameter : Overring R M :=
  IsLocalization.Away.invSelf (Polynomial.X : Polynomial (AddMonoidAlgebra R M))

theorem parameter_mul_inverse : sourceToOverring R M (qVar R M 0) * inverseParameter R M = 1 := by
  rw [sourceToOverring_qVar_zero]
  exact IsLocalization.Away.mul_invSelf Polynomial.X

/-- Evaluate the Rees parameter at the inverse source homogenizer. -/
def reesEvaluation : reesAlgebra (vertexIdeal R M) →+* Overring R M :=
  (Polynomial.eval₂RingHom (sourceToOverring R M).toRingHom (inverseParameter R M)).comp
    (reesAlgebra (vertexIdeal R M)).val.toRingHom

theorem reesEvaluation_mono (n : ℕ) (a : Q R M) (ha : a ∈ (vertexIdeal R M)^n) :
    reesEvaluation R M (ReesGrading.mono (vertexIdeal R M) n a ha) =
      sourceToOverring R M a * inverseParameter R M ^n := by
  change (Polynomial.monomial n a).eval₂ _ _ = _
  exact Polynomial.eval₂_monomial _ _

theorem reesEvaluation_homogenizer : reesEvaluation R M (reesGenerator R M 0) = 1 := by
  change reesEvaluation R M (ReesGrading.mono (vertexIdeal R M) 1 (qVar R M 0)
    (by simpa using qVar_mem_vertexIdeal R M 0)) = 1
  rw [reesEvaluation_mono,pow_one,parameter_mul_inverse]

/-- The induced map from the native homogeneous chart to the common localization. -/
def nativeEvaluation : NativeChart R M →+* Overring R M :=
  (Localization.awayLift (reesEvaluation R M) (reesGenerator R M 0)
    (isUnit_iff_exists_inv.mpr ⟨1,by rw [reesEvaluation_homogenizer,mul_one]⟩)).comp
      (algebraMap (NativeChart R M) (Localization.Away (reesGenerator R M 0)))

/-- The degree-zero fraction represented by an element of the nth vertex-ideal power. -/
def nativeFraction (n : ℕ) (a : Q R M) (ha : a ∈ (vertexIdeal R M)^n) : NativeChart R M :=
  HomogeneousLocalization.Away.mk (reesGrade R M)
    (ReesGrading.mono_mem_grade (vertexIdeal R M) 1 (qVar R M 0)
      (by simpa using qVar_mem_vertexIdeal R M 0)) n
    (ReesGrading.mono (vertexIdeal R M) n a ha)
    (by simpa only [smul_eq_mul,mul_one] using
      ReesGrading.mono_mem_grade (vertexIdeal R M) n a ha)

theorem nativeEvaluation_fraction (n : ℕ) (a : Q R M) (ha : a ∈ (vertexIdeal R M)^n) :
    nativeEvaluation R M (nativeFraction R M n a ha) =
      sourceToOverring R M a * inverseParameter R M ^n := by
  unfold nativeEvaluation nativeFraction
  rw [RingHom.comp_apply,HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk (reesEvaluation R M) (reesGenerator R M 0)
    (ReesGrading.mono (vertexIdeal R M) n a ha) 1
      (by rw [reesEvaluation_homogenizer,mul_one]) n]
  simp only [one_pow,mul_one,reesEvaluation_mono]

theorem nativeFraction_surjective (x : NativeChart R M) :
    ∃ n a ha, nativeFraction R M n a ha = x := by
  obtain ⟨n,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesGrade R M)
    (ReesGrading.mono_mem_grade (vertexIdeal R M) 1 (qVar R M 0)
      (by simpa using qVar_mem_vertexIdeal R M 0)) x
  have he : f = ReesGrading.mono (vertexIdeal R M) n
      ((f : Polynomial (Q R M)).coeff n) (f.2 n) := by
    apply Subtype.ext
    have hff : f ∈ reesGrade R M n := by simpa only [smul_eq_mul,mul_one] using hf
    exact hff
  refine ⟨n,(f : Polynomial (Q R M)).coeff n,f.2 n,?_⟩
  unfold nativeFraction
  congr 1
  exact he.symm

theorem nativeEvaluation_injective : Function.Injective (nativeEvaluation R M) := by
  apply (injective_iff_map_eq_zero (nativeEvaluation R M)).2
  intro x hx
  obtain ⟨n,a,ha,rfl⟩ := nativeFraction_surjective R M x
  rw [nativeEvaluation_fraction] at hx
  have hh := congrArg (fun z => z * sourceToOverring R M (qVar R M 0)^n) hx
  have hi : inverseParameter R M * sourceToOverring R M (qVar R M 0) = 1 := by
    rw [mul_comm,parameter_mul_inverse]
  have he : sourceToOverring R M a = 0 := by
    simpa only [mul_assoc,← mul_pow,hi,one_pow,mul_one,zero_mul] using hh
  have ha0 : a = 0 := sourceToOverring_injective R M (by simpa only [map_zero] using he)
  subst a
  apply HomogeneousLocalization.val_injective
  simp only [nativeFraction,HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.val_zero]
  have hm : ReesGrading.mono (vertexIdeal R M) n 0 ha = 0 := by
    apply Subtype.ext
    exact map_zero (Polynomial.monomial n)
  rw [hm,Localization.mk_zero]


theorem source_mem_nativeRange (a : Q R M) :
    sourceToOverring R M a ∈ (nativeEvaluation R M).range := by
  refine ⟨nativeFraction R M 0 a (by rw [Submodule.pow_zero,Ideal.one_eq_top]; trivial),?_⟩
  rw [nativeEvaluation_fraction,pow_zero,mul_one]

/-- The image of the native chart, with its scalar-algebra structure. -/
def nativeImage : Subalgebra R (Overring R M) where
  toSubsemiring := (nativeEvaluation R M).range.toSubsemiring
  algebraMap_mem' r := by
    rw [← (sourceToOverring R M).commutes r]
    exact source_mem_nativeRange R M (algebraMap R (Q R M) r)

theorem ratio_mem_nativeRange (a : M) : chartRatio R M a ∈ (nativeEvaluation R M).range := by
  refine ⟨nativeFraction R M 1 (qVar R M a) (by
    rw [Submodule.pow_one]
    exact qVar_mem_vertexIdeal R M a),?_⟩
  rw [nativeEvaluation_fraction,pow_one]
  rfl

theorem nativeFraction_mem_affineChart (n : ℕ) (a : Q R M) (ha : a ∈ (vertexIdeal R M)^n) :
    nativeEvaluation R M (nativeFraction R M n a ha) ∈ affineChart R M := by
  rw [nativeEvaluation_fraction]
  cases n with
  | zero =>
    rw [pow_zero,mul_one]
    exact source_mem_affineChart R M a
  | succ n =>
    have hh := ha
    rw [vertexIdeal_pow,Ideal.span_singleton_pow,Ideal.mem_span_singleton_mul] at hh
    obtain ⟨b,hb,hba⟩ := hh
    rw [← hba,map_mul,map_pow,pow_succ]
    have he : (sourceToOverring R M (qVar R M 0)^n * sourceToOverring R M b) *
        (inverseParameter R M ^n * inverseParameter R M) =
          sourceToOverring R M b * inverseParameter R M := by
      calc
        _ = (sourceToOverring R M (qVar R M 0) * inverseParameter R M)^n *
          (sourceToOverring R M b * inverseParameter R M) := by rw [mul_pow]; ring
        _ = _ := by rw [parameter_mul_inverse,one_pow,one_mul]
    rw [he]
    exact idealRatio_mem_affineChart R M hb

theorem nativeImage_eq_affineChart : nativeImage R M = affineChart R M := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    obtain ⟨n,a,ha,rfl⟩ := nativeFraction_surjective R M z
    exact nativeFraction_mem_affineChart R M n a ha
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact source_mem_nativeRange R M a
    · exact ratio_mem_nativeRange R M a

/-- The native homogeneous chart is the previously constructed affine chart. -/
def nativeChartRingEquiv : NativeChart R M ≃+* affineChart R M :=
  RingEquiv.ofBijective ((nativeEvaluation R M).codRestrict (affineChart R M) (fun x => by
    rw [← nativeImage_eq_affineChart]
    exact ⟨x,rfl⟩)) (by
      constructor
      · intro x y h
        exact nativeEvaluation_injective R M (congrArg Subtype.val h)
      · intro y
        have hy : (y : Overring R M) ∈ nativeImage R M := by
          rw [nativeImage_eq_affineChart]
          exact y.property
        obtain ⟨x,hx⟩ := hy
        exact ⟨x,Subtype.ext hx⟩)

/-- The native homogeneous chart is the polynomial ring over the label algebra. -/
def nativeChartPolynomialEquiv : NativeChart R M ≃+* Polynomial (AddMonoidAlgebra R M) :=
  (nativeChartRingEquiv R M).trans (affineChartEquiv R M).toRingEquiv

theorem overringMap_affineChartEquiv (x : affineChart R M) :
    overringMap R M (affineChartEquiv R M x) = (x : Overring R M) := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective (overringMap R M) (overringMap_injective R M)).apply_symm_apply
      (Subalgebra.equivOfEq _ _ (affineChart_eq_range R M) x))

theorem nativeChartPolynomialEquiv_spec (x : NativeChart R M) :
    overringMap R M (nativeChartPolynomialEquiv R M x) = nativeEvaluation R M x := by
  exact overringMap_affineChartEquiv R M (nativeChartRingEquiv R M x)

theorem nativeChartPolynomialEquiv_source (a : Q R M) :
    nativeChartPolynomialEquiv R M
      (nativeFraction R M 0 a (by rw [Submodule.pow_zero,Ideal.one_eq_top]; trivial)) =
        quotientPolynomial R M a := by
  apply overringMap_injective R M
  rw [nativeChartPolynomialEquiv_spec,nativeEvaluation_fraction,pow_zero,mul_one]
  rfl

theorem nativeChartPolynomialEquiv_mark (a : M) :
    nativeChartPolynomialEquiv R M (nativeFraction R M 1 (qVar R M a)
      (by rw [Submodule.pow_one]; exact qVar_mem_vertexIdeal R M a)) =
        Polynomial.C (AddMonoidAlgebra.single a 1) := by
  apply overringMap_injective R M
  rw [nativeChartPolynomialEquiv_spec,nativeEvaluation_fraction,pow_one]
  exact chartRatio_eq R M a

open CategoryTheory

/-- The blowup of the pinched monoid algebra at its vertex is the polynomial chart. -/
def projIsoPolynomialChart :
    AlgebraicGeometry.Proj (reesGrade R M) ≅
      AlgebraicGeometry.Spec (.of (Polynomial (AddMonoidAlgebra R M))) :=
  projIsoHomogeneousChart R M ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso
    (nativeChartPolynomialEquiv R M).symm.toCommRingCatIso.op

end GaloisForLFunctions.HTGeometry.HomogenizedMonoidAlgebra
