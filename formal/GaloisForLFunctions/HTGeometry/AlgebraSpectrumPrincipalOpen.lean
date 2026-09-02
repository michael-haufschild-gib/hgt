import GaloisForLFunctions.HTGeometry.AlgebraSpectrumEquiv

/-!
# Complex points of a principal localization

For any complex algebra `R`, the complex points of `R[1/g]` are exactly the principal open where
`g` does not vanish.  The equivalence is topological for the pointwise-convergence topology on
`AlgSpec`: a localized element has one fixed numerator/denominator presentation, so its value is a
continuous quotient on the nonvanishing locus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AlgSpec

set_option maxHeartbeats 4000000

variable {R : Type*} [CommRing R]

theorem isUnit_algebraMap_localizationAway (g : R) :
    IsUnit (algebraMap R (Localization.Away g) g) :=
  IsLocalization.map_units (M := Submonoid.powers g) (Localization.Away g)
    (⟨g, ⟨1, pow_one g⟩⟩ : Submonoid.powers g)

variable [Algebra ℂ R]

theorem apply_localizationAway_ne_zero (g : R) (chi : AlgSpec (Localization.Away g)) :
    chi (algebraMap R (Localization.Away g) g) ≠ 0 :=
  ((isUnit_algebraMap_localizationAway g).map
    (chi : Localization.Away g →ₐ[ℂ] ℂ)).ne_zero

theorem algSpec_isUnit_powers_of_apply_ne_zero {g : R} {chi : AlgSpec R} (hchi : chi g ≠ 0)
    (y : Submonoid.powers g) : IsUnit (chi (y : R)) := by
  obtain ⟨k, hk⟩ := y.property
  rw [← hk, map_pow]
  exact IsUnit.pow k (isUnit_iff_ne_zero.2 hchi)

/-- A complex point extends uniquely across a principal localization whenever the inverted
element is nonzero there. -/
def localizationAwayLift (g : R) {chi : AlgSpec R} (hchi : chi g ≠ 0) :
    AlgSpec (Localization.Away g) :=
  AlgHom.mk (IsLocalization.lift (algSpec_isUnit_powers_of_apply_ne_zero hchi)) fun c => by
    change IsLocalization.lift (algSpec_isUnit_powers_of_apply_ne_zero hchi)
        (algebraMap R (Localization.Away g) (algebraMap ℂ R c)) = c
    rw [IsLocalization.lift_eq]
    exact chi.commutes c

theorem localizationAwayLift_algebraMap (g : R) {chi : AlgSpec R} (hchi : chi g ≠ 0) (r : R) :
    localizationAwayLift g hchi (algebraMap R (Localization.Away g) r) = chi r := by
  change IsLocalization.lift (algSpec_isUnit_powers_of_apply_ne_zero hchi)
      (algebraMap R (Localization.Away g) r) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- Restriction of a complex point of a principal localization to its base algebra. -/
def localizationAwayRestrict (g : R) (chi : AlgSpec (Localization.Away g)) :
    {chi : AlgSpec R // chi g ≠ 0} :=
  ⟨AlgSpec.precomp (IsScalarTower.toAlgHom ℂ R (Localization.Away g)) chi,
    apply_localizationAway_ne_zero g chi⟩

theorem continuous_localizationAwayRestrict (g : R) :
    Continuous (localizationAwayRestrict g) := by
  apply continuous_induced_rng.mpr
  exact continuous_precomp (IsScalarTower.toAlgHom ℂ R (Localization.Away g))

theorem continuous_localizationAwayLift (g : R) :
    Continuous fun chi : {chi : AlgSpec R // chi g ≠ 0} => localizationAwayLift g chi.2 := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  set s := IsLocalization.sec (Submonoid.powers g) b with hs
  have hden : Continuous fun chi : {chi : AlgSpec R // chi g ≠ 0} => chi.1 (s.2 : R) :=
    (continuous_eval (s.2 : R)).comp continuous_subtype_val
  have hnum : Continuous fun chi : {chi : AlgSpec R // chi g ≠ 0} => chi.1 s.1 :=
    (continuous_eval s.1).comp continuous_subtype_val
  have hden_ne : ∀ chi : {chi : AlgSpec R // chi g ≠ 0}, chi.1 (s.2 : R) ≠ 0 := by
    intro chi
    exact (algSpec_isUnit_powers_of_apply_ne_zero chi.2 s.2).ne_zero
  have hvalue : ∀ chi : {chi : AlgSpec R // chi g ≠ 0},
      localizationAwayLift g chi.2 b = chi.1 s.1 / chi.1 (s.2 : R) := by
    intro chi
    apply (eq_div_iff (hden_ne chi)).2
    have h := congrArg (fun z => localizationAwayLift g chi.2 z)
      (IsLocalization.sec_spec (Submonoid.powers g) b)
    simp only [map_mul] at h
    rw [localizationAwayLift_algebraMap, localizationAwayLift_algebraMap] at h
    exact h
  convert hnum.div₀ hden hden_ne using 1
  funext chi
  exact hvalue chi

/-- Complex points of a principal localization are homeomorphic to the corresponding principal
open in the complex-point space of the base algebra. -/
def homeomorphLocalizationAway (g : R) :
    AlgSpec (Localization.Away g) ≃ₜ {chi : AlgSpec R // chi g ≠ 0} where
  toFun := localizationAwayRestrict g
  invFun := fun chi => localizationAwayLift g chi.2
  left_inv chi := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    ext r
    exact localizationAwayLift_algebraMap g (apply_localizationAway_ne_zero g chi) r
  right_inv chi := by
    apply Subtype.ext
    apply DFunLike.ext
    intro r
    exact localizationAwayLift_algebraMap g chi.2 r
  continuous_toFun := continuous_localizationAwayRestrict g
  continuous_invFun := continuous_localizationAwayLift g

section TensorProduct

open scoped TensorProduct

variable {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra R B] [IsScalarTower ℂ R B]

/-- Restriction of a point of `B` to the base principal open. -/
def tensorLocalizationAwayBasePoint (g : R)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}) :
    {chi : AlgSpec R // chi g ≠ 0} :=
  ⟨AlgSpec.precomp (IsScalarTower.toAlgHom ℂ R B) chi.1, chi.2⟩

theorem continuous_tensorLocalizationAwayBasePoint (g : R) :
    Continuous (tensorLocalizationAwayBasePoint (B := B) g) := by
  apply continuous_induced_rng.mpr
  exact (continuous_precomp (IsScalarTower.toAlgHom ℂ R B)).comp continuous_subtype_val

/-- A pointwise construction together with its defining tensor formula.  Packaging the formula
with the map keeps the point-dependent `R`-algebra structure on `ℂ` internal. -/
structure TensorLocalizationAwayLiftData (g : R)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}) :
    Type _ where
  toAlgSpec : AlgSpec (TensorProduct R (Localization.Away g) B)
  apply_tmul (t : Localization.Away g) (b : B) :
    toAlgSpec (t ⊗ₜ[R] b) =
      localizationAwayLift g (tensorLocalizationAwayBasePoint g chi).2 t * chi.1 b

def tensorLocalizationAwayLiftData (g : R)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}) :
    TensorLocalizationAwayLiftData g chi := by
  let chiR : R →+* ℂ :=
    chi.1.toRingHom.comp (algebraMap R B)
  letI : Algebra R ℂ := chiR.toAlgebra
  let chiB : B →ₐ[R] ℂ :=
    { chi.1.toRingHom with
      commutes' := fun r => rfl }
  let chiT0 : AlgSpec (Localization.Away g) :=
    localizationAwayLift g (tensorLocalizationAwayBasePoint g chi).2
  let chiT : Localization.Away g →ₐ[R] ℂ :=
    { chiT0.toRingHom with
      commutes' := fun r => localizationAwayLift_algebraMap g
        (tensorLocalizationAwayBasePoint g chi).2 r }
  let hcomm : ∀ (t : Localization.Away g) (b : B), Commute (chiT t) (chiB b) :=
    fun _ _ => mul_comm _ _
  let hR : TensorProduct R (Localization.Away g) B →ₐ[R] ℂ :=
    Algebra.TensorProduct.lift chiT chiB hcomm
  let hom : AlgSpec (TensorProduct R (Localization.Away g) B) :=
    { hR.toRingHom with
      commutes' := fun c => by
        change hR (algebraMap ℂ (TensorProduct R (Localization.Away g) B) c) = c
        change hR ((algebraMap ℂ (Localization.Away g) c) ⊗ₜ[R] (1 : B)) = c
        rw [Algebra.TensorProduct.lift_tmul]
        change chiT0 (algebraMap ℂ (Localization.Away g) c) * chi.1 1 = c
        rw [map_one, mul_one]
        exact chiT0.commutes c }
  refine ⟨hom, ?_⟩
  intro t b
  change (Algebra.TensorProduct.lift chiT chiB hcomm) (t ⊗ₜ[R] b) = _
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

def tensorLocalizationAwayLift (g : R)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}) :
    AlgSpec (TensorProduct R (Localization.Away g) B) :=
  (tensorLocalizationAwayLiftData g chi).toAlgSpec

theorem tensorLocalizationAwayLift_tmul (g : R)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0})
    (t : Localization.Away g) (b : B) :
    tensorLocalizationAwayLift g chi (t ⊗ₜ[R] b) =
      localizationAwayLift g (tensorLocalizationAwayBasePoint g chi).2 t * chi.1 b := by
  exact (tensorLocalizationAwayLiftData g chi).apply_tmul t b

def tensorLocalizationAwayRestrict (g : R)
    (chi : AlgSpec (TensorProduct R (Localization.Away g) B)) :
    {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} := by
  let f : B →ₐ[ℂ] TensorProduct R (Localization.Away g) B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[R]
      TensorProduct R (Localization.Away g) B).restrictScalars ℂ
  refine ⟨AlgSpec.precomp f chi, ?_⟩
  have hu : IsUnit
      ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
        TensorProduct R (Localization.Away g) B) (algebraMap R (Localization.Away g) g)) :=
    (isUnit_algebraMap_localizationAway g).map
      (Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
        TensorProduct R (Localization.Away g) B)
  have heq :
      (Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
          TensorProduct R (Localization.Away g) B) (algebraMap R (Localization.Away g) g) =
        (Algebra.TensorProduct.includeRight : B →ₐ[R]
          TensorProduct R (Localization.Away g) B) (algebraMap R B g) := by
    simp
  change chi ((Algebra.TensorProduct.includeRight : B →ₐ[R]
    TensorProduct R (Localization.Away g) B) (algebraMap R B g)) ≠ 0
  rw [← heq]
  exact (hu.map chi).ne_zero

theorem continuous_tensorLocalizationAwayRestrict (g : R) :
    Continuous (tensorLocalizationAwayRestrict (B := B) g) := by
  apply continuous_induced_rng.mpr
  exact continuous_precomp
    ((Algebra.TensorProduct.includeRight : B →ₐ[R]
      TensorProduct R (Localization.Away g) B).restrictScalars ℂ)

theorem continuous_tensorLocalizationAwayLift (g : R) :
    Continuous (tensorLocalizationAwayLift (B := B) g) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simpa using (continuous_const : Continuous fun _ :
      {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} => (0 : ℂ))
  | tmul t b =>
      change Continuous fun chi => tensorLocalizationAwayLift g chi (t ⊗ₜ[R] b)
      rw [show (fun chi => tensorLocalizationAwayLift g chi (t ⊗ₜ[R] b)) =
          fun chi => localizationAwayLift g (tensorLocalizationAwayBasePoint g chi).2 t *
            chi.1 b by
        funext chi
        exact tensorLocalizationAwayLift_tmul g chi t b]
      exact ((continuous_eval t).comp
          ((continuous_localizationAwayLift g).comp
            (continuous_tensorLocalizationAwayBasePoint g))).mul
        ((continuous_eval b).comp continuous_subtype_val)
  | add x y hx hy =>
      change Continuous fun chi => tensorLocalizationAwayLift g chi (x + y)
      rw [show (fun chi => tensorLocalizationAwayLift g chi (x + y)) =
          (fun chi => tensorLocalizationAwayLift g chi x) +
            fun chi => tensorLocalizationAwayLift g chi y by
        funext chi
        exact map_add _ _ _]
      exact hx.add hy

/-- Scalar extension to a principal localization does exactly the same thing on complex points as
restricting the total algebra to the corresponding principal open. -/
def homeomorphTensorLocalizationAway (g : R) :
    AlgSpec (TensorProduct R (Localization.Away g) B) ≃ₜ
      {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} where
  toFun := tensorLocalizationAwayRestrict g
  invFun := tensorLocalizationAwayLift g
  left_inv chi := by
    apply DFunLike.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
        rw [tensorLocalizationAwayLift_tmul]
        change localizationAwayLift g _ t * chi
          ((Algebra.TensorProduct.includeRight : B →ₐ[R]
            TensorProduct R (Localization.Away g) B) b) = chi (t ⊗ₜ[R] b)
        have hbase : tensorLocalizationAwayBasePoint g
            (tensorLocalizationAwayRestrict g chi) = localizationAwayRestrict g
              (AlgSpec.precomp
                ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
                  TensorProduct R (Localization.Away g) B).restrictScalars ℂ) chi) := by
          apply Subtype.ext
          apply DFunLike.ext
          intro r
          change chi ((Algebra.TensorProduct.includeRight : B →ₐ[R]
              TensorProduct R (Localization.Away g) B) (algebraMap R B r)) =
            chi ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
              TensorProduct R (Localization.Away g) B)
                (algebraMap R (Localization.Away g) r))
          congr 1
          simp
        rw [hbase]
        have hloc : localizationAwayLift g
            (localizationAwayRestrict g
              (AlgSpec.precomp
                ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
                  TensorProduct R (Localization.Away g) B).restrictScalars ℂ) chi)).2 =
            AlgSpec.precomp
              ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
                TensorProduct R (Localization.Away g) B).restrictScalars ℂ) chi :=
          (homeomorphLocalizationAway g).left_inv _
        rw [hloc]
        change chi ((Algebra.TensorProduct.includeLeft : Localization.Away g →ₐ[R]
          TensorProduct R (Localization.Away g) B) t) *
          chi ((Algebra.TensorProduct.includeRight : B →ₐ[R]
            TensorProduct R (Localization.Away g) B) b) = chi (t ⊗ₜ[R] b)
        rw [← map_mul]
        congr 2
        simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  right_inv chi := by
    apply Subtype.ext
    apply DFunLike.ext
    intro b
    change tensorLocalizationAwayLift g chi
      ((Algebra.TensorProduct.includeRight : B →ₐ[R]
        TensorProduct R (Localization.Away g) B) b) = chi.1 b
    rw [show (Algebra.TensorProduct.includeRight : B →ₐ[R]
        TensorProduct R (Localization.Away g) B) b = (1 : Localization.Away g) ⊗ₜ[R] b by rfl,
      tensorLocalizationAwayLift_tmul]
    simp
  continuous_toFun := continuous_tensorLocalizationAwayRestrict g
  continuous_invFun := continuous_tensorLocalizationAwayLift g

end TensorProduct

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
