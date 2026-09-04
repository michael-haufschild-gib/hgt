import GaloisForLFunctions.HTGeometry.TensorFractionRingDomain
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedFieldDomain
import GaloisForLFunctions.HTGeometry.CriticalObservationField
import GaloisForLFunctions.HTGeometry.CriticalRawCoordinateValuation
import GaloisForLFunctions.HTGeometry.CriticalGenericArc

/-!
# Constant-field extension of multivariate rational function fields

Polynomial coefficient extension is the tensor product with the enlarged coefficient field.
After localizing first the old polynomial factor and then the whole tensor product, this gives the
canonical equivalence between the scalar extension of a rational function field and the rational
function field over the enlarged constants.  The final declarations specialize this exact
equivalence to the critical source and observation fields.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable (k K ι : Type*) [Field k] [Field K] [Algebra k K]

/-- The right tensor factor supplies the canonical enlarged-coefficient algebra structure. -/
noncomputable instance rightTensorProductAlgebra
    (A : Type*) [CommRing A] [Algebra k A] : Algebra K (A ⊗[k] K) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra

/-- Coefficient extension on multivariate polynomials. -/
def mvPolynomialCoefficientMap : MvPolynomial ι k →ₐ[k] MvPolynomial ι K where
  toRingHom := MvPolynomial.map (algebraMap k K)
  commutes' c := by simp

/-- Polynomial tensor evaluation, with the enlarged constants in the left factor. -/
def mvPolynomialTensorForward :
    (K ⊗[k] MvPolynomial ι k) →ₐ[K] MvPolynomial ι K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (MvPolynomial ι K))
    (mvPolynomialCoefficientMap k K ι) (fun _ _ => Commute.all _ _)

/-- Inverse polynomial tensor map, sending every variable to its pure tensor. -/
def mvPolynomialTensorBackward :
    MvPolynomial ι K →ₐ[K] (K ⊗[k] MvPolynomial ι k) :=
  MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] MvPolynomial.X i)

@[simp] theorem mvPolynomialTensorForward_tmul (x : K) (p : MvPolynomial ι k) :
    mvPolynomialTensorForward k K ι (x ⊗ₜ[k] p) =
      MvPolynomial.C x * MvPolynomial.map (algebraMap k K) p := by
  simp [mvPolynomialTensorForward, mvPolynomialCoefficientMap]

@[simp] theorem mvPolynomialTensorBackward_C (x : K) :
    mvPolynomialTensorBackward k K ι (MvPolynomial.C x) = x ⊗ₜ[k] 1 := by
  simp [mvPolynomialTensorBackward]

@[simp] theorem mvPolynomialTensorBackward_X (i : ι) :
    mvPolynomialTensorBackward k K ι (MvPolynomial.X i) =
      1 ⊗ₜ[k] MvPolynomial.X i := by
  simp [mvPolynomialTensorBackward]

theorem mvPolynomialTensorBackward_coefficientMap (p : MvPolynomial ι k) :
    mvPolynomialTensorBackward k K ι (MvPolynomial.map (algebraMap k K) p) =
      1 ⊗ₜ[k] p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.map_C, mvPolynomialTensorBackward_C]
      change (algebraMap k K c) ⊗ₜ[k] (1 : MvPolynomial ι k) =
        (1 : K) ⊗ₜ[k] algebraMap k (MvPolynomial ι k) c
      rw [← mul_one (algebraMap k K c), ← Algebra.smul_def,
        ← mul_one (algebraMap k (MvPolynomial ι k) c), ← Algebra.smul_def]
      exact (TensorProduct.tmul_smul (R := k) (R' := k)
        c (1 : K) (1 : MvPolynomial ι k)).symm
  | add p q hp hq =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (.+.) hp hq
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.map_X, map_mul, hp, mvPolynomialTensorBackward_X,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp

theorem mvPolynomialTensor_leftInverse :
    Function.LeftInverse (mvPolynomialTensorBackward k K ι)
      (mvPolynomialTensorForward k K ι) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [mvPolynomialTensorForward_tmul, map_mul, mvPolynomialTensorBackward_C,
        mvPolynomialTensorBackward_coefficientMap,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
  | add x y hx hy => simp_all [map_add]

theorem mvPolynomialTensor_rightInverse :
    Function.RightInverse (mvPolynomialTensorBackward k K ι)
      (mvPolynomialTensorForward k K ι) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => simp [mvPolynomialTensorForward, mvPolynomialTensorBackward,
      mvPolynomialCoefficientMap]
  | add p q hp hq => simp_all [map_add]
  | mul_X p i hp => simp_all [map_mul, mvPolynomialTensorForward,
      mvPolynomialTensorBackward, mvPolynomialCoefficientMap]

/-- Polynomial coefficient extension is tensor extension of constants. -/
def mvPolynomialTensorEquiv :
    (K ⊗[k] MvPolynomial ι k) ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (mvPolynomialTensorForward k K ι)
    (mvPolynomialTensorBackward k K ι)
    (AlgHom.ext fun p => mvPolynomialTensor_rightInverse k K ι p)
    (AlgHom.ext fun z => mvPolynomialTensor_leftInverse k K ι z)

/-- Polynomial coefficient-tensor equivalence in the conventional right-factor orientation. -/
def mvPolynomialRightTensorEquiv :
    (MvPolynomial ι k ⊗[k] K) ≃ₐ[K] MvPolynomial ι K := by
  exact AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm k (MvPolynomial ι k) K).toRingEquiv.trans
      (mvPolynomialTensorEquiv k K ι).toRingEquiv)
    (by
      intro c
      change mvPolynomialTensorForward k K ι
        ((Algebra.TensorProduct.comm k (MvPolynomial ι k) K)
          ((1 : MvPolynomial ι k) ⊗ₜ[k] c)) = MvPolynomial.C c
      simp [mvPolynomialTensorForward, mvPolynomialCoefficientMap])

/-- Localization of the old polynomial factor inside the right coefficient tensor. -/
def rationalFunctionTensorBaseMap :
    (MvPolynomial ι k ⊗[k] K) →ₐ[k]
      (FractionRing (MvPolynomial ι k) ⊗[k] K) :=
  Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k))) (AlgHom.id k K)

noncomputable instance rationalFunctionTensorBaseAlgebra :
    Algebra (MvPolynomial ι k ⊗[k] K)
      (FractionRing (MvPolynomial ι k) ⊗[k] K) :=
  (rationalFunctionTensorBaseMap k K ι).toRingHom.toAlgebra

noncomputable instance rationalFunctionTensorBaseScalarTower :
    IsScalarTower K (MvPolynomial ι k ⊗[k] K)
      (FractionRing (MvPolynomial ι k) ⊗[k] K) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := MvPolynomial ι k ⊗[k] K)
    (A := FractionRing (MvPolynomial ι k) ⊗[k] K) (by
      apply DFunLike.ext _ _
      intro c
      change (1 : FractionRing (MvPolynomial ι k)) ⊗ₜ[k] c =
        rationalFunctionTensorBaseMap k K ι
          ((1 : MvPolynomial ι k) ⊗ₜ[k] c)
      rw [show rationalFunctionTensorBaseMap k K ι
        ((1 : MvPolynomial ι k) ⊗ₜ[k] c) =
          (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) 1) ⊗ₜ[k] c
        from rfl]
      simp)

noncomputable instance rationalFunctionPolynomialTensorScalarTower :
    IsScalarTower (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] K)
      (FractionRing (MvPolynomial ι k) ⊗[k] K) :=
  IsScalarTower.of_algebraMap_eq'
    (R := MvPolynomial ι k) (S := MvPolynomial ι k ⊗[k] K)
    (A := FractionRing (MvPolynomial ι k) ⊗[k] K) (by
      apply DFunLike.ext _ _
      intro p
      change (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) p) ⊗ₜ[k]
          (1 : K) = rationalFunctionTensorBaseMap k K ι (p ⊗ₜ[k] (1 : K))
      rfl)

noncomputable instance rationalFunctionTensorBaseLocalization :
    IsLocalization
      ((nonZeroDivisors (MvPolynomial ι k)).map
        (Algebra.TensorProduct.includeLeft
          (R := k) (S := k) (A := MvPolynomial ι k) (B := K)))
      (FractionRing (MvPolynomial ι k) ⊗[k] K) := by
  refine IsLocalization.tensorProduct_tensorProduct k K
    (nonZeroDivisors (MvPolynomial ι k)) (FractionRing (MvPolynomial ι k)) ?_
  apply DFunLike.ext _ _
  intro c
  change rationalFunctionTensorBaseMap k K ι
      ((1 : MvPolynomial ι k) ⊗ₜ[k] c) =
    (1 : FractionRing (MvPolynomial ι k)) ⊗ₜ[k] c
  rw [show rationalFunctionTensorBaseMap k K ι
    ((1 : MvPolynomial ι k) ⊗ₜ[k] c) =
      (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) 1) ⊗ₜ[k] c
    from rfl]
  simp

noncomputable instance mvPolynomialRightTensor_isDomain :
    IsDomain (MvPolynomial ι k ⊗[k] K) :=
  (mvPolynomialRightTensorEquiv k K ι).toMulEquiv.isDomain

theorem rationalFunctionTensorBaseSubmonoid_le_nonZeroDivisors :
    ((nonZeroDivisors (MvPolynomial ι k)).map
      (Algebra.TensorProduct.includeLeft
        (R := k) (S := k) (A := MvPolynomial ι k) (B := K))) ≤
      nonZeroDivisors (MvPolynomial ι k ⊗[k] K) := by
  intro z hz
  rw [Submonoid.mem_map] at hz
  rcases hz with ⟨p, hp, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  simpa only [map_zero] using
    (Algebra.TensorProduct.includeLeft_injective
      (R := k) (S := k) (A := MvPolynomial ι k) (B := K)
      (algebraMap k K).injective).ne (mem_nonZeroDivisors_iff_ne_zero.mp hp)

noncomputable instance rationalFunctionRightTensor_isDomain :
    IsDomain (FractionRing (MvPolynomial ι k) ⊗[k] K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (rationalFunctionTensorBaseSubmonoid_le_nonZeroDivisors k K ι)

noncomputable instance rationalFunctionConstantExtension_faithful :
    FaithfulSMul (MvPolynomial ι k ⊗[k] K)
      (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K)) := by
  apply (faithfulSMul_iff_algebraMap_injective
    (MvPolynomial ι k ⊗[k] K)
    (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K))).2
  change Function.Injective
    (algebraMap (MvPolynomial ι k ⊗[k] K)
      (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K)))
  intro x y hxy
  apply IsLocalization.injective
    (FractionRing (MvPolynomial ι k) ⊗[k] K)
    (rationalFunctionTensorBaseSubmonoid_le_nonZeroDivisors k K ι)
  apply IsFractionRing.injective
    (FractionRing (MvPolynomial ι k) ⊗[k] K)
    (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K))
  simpa only [IsScalarTower.algebraMap_apply
    (MvPolynomial ι k ⊗[k] K)
    (FractionRing (MvPolynomial ι k) ⊗[k] K)
    (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K))] using hxy

/-- The two successive localizations form the full fraction field of the coefficient tensor. -/
noncomputable instance rationalFunctionConstantExtension_isFractionRing :
    IsFractionRing (MvPolynomial ι k ⊗[k] K)
      (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K)) := by
  let P := MvPolynomial ι k
  let T0 := P ⊗[k] K
  let T1 := FractionRing P ⊗[k] K
  let C := FractionRing T1
  apply IsFractionRing.of_field T0 C
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective T1 z
  obtain ⟨⟨pa, da⟩, ha⟩ := IsLocalization.mk'_surjective
    ((nonZeroDivisors P).map
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := P) (B := K))) a
  obtain ⟨⟨pb, db⟩, hb'⟩ := IsLocalization.mk'_surjective
    ((nonZeroDivisors P).map
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := P) (B := K))) b
  have hda : algebraMap T0 C da ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply T0 T1 C]
    simpa only [map_zero] using (IsFractionRing.injective T1 C).ne
      (IsLocalization.map_units T1 da).ne_zero
  have hdb : algebraMap T0 C db ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply T0 T1 C]
    simpa only [map_zero] using (IsFractionRing.injective T1 C).ne
      (IsLocalization.map_units T1 db).ne_zero
  have haC : algebraMap T1 C a = algebraMap T0 C pa / algebraMap T0 C da := by
    apply (eq_div_iff hda).2
    rw [IsScalarTower.algebraMap_apply T0 T1 C,
      ← map_mul, IsScalarTower.algebraMap_apply T0 T1 C]
    apply congrArg (algebraMap T1 C)
    rw [← ha]
    exact IsLocalization.mk'_spec T1 pa da
  have hbC : algebraMap T1 C b = algebraMap T0 C pb / algebraMap T0 C db := by
    apply (eq_div_iff hdb).2
    rw [IsScalarTower.algebraMap_apply T0 T1 C,
      ← map_mul, IsScalarTower.algebraMap_apply T0 T1 C]
    apply congrArg (algebraMap T1 C)
    rw [← hb']
    exact IsLocalization.mk'_spec T1 pb db
  have hpb : algebraMap T0 C pb ≠ 0 := by
    intro hp
    have hbzero : algebraMap T1 C b = 0 := by rw [hbC, hp, zero_div]
    have : b = 0 := (IsFractionRing.injective T1 C) (by simpa using hbzero)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) this
  refine ⟨pa * db, da * pb, ?_⟩
  rw [map_mul, map_mul, ← hab, haC, hbC]
  rw [div_div_eq_mul_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Extending constants in a multivariate rational function field gives the rational function
field over the enlarged constants. -/
def rationalFunctionConstantBaseChange :
    FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K) ≃ₐ[K]
      FractionRing (MvPolynomial ι K) :=
  IsFractionRing.algEquivOfAlgEquiv (mvPolynomialRightTensorEquiv k K ι)

@[simp] theorem rationalFunctionConstantBaseChange_algebraMap
    (p : MvPolynomial ι k ⊗[k] K) :
    rationalFunctionConstantBaseChange k K ι
        (algebraMap (MvPolynomial ι k ⊗[k] K)
          (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K)) p) =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (mvPolynomialRightTensorEquiv k K ι p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (mvPolynomialRightTensorEquiv k K ι) p

@[simp] theorem rationalFunctionConstantBaseChange_X (i : ι) :
    rationalFunctionConstantBaseChange k K ι
        (algebraMap
          (FractionRing (MvPolynomial ι k) ⊗[k] K)
          (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K))
          ((algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
              (MvPolynomial.X i)) ⊗ₜ[k] (1 : K))) =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (MvPolynomial.X i) := by
  change rationalFunctionConstantBaseChange k K ι
      (algebraMap (FractionRing (MvPolynomial ι k) ⊗[k] K)
        (FractionRing (FractionRing (MvPolynomial ι k) ⊗[k] K))
        (algebraMap (MvPolynomial ι k ⊗[k] K)
          (FractionRing (MvPolynomial ι k) ⊗[k] K)
          ((MvPolynomial.X i) ⊗ₜ[k] (1 : K)))) = _
  rw [← IsScalarTower.algebraMap_apply,
    rationalFunctionConstantBaseChange_algebraMap]
  congr 1
  simp [mvPolynomialRightTensorEquiv, mvPolynomialTensorEquiv,
    mvPolynomialTensorForward, mvPolynomialCoefficientMap]

/-- Algebra equivalences commute with extension in the right constant factor. -/
def rightScalarExtensionAlgEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) : (A ⊗[k] K) ≃ₐ[K] (B ⊗[k] K) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv)
    (by
      intro c
      change (Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K))
        ((1 : A) ⊗ₜ[k] c) = (1 : B) ⊗ₜ[k] c
      simp)

/-- Fraction fields commute with an equivalence before extending the right constant factor. -/
def rightFractionScalarExtensionAlgEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [IsDomain (A ⊗[k] K)] [IsDomain (B ⊗[k] K)]
    (e : A ≃ₐ[k] B) :
    FractionRing (A ⊗[k] K) ≃ₐ[K] FractionRing (B ⊗[k] K) :=
  IsFractionRing.algEquivOfAlgEquiv (rightScalarExtensionAlgEquiv k K e)

@[simp] theorem rightScalarExtensionAlgEquiv_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : A) (c : K) :
    rightScalarExtensionAlgEquiv k K e (a ⊗ₜ[k] c) = e a ⊗ₜ[k] c := by
  simp [rightScalarExtensionAlgEquiv]

@[simp] theorem rightFractionScalarExtensionAlgEquiv_algebraMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [IsDomain (A ⊗[k] K)] [IsDomain (B ⊗[k] K)]
    (e : A ≃ₐ[k] B) (x : A ⊗[k] K) :
    rightFractionScalarExtensionAlgEquiv k K e
        (algebraMap (A ⊗[k] K) (FractionRing (A ⊗[k] K)) x) =
      algebraMap (B ⊗[k] K) (FractionRing (B ⊗[k] K))
        (rightScalarExtensionAlgEquiv k K e x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (rightScalarExtensionAlgEquiv k K e) x

@[simp] theorem rightFractionScalarExtensionAlgEquiv_symm_algebraMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [IsDomain (A ⊗[k] K)] [IsDomain (B ⊗[k] K)]
    (e : A ≃ₐ[k] B) (x : B ⊗[k] K) :
    (rightFractionScalarExtensionAlgEquiv k K e).symm
        (algebraMap (B ⊗[k] K) (FractionRing (B ⊗[k] K)) x) =
      algebraMap (A ⊗[k] K) (FractionRing (A ⊗[k] K))
        ((rightScalarExtensionAlgEquiv k K e).symm x) := by
  apply (rightFractionScalarExtensionAlgEquiv k K e).injective
  rw [AlgEquiv.apply_symm_apply,
    rightFractionScalarExtensionAlgEquiv_algebraMap,
    (rightScalarExtensionAlgEquiv k K e).apply_symm_apply]

/-- Scalar extension of the rational critical source field is the actual source field over the
enlarged constants. -/
def criticalSourceConstantBaseChange [IsAlgClosed k] [CharZero k]
    [IsAlgClosed K] [CharZero K] (m n : ℕ) :
    FractionRing (criticalSourceField k m n ⊗[k] K) ≃ₐ[K]
      criticalSourceField K m n := by
  letI : IsDomain (FractionRing (MvPolynomial (Fin (m + n)) k) ⊗[k] K) :=
    isDomain_tensorProduct_of_fields
  letI : IsDomain (criticalSourceField k m n ⊗[k] K) :=
    isDomain_tensorProduct_of_fields
  exact (rightFractionScalarExtensionAlgEquiv k K
      (criticalSourceFieldEquiv k m n)).symm.trans <|
    (rationalFunctionConstantBaseChange k K (Fin (m + n))).trans <|
      criticalSourceFieldEquiv K m n

/-- Constant-field extension carries every source coordinate to the corresponding enlarged-field
coordinate. -/
@[simp] theorem criticalSourceConstantBaseChange_raw [IsAlgClosed k] [CharZero k]
    [IsAlgClosed K] [CharZero K] (m n : ℕ) (j : Fin (m + n)) :
    criticalSourceConstantBaseChange k K m n
        (algebraMap (criticalSourceField k m n ⊗[k] K)
          (FractionRing (criticalSourceField k m n ⊗[k] K))
          (criticalSourceRaw k m n j ⊗ₜ[k] (1 : K))) =
      criticalSourceRaw K m n j := by
  rw [criticalSourceConstantBaseChange]
  simp only [AlgEquiv.trans_apply]
  rw [rightFractionScalarExtensionAlgEquiv_symm_algebraMap]
  change (criticalSourceFieldEquiv K m n)
      (rationalFunctionConstantBaseChange k K (Fin (m + n))
        (algebraMap
          (FractionRing (MvPolynomial (Fin (m + n)) k) ⊗[k] K)
          (FractionRing
            (FractionRing (MvPolynomial (Fin (m + n)) k) ⊗[k] K))
          (((criticalSourceFieldEquiv k m n).symm
            (criticalSourceRaw k m n j)) ⊗ₜ[k] (1 : K)))) = _
  have hsmall := criticalSourceFieldEquiv_symm_aeval k m n
    (MvPolynomial.X j)
  simp only [MvPolynomial.aeval_X] at hsmall
  rw [hsmall, rationalFunctionConstantBaseChange_X]
  rw [← criticalSourceFieldEquiv_symm_aeval K m n (MvPolynomial.X j)]
  simp

/-- Scalar extension of the rational critical observation field is the actual observation field
over the enlarged constants. -/
def criticalObservationConstantBaseChange [IsAlgClosed k] [CharZero k]
    [IsAlgClosed K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FractionRing (criticalObservationField k m n ⊗[k] K) ≃ₐ[K]
      criticalObservationField K m n := by
  letI : IsDomain (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k) ⊗[k] K) :=
    isDomain_tensorProduct_of_fields
  letI : IsDomain (criticalObservationField k m n ⊗[k] K) :=
    isDomain_tensorProduct_of_fields
  exact (rightFractionScalarExtensionAlgEquiv k K
      (criticalObservationFieldEquiv k hm hn)).symm.trans <|
    (rationalFunctionConstantBaseChange k K (Fin n ⊕ Fin m)).trans <|
      criticalObservationFieldEquiv K hm hn

/-- Constant-field extension carries each observed raw coordinate to the corresponding
enlarged-field coordinate. -/
@[simp] theorem criticalObservationConstantBaseChange_raw [IsAlgClosed k] [CharZero k]
    [IsAlgClosed K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin n) :
    criticalObservationConstantBaseChange k K hm hn
        (algebraMap (criticalObservationField k m n ⊗[k] K)
          (FractionRing (criticalObservationField k m n ⊗[k] K))
          (criticalObservationRaw k m n i ⊗ₜ[k] (1 : K))) =
      criticalObservationRaw K m n i := by
  rw [criticalObservationConstantBaseChange]
  simp only [AlgEquiv.trans_apply]
  rw [rightFractionScalarExtensionAlgEquiv_symm_algebraMap]
  change (criticalObservationFieldEquiv K hm hn)
      (rationalFunctionConstantBaseChange k K (Fin n ⊕ Fin m)
        (algebraMap
          (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k) ⊗[k] K)
          (FractionRing
            (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k) ⊗[k] K))
          (((criticalObservationFieldEquiv k hm hn).symm
            (criticalObservationRaw k m n i)) ⊗ₜ[k] (1 : K)))) = _
  rw [criticalObservationFieldEquiv_symm_raw,
    rationalFunctionConstantBaseChange_X,
    ← criticalObservationFieldEquiv_symm_raw K hm hn i]
  exact (criticalObservationFieldEquiv K hm hn).apply_symm_apply _

/-- Constant-field extension carries each observed reciprocal coordinate to the corresponding
enlarged-field coordinate. -/
@[simp] theorem criticalObservationConstantBaseChange_recip [IsAlgClosed k] [CharZero k]
    [IsAlgClosed K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (j : Fin m) :
    criticalObservationConstantBaseChange k K hm hn
        (algebraMap (criticalObservationField k m n ⊗[k] K)
          (FractionRing (criticalObservationField k m n ⊗[k] K))
          (criticalObservationRecip k m n j ⊗ₜ[k] (1 : K))) =
      criticalObservationRecip K m n j := by
  rw [criticalObservationConstantBaseChange]
  simp only [AlgEquiv.trans_apply]
  rw [rightFractionScalarExtensionAlgEquiv_symm_algebraMap]
  change (criticalObservationFieldEquiv K hm hn)
      (rationalFunctionConstantBaseChange k K (Fin n ⊕ Fin m)
        (algebraMap
          (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k) ⊗[k] K)
          (FractionRing
            (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k) ⊗[k] K))
          (((criticalObservationFieldEquiv k hm hn).symm
            (criticalObservationRecip k m n j)) ⊗ₜ[k] (1 : K)))) = _
  rw [criticalObservationFieldEquiv_symm_recip,
    rationalFunctionConstantBaseChange_X,
    ← criticalObservationFieldEquiv_symm_recip K hm hn j]
  exact (criticalObservationFieldEquiv K hm hn).apply_symm_apply _

end

end GaloisForLFunctions.HTGeometry
