import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductHopfIdeal
import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehlerMultiplication

/-!
# Symmetric translated-product sources

The two-factor map `(x,y) ↦ x y⁻¹` turns any affine source into an inversion-symmetric source.
This file proves its coordinate formulas, identity and swap laws, and exact vanishing of mixed
invariant Kähler forms.  It also supplies the missing antipode pullback law for those forms.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

open AffineExponentialGroup

universe u

noncomputable section

def tensorPoint
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (e₁ e₂ : B →ₐ[k] k) : B ⊗[k] B →ₐ[k] k :=
  Algebra.TensorProduct.lift e₁ e₂ (fun _ _ => Commute.all _ _)

def affineExponentialSymmetricSourceMap
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B) :
    CoordinateAlgebra k n →ₐ[k] B ⊗[k] B :=
  (tensorAlgHom f
    (f.comp (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)))).comp
      (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))

@[simp] theorem affineExponentialSymmetricSourceMap_torusCharacter
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B) (m : Fin n →₀ ℤ) :
    affineExponentialSymmetricSourceMap f (torusCharacter k m) =
      f (torusCharacter k m) ⊗ₜ[k] f (torusCharacter k (-m)) := by
  rw [affineExponentialSymmetricSourceMap, AlgHom.comp_apply]
  change tensorAlgHom f
      (f.comp (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)))
      (Coalgebra.comul (R := k) (torusCharacter k m)) = _
  rw [comul_torusCharacter, tensorAlgHom_tmul, AlgHom.comp_apply]
  rw [show
    HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (torusCharacter k m) =
      torusCharacter k (-m) by exact antipode_torusCharacter k m]

@[simp] theorem affineExponentialSymmetricSourceMap_additiveCoordinate
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B) (i : Fin n) :
    affineExponentialSymmetricSourceMap f (additiveCoordinate k i) =
      f (additiveCoordinate k i) ⊗ₜ[k] 1 -
        1 ⊗ₜ[k] f (additiveCoordinate k i) := by
  rw [affineExponentialSymmetricSourceMap, AlgHom.comp_apply]
  change tensorAlgHom f
      (f.comp (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)))
      (Coalgebra.comul (R := k) (additiveCoordinate k i)) = _
  rw [comul_additiveCoordinate, map_add, tensorAlgHom_tmul,
    tensorAlgHom_tmul]
  simp only [AlgHom.comp_apply, map_one]
  rw [show
    HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (additiveCoordinate k i) =
      -additiveCoordinate k i by exact antipode_additiveCoordinate k i]
  rw [map_neg, TensorProduct.tmul_neg]
  rfl

theorem affineExponential_antipode_involutive
    (k : Type u) [Field k] {n : ℕ} :
    (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)).comp
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)) =
      AlgHom.id k (CoordinateAlgebra k n) := by
  ext m
  · change HopfAlgebra.antipode k
      (HopfAlgebra.antipode k (torusCharacter k m)) = torusCharacter k m
    rw [antipode_torusCharacter, antipode_torusCharacter]
    simp
  · change HopfAlgebra.antipode k
      (HopfAlgebra.antipode k (additiveCoordinate k m)) = additiveCoordinate k m
    rw [antipode_additiveCoordinate, map_neg, antipode_additiveCoordinate]
    simp

theorem affineExponentialSymmetricSourceMap_swap
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B) :
    (Algebra.TensorProduct.comm k B B).toAlgHom.comp
        (affineExponentialSymmetricSourceMap f) =
      (affineExponentialSymmetricSourceMap f).comp
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)) := by
  ext m
  · change (Algebra.TensorProduct.comm k B B)
      (affineExponentialSymmetricSourceMap f (torusCharacter k m)) =
        affineExponentialSymmetricSourceMap f
          (HopfAlgebra.antipode k (torusCharacter k m))
    rw [affineExponentialSymmetricSourceMap_torusCharacter,
      antipode_torusCharacter,
      affineExponentialSymmetricSourceMap_torusCharacter]
    simp
  · change (Algebra.TensorProduct.comm k B B)
      (affineExponentialSymmetricSourceMap f (additiveCoordinate k m)) =
        affineExponentialSymmetricSourceMap f
          (HopfAlgebra.antipode k (additiveCoordinate k m))
    rw [affineExponentialSymmetricSourceMap_additiveCoordinate,
      antipode_additiveCoordinate, map_neg,
      affineExponentialSymmetricSourceMap_additiveCoordinate]
    simp

theorem tensorPoint_comp_affineExponentialSymmetricSourceMap
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k (CoordinateAlgebra k n)) :
    (tensorPoint e e).comp (affineExponentialSymmetricSourceMap f) =
      Bialgebra.counitAlgHom k (CoordinateAlgebra k n) := by
  ext m
  · change tensorPoint e e
      (affineExponentialSymmetricSourceMap f (torusCharacter k m)) =
        Coalgebra.counit (R := k) (torusCharacter k m)
    have hef (a : CoordinateAlgebra k n) :
        e (f a) = Coalgebra.counit (R := k) a :=
      DFunLike.congr_fun he a
    simp [tensorPoint, hef]
  · change tensorPoint e e
      (affineExponentialSymmetricSourceMap f (additiveCoordinate k m)) =
        Coalgebra.counit (R := k) (additiveCoordinate k m)
    have hef (a : CoordinateAlgebra k n) :
        e (f a) = Coalgebra.counit (R := k) a :=
      DFunLike.congr_fun he a
    simp [tensorPoint, hef]

/-- Specializing the second symmetric-source factor at the identity recovers the first source
map, even when the first factor is evaluated in an extension algebra. -/
theorem tensorExtensionPoint_comp_affineExponentialSymmetricSourceMap_right_identity
    {k B L : Type u} [Field k] [CommRing B] [Algebra k B]
    [CommRing L] [Algebra k L]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B)
    (e : B →ₐ[k] k) (r : B →ₐ[k] L)
    (he : e.comp f = Bialgebra.counitAlgHom k (CoordinateAlgebra k n)) :
    (Algebra.TensorProduct.lift r ((Algebra.ofId k L).comp e)
        (fun _ _ => Commute.all _ _)).comp
        (affineExponentialSymmetricSourceMap f) =
      r.comp f := by
  ext m
  · have hef (a : CoordinateAlgebra k n) :
        e (f a) = Coalgebra.counit (R := k) a :=
      DFunLike.congr_fun he a
    simp only [AlgHom.comp_apply]
    change (Algebra.TensorProduct.lift r ((Algebra.ofId k L).comp e)
        (fun _ _ => Commute.all _ _))
          (affineExponentialSymmetricSourceMap f (torusCharacter k m)) =
      r (f (torusCharacter k m))
    rw [affineExponentialSymmetricSourceMap_torusCharacter]
    change r (f (torusCharacter k m)) *
        algebraMap k L (e (f (torusCharacter k (-m)))) =
      r (f (torusCharacter k m))
    rw [hef]
    simp
  · have hef (a : CoordinateAlgebra k n) :
        e (f a) = Coalgebra.counit (R := k) a :=
      DFunLike.congr_fun he a
    simp only [LinearMap.comp_apply]
    change (Algebra.TensorProduct.lift r ((Algebra.ofId k L).comp e)
        (fun _ _ => Commute.all _ _))
          (affineExponentialSymmetricSourceMap f (additiveCoordinate k m)) =
      r (f (additiveCoordinate k m))
    rw [affineExponentialSymmetricSourceMap_additiveCoordinate]
    rw [map_sub]
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      map_one, mul_one, one_mul]
    rw [hef]
    simp

namespace AffineExponentialInvariantKaehler

theorem algHomKaehlerMap_dlog_antipode
    (k : Type u) [Field k] {n : ℕ} (m : Fin n →₀ ℤ) :
    algHomKaehlerMap
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
        ((torusCharacter k (-m)) •
          KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m)) =
      -((torusCharacter k (-m)) •
          KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m)) := by
  rw [algHomKaehlerMap_smul, algHomKaehlerMap_D]
  rw [show
    HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (torusCharacter k (-m)) =
      torusCharacter k m by simpa using antipode_torusCharacter k (-m)]
  rw [show
    HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (torusCharacter k m) =
      torusCharacter k (-m) by exact antipode_torusCharacter k m]
  have hprod : torusCharacter k m * torusCharacter k (-m) = 1 := by
    rw [← torusCharacter_add]
    simp
  have hd := congrArg
    (KaehlerDifferential.D k (CoordinateAlgebra k n)) hprod
  rw [Derivation.leibniz] at hd
  have hd0 :
      torusCharacter k m •
          KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k (-m)) +
        torusCharacter k (-m) •
          KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m) = 0 := by
    simpa using hd
  exact eq_neg_of_add_eq_zero_left hd0

theorem algHomKaehlerMap_additiveCoordinate_antipode
    (k : Type u) [Field k] {n : ℕ} (i : Fin n) :
    algHomKaehlerMap
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
        (KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i)) =
      -KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i) := by
  rw [algHomKaehlerMap_D]
  rw [show
    HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (additiveCoordinate k i) =
      -additiveCoordinate k i by exact antipode_additiveCoordinate k i]
  exact map_neg _ _

theorem algHomKaehlerMap_mixedInvariantKaehlerVector_antipode
    (k : Type u) [Field k] {n : ℕ} (tor add : Fin n → k) :
    algHomKaehlerMap
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
        (mixedInvariantKaehlerVector k tor add) =
      -mixedInvariantKaehlerVector k tor add := by
  classical
  rw [mixedInvariantKaehlerVector_normalized]
  simp only [map_add, map_sum, map_smul]
  simp_rw [algHomKaehlerMap_dlog_antipode,
    algHomKaehlerMap_additiveCoordinate_antipode]
  simp only [smul_neg]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, neg_add_rev]
  abel

theorem algHomKaehlerMap_affineExponentialSymmetricSourceMap_eq_zero
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : CoordinateAlgebra k n →ₐ[k] B)
    (tor add : Fin n → k)
    (hf : algHomKaehlerMap f (mixedInvariantKaehlerVector k tor add) = 0) :
    algHomKaehlerMap (affineExponentialSymmetricSourceMap f)
        (mixedInvariantKaehlerVector k tor add) = 0 := by
  letI : CommRing (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
  letI : CommRing (B ⊗[k] B) := inferInstance
  let S := HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)
  let Φ : CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n →ₐ[k] B ⊗[k] B :=
    tensorAlgHom f (f.comp S)
  have hleftHom : Φ.comp
        (Algebra.TensorProduct.includeLeft : CoordinateAlgebra k n →ₐ[k]
          CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).comp f := by
    apply DFunLike.ext _ _
    intro a
    simp [Φ, tensorAlgHom]
  have hrightHom : Φ.comp
        (Algebra.TensorProduct.includeRight : CoordinateAlgebra k n →ₐ[k]
          CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B).comp (f.comp S) := by
    apply DFunLike.ext _ _
    intro a
    simp [Φ, tensorAlgHom]
  have hfS : algHomKaehlerMap (f.comp S)
      (mixedInvariantKaehlerVector k tor add) = 0 := by
    rw [algHomKaehlerMap_comp,
      algHomKaehlerMap_mixedInvariantKaehlerVector_antipode,
      map_neg, hf, neg_zero]
  have hleft : algHomKaehlerMap Φ
      (algHomKaehlerMap
        (Algebra.TensorProduct.includeLeft : CoordinateAlgebra k n →ₐ[k]
          CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
        (mixedInvariantKaehlerVector k tor add)) = 0 := by
    rw [← algHomKaehlerMap_comp, hleftHom, algHomKaehlerMap_comp, hf, map_zero]
  have hright : algHomKaehlerMap Φ
      (algHomKaehlerMap
        (Algebra.TensorProduct.includeRight : CoordinateAlgebra k n →ₐ[k]
          CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
        (mixedInvariantKaehlerVector k tor add)) = 0 := by
    rw [← algHomKaehlerMap_comp, hrightHom, algHomKaehlerMap_comp, hfS, map_zero]
  rw [affineExponentialSymmetricSourceMap, algHomKaehlerMap_comp]
  change algHomKaehlerMap Φ
      (algHomKaehlerMap
        (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))
        (mixedInvariantKaehlerVector k tor add)) = 0
  rw [algHomKaehlerMap_mixedInvariantKaehlerVector_comul]
  change algHomKaehlerMap Φ
      (algHomKaehlerMap
          (Algebra.TensorProduct.includeLeft : CoordinateAlgebra k n →ₐ[k]
            CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (mixedInvariantKaehlerVector k tor add) +
        algHomKaehlerMap
          (Algebra.TensorProduct.includeRight : CoordinateAlgebra k n →ₐ[k]
            CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (mixedInvariantKaehlerVector k tor add)) = 0
  rw [map_add, hleft, hright, add_zero]

end AffineExponentialInvariantKaehler

end

end GaloisForLFunctions.HTGeometry
