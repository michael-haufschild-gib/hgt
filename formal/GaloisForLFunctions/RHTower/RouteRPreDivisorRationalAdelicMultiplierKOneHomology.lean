import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import GaloisForLFunctions.RHTower.RouteRPrimeChainHochschildCycleWall

/-!
# Pre-divisor rational-adelic multiplier K1 homology for Route R

The Bruhat-decorated prime tensor previously used by Route R is not a Hochschild cycle.  This
module repairs that defect without changing prime provenance: it unitizes the actual adelic
Bruhat coefficient core, forms its rational-scaling multiplier crossed product, and constructs
the genuine unit cycle `u_p⁻¹ ⊗ u_p`.

The alternating Hochschild maps satisfy `b₁ b₂ = 0` unconditionally.  Scalar augmentation to the
rational dilation group ring pulls back the logarithmic Kummer cyclic cocycle, which vanishes on
all degree-two boundaries and evaluates the prime cycle as `log p`.  Hence the retained ordinary
prime defines a nonzero class in genuine Hochschild-one homology.

No divisor, Xi zero, critical-line premise, fixed-ideal preservation, or mate-gain vanishing is
used.  This module supplies a genuine source homology carrier; a coefficient-faithful comparison
with the Bruhat-decorated Xi landing remains a separate theorem.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower
namespace RouteRMultiplierKOne

noncomputable section

structure SCore where
  toCore : CCMRationalAdelicBruhatSimpleTensor

def sCoreEquiv : SCore ≃ CCMRationalAdelicBruhatSimpleTensor where
  toFun := SCore.toCore
  invFun := SCore.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup SCore := sCoreEquiv.addCommGroup
noncomputable instance : Module ℂ SCore := sCoreEquiv.module ℂ
noncomputable instance : Mul SCore := ⟨fun x y => ⟨x.toCore * y.toCore⟩⟩

@[simp] theorem SCore.toCore_zero : (0 : SCore).toCore = 0 := rfl
@[simp] theorem SCore.toCore_add (x y : SCore) : (x + y).toCore = x.toCore + y.toCore := rfl
@[simp] theorem SCore.toCore_smul (c : ℂ) (x : SCore) :
    (c • x).toCore = c • x.toCore := rfl
@[simp] theorem SCore.toCore_mul (x y : SCore) :
    (x * y).toCore = x.toCore * y.toCore := rfl
@[simp] theorem SCore.toCore_smul_self (x y : SCore) :
    (x • y).toCore = x.toCore * y.toCore := rfl

@[ext] theorem SCore.ext {x y : SCore} (h : x.toCore = y.toCore) : x = y := by
  cases x; cases y; cases h; rfl

noncomputable instance : NonUnitalCommRing SCore where
  zero_mul x := by apply SCore.ext; exact ccmRationalAdelicBruhat_zero_mul x.toCore
  mul_zero x := by apply SCore.ext; exact ccmRationalAdelicBruhat_mul_zero x.toCore
  left_distrib x y z := by
    apply SCore.ext
    exact ccmRationalAdelicBruhat_mul_add x.toCore y.toCore z.toCore
  right_distrib x y z := by
    apply SCore.ext
    exact ccmRationalAdelicBruhat_add_mul x.toCore y.toCore z.toCore
  mul_assoc x y z := by
    apply SCore.ext
    exact ccmRationalAdelicBruhat_mul_assoc x.toCore y.toCore z.toCore
  mul_comm x y := by
    apply SCore.ext
    exact ccmRationalAdelicBruhat_mul_comm x.toCore y.toCore

noncomputable instance : SMulCommClass ℂ SCore SCore where
  smul_comm c x y := by
    apply SCore.ext
    simp only [SCore.toCore_smul, SCore.toCore_smul_self]
    exact (mul_smul_comm c x.toCore y.toCore).symm

noncomputable instance : IsScalarTower ℂ SCore SCore where
  smul_assoc c x y := by
    apply SCore.ext
    simp only [SCore.toCore_smul, SCore.toCore_smul_self]
    exact smul_mul_assoc c x.toCore y.toCore

def scaleSCore (k : CCMRationalAdelicScaling) (x : SCore) : SCore :=
  ⟨k • x.toCore⟩

instance : SMul CCMRationalAdelicScaling SCore := ⟨scaleSCore⟩

@[simp] theorem scaleSCore_toCore (k : CCMRationalAdelicScaling) (x : SCore) :
    (k • x).toCore = k • x.toCore := rfl

instance : DistribMulAction CCMRationalAdelicScaling SCore where
  one_smul x := by apply SCore.ext; exact one_smul _ x.toCore
  mul_smul k l x := by apply SCore.ext; exact mul_smul k l x.toCore
  smul_zero k := by apply SCore.ext; exact smul_zero k
  smul_add k x y := by apply SCore.ext; exact smul_add k x.toCore y.toCore

abbrev MCore := Unitization ℂ SCore

def scaleMCore (k : CCMRationalAdelicScaling) (x : MCore) : MCore :=
  ⟨x.fst, k • x.snd⟩

instance : SMul CCMRationalAdelicScaling MCore := ⟨scaleMCore⟩

@[simp] theorem scalingMCore_fst (k : CCMRationalAdelicScaling) (x : MCore) :
    (k • x).fst = x.fst := rfl

@[simp] theorem scalingMCore_snd (k : CCMRationalAdelicScaling) (x : MCore) :
    (k • x).snd = k • x.snd := rfl

instance : MulSemiringAction CCMRationalAdelicScaling MCore where
  one_smul x := by apply Unitization.ext <;> simp
  mul_smul k l x := by apply Unitization.ext <;> simp [mul_smul]
  smul_zero k := by apply Unitization.ext <;> simp
  smul_add k x y := by apply Unitization.ext <;> simp
  smul_one k := by apply Unitization.ext <;> simp
  smul_mul k x y := by
    apply Unitization.ext
    · simp
    · rw [scalingMCore_snd, Unitization.snd_mul, Unitization.snd_mul]
      simp only [scalingMCore_fst, scalingMCore_snd]
      apply SCore.ext
      simp only [scaleSCore_toCore, SCore.toCore_add, SCore.toCore_smul,
        SCore.toCore_mul]
      rw [smul_add, smul_add]
      change
        ccmRationalAdelicBruhatScaling k (x.fst • y.snd.toCore) +
            ccmRationalAdelicBruhatScaling k (y.fst • x.snd.toCore) +
            ccmRationalAdelicBruhatScaling k (x.snd.toCore * y.snd.toCore) =
          x.fst • ccmRationalAdelicBruhatScaling k y.snd.toCore +
            y.fst • ccmRationalAdelicBruhatScaling k x.snd.toCore +
              ccmRationalAdelicBruhatScaling k x.snd.toCore *
                ccmRationalAdelicBruhatScaling k y.snd.toCore
      rw [(ccmRationalAdelicBruhatScaling k).map_smul,
        (ccmRationalAdelicBruhatScaling k).map_smul]
      have hm := ccmRationalAdelicBruhatScaling_map_mul
        k x.snd.toCore y.snd.toCore
      change ccmRationalAdelicBruhatScaling k
          (x.snd.toCore * y.snd.toCore) =
        ccmRationalAdelicBruhatScaling k x.snd.toCore *
          ccmRationalAdelicBruhatScaling k y.snd.toCore at hm
      rw [hm]

instance : SMulCommClass CCMRationalAdelicScaling ℂ MCore where
  smul_comm k c x := by
    apply Unitization.ext
    · simp
    · change k • (c • x.snd) = c • (k • x.snd)
      apply SCore.ext
      exact (ccmRationalAdelicBruhatScaling k).map_smul c x.snd.toCore

abbrev Mult := SkewMonoidAlgebra MCore CCMRationalAdelicScaling

def dil (k : CCMRationalAdelicScaling) : Mult :=
  SkewMonoidAlgebra.of MCore CCMRationalAdelicScaling k

def dilUnit (k : CCMRationalAdelicScaling) : Multˣ :=
  (SkewMonoidAlgebra.of MCore CCMRationalAdelicScaling).toHomUnits k

abbrev MC1 := CyclicBarTensor ℂ Mult 1

def mBoundaryOne : MC1 →ₗ[ℂ] Mult :=
  (cyclicBarDegreeZeroProduct (R := ℂ)).comp
    (cyclicBarFace (R := ℂ) (A := Mult) (0 : Fin 2) -
      cyclicBarFace (R := ℂ) (A := Mult) (1 : Fin 2))

theorem mBoundaryOne_tprod (a b : Mult) :
    mBoundaryOne (PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
      Fin.cases a (fun _ => b) i)) = a * b - b * a := by
  let x : Fin 2 → Mult := fun i => Fin.cases a (fun _ => b) i
  have hface0 : cyclicBarFaceTuple (0 : Fin 2) x 0 = a * b := by
    rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) by rfl]
    rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
    simp [x, cyclicBarFaceNonwrapTuple]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ]
  have hface1 : cyclicBarFaceTuple (1 : Fin 2) x 0 = b * a := by
    rw [show (1 : Fin 2) = Fin.last 1 by rfl]
    rw [cyclicBarFaceTuple, Fin.lastCases_last]
    simp [x, cyclicBarFaceWrapTuple]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ]
  change mBoundaryOne (PiTensorProduct.tprod ℂ x) = _
  simp only [mBoundaryOne, LinearMap.comp_apply, LinearMap.sub_apply,
    cyclicBarFace_tprod, map_sub, cyclicBarDegreeZeroProduct_tprod]
  rw [hface0, hface1]

theorem mBoundaryOne_tprod' (x : Fin 2 → Mult) :
    mBoundaryOne (PiTensorProduct.tprod ℂ x) = x 0 * x 1 - x 1 * x 0 := by
  have hx : x = fun i : Fin 2 => Fin.cases (x 0) (fun _ => x 1) i := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact mBoundaryOne_tprod (x 0) (x 1)

def primeKOneCycle (p : Nat.Primes) : MC1 :=
  let u := dilUnit (ccmRationalAdelicPrimeScaling p)
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (↑u⁻¹ : Mult) (fun _ => (u : Mult)) i)

theorem primeKOneCycle_boundary (p : Nat.Primes) :
    mBoundaryOne (primeKOneCycle p) = 0 := by
  rw [primeKOneCycle]
  rw [mBoundaryOne_tprod]
  simp

/-! ## Scalar augmentation to the rational dilation group algebra -/

abbrev KummerGroupRing := MonoidAlgebra ℂ CCMRationalAdelicScaling

def multiplierCoefficientAugmentation : MCore →ₐ[ℂ] KummerGroupRing :=
  (MonoidAlgebra.singleOneAlgHom).comp (Unitization.fstHom ℂ SCore)

def multiplierToKummerGroupRing : Mult →ₐ[ℂ] KummerGroupRing :=
  SkewMonoidAlgebra.liftNCAlgHom multiplierCoefficientAugmentation
    (MonoidAlgebra.of ℂ CCMRationalAdelicScaling) (by
      intro x y
      rw [show multiplierCoefficientAugmentation (y • x) =
          multiplierCoefficientAugmentation x by
        simp [multiplierCoefficientAugmentation]]
      exact mul_comm _ _)

@[simp] theorem multiplierToKummerGroupRing_dil
    (k : CCMRationalAdelicScaling) :
    multiplierToKummerGroupRing (dil k) =
      MonoidAlgebra.of ℂ CCMRationalAdelicScaling k := by
  simp [multiplierToKummerGroupRing, SkewMonoidAlgebra.liftNCAlgHom,
    SkewMonoidAlgebra.liftNCRingHom, dil]

/-! ## Kummer derivation and identity-coefficient trace -/

def kummerGroupRingCoefficientDerivation :
    (CCMRationalAdelicScaling →₀ ℂ) →ₗ[ℂ]
      (CCMRationalAdelicScaling →₀ ℂ) :=
  Finsupp.lsum ℂ fun k =>
    ccmRationalAdelicKummerLogWeight k • Finsupp.lsingle k

def kummerGroupRingDerivation : KummerGroupRing →ₗ[ℂ] KummerGroupRing :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap.comp
    (kummerGroupRingCoefficientDerivation.comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

@[simp] theorem kummerGroupRingDerivation_single
    (k : CCMRationalAdelicScaling) (c : ℂ) :
    kummerGroupRingDerivation (MonoidAlgebra.single k c) =
      MonoidAlgebra.single k (ccmRationalAdelicKummerLogWeight k * c) := by
  apply (MonoidAlgebra.coeffLinearEquiv ℂ).injective
  simp [kummerGroupRingDerivation, kummerGroupRingCoefficientDerivation,
    smul_eq_mul]

theorem kummerGroupRingDerivation_single_mul_single
    (k l : CCMRationalAdelicScaling) (a b : ℂ) :
    kummerGroupRingDerivation
        (MonoidAlgebra.single k a * MonoidAlgebra.single l b) =
      kummerGroupRingDerivation (MonoidAlgebra.single k a) *
          MonoidAlgebra.single l b +
        MonoidAlgebra.single k a *
          kummerGroupRingDerivation (MonoidAlgebra.single l b) := by
  simp only [MonoidAlgebra.single_mul_single, kummerGroupRingDerivation_single,
    ccmRationalAdelicKummerLogWeight_mul]
  rw [← MonoidAlgebra.single_add]
  congr 1
  ring

theorem kummerGroupRingDerivation_mul (F H : KummerGroupRing) :
    kummerGroupRingDerivation (F * H) =
      kummerGroupRingDerivation F * H + F * kummerGroupRingDerivation H := by
  have hpure (k : CCMRationalAdelicScaling) (a : ℂ) (H : KummerGroupRing) :
      kummerGroupRingDerivation (MonoidAlgebra.single k a * H) =
        kummerGroupRingDerivation (MonoidAlgebra.single k a) * H +
          MonoidAlgebra.single k a * kummerGroupRingDerivation H := by
    induction H using MonoidAlgebra.induction_on with
    | hM l =>
        simpa using kummerGroupRingDerivation_single_mul_single k l a 1
    | hadd H J hH hJ =>
        simp only [mul_add, map_add, hH, hJ]
        ring
    | hsmul c H hH =>
        simp only [mul_smul_comm, map_smul, hH]
        module
  induction F using MonoidAlgebra.induction_on with
  | hM k => simpa using hpure k 1 H
  | hadd F J hF hJ =>
      simp only [add_mul, map_add, hF, hJ]
      ring
  | hsmul c F hF =>
      simp only [smul_mul_assoc, map_smul, hF]
      module

def kummerGroupRingTrace : KummerGroupRing →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (1 : CCMRationalAdelicScaling)).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

local instance : DecidableEq CCMRationalAdelicScaling := Classical.decEq _

@[simp] theorem kummerGroupRingTrace_single
    (k : CCMRationalAdelicScaling) (c : ℂ) :
    kummerGroupRingTrace (MonoidAlgebra.single k c) = if k = 1 then c else 0 := by
  by_cases hk : k = 1
  · subst k
    simp [kummerGroupRingTrace]
  · have hk' : (1 : CCMRationalAdelicScaling) ≠ k := ne_comm.mpr hk
    simp [kummerGroupRingTrace, hk, hk']

theorem kummerGroupRingTrace_isTrace (F H : KummerGroupRing) :
    kummerGroupRingTrace (F * H) = kummerGroupRingTrace (H * F) := by
  rw [mul_comm]

theorem kummerGroupRingTrace_derivation (F : KummerGroupRing) :
    kummerGroupRingTrace (kummerGroupRingDerivation F) = 0 := by
  induction F using MonoidAlgebra.induction_on with
  | hM k =>
      classical
      by_cases hk1 : k = 1
      · subst k
        simp [ccmRationalAdelicKummerLogWeight]
      · simp [hk1]
  | hadd F H hF hH => simp [hF, hH]
  | hsmul c F hF => simp [hF]

/-! ## Pullback Kummer cyclic cocycle on the multiplier algebra -/

def multiplierKummerCyclicOneCocycleTuple (x : Fin 2 → Mult) : ℂ :=
  kummerGroupRingTrace
    (multiplierToKummerGroupRing (x 0) *
      kummerGroupRingDerivation (multiplierToKummerGroupRing (x 1)))

def multiplierKummerCyclicOneCocycleMultilinear :
    MultilinearMap ℂ (fun _ : Fin 2 => Mult) ℂ :=
  MultilinearMap.mk' multiplierKummerCyclicOneCocycleTuple
    (by
      intro x j a b
      fin_cases j <;>
        simp [multiplierKummerCyclicOneCocycleTuple, Function.update,
          add_mul, mul_add])
    (by
      intro x j c a
      fin_cases j
      · simp [multiplierKummerCyclicOneCocycleTuple, Function.update]
      · simp [multiplierKummerCyclicOneCocycleTuple, Function.update]
        )

def multiplierKummerCyclicOneCocycle : MC1 →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift multiplierKummerCyclicOneCocycleMultilinear

@[simp] theorem multiplierKummerCyclicOneCocycle_tprod (x : Fin 2 → Mult) :
    multiplierKummerCyclicOneCocycle (PiTensorProduct.tprod ℂ x) =
      kummerGroupRingTrace
        (multiplierToKummerGroupRing (x 0) *
          kummerGroupRingDerivation (multiplierToKummerGroupRing (x 1))) := by
  simp [multiplierKummerCyclicOneCocycle,
    multiplierKummerCyclicOneCocycleMultilinear,
    multiplierKummerCyclicOneCocycleTuple]

theorem multiplierKummerCyclicOneCocycle_cyclic (a b : Mult) :
    kummerGroupRingTrace
        (multiplierToKummerGroupRing a *
          kummerGroupRingDerivation (multiplierToKummerGroupRing b)) =
      -kummerGroupRingTrace
        (multiplierToKummerGroupRing b *
          kummerGroupRingDerivation (multiplierToKummerGroupRing a)) := by
  have hzero := kummerGroupRingTrace_derivation
    (multiplierToKummerGroupRing a * multiplierToKummerGroupRing b)
  rw [kummerGroupRingDerivation_mul, map_add,
    kummerGroupRingTrace_isTrace
      (kummerGroupRingDerivation (multiplierToKummerGroupRing a))
      (multiplierToKummerGroupRing b)] at hzero
  linear_combination hzero

theorem multiplierKummerCyclicOneCocycle_boundaryTwoPure (a b c : Mult) :
    kummerGroupRingTrace
          (multiplierToKummerGroupRing (a * b) *
            kummerGroupRingDerivation (multiplierToKummerGroupRing c)) -
        kummerGroupRingTrace
          (multiplierToKummerGroupRing a *
            kummerGroupRingDerivation (multiplierToKummerGroupRing (b * c))) +
      kummerGroupRingTrace
        (multiplierToKummerGroupRing (c * a) *
          kummerGroupRingDerivation (multiplierToKummerGroupRing b)) = 0 := by
  simp only [map_mul]
  rw [kummerGroupRingDerivation_mul, mul_add, map_add]
  have htrace :
      kummerGroupRingTrace
          (multiplierToKummerGroupRing a *
            (kummerGroupRingDerivation (multiplierToKummerGroupRing b) *
              multiplierToKummerGroupRing c)) =
        kummerGroupRingTrace
          ((multiplierToKummerGroupRing c * multiplierToKummerGroupRing a) *
            kummerGroupRingDerivation (multiplierToKummerGroupRing b)) := by
    calc
      _ = kummerGroupRingTrace
          ((multiplierToKummerGroupRing a *
              kummerGroupRingDerivation (multiplierToKummerGroupRing b)) *
            multiplierToKummerGroupRing c) := by rw [mul_assoc]
      _ = kummerGroupRingTrace
          (multiplierToKummerGroupRing c *
            (multiplierToKummerGroupRing a *
              kummerGroupRingDerivation (multiplierToKummerGroupRing b))) :=
        kummerGroupRingTrace_isTrace _ _
      _ = _ := by rw [mul_assoc]
  rw [htrace]
  simp only [mul_assoc]
  ring

abbrev MultiplierDegreeTwoCyclicSource := CyclicBarTensor ℂ Mult 2

def multiplierHochschildBoundaryTwo :
    MultiplierDegreeTwoCyclicSource →ₗ[ℂ] MC1 :=
  (cyclicBarFace (R := ℂ) (A := Mult) (0 : Fin 3) -
    cyclicBarFace (R := ℂ) (A := Mult) (1 : Fin 3)) +
  cyclicBarFace (R := ℂ) (A := Mult) (2 : Fin 3)

theorem multiplierKummerCyclicOneCocycle_comp_boundaryTwo :
    multiplierKummerCyclicOneCocycle.comp multiplierHochschildBoundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  simp only [multiplierHochschildBoundaryTwo, LinearMap.add_apply,
    LinearMap.sub_apply, cyclicBarFace_tprod, map_add, map_sub]
  rw [multiplierKummerCyclicOneCocycle_tprod,
    multiplierKummerCyclicOneCocycle_tprod,
    multiplierKummerCyclicOneCocycle_tprod]
  exact multiplierKummerCyclicOneCocycle_boundaryTwoPure (x 0) (x 1) (x 2)

/-! ## Exact prime K1 evaluation -/

@[simp] theorem multiplierToKummerGroupRing_dilUnit
    (k : CCMRationalAdelicScaling) :
    multiplierToKummerGroupRing ((dilUnit k : Multˣ) : Mult) =
      MonoidAlgebra.of ℂ CCMRationalAdelicScaling k := by
  exact multiplierToKummerGroupRing_dil k

@[simp] theorem multiplierToKummerGroupRing_dilUnit_inv
    (k : CCMRationalAdelicScaling) :
    multiplierToKummerGroupRing (↑((dilUnit k)⁻¹) : Mult) =
      MonoidAlgebra.of ℂ CCMRationalAdelicScaling k⁻¹ := by
  let f := SkewMonoidAlgebra.of MCore CCMRationalAdelicScaling
  have hinv : f.toHomUnits k⁻¹ = (f.toHomUnits k)⁻¹ := f.toHomUnits.map_inv k
  change multiplierToKummerGroupRing (↑((f.toHomUnits k)⁻¹) : Mult) = _
  rw [← hinv]
  exact multiplierToKummerGroupRing_dil k⁻¹

@[simp] theorem kummerGroupRingDerivation_of
    (k : CCMRationalAdelicScaling) :
    kummerGroupRingDerivation
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling k) =
      ccmRationalAdelicKummerLogWeight k •
        MonoidAlgebra.of ℂ CCMRationalAdelicScaling k := by
  simp [MonoidAlgebra.of_apply, smul_eq_mul]

theorem kummerGroupRingPair_inv_of
    (k : CCMRationalAdelicScaling) :
    kummerGroupRingTrace
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling k⁻¹ *
          kummerGroupRingDerivation
            (MonoidAlgebra.of ℂ CCMRationalAdelicScaling k)) =
      ccmRationalAdelicKummerLogWeight k := by
  simp [MonoidAlgebra.of_apply]

theorem multiplierKummerCyclicOneCocycle_primeKOneCycle
    (p : Nat.Primes) :
    multiplierKummerCyclicOneCocycle (primeKOneCycle p) =
      (Real.log (p : ℝ) : ℂ) := by
  rw [primeKOneCycle, multiplierKummerCyclicOneCocycle_tprod]
  change kummerGroupRingTrace
      (multiplierToKummerGroupRing
          (↑((dilUnit (ccmRationalAdelicPrimeScaling p))⁻¹) : Mult) *
        kummerGroupRingDerivation
          (multiplierToKummerGroupRing
            ((dilUnit (ccmRationalAdelicPrimeScaling p) : Multˣ) : Mult))) = _
  rw [multiplierToKummerGroupRing_dilUnit_inv,
    multiplierToKummerGroupRing_dilUnit,
    kummerGroupRingPair_inv_of,
    ccmRationalAdelicKummerLogWeight_primeScaling]

/-! ## Genuine Hochschild-one homology class -/

theorem mBoundaryOne_comp_multiplierHochschildBoundaryTwo :
    mBoundaryOne.comp multiplierHochschildBoundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x : 1
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  simp only [multiplierHochschildBoundaryTwo, LinearMap.add_apply,
    LinearMap.sub_apply, cyclicBarFace_tprod, map_add, map_sub]
  rw [mBoundaryOne_tprod', mBoundaryOne_tprod', mBoundaryOne_tprod']
  change
    ((x 0 * x 1) * x 2 - x 2 * (x 0 * x 1)) -
        (x 0 * (x 1 * x 2) - (x 1 * x 2) * x 0) +
      ((x 2 * x 0) * x 1 - x 1 * (x 2 * x 0)) = 0
  noncomm_ring

def multiplierHochschildOneCycles : Submodule ℂ MC1 :=
  LinearMap.ker mBoundaryOne

theorem multiplierHochschildBoundaryTwo_range_le_cycles :
    LinearMap.range multiplierHochschildBoundaryTwo ≤
      multiplierHochschildOneCycles := by
  rintro _ ⟨x, rfl⟩
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun
    mBoundaryOne_comp_multiplierHochschildBoundaryTwo x
  simpa using h

def multiplierHochschildOneBoundaries :
    Submodule ℂ multiplierHochschildOneCycles :=
  (LinearMap.range multiplierHochschildBoundaryTwo).comap
    multiplierHochschildOneCycles.subtype

abbrev MultiplierHochschildOneHomology :=
  multiplierHochschildOneCycles ⧸ multiplierHochschildOneBoundaries

def primeKOneHochschildCycle (p : Nat.Primes) :
    multiplierHochschildOneCycles :=
  ⟨primeKOneCycle p, LinearMap.mem_ker.mpr (primeKOneCycle_boundary p)⟩

def primeKOneHochschildClass (p : Nat.Primes) :
    MultiplierHochschildOneHomology :=
  multiplierHochschildOneBoundaries.mkQ (primeKOneHochschildCycle p)

def multiplierKummerCycleRegulator :
    multiplierHochschildOneCycles →ₗ[ℂ] ℂ :=
  multiplierKummerCyclicOneCocycle.comp multiplierHochschildOneCycles.subtype

theorem multiplierHochschildOneBoundaries_le_regulator_ker :
    multiplierHochschildOneBoundaries ≤
      LinearMap.ker multiplierKummerCycleRegulator := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun
    multiplierKummerCyclicOneCocycle_comp_boundaryTwo y
  calc
    multiplierKummerCycleRegulator x =
        multiplierKummerCyclicOneCocycle
          (multiplierHochschildBoundaryTwo y) := by
      simpa [multiplierKummerCycleRegulator] using
        congrArg multiplierKummerCyclicOneCocycle hy.symm
    _ = 0 := by simpa using h

def multiplierKummerHomologyRegulator :
    MultiplierHochschildOneHomology →ₗ[ℂ] ℂ :=
  multiplierHochschildOneBoundaries.liftQ multiplierKummerCycleRegulator
    multiplierHochschildOneBoundaries_le_regulator_ker

@[simp] theorem multiplierKummerHomologyRegulator_primeClass
    (p : Nat.Primes) :
    multiplierKummerHomologyRegulator (primeKOneHochschildClass p) =
      (Real.log (p : ℝ) : ℂ) := by
  change multiplierKummerCyclicOneCocycle (primeKOneCycle p) = _
  exact multiplierKummerCyclicOneCocycle_primeKOneCycle p

theorem primeLogComplex_ne_zero (p : Nat.Primes) :
    (Real.log (p : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one))

theorem primeKOneHochschildClass_ne_zero (p : Nat.Primes) :
    primeKOneHochschildClass p ≠ 0 := by
  intro hzero
  have hread := congrArg multiplierKummerHomologyRegulator hzero
  rw [multiplierKummerHomologyRegulator_primeClass, map_zero] at hread
  exact primeLogComplex_ne_zero p hread

theorem primeKOneCycle_not_mem_boundaryRange (p : Nat.Primes) :
    primeKOneCycle p ∉ LinearMap.range multiplierHochschildBoundaryTwo := by
  rintro ⟨x, hx⟩
  have h := congrArg multiplierKummerCyclicOneCocycle hx
  rw [multiplierKummerCyclicOneCocycle_primeKOneCycle] at h
  have hboundary := LinearMap.congr_fun
    multiplierKummerCyclicOneCocycle_comp_boundaryTwo x
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at hboundary
  rw [hboundary] at h
  exact primeLogComplex_ne_zero p h.symm

end
end RouteRMultiplierKOne

/-! ## Route-R-facing exported endpoints -/

/-- Unital rational-scaling multiplier algebra of the actual adelic Bruhat coefficient core. -/
abbrev CCMRationalAdelicPrimeMultiplierAlgebra :=
  RouteRMultiplierKOne.Mult

/-- Degree-one cyclic-bar source of the multiplier algebra. -/
abbrev CCMRationalAdelicPrimeMultiplierDegreeOneSource :=
  RouteRMultiplierKOne.MC1

/-- Genuine Hochschild-one homology of the multiplier source. -/
abbrev CCMRationalAdelicPrimeMultiplierHochschildOneHomology :=
  RouteRMultiplierKOne.MultiplierHochschildOneHomology

/-- Genuine ordinary-prime K1 cycle `u_p⁻¹ ⊗ u_p`. -/
noncomputable def ccmRationalAdelicPrimeMultiplierKOneCycle (p : Nat.Primes) :
    CCMRationalAdelicPrimeMultiplierDegreeOneSource :=
  RouteRMultiplierKOne.primeKOneCycle p

/-- The genuine multiplier K1 cycle has zero Hochschild boundary. -/
theorem ccmRationalAdelicPrimeMultiplierKOneCycle_boundary_eq_zero
    (p : Nat.Primes) :
    RouteRMultiplierKOne.mBoundaryOne
        (ccmRationalAdelicPrimeMultiplierKOneCycle p) = 0 :=
  RouteRMultiplierKOne.primeKOneCycle_boundary p

/-- Unconditional chain law `b₁ b₂ = 0` on the multiplier source. -/
theorem ccmRationalAdelicPrimeMultiplierHochschild_boundary_boundary :
    RouteRMultiplierKOne.mBoundaryOne.comp
        RouteRMultiplierKOne.multiplierHochschildBoundaryTwo = 0 :=
  RouteRMultiplierKOne.mBoundaryOne_comp_multiplierHochschildBoundaryTwo

/-- Homology class of the retained ordinary-prime multiplier cycle. -/
noncomputable def ccmRationalAdelicPrimeMultiplierKOneHomologyClass (p : Nat.Primes) :
    CCMRationalAdelicPrimeMultiplierHochschildOneHomology :=
  RouteRMultiplierKOne.primeKOneHochschildClass p

/-- Kummer regulator descended to genuine Hochschild-one homology. -/
noncomputable def ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator :
    CCMRationalAdelicPrimeMultiplierHochschildOneHomology →ₗ[ℂ] ℂ :=
  RouteRMultiplierKOne.multiplierKummerHomologyRegulator

/-- Exact prime value of the descended multiplier Kummer regulator. -/
@[simp] theorem ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator_primeClass
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator
        (ccmRationalAdelicPrimeMultiplierKOneHomologyClass p) =
      (Real.log (p : ℝ) : ℂ) :=
  RouteRMultiplierKOne.multiplierKummerHomologyRegulator_primeClass p

/-- Retained ordinary-prime multiplier class is nonzero in genuine Hochschild homology. -/
theorem ccmRationalAdelicPrimeMultiplierKOneHomologyClass_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeMultiplierKOneHomologyClass p ≠ 0 :=
  RouteRMultiplierKOne.primeKOneHochschildClass_ne_zero p

/-- Prime K1 cycle cannot be a degree-two Hochschild boundary. -/
theorem ccmRationalAdelicPrimeMultiplierKOneCycle_not_boundary
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeMultiplierKOneCycle p ∉
      LinearMap.range RouteRMultiplierKOne.multiplierHochschildBoundaryTwo :=
  RouteRMultiplierKOne.primeKOneCycle_not_mem_boundaryRange p

end RHTower
