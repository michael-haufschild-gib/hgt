import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicScalingAction

/-!
# The actual nonunital rational adeles-class-space crossed product

The CCM algebra `𝒮(𝔸_ℚ) ⋊ ℚˣ` is nonunital.  This file constructs it exactly as finite-support
families `ℚˣ →₀ 𝒮(𝔸_ℚ)` with twisted convolution.  All distributive and associative laws are
proved directly from the scaling action; no unital function-algebra surrogate is introduced.

Only after the nonunital algebra is complete do we form its minimal unitization, exactly as in
the CCM cyclic-module construction.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling

/-- Finite-support algebraic CCM crossed product with the actual Bruhat--Schwartz core. -/
abbrev CCMRationalAdelicAlgebraicCrossedProduct :=
  Scale →₀ Core

/-- Twisted convolution on finite-support coefficient families. -/
def ccmRationalAdelicCrossedProductMul
    (F H : CCMRationalAdelicAlgebraicCrossedProduct) :
    CCMRationalAdelicAlgebraicCrossedProduct :=
  F.sum fun k a =>
    H.sum fun l b =>
      Finsupp.single (k * l) (a * (k • b))

instance : Mul CCMRationalAdelicAlgebraicCrossedProduct :=
  ⟨ccmRationalAdelicCrossedProductMul⟩

@[simp]
theorem ccmRationalAdelicCrossedProduct_single_mul_single
    (k l : Scale) (a b : Core) :
    (Finsupp.single k a : CCMRationalAdelicAlgebraicCrossedProduct) *
        Finsupp.single l b =
      Finsupp.single (k * l) (a * (k • b)) := by
  classical
  change ccmRationalAdelicCrossedProductMul
      (Finsupp.single k a) (Finsupp.single l b) = _
  simp [ccmRationalAdelicCrossedProductMul]

@[simp]
theorem ccmRationalAdelicCrossedProduct_zero_mul
    (F : CCMRationalAdelicAlgebraicCrossedProduct) :
    0 * F = 0 := by
  classical
  change ccmRationalAdelicCrossedProductMul 0 F = 0
  simp [ccmRationalAdelicCrossedProductMul]

@[simp]
theorem ccmRationalAdelicCrossedProduct_mul_zero
    (F : CCMRationalAdelicAlgebraicCrossedProduct) :
    F * 0 = 0 := by
  classical
  change ccmRationalAdelicCrossedProductMul F 0 = 0
  simp [ccmRationalAdelicCrossedProductMul]

theorem ccmRationalAdelicCrossedProduct_add_mul
    (F H J : CCMRationalAdelicAlgebraicCrossedProduct) :
    (F + H) * J = F * J + H * J := by
  classical
  change ccmRationalAdelicCrossedProductMul (F + H) J =
    ccmRationalAdelicCrossedProductMul F J +
      ccmRationalAdelicCrossedProductMul H J
  unfold ccmRationalAdelicCrossedProductMul
  rw [Finsupp.sum_add_index']
  · intro k
    simp
  · intro k a b
    simp_rw [ccmRationalAdelicBruhat_add_mul]
    simp only [Finsupp.single_add, Finsupp.sum_add]

theorem ccmRationalAdelicCrossedProduct_mul_add
    (F H J : CCMRationalAdelicAlgebraicCrossedProduct) :
    F * (H + J) = F * H + F * J := by
  classical
  change ccmRationalAdelicCrossedProductMul F (H + J) =
    ccmRationalAdelicCrossedProductMul F H +
      ccmRationalAdelicCrossedProductMul F J
  unfold ccmRationalAdelicCrossedProductMul
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro k a
  rw [Finsupp.sum_add_index']
  · intro l
    simp
  · intro l b c
    rw [smul_add, ccmRationalAdelicBruhat_mul_add,
      Finsupp.single_add]

/-- Associativity on three crossed-product monomials. -/
theorem ccmRationalAdelicCrossedProduct_single_mul_assoc
    (k l m : Scale) (a b c : Core) :
    ((Finsupp.single k a : CCMRationalAdelicAlgebraicCrossedProduct) *
        Finsupp.single l b) * Finsupp.single m c =
      Finsupp.single k a *
        (Finsupp.single l b * Finsupp.single m c) := by
  classical
  simp only [ccmRationalAdelicCrossedProduct_single_mul_single]
  rw [mul_assoc, ccmRationalAdelicBruhatScaling_map_mul, mul_smul]
  congr 1
  exact ccmRationalAdelicBruhat_mul_assoc _ _ _

/-- Associativity of twisted convolution on the full finite-support source. -/
theorem ccmRationalAdelicCrossedProduct_mul_assoc
    (F H J : CCMRationalAdelicAlgebraicCrossedProduct) :
    (F * H) * J = F * (H * J) := by
  have hpure₂ (k l : Scale) (a b : Core)
      (J : CCMRationalAdelicAlgebraicCrossedProduct) :
      (Finsupp.single k a * Finsupp.single l b) * J =
        Finsupp.single k a * (Finsupp.single l b * J) := by
    induction J using Finsupp.induction with
    | zero => simp
    | @single_add m c J hm hc hJ =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProduct_mul_add, hJ]
        congr 1
        exact ccmRationalAdelicCrossedProduct_single_mul_assoc
          k l m a b c
  have hpure (k : Scale) (a : Core)
      (H J : CCMRationalAdelicAlgebraicCrossedProduct) :
      (Finsupp.single k a * H) * J =
        Finsupp.single k a * (H * J) := by
    induction H using Finsupp.induction with
    | zero => simp
    | @single_add l b H hl hb hH =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProduct_add_mul,
          ccmRationalAdelicCrossedProduct_add_mul,
          ccmRationalAdelicCrossedProduct_mul_add, hpure₂, hH]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedProduct_add_mul, hpure, hF]

instance : NonUnitalRing CCMRationalAdelicAlgebraicCrossedProduct where
  zero_mul := ccmRationalAdelicCrossedProduct_zero_mul
  mul_zero := ccmRationalAdelicCrossedProduct_mul_zero
  left_distrib := ccmRationalAdelicCrossedProduct_mul_add
  right_distrib := ccmRationalAdelicCrossedProduct_add_mul
  mul_assoc := ccmRationalAdelicCrossedProduct_mul_assoc

instance : SMulCommClass ℂ CCMRationalAdelicAlgebraicCrossedProduct
    CCMRationalAdelicAlgebraicCrossedProduct where
  smul_comm z F H := by
    change z • (F * H) = F * (z • H)
    have hpure (k : Scale) (a : Core)
        (H : CCMRationalAdelicAlgebraicCrossedProduct) :
        z • (Finsupp.single k a * H) =
          Finsupp.single k a * (z • H) := by
      induction H using Finsupp.induction with
      | zero => simp
      | @single_add l b H hl hb hH =>
          rw [ccmRationalAdelicCrossedProduct_mul_add, smul_add,
            smul_add, ccmRationalAdelicCrossedProduct_mul_add, hH]
          congr 1
          simp only [Finsupp.smul_single,
            ccmRationalAdelicCrossedProduct_single_mul_single]
          congr 1
          have hk : k • (z • b) = z • (k • b) :=
            (ccmRationalAdelicBruhatScaling k).map_smul z b
          rw [hk]
          exact smul_comm z a (k • b)
    induction F using Finsupp.induction with
    | zero => simp
    | @single_add k a F hk ha hF =>
        rw [ccmRationalAdelicCrossedProduct_add_mul, smul_add,
          ccmRationalAdelicCrossedProduct_add_mul, hpure, hF]

instance : IsScalarTower ℂ CCMRationalAdelicAlgebraicCrossedProduct
    CCMRationalAdelicAlgebraicCrossedProduct where
  smul_assoc z F H := by
    change (z • F) * H = z • (F * H)
    have hpure (k : Scale) (a : Core)
        (H : CCMRationalAdelicAlgebraicCrossedProduct) :
        (z • Finsupp.single k a) * H =
          z • (Finsupp.single k a * H) := by
      induction H using Finsupp.induction with
      | zero => simp
      | @single_add l b H hl hb hH =>
          rw [ccmRationalAdelicCrossedProduct_mul_add,
            ccmRationalAdelicCrossedProduct_mul_add, smul_add, hH]
          congr 1
          simp only [Finsupp.smul_single,
            ccmRationalAdelicCrossedProduct_single_mul_single]
          congr 1
          exact smul_assoc z a (k • b)
    induction F using Finsupp.induction with
    | zero => simp
    | @single_add k a F hk ha hF =>
        rw [smul_add, ccmRationalAdelicCrossedProduct_add_mul,
          ccmRationalAdelicCrossedProduct_add_mul, smul_add, hpure, hF]

/-- Source algebra used by the cyclic module: minimal unitization of the exact nonunital CCM
crossed product. -/
abbrev CCMRationalAdelicCyclicSourceAlgebra :=
  Unitization ℂ CCMRationalAdelicAlgebraicCrossedProduct

@[simp]
theorem ccmRationalAdelicCyclicSource_inr_mul
    (F H : CCMRationalAdelicAlgebraicCrossedProduct) :
    (F : CCMRationalAdelicCyclicSourceAlgebra) *
      (H : CCMRationalAdelicCyclicSourceAlgebra) =
      (F * H : CCMRationalAdelicAlgebraicCrossedProduct) :=
  (Unitization.inr_mul ℂ F H).symm

end RHTower
end GaloisForLFunctions
