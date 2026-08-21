/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinBounds

/-!
# The two-variable Wasserstein mean

For strictly positive `a, b` in a unital C⋆-algebra and `t ∈ ℝ`, Hwang–Kim and Kim–Mer–Pálfia
(arXiv:2607.29142, §6) define

`a ◇_t b = [1 ∇_t (a⁻¹ # b)] a [1 ∇_t (a⁻¹ # b)]`,   `1 ∇_t g = (1-t) + t g`,

and prove that it is the unique strictly positive solution of the two-point Wasserstein equation
`(1-t)(a # x⁻¹) + t (b # x⁻¹) = 1` whenever the parameter `1 ∇_t (a⁻¹ # b)` is strictly positive.

The mechanism is purely Riccati-theoretic: writing `g = a⁻¹ # b` (so `g a g = b`) and
`m = 1 ∇_t g`, the element `m⁻¹` solves `m⁻¹ a⁻¹ m⁻¹ = (m a m)⁻¹`, hence `a # x⁻¹ = m⁻¹`, while
`g m⁻¹ = m⁻¹ g` solves the Riccati equation for `b`, hence `b # x⁻¹ = g m⁻¹`; adding gives
`(1-t) m⁻¹ + t g m⁻¹ = m m⁻¹ = 1`.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a b : A} {t : ℝ}

/-- The parameter operator `1 ∇_t (a⁻¹ # b) = (1-t) + t (a⁻¹ # b)`. -/
def wassParam (t : ℝ) (a b : A) : A := (1 - t) • (1 : A) + t • gm a⁻¹ʳ b

/-- The **two-variable Wasserstein mean** `a ◇_t b = [1 ∇_t (a⁻¹ # b)] a [1 ∇_t (a⁻¹ # b)]`. -/
def wass2 (t : ℝ) (a b : A) : A := wassParam t a b * a * wassParam t a b

@[inherit_doc] scoped notation:70 a " ◇[" t "] " b => wass2 t a b

/-! ### The Riccati identity for `a⁻¹ # b` -/

/-- `(a⁻¹ # b) a (a⁻¹ # b) = b`. -/
lemma gmInv_riccati (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    gm a⁻¹ʳ b * a * gm a⁻¹ʳ b = b := by
  have h := gm_riccati ha.ringInverse hb
  rwa [Ring.inverse_inverse ha.isUnit] at h

lemma gmInv_strictlyPositive (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (gm a⁻¹ʳ b) := gm_strictlyPositive ha.ringInverse hb

/-! ### Basic properties of the parameter -/

lemma wassParam_isSelfAdjoint : IsSelfAdjoint (wassParam t a b) := by
  refine IsSelfAdjoint.add ?_ ?_
  · exact IsSelfAdjoint.smul (star_trivial _) (IsSelfAdjoint.one A)
  · exact IsSelfAdjoint.smul (star_trivial _) (gm_nonneg _ _).isSelfAdjoint

lemma commute_wassParam_gmInv : Commute (wassParam t a b) (gm a⁻¹ʳ b) := by
  unfold wassParam Commute SemiconjBy
  simp [add_mul, mul_add]

/-- For `t ∈ [0,1]` the parameter is automatically strictly positive. -/
lemma wassParam_isStrictlyPositive_of_mem_Icc (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (wassParam t a b) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with h | h
  · simp [wassParam, ← h]
  · refine IsStrictlyPositive.nonneg_add ?_ ((gmInv_strictlyPositive ha hb).smul h)
    exact smul_nonneg (by linarith) zero_le_one

lemma wass2_isStrictlyPositive (hM : IsStrictlyPositive (wassParam t a b))
    (ha : IsStrictlyPositive a) : IsStrictlyPositive (wass2 t a b) :=
  IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint a _ hM.isUnit
    wassParam_isSelfAdjoint ha

lemma wass2_ringInverse (hM : IsStrictlyPositive (wassParam t a b)) (ha : IsStrictlyPositive a) :
    (wass2 t a b)⁻¹ʳ = (wassParam t a b)⁻¹ʳ * a⁻¹ʳ * (wassParam t a b)⁻¹ʳ := by
  unfold wass2
  rw [Ring.inverse_mul (Or.inl (hM.isUnit.mul ha.isUnit)), Ring.inverse_mul (Or.inl hM.isUnit),
    mul_assoc]

/-! ### The Riccati solutions -/

/-- `a # (a ◇_t b)⁻¹ = (1 ∇_t (a⁻¹ # b))⁻¹`. -/
theorem gm_left_wass2 (hM : IsStrictlyPositive (wassParam t a b)) (ha : IsStrictlyPositive a) :
    gm a (wass2 t a b)⁻¹ʳ = (wassParam t a b)⁻¹ʳ :=
  (gm_unique ha hM.ringInverse.nonneg (wass2_ringInverse hM ha).symm).symm

/-- The auxiliary element `(a⁻¹ # b) (1 ∇_t (a⁻¹ # b))⁻¹` is nonnegative. -/
lemma gmInv_mul_wassParam_ringInverse_nonneg (hM : IsStrictlyPositive (wassParam t a b)) :
    0 ≤ gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ := by
  have hc : Commute (wassParam t a b ^ (-(1/2) : ℝ)) (gm a⁻¹ʳ b) := by
    have hcm : Commute (wassParam t a b) (gm a⁻¹ʳ b) := commute_wassParam_gmInv
    simpa [CFC.rpow_def] using hcm.cfc_nnreal (fun x : ℝ≥0 => x ^ (-(1/2) : ℝ))
  have hZ : wassParam t a b ^ (-(1/2) : ℝ) * gm a⁻¹ʳ b * wassParam t a b ^ (-(1/2) : ℝ)
      = gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ := by
    rw [hc.eq, mul_assoc, rpow_neg_half_mul_rpow_neg_half hM]
  rw [← hZ]
  exact nonneg_conjugate (isSelfAdjoint_rpow _ _) (gm_nonneg _ _)

/-- `b # (a ◇_t b)⁻¹ = (a⁻¹ # b) (1 ∇_t (a⁻¹ # b))⁻¹`. -/
theorem gm_right_wass2 (hM : IsStrictlyPositive (wassParam t a b)) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    gm b (wass2 t a b)⁻¹ʳ = gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ := by
  have hg : IsStrictlyPositive (gm a⁻¹ʳ b) := gmInv_strictlyPositive ha hb
  have hbinv : b⁻¹ʳ = (gm a⁻¹ʳ b)⁻¹ʳ * a⁻¹ʳ * (gm a⁻¹ʳ b)⁻¹ʳ := by
    have h2 : (gm a⁻¹ʳ b * a * gm a⁻¹ʳ b)⁻¹ʳ
        = (gm a⁻¹ʳ b)⁻¹ʳ * a⁻¹ʳ * (gm a⁻¹ʳ b)⁻¹ʳ := by
      rw [Ring.inverse_mul (Or.inl (hg.isUnit.mul ha.isUnit)), Ring.inverse_mul (Or.inl hg.isUnit),
        mul_assoc]
    rw [← h2, gmInv_riccati ha hb]
  have hcinv : (wassParam t a b)⁻¹ʳ * gm a⁻¹ʳ b = gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ := by
    calc (wassParam t a b)⁻¹ʳ * gm a⁻¹ʳ b
        = (wassParam t a b)⁻¹ʳ * (gm a⁻¹ʳ b * wassParam t a b) * (wassParam t a b)⁻¹ʳ := by
          rw [mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hM.isUnit, mul_one]
      _ = (wassParam t a b)⁻¹ʳ * (wassParam t a b * gm a⁻¹ʳ b) * (wassParam t a b)⁻¹ʳ := by
          rw [← commute_wassParam_gmInv.eq]
      _ = gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hM.isUnit, one_mul]
  have hcL : ∀ y : A, gm a⁻¹ʳ b * ((gm a⁻¹ʳ b)⁻¹ʳ * y) = y := fun y =>
    Ring.mul_inverse_cancel_left _ y hg.isUnit
  have hcR : ∀ y : A, (gm a⁻¹ʳ b)⁻¹ʳ * (gm a⁻¹ʳ b * y) = y := fun y =>
    Ring.inverse_mul_cancel_left _ y hg.isUnit
  refine (gm_unique hb (gmInv_mul_wassParam_ringInverse_nonneg hM) ?_).symm
  rw [hbinv, wass2_ringInverse hM ha]
  nth_rewrite 1 [← hcinv]
  simp only [mul_assoc, hcL, hcR]

/-! ### The two-variable Wasserstein equation -/

/-- **Existence**: `a ◇_t b` solves `(1-t)(a # x⁻¹) + t (b # x⁻¹) = 1`. -/
theorem wass2_solves (hM : IsStrictlyPositive (wassParam t a b)) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    (1 - t) • gm a (wass2 t a b)⁻¹ʳ + t • gm b (wass2 t a b)⁻¹ʳ = 1 := by
  rw [gm_left_wass2 hM ha, gm_right_wass2 hM ha hb]
  have : (1 - t) • (wassParam t a b)⁻¹ʳ + t • (gm a⁻¹ʳ b * (wassParam t a b)⁻¹ʳ)
      = wassParam t a b * (wassParam t a b)⁻¹ʳ := by
    unfold wassParam
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  rw [this, Ring.mul_inverse_cancel _ hM.isUnit]

/-! ### The explicit formulas -/

/-- `1 ∇_t (a⁻¹ # b) = a^{-1/2} [(1-t) a + t (a^{1/2} b a^{1/2})^{1/2}] a^{-1/2}`. -/
lemma wassParam_eq_conj (ha : IsStrictlyPositive a) (b : A) :
    wassParam t a b = a ^ (-(1/2) : ℝ)
      * ((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))) * a ^ (-(1/2) : ℝ) := by
  unfold wassParam
  rw [gm_ringInverse_left ha, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, rpow_neg_half_mul_self_mul_rpow_neg_half ha]

/-- Cancelling `a` between two `a^{-1/2}`-conjugations. -/
lemma conj_mul_self_mul_conj (ha : IsStrictlyPositive a) (u v : A) :
    (a ^ (-(1/2) : ℝ) * u * a ^ (-(1/2) : ℝ)) * a * (a ^ (-(1/2) : ℝ) * v * a ^ (-(1/2) : ℝ))
      = a ^ (-(1/2) : ℝ) * (u * v) * a ^ (-(1/2) : ℝ) := by
  have hkey : ∀ z : A, a ^ (-(1/2) : ℝ) * (a * (a ^ (-(1/2) : ℝ) * z)) = z := fun z => by
    rw [← mul_assoc, ← mul_assoc, rpow_neg_half_mul_self_mul_rpow_neg_half ha, one_mul]
  simp only [mul_assoc, hkey]

/-- The Bhatia–Jain–Lim closed form
`a ◇_t b = a^{-1/2} [(1-t) a + t (a^{1/2} b a^{1/2})^{1/2}]² a^{-1/2}`. -/
theorem wass2_eq_conj (ha : IsStrictlyPositive a) (b : A) :
    wass2 t a b = a ^ (-(1/2) : ℝ)
      * (((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))
        * ((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))) * a ^ (-(1/2) : ℝ) := by
  unfold wass2
  rw [wassParam_eq_conj ha, conj_mul_self_mul_conj ha]

/-- The expansion `a ◇_t b = (1-t)² a + t² b + t(1-t) [a g + g a]`, `g = a⁻¹ # b`. -/
theorem wass2_expansion (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    wass2 t a b = ((1 - t) * (1 - t)) • a + (t * t) • b
      + (t * (1 - t)) • (a * gm a⁻¹ʳ b + gm a⁻¹ʳ b * a) := by
  have hR : gm a⁻¹ʳ b * a * gm a⁻¹ʳ b = b := gmInv_riccati ha hb
  unfold wass2 wassParam
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hR]
  module

/-! ### Symmetry -/

/-- **Lemma 6.10**: `a ◇_t b = b ◇_{1-t} a`. -/
theorem wass2_symm (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    wass2 t a b = wass2 (1 - t) b a := by
  have hg : IsStrictlyPositive (gm a⁻¹ʳ b) := gmInv_strictlyPositive ha hb
  have hswap : gm b⁻¹ʳ a = (gm a⁻¹ʳ b)⁻¹ʳ := by
    rw [gm_ringInverse ha.ringInverse hb, Ring.inverse_inverse ha.isUnit]
    exact gm_comm hb.ringInverse ha
  have hM : wassParam (1 - t) b a * gm a⁻¹ʳ b = wassParam t a b := by
    unfold wassParam
    rw [hswap, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
      Ring.inverse_mul_cancel _ hg.isUnit]
    rw [show (1 : ℝ) - (1 - t) = t by ring]
    abel
  have hM' : gm a⁻¹ʳ b * wassParam (1 - t) b a = wassParam t a b := by
    unfold wassParam
    rw [hswap, mul_add, mul_smul_comm, mul_smul_comm, mul_one,
      Ring.mul_inverse_cancel _ hg.isUnit]
    rw [show (1 : ℝ) - (1 - t) = t by ring]
    abel
  unfold wass2
  have hb' : wassParam (1 - t) b a * b * wassParam (1 - t) b a
      = wassParam (1 - t) b a * (gm a⁻¹ʳ b * a * gm a⁻¹ʳ b) * wassParam (1 - t) b a := by
    rw [gmInv_riccati ha hb]
  rw [hb']
  calc wassParam t a b * a * wassParam t a b
      = (wassParam (1 - t) b a * gm a⁻¹ʳ b) * a * (gm a⁻¹ʳ b * wassParam (1 - t) b a) := by
        rw [hM, hM']
    _ = wassParam (1 - t) b a * (gm a⁻¹ʳ b * a * gm a⁻¹ʳ b) * wassParam (1 - t) b a := by
        simp only [mul_assoc]

/-! ### Uniqueness -/

lemma ringInverse_rpow_half (ha : IsStrictlyPositive a) :
    (a ^ (1/2 : ℝ))⁻¹ʳ = a ^ (-(1/2) : ℝ) := by
  rw [← mul_one ((a ^ (1/2 : ℝ))⁻¹ʳ),
    Ring.inverse_mul_eq_iff_eq_mul _ _ _ (ha.rpow a _).isUnit,
    rpow_half_mul_rpow_neg_half ha]

/-- **Uniqueness** in the two-variable Wasserstein equation. -/
theorem wass2_unique (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) {x : A}
    (hx : IsStrictlyPositive x)
    (hxe : (1 - t) • gm a x⁻¹ʳ + t • gm b x⁻¹ʳ = 1) : x = wass2 t a b := by
  have hPsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ)) := isSelfAdjoint_rpow a _
  have hPu : IsUnit (a ^ (-(1/2) : ℝ)) := (ha.rpow a _).isUnit
  have hPstar : star (a ^ (-(1/2) : ℝ)) = a ^ (-(1/2) : ℝ) := hPsa.star_eq
  -- the conjugated data
  have hY : IsStrictlyPositive (a ^ (-(1/2) : ℝ) * x⁻¹ʳ * a ^ (-(1/2) : ℝ)) :=
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _ hPu hPsa hx.ringInverse
  have hZ : IsStrictlyPositive (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) :=
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _ hPu hPsa hb
  set Y := a ^ (-(1/2) : ℝ) * x⁻¹ʳ * a ^ (-(1/2) : ℝ) with hYdef
  set Z := a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) with hZdef
  set R := CFC.sqrt Y with hRdef
  have hRpos : IsStrictlyPositive R := hY.sqrt _
  have hRR : R * R = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hYinv : Y⁻¹ʳ = R⁻¹ʳ * R⁻¹ʳ := by
    rw [← hRR, Ring.inverse_mul (Or.inl hRpos.isUnit)]
  -- conjugating the equation by `a^{-1/2}`
  have hcA : a ^ (-(1/2) : ℝ) * gm a x⁻¹ʳ * a ^ (-(1/2) : ℝ) = R := by
    have hc := gm_conjugate (m := a ^ (-(1/2) : ℝ)) hPu ha hx.ringInverse
    rw [hPstar] at hc
    rw [hc, rpow_neg_half_mul_self_mul_rpow_neg_half ha, gm_one_left, hRdef, hYdef]
  have hcB : a ^ (-(1/2) : ℝ) * gm b x⁻¹ʳ * a ^ (-(1/2) : ℝ) = gm Z Y := by
    have hc := gm_conjugate (m := a ^ (-(1/2) : ℝ)) hPu hb hx.ringInverse
    rw [hPstar] at hc
    rw [hc, hZdef, hYdef]
  have hconj : (1 - t) • R + t • gm Z Y = a⁻¹ʳ := by
    have hL := congrArg (fun z : A => a ^ (-(1/2) : ℝ) * z * a ^ (-(1/2) : ℝ)) hxe
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one] at hL
    rw [hcA, hcB, rpow_neg_half_mul_rpow_neg_half ha] at hL
    exact hL
  -- the Riccati equation for the second geometric mean
  have hV : gm Z Y * Y⁻¹ʳ * gm Z Y = Z := by
    rw [gm_comm hZ hY]
    exact gm_riccati hY hZ
  -- squaring
  set D := R⁻¹ʳ - (1 - t) • a with hDdef
  have hCnn : (0 : A) ≤ a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ) :=
    nonneg_conjugate (isSelfAdjoint_rpow a _) hb.nonneg
  have hE : t • gm Z Y = a⁻¹ʳ - (1 - t) • R := by rw [← hconj]; abel
  have h1 : a * (a⁻¹ʳ - (1 - t) • R) * R⁻¹ʳ = D := by
    rw [mul_sub, sub_mul, Ring.mul_inverse_cancel _ ha.isUnit, one_mul, mul_smul_comm,
      smul_mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hRpos.isUnit, mul_one]
  have h2 : R⁻¹ʳ * (a⁻¹ʳ - (1 - t) • R) * a = D := by
    rw [mul_sub, sub_mul, mul_assoc, Ring.inverse_mul_cancel _ ha.isUnit, mul_one,
      mul_smul_comm, smul_mul_assoc, Ring.inverse_mul_cancel _ hRpos.isUnit, one_mul]
  have hD2 : D * D = (t * t) • (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)) := by
    have hmid : a * gm Z Y * Y⁻¹ʳ * gm Z Y * a = a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ) := by
      rw [show a * gm Z Y * Y⁻¹ʳ * gm Z Y * a = a * (gm Z Y * Y⁻¹ʳ * gm Z Y) * a by
        simp only [mul_assoc], hV, hZdef]
      rw [show a * (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) * a
          = (a * a ^ (-(1/2) : ℝ)) * b * (a ^ (-(1/2) : ℝ) * a) by simp only [mul_assoc],
        mul_rpow_neg_half ha, rpow_neg_half_mul_self ha]
    have hstep : a * (t • gm Z Y) * Y⁻¹ʳ * (t • gm Z Y) * a
        = (t * t) • (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)) := by
      simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
      rw [hmid]
    rw [hE] at hstep
    rw [← hstep, hYinv]
    calc D * D = (a * (a⁻¹ʳ - (1 - t) • R) * R⁻¹ʳ) * (R⁻¹ʳ * (a⁻¹ʳ - (1 - t) • R) * a) := by
          rw [h1, h2]
      _ = a * (a⁻¹ʳ - (1 - t) • R) * (R⁻¹ʳ * R⁻¹ʳ) * (a⁻¹ʳ - (1 - t) • R) * a := by
          simp only [mul_assoc]
  -- sign analysis
  have hDsq : D * D = (t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))
      * (t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))) := by
    rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self _ hCnn, hD2]
  have hRinv_nonneg : (0 : A) ≤ R⁻¹ʳ := hRpos.ringInverse.nonneg
  have hkey : D = t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)) := by
    rcases le_or_gt 0 t with ht | ht
    · have hVnn : (0 : A) ≤ t • gm Z Y := smul_nonneg ht (gm_nonneg Z Y)
      have hDnn : (0 : A) ≤ D := by
        rcases lt_or_ge t 1 with ht1 | ht1
        · have hVle : (1 - t) • R ≤ a⁻¹ʳ := by
            rw [← hconj]; exact le_add_of_nonneg_right hVnn
          have hpos : IsStrictlyPositive ((1 - t) • R) := hRpos.smul (by linarith)
          have hcmp := CStarAlgebra.ringInverse_le_ringInverse hVle hpos
          rw [Ring.inverse_inverse ha.isUnit, ringInverse_smul (by linarith) hRpos] at hcmp
          have hfin := smul_le_smul_of_nonneg_left hcmp (by linarith : (0:ℝ) ≤ 1 - t)
          rw [smul_smul, mul_inv_cancel₀ (by linarith : (1:ℝ) - t ≠ 0), one_smul] at hfin
          rw [hDdef]
          exact sub_nonneg.mpr hfin
        · have hneg : (1 - t) • a ≤ 0 := by
            have h0 : (0 : A) ≤ (-(1 - t)) • a := smul_nonneg (by linarith) ha.nonneg
            rw [neg_smul] at h0
            exact neg_nonneg.mp h0
          rw [hDdef]
          exact sub_nonneg.mpr (hneg.trans hRinv_nonneg)
      exact (CFC.mul_self_eq_mul_self_iff D _ hDnn
        (smul_nonneg ht (CFC.sqrt_nonneg _))).mp hDsq
    · have hVnp : t • gm Z Y ≤ 0 := by
        have h0 : (0 : A) ≤ (-t) • gm Z Y := smul_nonneg (by linarith) (gm_nonneg Z Y)
        rw [neg_smul] at h0
        exact neg_nonneg.mp h0
      have hDnp : (0 : A) ≤ -D := by
        have hVle : a⁻¹ʳ ≤ (1 - t) • R := by
          rw [← hconj]; exact add_le_of_nonpos_right hVnp
        have hcmp := CStarAlgebra.ringInverse_le_ringInverse hVle ha.ringInverse
        rw [Ring.inverse_inverse ha.isUnit, ringInverse_smul (by linarith) hRpos] at hcmp
        have hfin := smul_le_smul_of_nonneg_left hcmp (by linarith : (0:ℝ) ≤ 1 - t)
        rw [smul_smul, mul_inv_cancel₀ (by linarith : (1:ℝ) - t ≠ 0), one_smul] at hfin
        rw [hDdef, neg_sub]
        exact sub_nonneg.mpr hfin
      have hnegsq : (-D) * (-D) = ((-t) • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))
          * ((-t) • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))) := by
        rw [neg_mul_neg, hDsq, neg_smul, neg_mul_neg]
      have hres := (CFC.mul_self_eq_mul_self_iff (-D) _ hDnp
        (smul_nonneg (by linarith : (0:ℝ) ≤ -t) (CFC.sqrt_nonneg _))).mp hnegsq
      rw [neg_smul, neg_inj] at hres
      exact hres
  -- reconstruct `x`
  have hRinv : R⁻¹ʳ = (1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)) := by
    rw [← hkey, hDdef]; abel
  have hNu : IsUnit ((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))) := by
    rw [← hRinv]; exact hRpos.isUnit.ringInverse
  have hR : R = ((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))⁻¹ʳ := by
    rw [← hRinv, Ring.inverse_inverse hRpos.isUnit]
  have hxinv : x⁻¹ʳ = a ^ (1/2 : ℝ) * Y * a ^ (1/2 : ℝ) := by
    rw [hYdef]; exact (sandwich_peel ha x⁻¹ʳ).symm
  have hPinv : ((a ^ (-(1/2) : ℝ))⁻¹ʳ : A) = a ^ (1/2 : ℝ) := by
    rw [← ringInverse_rpow_half ha, Ring.inverse_inverse (ha.rpow a _).isUnit]
  rw [wass2_eq_conj ha]
  have hxeq : x⁻¹ʳ = (a ^ (-(1/2) : ℝ)
      * (((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ)))
        * ((1 - t) • a + t • CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))))
      * a ^ (-(1/2) : ℝ))⁻¹ʳ := by
    rw [Ring.inverse_mul (Or.inl (hPu.mul (hNu.mul hNu))), Ring.inverse_mul (Or.inl hPu),
      Ring.inverse_mul (Or.inl hNu), hPinv]
    rw [hxinv, ← hRR, hR, mul_assoc]
  rw [← Ring.inverse_inverse hx.isUnit, hxeq,
    Ring.inverse_inverse ((hPu.mul (hNu.mul hNu)).mul hPu)]

/-! ### Minimality (Theorem 6.9) -/

omit [PartialOrder A] [StarOrderedRing A] in
lemma conj_ringInverse_cancel {m : A} (hm : IsUnit m) (z : A) : m * (m⁻¹ʳ * z * m⁻¹ʳ) * m = z := by
  have hL : ∀ y : A, m * (m⁻¹ʳ * y) = y := fun y => Ring.mul_inverse_cancel_left _ y hm
  have hR : m⁻¹ʳ * m = 1 := Ring.inverse_mul_cancel _ hm
  simp only [mul_assoc, hR, mul_one, hL]

omit [PartialOrder A] [StarOrderedRing A] in
lemma ringInverse_conj_cancel {m : A} (hm : IsUnit m) (z : A) :
    m⁻¹ʳ * (m * z * m) * m⁻¹ʳ = z := by
  have hL : ∀ y : A, m⁻¹ʳ * (m * y) = y := fun y => Ring.inverse_mul_cancel_left _ y hm
  have hR : m * m⁻¹ʳ = 1 := Ring.mul_inverse_cancel _ hm
  simp only [mul_assoc, hR, mul_one, hL]

/-- The Schur-complement equality attained by `a ◇_t b`. -/
theorem wass2_conj_ringInverse (hM : IsStrictlyPositive (wassParam t a b))
    (ha : IsStrictlyPositive a) :
    wassParam t a b * (wass2 t a b)⁻¹ʳ * wassParam t a b = a⁻¹ʳ := by
  rw [wass2_ringInverse hM ha]
  exact conj_ringInverse_cancel hM.isUnit _

/-- **Theorem 6.9**: `a ◇_t b` is the least strictly positive `x` with
`[1 ∇_t (a⁻¹ # b)] x⁻¹ [1 ∇_t (a⁻¹ # b)] ≤ a⁻¹`. -/
theorem wass2_le_of_conj_ringInverse_le (hM : IsStrictlyPositive (wassParam t a b))
    (ha : IsStrictlyPositive a) {x : A} (hx : IsStrictlyPositive x)
    (h : wassParam t a b * x⁻¹ʳ * wassParam t a b ≤ a⁻¹ʳ) : wass2 t a b ≤ x := by
  have hMi : IsSelfAdjoint ((wassParam t a b)⁻¹ʳ) := hM.ringInverse.nonneg.isSelfAdjoint
  have h1 := hMi.conjugate_le_conjugate h
  rw [ringInverse_conj_cancel hM.isUnit, ← wass2_ringInverse hM ha] at h1
  have h2 := CStarAlgebra.ringInverse_le_ringInverse h1 hx.ringInverse
  rwa [Ring.inverse_inverse hx.isUnit,
    Ring.inverse_inverse (wass2_isStrictlyPositive hM ha).isUnit] at h2

/-! ### The near order and the dual comparison (Proposition 6.15) -/

/-- The near order `p ⪯ q ↔ 1 ≤ p⁻¹ # q`. -/
def NearLE (p q : A) : Prop := 1 ≤ gm p⁻¹ʳ q

@[inherit_doc] scoped infix:50 " ⪯ᴳ " => NearLE

/-- `g + g⁻¹ ≥ 2` for strictly positive `g`. -/
lemma two_le_add_ringInverse {g : A} (hg : IsStrictlyPositive g) :
    (2 : ℝ) • (1 : A) ≤ g + g⁻¹ʳ := by
  have hsa : IsSelfAdjoint (g ^ (1/2 : ℝ) - g ^ (-(1/2) : ℝ)) :=
    (isSelfAdjoint_rpow g _).sub (isSelfAdjoint_rpow g _)
  have hpos : (0 : A) ≤ (g ^ (1/2 : ℝ) - g ^ (-(1/2) : ℝ))
      * (g ^ (1/2 : ℝ) - g ^ (-(1/2) : ℝ)) := by
    nth_rewrite 1 [← hsa.star_eq]
    exact star_mul_self_nonneg _
  rw [sub_mul, mul_sub, mul_sub, rpow_half_mul_rpow_half hg, rpow_half_mul_rpow_neg_half hg,
    rpow_neg_half_mul_rpow_half hg, rpow_neg_half_mul_rpow_neg_half hg,
    show g - 1 - (1 - g⁻¹ʳ) = g + g⁻¹ʳ - (2 : ℝ) • (1 : A) by rw [two_smul]; abel] at hpos
  exact sub_nonneg.mp hpos

/-- **Proposition 6.15**: `(a⁻¹ ◇_t b⁻¹)⁻¹ ⪯ a ◇_t b` for `t ∈ [0,1]`. -/
theorem wass2_ringInverse_nearLE (ht : t ∈ Set.Icc (0 : ℝ) 1) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    NearLE (wass2 t a⁻¹ʳ b⁻¹ʳ)⁻¹ʳ (wass2 t a b) := by
  obtain ⟨ht0, ht1⟩ := ht
  have htt : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hg : IsStrictlyPositive (gm a⁻¹ʳ b) := gmInv_strictlyPositive ha hb
  have hswap : gm (a⁻¹ʳ)⁻¹ʳ b⁻¹ʳ = (gm a⁻¹ʳ b)⁻¹ʳ := (gm_ringInverse ha.ringInverse hb).symm
  have hM : IsStrictlyPositive (wassParam t a b) :=
    wassParam_isStrictlyPositive_of_mem_Icc ⟨ht0, ht1⟩ ha hb
  have hM' : IsStrictlyPositive (wassParam t a⁻¹ʳ b⁻¹ʳ) :=
    wassParam_isStrictlyPositive_of_mem_Icc ⟨ht0, ht1⟩ ha.ringInverse hb.ringInverse
  have hU : IsStrictlyPositive (wass2 t a⁻¹ʳ b⁻¹ʳ) :=
    wass2_isStrictlyPositive hM' ha.ringInverse
  have hginv : gm a⁻¹ʳ b * (gm a⁻¹ʳ b)⁻¹ʳ = 1 := Ring.mul_inverse_cancel _ hg.isUnit
  have hginv' : (gm a⁻¹ʳ b)⁻¹ʳ * gm a⁻¹ʳ b = 1 := Ring.inverse_mul_cancel _ hg.isUnit
  have hcomm : wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ
      = wassParam t a⁻¹ʳ b⁻¹ʳ * wassParam t a b := by
    unfold wassParam
    rw [hswap]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      hginv, hginv']
    module
  have hS : wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ
      = ((1 - t) * (1 - t) + t * t) • (1 : A)
        + (t * (1 - t)) • (gm a⁻¹ʳ b + (gm a⁻¹ʳ b)⁻¹ʳ) := by
    unfold wassParam
    rw [hswap]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hginv]
    module
  have hSge : (1 : A) ≤ wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ := by
    rw [hS]
    have hmul := smul_le_smul_of_nonneg_left (two_le_add_ringInverse hg) htt
    rw [smul_smul] at hmul
    refine le_trans (le_of_eq ?_) (add_le_add (le_refl _) hmul)
    rw [← add_smul, show (1 - t) * (1 - t) + t * t + t * (1 - t) * 2 = 1 by ring, one_smul]
  have hriccati : wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ * (wass2 t a⁻¹ʳ b⁻¹ʳ)⁻¹ʳ
      * (wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ) = wass2 t a b := by
    rw [wass2_ringInverse hM' ha.ringInverse, Ring.inverse_inverse ha.isUnit]
    have hcL : ∀ y : A, wassParam t a⁻¹ʳ b⁻¹ʳ * ((wassParam t a⁻¹ʳ b⁻¹ʳ)⁻¹ʳ * y) = y := fun y =>
      Ring.mul_inverse_cancel_left _ y hM'.isUnit
    have hcL2 : ∀ y : A, (wassParam t a⁻¹ʳ b⁻¹ʳ)⁻¹ʳ * (wassParam t a⁻¹ʳ b⁻¹ʳ * y) = y := fun y =>
      Ring.inverse_mul_cancel_left _ y hM'.isUnit
    unfold wass2
    simp only [mul_assoc, hcL]
    rw [hcomm]
    simp only [hcL2]
  have hgmeq : gm (wass2 t a⁻¹ʳ b⁻¹ʳ) (wass2 t a b)
      = wassParam t a b * wassParam t a⁻¹ʳ b⁻¹ʳ :=
    (gm_unique hU (le_trans zero_le_one hSge) hriccati).symm
  unfold NearLE
  rw [Ring.inverse_inverse hU.isUnit, hgmeq]
  exact hSge

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
