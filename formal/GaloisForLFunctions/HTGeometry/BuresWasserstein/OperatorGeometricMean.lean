/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The operator geometric mean in a C⋆-algebra

Mathlib knows the continuous functional calculus powers `CFC.rpow` and `CFC.sqrt` together with
their operator monotonicity and operator concavity, but it does not know the *geometric mean*
`a # b` of two strictly positive elements.  This file supplies it, in the weighted form

`a #_t b = a ^ (1/2) * (a ^ (-(1/2)) * b * a ^ (-(1/2))) ^ t * a ^ (1/2)`,

for an arbitrary unital C⋆-algebra, and establishes the classical toolkit:

* `gmRiccati` / `gm_unique` : `a # b` is the unique nonnegative solution of `x a⁻¹ x = b`;
* `gm_comm`, `gm_ringInverse` (self-duality), `gm_conjugate` (congruence invariance);
* `gm_one_left`, `gm_one_right` : `1 # b = √b`, `a # 1 = √a`;
* `gm_mono_right`, `gm_mono_left`, `gm_mono` : joint operator monotonicity;
* `le_gm_of_conj_le` : the maximality characterisation
  `x = x⋆, x a⁻¹ x ≤ b ⟹ x ≤ a # b`;
* `gm_le_arith` (arithmetic–geometric mean inequality) and `harm_le_gm`
  (geometric–harmonic mean inequality);
* `conj_ringInverse_convexOn` : joint operator convexity of `(x, a) ↦ x a⁻¹ x`, and the
  consequent `gm_concave` : joint operator concavity of the geometric mean.

This is the algebraic backbone used by the Bures–Wasserstein barycentre theory of
Kim–Mer–Pálfia (arXiv:2607.29142).
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Square-root power bookkeeping -/

section Helpers

variable {a : A}

@[simp]
lemma isSelfAdjoint_rpow (a : A) (t : ℝ) : IsSelfAdjoint (a ^ t) :=
  (CFC.rpow_nonneg (a := a) (y := t)).isSelfAdjoint

lemma rpow_half_mul_rpow_half (ha : IsStrictlyPositive a) :
    a ^ (1/2 : ℝ) * a ^ (1/2 : ℝ) = a := by
  rw [← CFC.rpow_add ha.isUnit]
  norm_num
  exact CFC.rpow_one a ha.nonneg

lemma rpow_half_mul_rpow_neg_half (ha : IsStrictlyPositive a) :
    a ^ (1/2 : ℝ) * a ^ (-(1/2) : ℝ) = 1 := CFC.rpow_mul_rpow_neg _ ha

lemma rpow_neg_half_mul_rpow_half (ha : IsStrictlyPositive a) :
    a ^ (-(1/2) : ℝ) * a ^ (1/2 : ℝ) = 1 := CFC.rpow_neg_mul_rpow _ ha

lemma rpow_neg_half_mul_rpow_neg_half (ha : IsStrictlyPositive a) :
    a ^ (-(1/2) : ℝ) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ := by
  rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]
  norm_num

/-- Conjugating a nonnegative element by a self-adjoint element stays nonnegative. -/
lemma nonneg_conjugate {c : A} (hc : IsSelfAdjoint c) {x : A} (hx : 0 ≤ x) : 0 ≤ c * x * c := by
  simpa using hc.conjugate_le_conjugate hx

/-- A self-adjoint element is dominated by its absolute value. -/
lemma le_cfcAbs {x : A} (hx : IsSelfAdjoint x) : x ≤ CFC.abs x := by
  have h := CFC.abs_sub_self x hx
  have h2 : (0 : A) ≤ 2 • x⁻ := smul_nonneg (by norm_num) (CFC.negPart_nonneg x)
  exact sub_nonneg.mp (h ▸ h2)

/-- For a self-adjoint element, the absolute value is the square root of the square. -/
lemma cfcAbs_eq_sqrt_mul_self {x : A} (hx : IsSelfAdjoint x) : CFC.abs x = CFC.sqrt (x * x) := by
  rw [CFC.abs, hx.star_eq]

end Helpers

/-! ### Definition -/

/-- The **weighted operator geometric mean**
`a #_t b = a ^ (1/2) (a ^ (-(1/2)) b a ^ (-(1/2))) ^ t a ^ (1/2)`. -/
def wgm (t : ℝ) (a b : A) : A :=
  a ^ (1/2 : ℝ) * ((a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) ^ t) * a ^ (1/2 : ℝ)

/-- The **operator geometric mean** `a # b = a ^ (1/2) (a ^ (-(1/2)) b a ^ (-(1/2))) ^ (1/2)
a ^ (1/2)`. -/
def gm (a b : A) : A := wgm (1/2 : ℝ) a b

@[inherit_doc] scoped infixl:70 " #ᴳ " => gm

variable {a b : A}

lemma wgm_def (t : ℝ) (a b : A) :
    wgm t a b = a ^ (1/2 : ℝ) * ((a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) ^ t) * a ^ (1/2 : ℝ) :=
  rfl

lemma gm_eq_sqrt (a b : A) :
    gm a b = a ^ (1/2 : ℝ) * CFC.sqrt (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ))
      * a ^ (1/2 : ℝ) := by
  rw [gm, wgm_def, CFC.sqrt_eq_rpow]

@[simp]
lemma wgm_nonneg (t : ℝ) (a b : A) : 0 ≤ wgm t a b := by
  rw [wgm_def]
  exact nonneg_conjugate (isSelfAdjoint_rpow a (1/2 : ℝ)) CFC.rpow_nonneg

@[simp]
lemma gm_nonneg (a b : A) : 0 ≤ gm a b := wgm_nonneg _ a b

lemma conj_strictlyPositive (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) :=
  IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint b _
    (ha.rpow a _).isUnit (isSelfAdjoint_rpow a _) hb

lemma gm_strictlyPositive (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (gm a b) := by
  rw [gm_eq_sqrt]
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _
    (ha.rpow a _).isUnit (isSelfAdjoint_rpow a _)
    ((conj_strictlyPositive ha hb).sqrt _)

/-! ### The Riccati equation -/

/-- Cancellation sandwich `(a^{1/2} u a^{1/2}) a⁻¹ (a^{1/2} v a^{1/2}) = a^{1/2} (u v) a^{1/2}`. -/
lemma sandwich_cancel (ha : IsStrictlyPositive a) (u v : A) :
    (a ^ (1/2 : ℝ) * u * a ^ (1/2 : ℝ)) * a⁻¹ʳ * (a ^ (1/2 : ℝ) * v * a ^ (1/2 : ℝ))
      = a ^ (1/2 : ℝ) * (u * v) * a ^ (1/2 : ℝ) := by
  have hss : a ^ (-(1/2) : ℝ) * a ^ (1/2 : ℝ) = 1 := rpow_neg_half_mul_rpow_half ha
  have hss' : a ^ (1/2 : ℝ) * a ^ (-(1/2) : ℝ) = 1 := rpow_half_mul_rpow_neg_half ha
  have hinv : a ^ (-(1/2) : ℝ) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ :=
    rpow_neg_half_mul_rpow_neg_half ha
  have hL : ∀ z : A, a ^ (-(1/2) : ℝ) * (a ^ (1/2 : ℝ) * z) = z := fun z => by
    rw [← mul_assoc, hss, one_mul]
  have hR : ∀ z : A, a ^ (1/2 : ℝ) * (a ^ (-(1/2) : ℝ) * z) = z := fun z => by
    rw [← mul_assoc, hss', one_mul]
  rw [← hinv]
  simp only [mul_assoc, hL, hR]

/-- Peeling `a^{±1/2}` off a sandwich. -/
lemma sandwich_peel (ha : IsStrictlyPositive a) (u : A) :
    a ^ (1/2 : ℝ) * (a ^ (-(1/2) : ℝ) * u * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ) = u := by
  have hss : a ^ (-(1/2) : ℝ) * a ^ (1/2 : ℝ) = 1 := rpow_neg_half_mul_rpow_half ha
  have hss' : a ^ (1/2 : ℝ) * a ^ (-(1/2) : ℝ) = 1 := rpow_half_mul_rpow_neg_half ha
  have hR : ∀ z : A, a ^ (1/2 : ℝ) * (a ^ (-(1/2) : ℝ) * z) = z := fun z => by
    rw [← mul_assoc, hss', one_mul]
  simp only [mul_assoc, hR, hss, mul_one]

/-- **Riccati equation.** `(a # b) a⁻¹ (a # b) = b`. -/
theorem gm_riccati (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    gm a b * a⁻¹ʳ * gm a b = b := by
  have hcnn : (0 : A) ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) :=
    (conj_strictlyPositive ha hb).nonneg
  rw [gm_eq_sqrt, sandwich_cancel ha, CFC.sqrt_mul_sqrt_self _ hcnn, sandwich_peel ha]

/-- **Uniqueness in the Riccati equation.** -/
theorem gm_unique (ha : IsStrictlyPositive a) {x : A}
    (hx : 0 ≤ x) (hxe : x * a⁻¹ʳ * x = b) : x = gm a b := by
  have hinv : a ^ (-(1/2) : ℝ) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ :=
    rpow_neg_half_mul_rpow_neg_half ha
  set si := a ^ (-(1/2) : ℝ) with hsi
  have hynn : (0 : A) ≤ si * x * si := nonneg_conjugate (isSelfAdjoint_rpow a _) hx
  have hyy : (si * x * si) * (si * x * si) = si * b * si := by
    rw [← hxe, ← hinv]; simp only [mul_assoc]
  have hsq : CFC.sqrt (si * b * si) = si * x * si := CFC.sqrt_unique hyy hynn
  rw [gm_eq_sqrt, ← hsi, hsq, sandwich_peel ha]

/-! ### Symmetry, self-duality and congruence invariance -/

/-- If `x a⁻¹ x = b` with `x` invertible, then `x b⁻¹ x = a`. -/
lemma riccati_symm {x : A} (ha : IsStrictlyPositive a) (hx : IsUnit x)
    (h : x * a⁻¹ʳ * x = b) : x * b⁻¹ʳ * x = a := by
  subst h
  have hai : IsUnit (a⁻¹ʳ) := ha.isUnit.ringInverse
  rw [Ring.inverse_mul (Or.inl (hx.mul hai)), Ring.inverse_mul (Or.inl hx),
    Ring.inverse_inverse ha.isUnit]
  simp only [mul_assoc]
  rw [Ring.inverse_mul_cancel x hx, mul_one, Ring.mul_inverse_cancel_left _ _ hx]

/-- **Symmetry** of the geometric mean. -/
theorem gm_comm (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) : gm a b = gm b a :=
  gm_unique hb (gm_nonneg a b)
    (riccati_symm ha (gm_strictlyPositive ha hb).isUnit (gm_riccati ha hb))

/-- Inverting a Riccati sandwich. -/
lemma ringInverse_sandwich {x : A} (ha : IsStrictlyPositive a) (hx : IsUnit x) :
    (x * a⁻¹ʳ * x)⁻¹ʳ = x⁻¹ʳ * a * x⁻¹ʳ := by
  rw [Ring.inverse_mul (Or.inl (hx.mul ha.isUnit.ringInverse)),
    Ring.inverse_mul (Or.inl hx), Ring.inverse_inverse ha.isUnit]
  simp only [mul_assoc]

/-- **Self-duality**: `(a # b)⁻¹ = a⁻¹ # b⁻¹`. -/
theorem gm_ringInverse (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    (gm a b)⁻¹ʳ = gm a⁻¹ʳ b⁻¹ʳ := by
  have hg : IsStrictlyPositive (gm a b) := gm_strictlyPositive ha hb
  refine gm_unique ha.ringInverse hg.ringInverse.nonneg ?_
  rw [Ring.inverse_inverse ha.isUnit, ← ringInverse_sandwich ha hg.isUnit, gm_riccati ha hb]

/-- **Congruence invariance**: `m (a # b) m⋆ = (m a m⋆) # (m b m⋆)` for invertible `m`. -/
theorem gm_conjugate {m : A} (hm : IsUnit m) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    m * gm a b * star m = gm (m * a * star m) (m * b * star m) := by
  have hma : IsStrictlyPositive (m * a * star m) :=
    hm.isStrictlyPositive_star_right_conjugate_iff.mpr ha
  have hsm : IsUnit (star m) := hm.star
  refine gm_unique hma (star_right_conjugate_nonneg (gm_nonneg a b) m) ?_
  rw [Ring.inverse_mul (Or.inl (hm.mul ha.isUnit)), Ring.inverse_mul (Or.inl hm)]
  calc m * gm a b * star m * ((star m)⁻¹ʳ * (a⁻¹ʳ * m⁻¹ʳ)) * (m * gm a b * star m)
      = m * (gm a b * (star m * (star m)⁻¹ʳ) * (a⁻¹ʳ * ((m⁻¹ʳ * m) * gm a b))) * star m := by
        simp only [mul_assoc]
    _ = m * (gm a b * a⁻¹ʳ * gm a b) * star m := by
        rw [Ring.mul_inverse_cancel _ hsm, Ring.inverse_mul_cancel _ hm]
        simp only [mul_one, one_mul, mul_assoc]
    _ = m * b * star m := by rw [gm_riccati ha hb]

/-! ### Unit and monotonicity -/

@[simp]
theorem gm_one_left (b : A) : gm (1 : A) b = CFC.sqrt b := by
  simp [gm_eq_sqrt]

theorem gm_one_right (ha : IsStrictlyPositive a) : gm a (1 : A) = CFC.sqrt a := by
  rw [gm_comm ha isStrictlyPositive_one, gm_one_left]

/-- Operator monotonicity of `a # ·`. -/
theorem gm_mono_right (a : A) {b c : A} (h : b ≤ c) : gm a b ≤ gm a c := by
  rw [gm_eq_sqrt, gm_eq_sqrt]
  exact (isSelfAdjoint_rpow a _).conjugate_le_conjugate
    (CFC.sqrt_le_sqrt _ _ ((isSelfAdjoint_rpow a _).conjugate_le_conjugate h))

/-- Operator monotonicity of `· # b`. -/
theorem gm_mono_left {a c : A} (ha : IsStrictlyPositive a) (hc : IsStrictlyPositive c)
    (hb : IsStrictlyPositive b) (h : a ≤ c) : gm a b ≤ gm c b := by
  rw [gm_comm ha hb, gm_comm hc hb]
  exact gm_mono_right b h

/-- Joint operator monotonicity of the geometric mean. -/
theorem gm_mono {a b c d : A} (ha : IsStrictlyPositive a) (hc : IsStrictlyPositive c)
    (hb : IsStrictlyPositive b) (hac : a ≤ c) (hbd : b ≤ d) : gm a b ≤ gm c d :=
  (gm_mono_left ha hc hb hac).trans (gm_mono_right c hbd)

/-! ### Maximality -/

/-- **Maximality characterisation.** If `x` is self-adjoint and `x a⁻¹ x ≤ b` then `x ≤ a # b`. -/
theorem le_gm_of_conj_le (ha : IsStrictlyPositive a) {x : A} (hx : IsSelfAdjoint x)
    (h : x * a⁻¹ʳ * x ≤ b) : x ≤ gm a b := by
  have hinv : a ^ (-(1/2) : ℝ) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ :=
    rpow_neg_half_mul_rpow_neg_half ha
  have hsisa : IsSelfAdjoint (a ^ (-(1/2) : ℝ)) := isSelfAdjoint_rpow a _
  have hy : IsSelfAdjoint (a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ)) := hx.conjugate_self hsisa
  have h1 : (a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ)) * (a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ))
      = a ^ (-(1/2) : ℝ) * (x * a⁻¹ʳ * x) * a ^ (-(1/2) : ℝ) := by
    rw [← hinv]; simp only [mul_assoc]
  have h2 : a ^ (-(1/2) : ℝ) * (x * a⁻¹ʳ * x) * a ^ (-(1/2) : ℝ)
      ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) := hsisa.conjugate_le_conjugate h
  have h3 : CFC.sqrt ((a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ))
        * (a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ)))
      ≤ CFC.sqrt (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) :=
    CFC.sqrt_le_sqrt _ _ (h1 ▸ h2)
  have h4 : a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ)
      ≤ CFC.sqrt ((a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ))
        * (a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ))) := by
    rw [← cfcAbs_eq_sqrt_mul_self hy]; exact le_cfcAbs hy
  have h5 := (isSelfAdjoint_rpow a (1/2 : ℝ)).conjugate_le_conjugate (h4.trans h3)
  rw [sandwich_peel ha] at h5
  rw [gm_eq_sqrt]
  exact h5

/-! ### The arithmetic–geometric–harmonic chain -/

/-- Scalar-free form of `2√c ≤ 1 + c`. -/
lemma sqrt_add_sqrt_le_one_add {c : A} (hc : 0 ≤ c) : CFC.sqrt c + CFC.sqrt c ≤ 1 + c := by
  have hsq : CFC.sqrt c * CFC.sqrt c = c := CFC.sqrt_mul_sqrt_self c hc
  have hsa : IsSelfAdjoint (1 - CFC.sqrt c) := by
    show star (1 - CFC.sqrt c) = 1 - CFC.sqrt c
    rw [star_sub, star_one, (CFC.sqrt_nonneg c).isSelfAdjoint.star_eq]
  have hpos : (0 : A) ≤ (1 - CFC.sqrt c) * (1 - CFC.sqrt c) := by
    nth_rewrite 1 [← hsa.star_eq]
    exact star_mul_self_nonneg _
  have hexp : (1 - CFC.sqrt c) * (1 - CFC.sqrt c) = 1 + c - (CFC.sqrt c + CFC.sqrt c) := by
    rw [sub_mul, mul_sub, mul_sub, hsq]; noncomm_ring
  rw [hexp] at hpos
  exact sub_nonneg.mp hpos

/-- **Arithmetic–geometric mean inequality**, additive form. -/
theorem gm_add_gm_le (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    gm a b + gm a b ≤ a + b := by
  have hcnn : (0 : A) ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) :=
    (conj_strictlyPositive ha hb).nonneg
  have hmono := (isSelfAdjoint_rpow a (1/2 : ℝ)).conjugate_le_conjugate
    (sqrt_add_sqrt_le_one_add hcnn)
  have hL : a ^ (1/2 : ℝ) * (CFC.sqrt (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ))
      + CFC.sqrt (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ))) * a ^ (1/2 : ℝ)
      = gm a b + gm a b := by
    rw [gm_eq_sqrt]; noncomm_ring
  have hR : a ^ (1/2 : ℝ) * (1 + a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ)
      = a + b := by
    have h1 : a ^ (1/2 : ℝ) * (1 : A) * a ^ (1/2 : ℝ) = a := by
      rw [mul_one]; exact rpow_half_mul_rpow_half ha
    have h2 : a ^ (1/2 : ℝ) * (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ) = b :=
      sandwich_peel ha b
    calc a ^ (1/2 : ℝ) * (1 + a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ)
        = a ^ (1/2 : ℝ) * (1 : A) * a ^ (1/2 : ℝ)
          + a ^ (1/2 : ℝ) * (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ) := by
          noncomm_ring
      _ = a + b := by rw [h1, h2]
  rw [hL, hR] at hmono
  exact hmono

/-- **Arithmetic–geometric mean inequality.** -/
theorem gm_le_arith (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    gm a b ≤ (2 : ℝ)⁻¹ • (a + b) := by
  have h2 : (2 : ℝ)⁻¹ • (gm a b + gm a b) ≤ (2 : ℝ)⁻¹ • (a + b) :=
    smul_le_smul_of_nonneg_left (gm_add_gm_le ha hb) (by norm_num)
  have h3 : (2 : ℝ)⁻¹ • (gm a b + gm a b) = gm a b := by
    rw [← two_smul ℝ (gm a b), smul_smul]; norm_num
  rwa [h3] at h2

/-- **Geometric–harmonic mean inequality.** -/
theorem harm_le_gm (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    ((2 : ℝ)⁻¹ • (a⁻¹ʳ + b⁻¹ʳ))⁻¹ʳ ≤ gm a b := by
  have hg : IsStrictlyPositive (gm a⁻¹ʳ b⁻¹ʳ) :=
    gm_strictlyPositive ha.ringInverse hb.ringInverse
  have h := CStarAlgebra.ringInverse_le_ringInverse
    (gm_le_arith ha.ringInverse hb.ringInverse) hg
  rwa [← gm_ringInverse ha hb, Ring.inverse_inverse (gm_strictlyPositive ha hb).isUnit] at h

/-! ### Joint operator convexity of `(x, a) ↦ x a⁻¹ x` -/

/-- The completing-the-square identity behind joint convexity of `(x,a) ↦ x a⁻¹ x`. -/
lemma conj_ringInverse_sub_eq (ha : IsStrictlyPositive a) {x : A} (hx : IsSelfAdjoint x) (y : A) :
    x * a⁻¹ʳ * x - (x * y + star y * x - star y * a * y)
      = star (x - a * y) * a⁻¹ʳ * (x - a * y) := by
  have hL : ∀ z : A, a⁻¹ʳ * (a * z) = z := fun z => Ring.inverse_mul_cancel_left a z ha.isUnit
  have hR : ∀ z : A, a * (a⁻¹ʳ * z) = z := fun z => Ring.mul_inverse_cancel_left a z ha.isUnit
  have hst : star (x - a * y) = x - star y * a := by
    rw [star_sub, star_mul, hx.star_eq, ha.isSelfAdjoint.star_eq]
  rw [hst, sub_mul, sub_mul, mul_sub, mul_sub]
  simp only [mul_assoc, hL, hR]
  abel

/-- The variational lower bound `x y + y⋆ x - y⋆ a y ≤ x a⁻¹ x`. -/
lemma le_conj_ringInverse (ha : IsStrictlyPositive a) {x : A} (hx : IsSelfAdjoint x) (y : A) :
    x * y + star y * x - star y * a * y ≤ x * a⁻¹ʳ * x := by
  have h := star_left_conjugate_nonneg ha.ringInverse.nonneg (x - a * y)
  rw [← conj_ringInverse_sub_eq ha hx y] at h
  exact sub_nonneg.mp h

/-- The variational lower bound is attained at `y = a⁻¹ x`. -/
lemma conj_ringInverse_eq_at (ha : IsStrictlyPositive a) {x : A} (hx : IsSelfAdjoint x) :
    x * (a⁻¹ʳ * x) + star (a⁻¹ʳ * x) * x - star (a⁻¹ʳ * x) * a * (a⁻¹ʳ * x)
      = x * a⁻¹ʳ * x := by
  have hL : ∀ z : A, a⁻¹ʳ * (a * z) = z := fun z => Ring.inverse_mul_cancel_left a z ha.isUnit
  have hst : star (a⁻¹ʳ * x) = x * a⁻¹ʳ := by
    rw [star_mul, hx.star_eq, ha.ringInverse.isSelfAdjoint.star_eq]
  rw [hst]
  simp only [mul_assoc, hL]
  abel

/-! ### Finite convex combinations -/

variable {ι : Type*}

/-- A positive convex combination of strictly positive elements is strictly positive. -/
lemma isStrictlyPositive_sum_smul {s : Finset ι} (hs : s.Nonempty) {w : ι → ℝ} {f : ι → A}
    (hw : ∀ i ∈ s, 0 < w i) (hf : ∀ i ∈ s, IsStrictlyPositive (f i)) :
    IsStrictlyPositive (∑ i ∈ s, w i • f i) := by
  classical
  obtain ⟨j, hj⟩ := hs
  have htail : (0 : A) ≤ ∑ i ∈ s.erase j, w i • f i :=
    Finset.sum_nonneg fun i hi => smul_nonneg (hw i (Finset.mem_of_mem_erase hi)).le
      (hf i (Finset.mem_of_mem_erase hi)).nonneg
  have h := ((hf j hj).smul (hw j hj)).add_nonneg htail
  rwa [Finset.add_sum_erase s (fun i => w i • f i) hj] at h

/-- **Joint operator convexity** of `(x, a) ↦ x a⁻¹ x` over a finite positive combination.
No normalisation of the weights is needed: the map is positively homogeneous of degree one. -/
theorem conj_ringInverse_convex {s : Finset ι} (hs : s.Nonempty) {w : ι → ℝ} {x f : ι → A}
    (hw : ∀ i ∈ s, 0 < w i)
    (hx : ∀ i ∈ s, IsSelfAdjoint (x i)) (hf : ∀ i ∈ s, IsStrictlyPositive (f i)) :
    (∑ i ∈ s, w i • x i) * (∑ i ∈ s, w i • f i)⁻¹ʳ * (∑ i ∈ s, w i • x i)
      ≤ ∑ i ∈ s, w i • (x i * (f i)⁻¹ʳ * x i) := by
  have hFpos : IsStrictlyPositive (∑ i ∈ s, w i • f i) := isStrictlyPositive_sum_smul hs hw hf
  have hXsa : IsSelfAdjoint (∑ i ∈ s, w i • x i) :=
    isSelfAdjoint_sum s fun i hi => IsSelfAdjoint.smul (star_trivial (w i)) (hx i hi)
  set X := ∑ i ∈ s, w i • x i with hX
  set F := ∑ i ∈ s, w i • f i with hF
  set y := F⁻¹ʳ * X with hy
  have h1 : X * y = ∑ i ∈ s, w i • (x i * y) := by
    rw [hX, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => smul_mul_assoc _ _ _
  have h2 : star y * X = ∑ i ∈ s, w i • (star y * x i) := by
    rw [hX, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have h3 : star y * F * y = ∑ i ∈ s, w i • (star y * f i * y) := by
    rw [hF, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc]
  have hkey : X * F⁻¹ʳ * X = ∑ i ∈ s, w i • (x i * y + star y * x i - star y * f i * y) := by
    rw [← conj_ringInverse_eq_at hFpos hXsa, ← hy, h1, h2, h3,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← smul_add, ← smul_sub]
  rw [hkey]
  refine Finset.sum_le_sum fun i hi => ?_
  exact smul_le_smul_of_nonneg_left (le_conj_ringInverse (hf i hi) (hx i hi) y) (hw i hi).le

/-- **Joint operator concavity of the geometric mean** (superadditivity in the homogeneous form). -/
theorem gm_concave {s : Finset ι} (hs : s.Nonempty) {w : ι → ℝ} {f g : ι → A}
    (hw : ∀ i ∈ s, 0 < w i)
    (hf : ∀ i ∈ s, IsStrictlyPositive (f i)) (hg : ∀ i ∈ s, IsStrictlyPositive (g i)) :
    ∑ i ∈ s, w i • gm (f i) (g i) ≤ gm (∑ i ∈ s, w i • f i) (∑ i ∈ s, w i • g i) := by
  have hXsa : IsSelfAdjoint (∑ i ∈ s, w i • gm (f i) (g i)) :=
    isSelfAdjoint_sum s fun i _ =>
      IsSelfAdjoint.smul (star_trivial (w i)) (gm_nonneg (f i) (g i)).isSelfAdjoint
  refine le_gm_of_conj_le (isStrictlyPositive_sum_smul hs hw hf) hXsa ?_
  refine le_trans (conj_ringInverse_convex hs hw
    (fun i _ => (gm_nonneg (f i) (g i)).isSelfAdjoint) hf) ?_
  exact le_of_eq (Finset.sum_congr rfl fun i hi => by rw [gm_riccati (hf i hi) (hg i hi)])

/-! ### Scalar multiples and inverses -/

lemma ringInverse_smul {r : ℝ} (hr : 0 < r) (ha : IsStrictlyPositive a) :
    (r • a)⁻¹ʳ = r⁻¹ • a⁻¹ʳ := by
  rw [← mul_one ((r • a)⁻¹ʳ), Ring.inverse_mul_eq_iff_eq_mul _ _ _ (ha.smul hr).isUnit,
    smul_mul_smul_comm, Ring.mul_inverse_cancel _ ha.isUnit]
  field_simp
  simp

lemma rpow_half_ringInverse (ha : IsStrictlyPositive a) :
    (a⁻¹ʳ) ^ (1/2 : ℝ) = a ^ (-(1/2) : ℝ) := by
  rw [CFC.inverse_eq_rpow_neg_one ha, CFC.rpow_rpow _ _ _ (by norm_num)]
  norm_num

lemma rpow_neg_half_ringInverse (ha : IsStrictlyPositive a) :
    (a⁻¹ʳ) ^ (-(1/2) : ℝ) = a ^ (1/2 : ℝ) := by
  rw [CFC.inverse_eq_rpow_neg_one ha, CFC.rpow_rpow _ _ _ (by norm_num)]
  norm_num

/-- The geometric mean of the inverse: `a⁻¹ # b = a^{-1/2}(a^{1/2} b a^{1/2})^{1/2} a^{-1/2}`. -/
lemma gm_ringInverse_left (ha : IsStrictlyPositive a) (b : A) :
    gm a⁻¹ʳ b = a ^ (-(1/2) : ℝ) * CFC.sqrt (a ^ (1/2 : ℝ) * b * a ^ (1/2 : ℝ))
      * a ^ (-(1/2) : ℝ) := by
  rw [gm_eq_sqrt, rpow_half_ringInverse ha, rpow_neg_half_ringInverse ha]

/-- **Joint homogeneity** of the geometric mean. -/
theorem gm_smul {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    gm (r • a) (t • b) = Real.sqrt (r * t) • gm a b := by
  refine (gm_unique (ha.smul hr) (smul_nonneg (Real.sqrt_nonneg _) (gm_nonneg a b)) ?_).symm
  rw [ringInverse_smul hr ha]
  have hrt : Real.sqrt (r * t) * Real.sqrt (r * t) = r * t := Real.mul_self_sqrt (by positivity)
  calc Real.sqrt (r * t) • gm a b * (r⁻¹ • a⁻¹ʳ) * (Real.sqrt (r * t) • gm a b)
      = (Real.sqrt (r * t) * (r⁻¹ * Real.sqrt (r * t))) • (gm a b * a⁻¹ʳ * gm a b) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = t • b := by
        rw [gm_riccati ha hb]
        congr 1
        rw [show Real.sqrt (r * t) * (r⁻¹ * Real.sqrt (r * t))
          = r⁻¹ * (Real.sqrt (r * t) * Real.sqrt (r * t)) by ring, hrt]
        field_simp

/-- Homogeneity in a single common scalar. -/
theorem gm_smul_self {r : ℝ} (hr : 0 < r) (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) : gm (r • a) (r • b) = r • gm a b := by
  rw [gm_smul hr hr ha hb, Real.sqrt_mul_self hr.le]

/-! ### Weighted geometric means -/

@[simp] lemma wgm_half (a b : A) : wgm (1/2 : ℝ) a b = gm a b := rfl

lemma wgm_zero (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : wgm 0 a b = a := by
  have hc : (0 : A) ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) :=
    nonneg_conjugate (isSelfAdjoint_rpow a _) hb
  rw [wgm_def, CFC.rpow_zero _ hc, mul_one]
  exact rpow_half_mul_rpow_half ha

lemma wgm_one (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : wgm 1 a b = b := by
  have hc : (0 : A) ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) :=
    nonneg_conjugate (isSelfAdjoint_rpow a _) hb
  rw [wgm_def, CFC.rpow_one _ hc]
  exact sandwich_peel ha b

/-- Operator monotonicity of `a #_t ·` for `t ∈ [0,1]`. -/
theorem wgm_mono_right {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (a : A) {b c : A} (h : b ≤ c) :
    wgm t a b ≤ wgm t a c := by
  rw [wgm_def, wgm_def]
  exact (isSelfAdjoint_rpow a _).conjugate_le_conjugate
    (CFC.rpow_le_rpow ht ((isSelfAdjoint_rpow a _).conjugate_le_conjugate h))

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
