import Mathlib
import GaloisForLFunctions.RHTower.GibbsRecursiveStability

/-!
# The two-scale positivity engine

Sector stability of the gas propagates along the cutoff recursion through a single
positivity.  If `P_{S∪p}(z,x) = P_S(z,x) + z·P_S(z,px)` vanishes at some `z` with
`Re z ≥ 0`, then `P_S(z,x) = -z·P_S(z,px)`, hence

  `P_S(z,x)·conj P_S(z,px) = -z·|P_S(z,px)|²`,

whose real part is `≤ 0`.  So the *two-scale positivity*

  `TSP_S(x,y) :  0 < Re[ P_S(z,x)·conj P_S(z,y) ]`  for all `Re z ≥ 0`

at the pair of scales `(x, px)` forbids any zero of the extended gas in the closed right
half-plane.  This converts sector stability into positivity of an explicit real quadratic
form in the gas coefficients — no root tracking and no Routh chain.

The engine is verified unconditionally at the first two levels (empty and singleton sets,
at every pair of scales), and for every `k` in the weak-coupling regime supplied by the
relative estimate.
-/

namespace RHTower.GibbsGas

open Real

/-- **Two-scale positivity** of the gas at a pair of couplings. -/
def TwoScalePositive (S : Finset ℕ) (x y : ℝ) : Prop :=
  ∀ z : ℂ, 0 ≤ z.re → 0 < (gibbsDiagC S x z * (starRingEnd ℂ) (gibbsDiagC S y z)).re

/-- **The reduction.**  Two-scale positivity at the dilated pair forbids zeros of the
extended gas in the closed right half-plane. -/
theorem gibbsDiagC_insert_ne_zero_of_twoScale (p : ℕ) (S : Finset ℕ) (hp : p ∉ S)
    (x : ℝ) (hpos : TwoScalePositive S x ((p : ℝ) * x))
    (z : ℂ) (hz : 0 ≤ z.re) :
    gibbsDiagC (insert p S) x z ≠ 0 := by
  intro h0
  rw [gibbsDiagC_insert p S hp] at h0
  have hA : gibbsDiagC S x z = -(z * gibbsDiagC S ((p : ℝ) * x) z) := by
    linear_combination h0
  have hkey : (gibbsDiagC S x z
      * (starRingEnd ℂ) (gibbsDiagC S ((p : ℝ) * x) z)).re
      = -(z.re * Complex.normSq (gibbsDiagC S ((p : ℝ) * x) z)) := by
    rw [hA, show -(z * gibbsDiagC S ((p : ℝ) * x) z)
        * (starRingEnd ℂ) (gibbsDiagC S ((p : ℝ) * x) z)
      = -(z * (gibbsDiagC S ((p : ℝ) * x) z
        * (starRingEnd ℂ) (gibbsDiagC S ((p : ℝ) * x) z))) from by ring,
      Complex.mul_conj]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpos' := hpos z hz
  rw [hkey] at hpos'
  have hnn : 0 ≤ z.re * Complex.normSq (gibbsDiagC S ((p : ℝ) * x) z) :=
    mul_nonneg hz (Complex.normSq_nonneg _)
  linarith

/-- The real part of a product of two affine functions against a conjugate. -/
theorem re_mul_conj_affine (a₁ b₁ a₂ b₂ : ℝ) (z : ℂ) :
    ((((a₁ : ℝ) : ℂ) + z * ((b₁ : ℝ) : ℂ))
        * (starRingEnd ℂ) (((a₂ : ℝ) : ℂ) + z * ((b₂ : ℝ) : ℂ))).re
      = a₁ * a₂ + (a₁ * b₂ + a₂ * b₁) * z.re
        + b₁ * b₂ * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Level zero**: the empty gas is two-scale positive at every pair of couplings. -/
theorem twoScalePositive_empty (x y : ℝ) : TwoScalePositive ∅ x y := by
  intro z _
  rw [gibbsDiagC_empty, gibbsDiagC_empty, Complex.conj_ofReal]
  have h : (((Real.exp (-x) : ℝ) : ℂ) * ((Real.exp (-y) : ℝ) : ℂ)).re
      = Real.exp (-x) * Real.exp (-y) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h]
  positivity

/-- The singleton gas in affine form. -/
theorem gibbsDiagC_singleton (q : ℕ) (x : ℝ) (z : ℂ) :
    gibbsDiagC {q} x z
      = ((Real.exp (-x) : ℝ) : ℂ) + z * ((Real.exp (-((q : ℝ) * x)) : ℝ) : ℂ) := by
  have h : ({q} : Finset ℕ) = insert q ∅ := by simp
  rw [h, gibbsDiagC_insert q ∅ (Finset.notMem_empty q), gibbsDiagC_empty,
    gibbsDiagC_empty]

/-- **Level one**: every singleton gas is two-scale positive at every pair of couplings.
With the reduction this re-proves stability of the pair gas at every coupling. -/
theorem twoScalePositive_singleton (q : ℕ) (x y : ℝ) : TwoScalePositive {q} x y := by
  intro z hz
  rw [gibbsDiagC_singleton, gibbsDiagC_singleton, re_mul_conj_affine]
  have h1 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have h2 : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
  have h3 : (0 : ℝ) < Real.exp (-((q : ℝ) * x)) := Real.exp_pos _
  have h4 : (0 : ℝ) < Real.exp (-((q : ℝ) * y)) := Real.exp_pos _
  have t1 : 0 < Real.exp (-x) * Real.exp (-y) := mul_pos h1 h2
  have t2 : 0 ≤ (Real.exp (-x) * Real.exp (-((q : ℝ) * y))
      + Real.exp (-y) * Real.exp (-((q : ℝ) * x))) * z.re :=
    mul_nonneg (by positivity) hz
  have t3 : 0 ≤ Real.exp (-((q : ℝ) * x)) * Real.exp (-((q : ℝ) * y))
      * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) := by positivity
  linarith [t1, t2, t3]

/-- **Every level, at weak coupling**: the relative estimate makes the engine
non-vacuous for all `k`. -/
theorem twoScalePositive_of_sigma (S : Finset ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x * (∏ p ∈ S, (1 + (p : ℝ))) + y * (∏ p ∈ S, (1 + (p : ℝ)))
        + (x * (∏ p ∈ S, (1 + (p : ℝ)))) * (y * (∏ p ∈ S, (1 + (p : ℝ)))) < 1) :
    TwoScalePositive S x y := by
  intro z hz
  have h1 : 1 ≤ ‖1 + z‖ := one_le_norm_one_add_of_re_nonneg z hz
  have h2 : ‖z‖ ≤ ‖1 + z‖ := norm_le_norm_one_add_of_re z (by linarith)
  have hA := norm_gibbsDiagC_sub_free_le S x hx z h1 h2
  have hB := norm_gibbsDiagC_sub_free_le S y hy z h1 h2
  set C : ℂ := (1 + z) ^ S.card with hC
  set E₁ : ℂ := gibbsDiagC S x z - C with hE₁
  set E₂ : ℂ := gibbsDiagC S y z - C with hE₂
  have hnC : ‖C‖ = ‖1 + z‖ ^ S.card := by rw [hC, norm_pow]
  have hnC1 : (1 : ℝ) ≤ ‖C‖ := by
    rw [hnC]
    calc (1 : ℝ) = 1 ^ S.card := (one_pow _).symm
      _ ≤ ‖1 + z‖ ^ S.card := pow_le_pow_left₀ zero_le_one h1 _
  have hAeq : gibbsDiagC S x z = C + E₁ := by rw [hE₁]; ring
  have hBeq : gibbsDiagC S y z = C + E₂ := by rw [hE₂]; ring
  have hnE₁ : ‖E₁‖ ≤ (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ := by
    rw [hnC]
    calc ‖E₁‖ ≤ x * (∏ p ∈ S, (1 + (p : ℝ))) * ‖1 + z‖ ^ S.card := hA
      _ = (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖1 + z‖ ^ S.card := by ring
  have hnE₂ : ‖E₂‖ ≤ (y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ := by
    rw [hnC]
    calc ‖E₂‖ ≤ y * (∏ p ∈ S, (1 + (p : ℝ))) * ‖1 + z‖ ^ S.card := hB
      _ = (y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖1 + z‖ ^ S.card := by ring
  rw [hAeq, hBeq, map_add]
  have hsplit : ((C + E₁) * ((starRingEnd ℂ) C + (starRingEnd ℂ) E₂)).re
      = (C * (starRingEnd ℂ) C).re + (C * (starRingEnd ℂ) E₂).re
        + (E₁ * (starRingEnd ℂ) C).re + (E₁ * (starRingEnd ℂ) E₂).re := by
    rw [show (C + E₁) * ((starRingEnd ℂ) C + (starRingEnd ℂ) E₂)
        = C * (starRingEnd ℂ) C + C * (starRingEnd ℂ) E₂
          + E₁ * (starRingEnd ℂ) C + E₁ * (starRingEnd ℂ) E₂ from by ring]
    simp only [Complex.add_re]
  rw [hsplit]
  have hCC : (C * (starRingEnd ℂ) C).re = ‖C‖ ^ (2 : ℕ) := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hbound : ∀ u v : ℂ, -(‖u‖ * ‖v‖) ≤ (u * (starRingEnd ℂ) v).re := by
    intro u v
    have h1' : -‖u * (starRingEnd ℂ) v‖ ≤ (u * (starRingEnd ℂ) v).re := by
      have := Complex.re_le_norm (-(u * (starRingEnd ℂ) v))
      rw [Complex.neg_re, norm_neg] at this
      linarith
    rw [norm_mul, RCLike.norm_conj] at h1'
    exact h1'
  have hb1 := hbound C E₂
  have hb2 := hbound E₁ C
  have hb3 := hbound E₁ E₂
  have hC0 : (0 : ℝ) ≤ ‖C‖ := norm_nonneg C
  have hE₂0 : (0 : ℝ) ≤ ‖E₂‖ := norm_nonneg E₂
  have hxs0 : (0 : ℝ) ≤ x * ∏ p ∈ S, (1 + (p : ℝ)) :=
    mul_nonneg hx (Finset.prod_nonneg fun q _ => by positivity)
  have e1 : ‖C‖ * ‖E₂‖ ≤ (y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ) := by
    calc ‖C‖ * ‖E₂‖ ≤ ‖C‖ * ((y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖) :=
          mul_le_mul_of_nonneg_left hnE₂ hC0
      _ = (y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ) := by ring
  have e2 : ‖E₁‖ * ‖C‖ ≤ (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ) := by
    calc ‖E₁‖ * ‖C‖ ≤ ((x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖) * ‖C‖ :=
          mul_le_mul_of_nonneg_right hnE₁ hC0
      _ = (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ) := by ring
  have e3 : ‖E₁‖ * ‖E₂‖
      ≤ ((x * ∏ p ∈ S, (1 + (p : ℝ))) * (y * ∏ p ∈ S, (1 + (p : ℝ)))) * ‖C‖ ^ (2 : ℕ) := by
    calc ‖E₁‖ * ‖E₂‖
        ≤ ((x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖)
            * ((y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖) :=
          mul_le_mul hnE₁ hnE₂ hE₂0 (mul_nonneg hxs0 hC0)
      _ = ((x * ∏ p ∈ S, (1 + (p : ℝ))) * (y * ∏ p ∈ S, (1 + (p : ℝ)))) * ‖C‖ ^ (2 : ℕ) := by
          ring
  have hK : (0 : ℝ) < ‖C‖ ^ (2 : ℕ) := by nlinarith [hnC1, hC0]
  have hδ : (0 : ℝ) < 1 - (x * (∏ p ∈ S, (1 + (p : ℝ))) + y * (∏ p ∈ S, (1 + (p : ℝ)))
      + (x * (∏ p ∈ S, (1 + (p : ℝ)))) * (y * (∏ p ∈ S, (1 + (p : ℝ))))) := by linarith
  have hlow : ‖C‖ ^ (2 : ℕ) - ((y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + ((x * ∏ p ∈ S, (1 + (p : ℝ))) * (y * ∏ p ∈ S, (1 + (p : ℝ)))) * ‖C‖ ^ (2 : ℕ))
      ≤ (C * (starRingEnd ℂ) C).re + (C * (starRingEnd ℂ) E₂).re
        + (E₁ * (starRingEnd ℂ) C).re + (E₁ * (starRingEnd ℂ) E₂).re := by
    rw [hCC]
    linarith [hb1, hb2, hb3, e1, e2, e3]
  have hposK : (0 : ℝ) < ‖C‖ ^ (2 : ℕ) - ((y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + ((x * ∏ p ∈ S, (1 + (p : ℝ))) * (y * ∏ p ∈ S, (1 + (p : ℝ)))) * ‖C‖ ^ (2 : ℕ)) := by
    have hrw : ‖C‖ ^ (2 : ℕ) - ((y * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + (x * ∏ p ∈ S, (1 + (p : ℝ))) * ‖C‖ ^ (2 : ℕ)
        + ((x * ∏ p ∈ S, (1 + (p : ℝ))) * (y * ∏ p ∈ S, (1 + (p : ℝ)))) * ‖C‖ ^ (2 : ℕ))
        = ‖C‖ ^ (2 : ℕ) * (1 - (x * (∏ p ∈ S, (1 + (p : ℝ)))
            + y * (∏ p ∈ S, (1 + (p : ℝ)))
            + (x * (∏ p ∈ S, (1 + (p : ℝ)))) * (y * (∏ p ∈ S, (1 + (p : ℝ)))))) := by
      ring
    rw [hrw]
    exact mul_pos hK hδ
  linarith [hlow, hposK]

/-- The pair gas has no zero in the closed right half-plane, at every coupling —
re-derived from the engine at level one. -/
theorem gibbsDiagC_pair_ne_zero (p q : ℕ) (hpq : p ∉ ({q} : Finset ℕ)) (x : ℝ)
    (z : ℂ) (hz : 0 ≤ z.re) :
    gibbsDiagC (insert p {q}) x z ≠ 0 :=
  gibbsDiagC_insert_ne_zero_of_twoScale p {q} hpq x
    (twoScalePositive_singleton q x ((p : ℝ) * x)) z hz

end RHTower.GibbsGas
