import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveGridCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Heights for two-sided eighth-power weights

A block with mass `A`, `n` nodes, and weights comparable to `A/n` is placed
above `(2n/A)^(1/8)`. An additional cumulative-count term gives linear height
counting. A bound on `A F^8` makes the upper weight constant uniform across
blocks while preserving the reciprocal eighth-power lower bound.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Match the uniform block weight to an inverse eighth power of height. -/
def massRadius (A : ℝ) (n : ℕ) : ℝ := (2*(n : ℝ)/A)^(1/8 : ℝ)

lemma massRadius_pos {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) :
    0 < massRadius A n := Real.rpow_pos_of_pos (by positivity) _

lemma massRadius_pow {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) :
    (massRadius A n)^8=2*(n : ℝ)/A := by
  rw [massRadius, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2*(n : ℝ)/A)]
  norm_num

/-- A weighted eighth moment of cumulative node counts controls every block uniformly. -/
theorem height_weight_bounds {A F K x w : ℝ} {n : ℕ}
    (hA : 0 < A) (hn : 0 < n) (hF : 1 ≤ F)
    (hK : A*F^8 ≤ K)
    (hxlo : max (massRadius A n) ((Real.pi+2)*F) ≤ x)
    (hxhi : x ≤ 2*max (massRadius A n) ((Real.pi+2)*F))
    (hwlo : A/(2*n) ≤ w) (hwhi : w ≤ 3*A/(2*n)) :
    1/(1+|x|)^8 ≤ w ∧
      w ≤ ((3 : ℝ)^9/2*(2+(Real.pi+2)^8*K))/(1+|x|)^8 := by
  let H := max (massRadius A n) ((Real.pi+2)*F)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hF0 : 0 ≤ F := le_trans (by norm_num) hF
  have hpi : 0 < Real.pi+2 := by linarith only [Real.pi_pos]
  have hH1 : 1 ≤ H := by
    have h : F ≤ (Real.pi+2)*F := le_mul_of_one_le_left hF0 (by linarith only [Real.pi_pos])
    exact hF.trans (h.trans (le_max_right _ _))
  have hx0 : 0 ≤ x := (le_trans (by norm_num) hH1).trans hxlo
  have hR := massRadius_pow hA hn
  have hR0 := (massRadius_pos hA hn).le
  have hden : 0 < (1+|x|)^8 := pow_pos (by positivity) 8
  have hH8 : H^8 ≤ 2*(n : ℝ)/A+((Real.pi+2)*F)^8 := by
    rcases le_total (massRadius A n) ((Real.pi+2)*F) with h | h
    · dsimp only [H]
      rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · dsimp only [H]
      rw [max_eq_left h, hR]
      exact le_add_of_nonneg_right (by positivity)
  constructor
  · apply (div_le_iff₀ hden).mpr
    have hpow : (massRadius A n)^8 ≤ (1+|x|)^8 :=
      pow_le_pow_left₀ hR0 ((le_max_left _ _).trans (hxlo.trans (by linarith only [le_abs_self x]))) 8
    rw [hR] at hpow
    have hprod : (A/(2*(n : ℝ)))*(2*(n : ℝ)/A)=1 := by field_simp [hA.ne', hnR.ne']
    calc
      1 = (A/(2*(n : ℝ)))*(2*(n : ℝ)/A) := hprod.symm
      _ ≤ (A/(2*(n : ℝ)))*(1+|x|)^8 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ w*(1+|x|)^8 := mul_le_mul_of_nonneg_right hwlo hden.le
  · apply (le_div_iff₀ hden).mpr
    have hdenH : (1+|x|)^8 ≤ (3*H)^8 := by
      rw [abs_of_nonneg hx0]
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hxhi, hH1]) 8
    have hscale : (A/(n : ℝ))*H^8 ≤ 2+(Real.pi+2)^8*K := by
      have h1 := mul_le_mul_of_nonneg_left hH8 (div_nonneg hA.le hnR.le)
      have he : (A/(n : ℝ))*(2*(n : ℝ)/A)=2 := by field_simp [hA.ne', hnR.ne']
      rw [mul_add, he, mul_pow] at h1
      have hAn : A/(n : ℝ) ≤ A := (div_le_iff₀ hnR).mpr (le_mul_of_one_le_right hA.le hn1)
      have h2 := mul_le_mul_of_nonneg_right hAn
        (mul_nonneg (pow_nonneg hpi.le 8) (pow_nonneg hF0 8))
      have h3 := mul_le_mul_of_nonneg_left hK (pow_nonneg hpi.le 8)
      nlinarith only [h1, h2, h3]
    have h1 := mul_le_mul hwhi hdenH hden.le (by positivity : 0 ≤ 3*A/(2*(n : ℝ)))
    calc
      w*(1+|x|)^8 ≤ (3*A/(2*(n : ℝ)))*(3*H)^8 := h1
      _ = (3 : ℝ)^9/2*((A/(n : ℝ))*H^8) := by ring
      _ ≤ (3 : ℝ)^9/2*(2+(Real.pi+2)^8*K) := mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The cumulative-count term in the height controls the whole equally spaced block. -/
lemma grid_height_interval {A F L : ℝ} {n : ℕ} (_hn : 0 < n) (hL : 1 ≤ L)
    (hF : (n : ℝ) ≤ F) (j : Fin n) :
    let H := max (massRadius A n) ((Real.pi+2)*F)
    H ≤ H+j.val*(Real.pi/(2*L)) ∧ H+j.val*(Real.pi/(2*L)) ≤ 2*H := by
  dsimp only
  let H := max (massRadius A n) ((Real.pi+2)*F)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hF0 : 0 ≤ F := (Nat.cast_nonneg n).trans hF
  have hjF : (j.val : ℝ) ≤ F := (show (j.val : ℝ) ≤ n by exact_mod_cast j.isLt.le).trans hF
  have hstep0 : 0 ≤ Real.pi/(2*L) := div_nonneg Real.pi_pos.le (by positivity)
  have hstep : Real.pi/(2*L) ≤ Real.pi/2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith only [hL])
  have hspan : (j.val : ℝ)*(Real.pi/(2*L)) ≤ H := by
    calc
      _ ≤ F*(Real.pi/2) := mul_le_mul hjF hstep hstep0 hF0
      _ ≤ F*(Real.pi+2) := mul_le_mul_of_nonneg_left (by linarith only [Real.pi_pos]) hF0
      _ = (Real.pi+2)*F := by ring
      _ ≤ H := le_max_right _ _
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j.val) hstep0)
  · change H+j.val*(Real.pi/(2*L)) ≤ 2*H
    linarith only [hspan]

lemma grid_height_injective {L : ℝ} (hL : 0 < L) (H : ℝ) (n : ℕ) :
    Function.Injective (fun j : Fin n => H+j.val*(Real.pi/(2*L))) := by
  intro i j hij
  apply Fin.ext
  have hstep : Real.pi/(2*L) ≠ 0 := (div_pos Real.pi_pos (by positivity)).ne'
  have h := mul_right_cancel₀ hstep (add_left_cancel hij)
  exact_mod_cast h

#print axioms height_weight_bounds
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
