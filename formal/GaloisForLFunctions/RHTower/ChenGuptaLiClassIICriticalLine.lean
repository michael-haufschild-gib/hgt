/-
# Chen--Gupta--Li class-II critical-line finite packet

Chen--Gupta--Li bound class-II zeros by a fourth moment of Dirichlet
L-functions sampled on the critical line.  This module makes the finite
character/ordinate packet and its detector values literal.  It proves the
closed fourth-moment large-value reduction, including the finite Möbius
mollifier factor.  The analytic fourth-moment estimate itself is a subsequent
source layer.

No RH, GRH, zero-density, zero-detection, or moment premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues
import GaloisForLFunctions.RHTower.ChenGuptaLiMollifierBound

open Complex

noncomputable section

namespace RHTower

/-- The actual Dirichlet-L value at the critical-line ordinate of a CGL row. -/
def cglClassIICriticalLineLValue {q : ℕ} (w : CGLCharacterDyadicRowData (q + 1)) : ℂ :=
  DirichletCharacter.LFunction w.character (cglCriticalLinePoint w.time).1

/-- The class-II finite detector value: the truncated Möbius inverse times the
critical-line Dirichlet-L value. -/
def cglClassIICriticalLineDetectorValue (X q : ℕ)
    (w : CGLCharacterDyadicRowData (q + 1)) : ℂ :=
  zeroDetectionMobiusPolynomial X (q + 1) w.character (cglCriticalLinePoint w.time).1 *
    cglClassIICriticalLineLValue w

/-- The class-II detector is controlled by the closed finite Möbius cutoff
times the corresponding critical-line Dirichlet-L value. -/
theorem norm_cglClassIICriticalLineDetectorValue_le (X q : ℕ)
    (w : CGLCharacterDyadicRowData (q + 1)) :
    ‖cglClassIICriticalLineDetectorValue X q w‖ ≤ ((X : ℝ) + 1) *
      ‖cglClassIICriticalLineLValue w‖ := by
  unfold cglClassIICriticalLineDetectorValue
  rw [norm_mul]
  calc
    ‖zeroDetectionMobiusPolynomial X (q + 1) w.character (cglCriticalLinePoint w.time).1‖ *
        ‖cglClassIICriticalLineLValue w‖ ≤
      ((X : ℝ) + 1) * ‖cglClassIICriticalLineLValue w‖ :=
      mul_le_mul_of_nonneg_right
        (by
          simpa only [Nat.cast_add, Nat.cast_one] using
            norm_zeroDetectionMobiusPolynomial_criticalLine_le_cutoff X (q + 1) w.character w.time)
        (norm_nonneg _)

/-- Rows whose literal class-II detector value exceeds a nonnegative finite
threshold. -/
def cglClassIICriticalLineLargeValues (X q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (V : NNReal) : Finset (Fin R) :=
  Finset.univ.filter fun r => (V : ℝ) ≤ ‖cglClassIICriticalLineDetectorValue X q (w r)‖

/-- Closed finite class-II fourth-moment large-value reduction.  Any bound for
the displayed sampled L-function fourth moment can now be inserted without
changing the detector or character carriers. -/
theorem card_cglClassIICriticalLineLargeValues_mul_fourth_le (X q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (V : NNReal) :
    ((cglClassIICriticalLineLargeValues X q R w V).card : ℝ) * (V : ℝ) ^ 4 ≤
      ((X : ℝ) + 1) ^ 4 * ∑ r : Fin R, ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by
  let S := cglClassIICriticalLineLargeValues X q R w V
  have hlarge : ∀ r ∈ S, (V : ℝ) ^ 4 ≤
      ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by
    intro r hr
    have hr' : (V : ℝ) ≤ ‖cglClassIICriticalLineDetectorValue X q (w r)‖ :=
      (Finset.mem_filter.mp hr).2
    have hdet : (V : ℝ) ^ 4 ≤ ‖cglClassIICriticalLineDetectorValue X q (w r)‖ ^ 4 :=
      pow_le_pow_left₀ NNReal.zero_le_coe hr' 4
    calc
      (V : ℝ) ^ 4 ≤ ‖cglClassIICriticalLineDetectorValue X q (w r)‖ ^ 4 := hdet
      _ ≤ (((X : ℝ) + 1) * ‖cglClassIICriticalLineLValue (w r)‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_cglClassIICriticalLineDetectorValue_le X q (w r)) 4
      _ = ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by ring
  have hsum : (S.card : ℝ) * (V : ℝ) ^ 4 ≤
      ∑ r ∈ S, ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by
    calc
      (S.card : ℝ) * (V : ℝ) ^ 4 = ∑ _r ∈ S, (V : ℝ) ^ 4 := by simp
      _ ≤ ∑ r ∈ S, ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 :=
        Finset.sum_le_sum hlarge
  calc
    (S.card : ℝ) * (V : ℝ) ^ 4 ≤
      ∑ r ∈ S, ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := hsum
    _ ≤ ∑ r : Fin R, ((X : ℝ) + 1) ^ 4 * ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro r hrS hrU
      positivity
    _ = ((X : ℝ) + 1) ^ 4 * ∑ r : Fin R, ‖cglClassIICriticalLineLValue (w r)‖ ^ 4 := by
      rw [Finset.mul_sum]

end RHTower
