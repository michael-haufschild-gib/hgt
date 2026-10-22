import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninCofinalReciprocalGaugeRigidity
import GaloisForLFunctions.RHTower.RiemannSingularGreenHodgeAdmissionLaw

/-!
# Singular Green sewing and Sonin Weyl escape

The actual Calderón--Witt Gamma reflection transport contains two reciprocal sewing costs.  Their
Weyl lower envelope is exactly the Sonin escape-cancelling cusp, with source coefficient fixed by
the two prime clocks and valuation depth.  Thus the singular Green survivor and the Hedenmalm--
Sonin survivor are the same determinant-one Cartan mechanism before and after Weyl reduction.

Raw oriented sewing remains reciprocal.  Weyl reduction makes the lower cost reflection-even and
creates a strict reciprocity defect at every nonzero displacement.  On the Riemann boundary this
defect is unit exactly on the critical line, and globally exactly under RH.
-/

open Complex Real Set

noncomputable section

namespace RHTower

def deningerCalderonWittGammaWeylLowerSewingCost
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  min (deningerCalderonWittGammaReflectionSewingCost a p q n)
    (deningerCalderonWittGammaReflectionSewingCost (-a) p q n)

theorem deningerCalderonWittGammaWeylLowerSewingCost_eq
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost a p q n =
      Real.exp (-2 * |a| *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) := by
  have hL : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) := by
    exact add_pos
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt))
  rcases le_total a 0 with ha | ha
  · rw [deningerCalderonWittGammaWeylLowerSewingCost,
      deningerCalderonWittGammaReflectionSewingCost_eq_exp,
      deningerCalderonWittGammaReflectionSewingCost_eq_exp,
      min_eq_left]
    · rw [abs_of_nonpos ha]
      congr 1
      ring
    · rw [Real.exp_le_exp]
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hcoef : 0 ≤
          2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by
        positivity
      calc
        2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) =
            a * (2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) := by ring
        _ ≤ (-a) * (2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hcoef
        _ = 2 * -a * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by ring
  · rw [deningerCalderonWittGammaWeylLowerSewingCost,
      deningerCalderonWittGammaReflectionSewingCost_eq_exp,
      deningerCalderonWittGammaReflectionSewingCost_eq_exp,
      min_eq_right]
    · rw [abs_of_nonneg ha]
      congr 1
      ring
    · rw [Real.exp_le_exp]
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hcoef : 0 ≤
          2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by
        positivity
      calc
        2 * -a * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) =
            (-a) * (2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) := by ring
        _ ≤ a * (2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hcoef
        _ = 2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by ring

theorem deningerCalderonWittGammaWeylLowerSewingCost_eq_soninModulus
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost a p q n =
      soninEscapeCancellingGaugeModulus
        (2 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) a := by
  rw [deningerCalderonWittGammaWeylLowerSewingCost_eq,
    soninEscapeCancellingGaugeModulus]
  congr 1
  ring

theorem deningerCalderonWittGammaWeylLowerSewingCost_reflect
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost (-a) p q n =
      deningerCalderonWittGammaWeylLowerSewingCost a p q n := by
  rw [deningerCalderonWittGammaWeylLowerSewingCost_eq,
    deningerCalderonWittGammaWeylLowerSewingCost_eq, abs_neg]

theorem deningerCalderonWittGammaWeylReciprocityDefect_eq
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost (-a) p q n *
        deningerCalderonWittGammaWeylLowerSewingCost a p q n =
      Real.exp (-4 * |a| *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) := by
  rw [deningerCalderonWittGammaWeylLowerSewingCost_reflect,
    deningerCalderonWittGammaWeylLowerSewingCost_eq, ← Real.exp_add]
  congr 1
  ring

theorem deningerCalderonWittGammaWeylReciprocityDefect_eq_one_iff
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost (-a) p q n *
        deningerCalderonWittGammaWeylLowerSewingCost a p q n = 1 ↔
      a = 0 := by
  rw [deningerCalderonWittGammaWeylReciprocityDefect_eq,
    Real.exp_eq_one_iff]
  have hL : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) := by
    exact add_pos
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt))
  have hn : 0 < (n : ℝ) + 1 := by positivity
  constructor
  · intro h
    have hcoef : 0 <
        4 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by
      positivity
    have habs : |a| = 0 := by
      have hprod : |a| *
          (4 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) = 0 := by
        nlinarith
      exact (mul_eq_zero.mp hprod).resolve_right hcoef.ne'
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

theorem deningerCalderonWittGammaWeylLowerSewingCost_boundaryFracture_eq
    (rho : ℂ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost
        (xiNearbyPoleDualityAdjunctionFracture rho).re p q n =
      soninEscapeCancellingGaugeModulus
        (4 * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1))
        (rho.re - 1 / 2) := by
  have hfracture :
      (xiNearbyPoleDualityAdjunctionFracture rho).re =
        2 * (rho.re - 1 / 2) := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    simp
  rw [deningerCalderonWittGammaWeylLowerSewingCost_eq,
    hfracture,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    soninEscapeCancellingGaugeModulus]
  congr 1
  ring

theorem deningerCalderonWittGammaWeylReciprocityDefect_boundaryFracture_eq_one_iff
    (rho : ℂ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylLowerSewingCost
          (-(xiNearbyPoleDualityAdjunctionFracture rho).re) p q n *
        deningerCalderonWittGammaWeylLowerSewingCost
          (xiNearbyPoleDualityAdjunctionFracture rho).re p q n = 1 ↔
      rho.re = 1 / 2 := by
  rw [deningerCalderonWittGammaWeylReciprocityDefect_eq_one_iff,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

theorem all_deningerCalderonWittGammaWeylReciprocityDefect_eq_one_iff_rh
    (p q : Nat.Primes) (n : ℕ) :
    (∀ rho : XiDivisorSupport,
      deningerCalderonWittGammaWeylLowerSewingCost
            (-(xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re) p q n *
          deningerCalderonWittGammaWeylLowerSewingCost
            (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re p q n = 1) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
    intro rho
    have hline :=
      (deningerCalderonWittGammaWeylReciprocityDefect_boundaryFracture_eq_one_iff
        (rho : ℂ) p q n).1 (h rho)
    rw [xiSpectralPointSupport_im, hline]
    norm_num
  · intro hRH rho
    apply
      (deningerCalderonWittGammaWeylReciprocityDefect_boundaryFracture_eq_one_iff
        (rho : ℂ) p q n).2
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end RHTower
