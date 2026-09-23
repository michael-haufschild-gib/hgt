import GaloisForLFunctions.RHTower.XiWardCanonicalTransverseScan
import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle

/-!
# Exact Schwarz-paired Ward cap kernel

At a lower transverse source edge, Schwarz pairing of the literal Ward Cauchy
weight has an exact two-pole form.  This is an algebraic identity for the
actual source weight, with its pole exclusion derived from the canonical
source transverse coordinate.  In particular, its resonant specialization is
recorded explicitly: the pairing alone does not erase the moving `tau = x`
resonance.  Thus this module supplies a kernel-level constraint for any
all-height cap proof; it does not assert a bound for the completed source
trace or an RH-bearing energy estimate.
-/

open Complex

namespace RHTower

noncomputable section

/-- Schwarz-paired literal Ward Cauchy weights on the two reflected points of
the lower canonical transverse cap. -/
def xiWardSchwarzCapDifference (tau s x : ℝ) : ℂ :=
  xiWardCauchySourceWeight
      (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ))
      ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) -
    starRingEnd ℂ
      (xiWardCauchySourceWeight
        (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ))
        (((-x : ℝ) : ℂ) - (xiWardTransverseLevel s : ℂ) * I))

/-- Exact two-pole law for a Schwarz-paired lower cap.  Both denominators have
positive real part, so the formula is unconditional. -/
theorem xiWardSchwarzCapDifference_eq (tau s x : ℝ) :
    xiWardSchwarzCapDifference tau s x =
      (-4 * I * (tau : ℂ)) *
        (((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((tau + x : ℝ) : ℂ)) *
        ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((x - tau : ℝ) : ℂ)))⁻¹ := by
  have htheta := xiWardTransverseLevel_mem_Ioo s
  change 0 < xiWardTransverseLevel s ∧ xiWardTransverseLevel s < 1 / 2 at htheta
  have ha : (0 : ℝ) < 51 / 100 + xiWardTransverseLevel s := by
    linarith [htheta.1]
  have h₁ :
      (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ) +
        I * ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  have h₂ :
      (((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ) +
        I * ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hconjW :
      starRingEnd ℂ (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) =
        ((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ) := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have hconjZ :
      starRingEnd ℂ (((-x : ℝ) : ℂ) -
        (xiWardTransverseLevel s : ℂ) * I) =
        ((-x : ℝ) : ℂ) + (xiWardTransverseLevel s : ℂ) * I := by
    rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have hItheta :
      I * ((xiWardTransverseLevel s : ℂ) * I) =
        -(xiWardTransverseLevel s : ℂ) := by
    calc
      I * ((xiWardTransverseLevel s : ℂ) * I) =
          (xiWardTransverseLevel s : ℂ) * I ^ (2 : ℕ) := by ring
      _ = -(xiWardTransverseLevel s : ℂ) := by rw [I_sq]; ring
  have hden₁ :
      ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
        I * ((tau + x : ℝ) : ℂ)) =
        ((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ) +
          I * ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hden₂ :
      ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
        I * ((x - tau : ℝ) : ℂ)) =
        ((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ) +
          I * ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hden₁ne :
      ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
        I * ((tau + x : ℝ) : ℂ)) ≠ 0 := hden₁.trans_ne h₁
  have hden₂ne :
      ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
        I * ((x - tau : ℝ) : ℂ)) ≠ 0 := hden₂.trans_ne h₂
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    simpa using map_natCast (starRingEnd ℂ) 2
  have hsecond :
      ((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ) +
        (-I) * (((-x : ℝ) : ℂ) + (xiWardTransverseLevel s : ℂ) * I) =
        ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((x - tau : ℝ) : ℂ)) := by
    push_cast
    rw [neg_mul, mul_add, mul_neg, hItheta]
    ring
  unfold xiWardSchwarzCapDifference xiWardCauchySourceWeight
  rw [map_mul (starRingEnd ℂ), map_inv₀ (starRingEnd ℂ),
    map_add (starRingEnd ℂ), hconjW, map_mul (starRingEnd ℂ),
    Complex.conj_I, hconjZ]
  rw [htwo, hden₁.symm, hsecond]
  calc
    2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))⁻¹ -
        2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau))⁻¹ =
      (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))⁻¹ * 2 -
        (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau))⁻¹ * 2 := by ring
    _ = (2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau)) -
          2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))) *
        ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x)) *
          (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau)))⁻¹ := by
      calc
        (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))⁻¹ * 2 -
            (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau))⁻¹ * 2 =
          ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))⁻¹ -
            (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau))⁻¹) * 2 := by ring
        _ = ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau) -
              (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))) /
            ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x)) *
              (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau))) ) * 2 := by
          rw [inv_sub_inv hden₁ne hden₂ne]
        _ = (2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau)) -
              2 * (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x))) *
            ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x)) *
              (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau)))⁻¹ := by
          rw [div_eq_mul_inv]
          ring
    _ = (-4 * I * (tau : ℂ)) *
        ((↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(tau + x)) *
          (↑(51 / 100 + xiWardTransverseLevel s) + I * ↑(x - tau)))⁻¹ := by
      congr 1
      push_cast
      ring

/-- At the symmetric height `tau = 0`, the Schwarz-paired cap kernel cancels exactly. -/
theorem xiWardSchwarzCapDifference_zero (s x : ℝ) :
    xiWardSchwarzCapDifference 0 s x = 0 := by
  rw [xiWardSchwarzCapDifference_eq]
  simp

/-- Exact moving-resonance specialization.  One Cauchy denominator is the fixed
positive transverse distance, so Schwarz pairing alone cannot be treated as a
uniform two-large-denominator estimate. -/
theorem xiWardSchwarzCapDifference_resonant (s x : ℝ) :
    xiWardSchwarzCapDifference x s x =
      (-4 * I * (x : ℂ)) *
        (((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((2 * x : ℝ) : ℂ)) *
        (((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ))⁻¹ := by
  rw [xiWardSchwarzCapDifference_eq]
  congr 2
  · push_cast
    ring

/-- The exact Schwarz cap kernel is continuous in the cap height.  Its two
denominators never vanish because their common real part is strictly positive. -/
theorem continuous_xiWardSchwarzCapDifference (tau s : ℝ) :
    Continuous (fun x : ℝ => xiWardSchwarzCapDifference tau s x) := by
  rw [show (fun x : ℝ => xiWardSchwarzCapDifference tau s x) =
      fun x : ℝ =>
        (-4 * I * (tau : ℂ)) *
          (((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
            I * ((tau + x : ℝ) : ℂ)) *
          ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
            I * ((x - tau : ℝ) : ℂ)))⁻¹ by
      funext x
      exact xiWardSchwarzCapDifference_eq tau s x]
  apply Continuous.mul continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro x
    apply mul_ne_zero
    all_goals
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [Complex.add_re, Complex.mul_re] at hre
      have hlevel := xiWardTransverseLevel_mem_Ioo s
      have hpos : 0 < 51 / 100 + xiWardTransverseLevel s := by
        linarith [hlevel.1]
      linarith

end

end RHTower
