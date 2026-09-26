import GaloisForLFunctions.RHTower.AnharmonicChebyshevMovingFiber
import GaloisForLFunctions.RHTower.AnharmonicCubicZeroFiber
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

/-!
# Cubic anharmonic descent criterion for RH

The anharmonic quotient coordinate

`q(s) = ((s - 2)(s + 1)(2s - 1)) / (2s(s - 1))`

is fixed by the order-three Mobius action and changes sign under reflection
`s ↦ 1 - s`. Consequently `q(s)^(2 : ℕ)` descends through the full six-point
anharmonic orbit. This file proves the exact Xi-zero endpoint: the square of
the descended coordinate is strictly negative real at every Xi zero if and
only if RH holds.

The reverse implication is not inferred from the sign alone. Exact fibre
classification leaves two extra real circles, `|s| = 1` and `|1-s| = 1`.
The unconditional Xi height gap excludes both, leaving only `re s = 1/2`.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- A complex number represented by a strictly negative real scalar. -/
def IsStrictlyNegativeReal (z : ℂ) : Prop :=
  ∃ x : ℝ, x < 0 ∧ z = (x : ℂ)

/-- The anharmonic quotient has real coefficients, hence commutes with
complex conjugation. -/
theorem chebyshevAnharmonicQ_map_conj (s : ℂ) :
    chebyshevAnharmonicQ (starRingEnd ℂ s) =
      starRingEnd ℂ (chebyshevAnharmonicQ s) := by
  simp only [chebyshevAnharmonicQ, map_div₀, map_mul, map_sub, map_add,
    map_one]
  rw [map_ofNat]

/-- The quotient coordinate does not vanish on an actual Xi zero. The three
zeros of its numerator are real, whereas every Xi zero has squared imaginary
part greater than one. -/
theorem chebyshevAnharmonicQ_ne_zero_of_xiZeroCopy (q : XiZeroCopy) :
    chebyshevAnharmonicQ (q.1 : ℂ) ≠ 0 := by
  let s : ℂ := q.1
  have him : 1 < s.im ^ (2 : ℕ) := by
    simpa only [s] using xiZeroCopy_one_lt_im_sq q
  have hsne (x : ℝ) : s ≠ (x : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [ofReal_im] at hi
    rw [hi] at him
    norm_num at him
  have hs0 : s ≠ 0 := by simpa using hsne 0
  have hs1 : s ≠ 1 := by simpa using hsne 1
  intro hq
  rcases (chebyshevAnharmonicQ_eq_zero_iff_orbit s).mp
      ⟨hs0, hs1, hq⟩ with htwo | hminus | hhalf
  · exact hsne 2 (by simpa using htwo)
  · exact hsne (-1) (by simpa using hminus)
  · exact hsne (1 / 2) (by simpa using hhalf)

/-- On the critical line the anharmonic quotient is purely imaginary. -/
theorem xiZeroCopy_chebyshevAnharmonicQ_re_eq_zero_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (chebyshevAnharmonicQ (q.1 : ℂ)).re = 0 := by
  let s : ℂ := q.1
  have hs0 : s ≠ 0 := by
    have him := xiZeroCopy_one_lt_im_sq q
    change 1 < s.im ^ (2 : ℕ) at him
    intro h
    rw [h] at him
    norm_num at him
  have hs1 : s ≠ 1 := by
    have him := xiZeroCopy_one_lt_im_sq q
    change 1 < s.im ^ (2 : ℕ) at him
    intro h
    rw [h] at him
    norm_num at him
  have hfix : 1 - starRingEnd ℂ s = s := by
    apply Complex.ext
    · change 1 - s.re = s.re
      change s.re = 1 / 2 at hline
      linarith
    · simp
  have hconj0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hconj1 : starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg (starRingEnd ℂ) h
  have hq : chebyshevAnharmonicQ s =
      -starRingEnd ℂ (chebyshevAnharmonicQ s) := by
    calc
      chebyshevAnharmonicQ s =
          chebyshevAnharmonicQ
            (chebyshevAnharmonicSigma (starRingEnd ℂ s)) := by
              rw [chebyshevAnharmonicSigma, hfix]
      _ = -chebyshevAnharmonicQ (starRingEnd ℂ s) :=
        chebyshevAnharmonicQ_sigma hconj0 hconj1
      _ = -starRingEnd ℂ (chebyshevAnharmonicQ s) := by
        rw [chebyshevAnharmonicQ_map_conj]
  have hre := congrArg Complex.re hq
  change (chebyshevAnharmonicQ s).re = 0
  simp at hre
  linarith

/-- Critical-line placement makes the squared quotient coordinate strictly
negative real. Strictness uses nonvanishing at Xi zeros. -/
theorem xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    IsStrictlyNegativeReal (chebyshevAnharmonicQ (q.1 : ℂ) ^ (2 : ℕ)) := by
  let Q := chebyshevAnharmonicQ (q.1 : ℂ)
  have hQre : Q.re = 0 :=
    xiZeroCopy_chebyshevAnharmonicQ_re_eq_zero_of_re_eq_half q hline
  have hQne : Q ≠ 0 := chebyshevAnharmonicQ_ne_zero_of_xiZeroCopy q
  have hQim : Q.im ≠ 0 := by
    intro him
    apply hQne
    apply Complex.ext <;> simp [hQre, him]
  refine ⟨-(Q.im ^ (2 : ℕ)), neg_lt_zero.mpr (sq_pos_of_ne_zero hQim), ?_⟩
  apply Complex.ext
  · simp only [pow_two, mul_re, ofReal_re]
    rw [hQre]
    ring
  · simp only [pow_two, mul_im, ofReal_im]
    rw [hQre]
    ring

/-- A strictly negative real squared quotient coordinate forces critical-line
placement. Fibre classification first permits two unit-circle alternatives;
the Xi height gap rules both out. -/
theorem xiZeroCopy_re_eq_half_of_chebyshevAnharmonicQ_sq_strictlyNegativeReal
    (q : XiZeroCopy)
    (hneg : IsStrictlyNegativeReal
      (chebyshevAnharmonicQ (q.1 : ℂ) ^ (2 : ℕ))) :
    (q.1 : ℂ).re = 1 / 2 := by
  let s : ℂ := q.1
  let Q : ℂ := chebyshevAnharmonicQ s
  obtain ⟨x, hx, hsq⟩ := hneg
  have hreSq := congrArg Complex.re hsq
  have himSq := congrArg Complex.im hsq
  simp only [pow_two, mul_re, mul_im, ofReal_re, ofReal_im] at hreSq himSq
  have hQre : Q.re = 0 := by
    by_contra hre
    have hprod : Q.re * Q.im = 0 := by linarith
    have hQim : Q.im = 0 := (mul_eq_zero.mp hprod).resolve_left hre
    rw [hQim] at hreSq
    nlinarith [sq_nonneg Q.re]
  have him : 1 < s.im ^ (2 : ℕ) := by
    simpa only [s] using xiZeroCopy_one_lt_im_sq q
  have hsne (y : ℝ) : s ≠ (y : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [ofReal_im] at hi
    rw [hi] at him
    norm_num at him
  have hs0 : s ≠ 0 := by simpa using hsne 0
  have hs1 : s ≠ 1 := by simpa using hsne 1
  have hz0 : 1 - starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs1
    have hc : starRingEnd ℂ s = 1 := by linear_combination -h
    have := congrArg (starRingEnd ℂ) hc
    simpa using this
  have hz1 : 1 - starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs0
    have hc : starRingEnd ℂ s = 0 := by linear_combination -h
    have := congrArg (starRingEnd ℂ) hc
    simpa using this
  have hconj0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hconj1 : starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg (starRingEnd ℂ) h
  have hQnegconj : Q = -starRingEnd ℂ Q := by
    apply Complex.ext
    · simp [hQre]
    · simp
  have hfiberQ : chebyshevAnharmonicQ (1 - starRingEnd ℂ s) =
      chebyshevAnharmonicQ s := by
    calc
      chebyshevAnharmonicQ (1 - starRingEnd ℂ s) =
          -chebyshevAnharmonicQ (starRingEnd ℂ s) :=
        chebyshevAnharmonicQ_sigma hconj0 hconj1
      _ = -starRingEnd ℂ (chebyshevAnharmonicQ s) := by
        rw [chebyshevAnharmonicQ_map_conj]
      _ = chebyshevAnharmonicQ s := hQnegconj.symm
  rcases (chebyshevAnharmonicQ_fiber_iff hs0 hs1 hz0 hz1).mp hfiberQ with
      hline | hcircle0 | hcircle1
  · have hre := congrArg Complex.re hline
    simp at hre
    change s.re = 1 / 2
    linarith
  · have hmul := congrArg (fun z : ℂ => z * s) hcircle0
    simp only [chebyshevAnharmonicW] at hmul
    rw [div_mul_cancel₀ _ hs0] at hmul
    have hnorm : (starRingEnd ℂ s) * s = 1 := by
      linear_combination -hmul
    have hre := congrArg Complex.re hnorm
    simp at hre
    nlinarith [sq_nonneg s.re]
  · have hmul := congrArg (fun z : ℂ => z * (1 - s)) hcircle1
    simp only [chebyshevAnharmonicWTwo] at hmul
    rw [one_div, inv_mul_cancel₀ (sub_ne_zero.mpr hs1.symm)] at hmul
    have hre := congrArg Complex.re hmul
    simp at hre
    nlinarith [sq_nonneg (1 - s.re)]

/-- Pointwise cubic-coordinate criterion on an actual Xi zero. -/
theorem xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_iff_re_eq_half
    (q : XiZeroCopy) :
    IsStrictlyNegativeReal (chebyshevAnharmonicQ (q.1 : ℂ) ^ (2 : ℕ)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact
    ⟨xiZeroCopy_re_eq_half_of_chebyshevAnharmonicQ_sq_strictlyNegativeReal q,
      xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_of_re_eq_half q⟩

/-- Every copied Xi divisor maps to the strictly negative real quotient ray. -/
def AllXiZeroChebyshevQSquaresStrictlyNegative : Prop :=
  ∀ q : XiZeroCopy,
    IsStrictlyNegativeReal (chebyshevAnharmonicQ (q.1 : ℂ) ^ (2 : ℕ))

/-- Exact cubic anharmonic descent endpoint: RH holds iff every Xi zero maps
to the strictly negative real ray under `q(s)^(2 : ℕ)`. -/
theorem allXiZeroChebyshevQSquaresStrictlyNegative_iff_riemannHypothesis :
    AllXiZeroChebyshevQSquaresStrictlyNegative ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let rhoSupport : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hpos := xi_divisor_pos_on_support rhoSupport
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by
      omega
    let q : XiZeroCopy :=
      ⟨rhoSupport, ⟨0, hn⟩⟩
    exact
      (xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_iff_re_eq_half q).1
        (h q)
  · intro hRH q
    apply
      (xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_iff_re_eq_half q).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)

end

end RHTower
