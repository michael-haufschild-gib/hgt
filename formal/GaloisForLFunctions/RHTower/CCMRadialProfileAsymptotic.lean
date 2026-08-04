import GaloisForLFunctions.RHTower.BesselJZeroConstant
import GaloisForLFunctions.RHTower.CCMRadialProlateProfileMeasure

/-!
# The fixed-degree radial profile

Assembling the radial profile of the constrained source means composing three unconditional facts:

* the Bessel asymptotic with its constant, `J_0(v) = sqrt(2/(pi v)) cos(v - pi/4) + O(v^{-3/4})`;
* the second-order phase expansion `xi_s(x) = sqrt(x²-1) - (s/2) theta(x) + O(s²)`;
* the amplitude expansion `A_s(x) = x^{-1/2} + O(s)`.

This file provides the two conversion steps that make the composition possible: the amplitude–phase form of
the Bessel asymptotic, and the transport of the phase expansion through the cosine.  With `c s = 2n+1` from
the separation law, the phase `c xi_s(x)` becomes `c sqrt(x²-1) - (2n+1) theta(x)/2` up to `O(c s²) = O(1/c)`,
which is exactly the degree marking of the card's `(8)`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## The amplitude–phase form of the Bessel asymptotic -/

/-- `cos v + sin v = sqrt 2 cos(v - pi/4)`: the phase shift `pi/4` in trigonometric form. -/
theorem cos_add_sin_eq (v : ℝ) :
    Real.cos v + Real.sin v = Real.sqrt 2 * Real.cos (v - Real.pi / 4) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h : Real.sqrt 2 * (Real.cos v * (Real.sqrt 2 / 2) + Real.sin v * (Real.sqrt 2 / 2))
      = Real.sqrt 2 ^ 2 / 2 * (Real.cos v + Real.sin v) := by ring
  rw [h, hs2]
  ring

theorem sqrt_two_div_pi_eq : Real.sqrt (2 / Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi :=
  Real.sqrt_div (by norm_num) Real.pi

/-- **The Bessel asymptotic in amplitude–phase form.**
`|J_0(v) - sqrt(2/(pi)) cos(v - pi/4)/sqrt v| <= 5/(v^{3/4})`. -/
theorem abs_besselJ0_sub_amplitude_le {v : ℝ} (hv : 1 ≤ v) :
    |besselJ0 v - Real.sqrt (2 / Real.pi) * Real.cos (v - Real.pi / 4) / Real.sqrt v|
      ≤ 5 / (Real.sqrt v * Real.sqrt (Real.sqrt v)) := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le zero_lt_one hv
  have hsv : (1 : ℝ) ≤ Real.sqrt v := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hv
  have hsv0 : (0 : ℝ) < Real.sqrt v := lt_of_lt_of_le zero_lt_one hsv
  have ht0 : (0 : ℝ) < Real.sqrt (Real.sqrt v) := Real.sqrt_pos.mpr hsv0
  have hspi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hmain := abs_sqrt_mul_besselJ0_sub_le hv
  -- rewrite the target constant
  have hconst : Real.sqrt (2 / Real.pi) * Real.cos (v - Real.pi / 4) / Real.sqrt v
      = (Real.cos v + Real.sin v) / Real.sqrt Real.pi / Real.sqrt v := by
    rw [sqrt_two_div_pi_eq, cos_add_sin_eq v]
    field_simp
  rw [hconst]
  -- divide the main estimate by `sqrt v`
  have hne : Real.sqrt v ≠ 0 := ne_of_gt hsv0
  have hinner : besselJ0 v - (Real.cos v + Real.sin v) / Real.sqrt Real.pi / Real.sqrt v
      = (Real.sqrt v * besselJ0 v - (Real.cos v + Real.sin v) / Real.sqrt Real.pi)
        / Real.sqrt v := by
    field_simp
  rw [hinner, abs_div, abs_of_pos hsv0, div_le_div_iff₀ hsv0 (by positivity)]
  have hstep : |Real.sqrt v * besselJ0 v - (Real.cos v + Real.sin v) / Real.sqrt Real.pi|
      * (Real.sqrt v * Real.sqrt (Real.sqrt v))
      ≤ (5 / Real.sqrt (Real.sqrt v)) * (Real.sqrt v * Real.sqrt (Real.sqrt v)) :=
    mul_le_mul_of_nonneg_right hmain (by positivity)
  refine le_trans hstep ?_
  have hval : (5 / Real.sqrt (Real.sqrt v)) * (Real.sqrt v * Real.sqrt (Real.sqrt v))
      = 5 * Real.sqrt v := by
    field_simp
  rw [hval]

/-! ## Transporting the phase expansion through the cosine -/

/-- The second-order phase expansion, transported through the cosine: the phase of the Bessel model differs
from the card's `c sqrt(x²-1) - (c s/2) theta(x)` by at most `c s²/4` times the endpoint logarithm. -/
theorem abs_cos_phase_sub_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 ≤ x)
    (hc : 0 ≤ c) :
    |Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
        - Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)|
      ≤ c * (s ^ 2 / 4) * GaloisForLFunctions.HTGeometry.endpointLog x := by
  have hphase := abs_xiEndpointPhase_sub_second_order_le hs0 hs1 hx
  have hlip := Real.abs_cos_sub_cos_le (c * xiEndpointPhase s x - Real.pi / 4)
    (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)
  refine le_trans hlip ?_
  have hval : c * xiEndpointPhase s x - Real.pi / 4
      - (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)
      = c * (xiEndpointPhase s x - (Real.sqrt (x ^ 2 - 1) - s / 2 * radialAngle x)) := by
    ring
  rw [hval, abs_mul, abs_of_nonneg hc]
  have hstep : c * |xiEndpointPhase s x - (Real.sqrt (x ^ 2 - 1) - s / 2 * radialAngle x)|
      ≤ c * (s ^ 2 / 4 * GaloisForLFunctions.HTGeometry.endpointLog x) :=
    mul_le_mul_of_nonneg_left hphase hc
  calc c * |xiEndpointPhase s x - (Real.sqrt (x ^ 2 - 1) - s / 2 * radialAngle x)|
      ≤ c * (s ^ 2 / 4 * GaloisForLFunctions.HTGeometry.endpointLog x) := hstep
    _ = c * (s ^ 2 / 4) * GaloisForLFunctions.HTGeometry.endpointLog x := by ring


/-! ## The radial profile

The amplitude of the model, rescaled by `sqrt c`, is *exactly* an algebraic fourth root: the phase inside
`A_s` cancels against the Bessel amplitude `(c xi)^{-1/2}`,

```text
sqrt c · A_s(x) / sqrt(c xi_s(x)) = [(x²-1)(x²-s)]^{-1/4},
```

with no error at all.  So the profile is the fourth root times the cosine, and the three errors are the
Bessel remainder, the phase expansion and the `s`-dependence of the fourth root. -/

/-- The algebraic fourth root `[(x²-1)(x²-s)]^{-1/4}`, the exact amplitude of the model. -/
def ampFourth (s x : ℝ) : ℝ := 1 / Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))

theorem ampFourth_pos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : 0 < ampFourth s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  rw [ampFourth]
  have : (0 : ℝ) < Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hd hn))
  positivity

/-- **The exact amplitude identity.**  The Liouville–Green amplitude, rescaled by `sqrt c` and divided by the
Bessel amplitude, is the algebraic fourth root — the phase cancels identically. -/
theorem sqrt_mul_xiAmplitude_div_eq {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    Real.sqrt c * xiAmplitude s x / Real.sqrt (c * xiEndpointPhase s x) = ampFourth s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hsph : 0 < Real.sqrt (xiEndpointPhase s x) := Real.sqrt_pos.mpr hph
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hD : 0 < Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hd hn))
  have hsplit : Real.sqrt (c * xiEndpointPhase s x)
      = Real.sqrt c * Real.sqrt (xiEndpointPhase s x) := Real.sqrt_mul hc.le _
  rw [hsplit, xiAmplitude, ampFourth]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-- **The fixed-degree radial profile.**  For every aperture and every admissible separation constant,

```text
|sqrt c A_s(x) J_0(c xi_s(x)) - sqrt(2/pi) [(x²-1)x²]^{-1/4} cos(c sqrt(x²-1) - c(s/2) theta(x) - pi/4)|
```

is at most the sum of three explicit errors: the phase expansion `c s²/4 · log(x + sqrt(x²-1))`, the
`s`-dependence of the fourth root, and the Bessel remainder `5 (c xi_s(x))^{-1/4}`.  With the separation law
`s = (2n+1)/c + O(c^{-2})` all three are `o(1)` on compacts, and `c s/2 = (2n+1)/2` is the degree marking —
this is the card's `(8)`. -/
theorem abs_radialProfile_sub_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) (hcxi : 1 ≤ c * xiEndpointPhase s x) :
    |Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        - Real.sqrt (2 / Real.pi) * ampFourth 0 x
          * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * ampFourth s x
          * (c * (s ^ 2 / 4) * GaloisForLFunctions.HTGeometry.endpointLog x)
        + Real.sqrt (2 / Real.pi) * |ampFourth s x - ampFourth 0 x|
        + 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hA : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx
  have hv0 : (0 : ℝ) < c * xiEndpointPhase s x := mul_pos hc hph
  have hsv0 : (0 : ℝ) < Real.sqrt (c * xiEndpointPhase s x) := Real.sqrt_pos.mpr hv0
  have hT : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hamp : 0 < ampFourth s x := ampFourth_pos hs1 hx
  have hratio := sqrt_mul_xiAmplitude_div_eq hs0 hs1 hx hc
  -- the Bessel remainder
  have hbes := abs_besselJ0_sub_amplitude_le hcxi
  have hrem : |Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        - Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
    have hfac : Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        - Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
        = (Real.sqrt c * xiAmplitude s x)
          * (besselJ0 (c * xiEndpointPhase s x)
            - Real.sqrt (2 / Real.pi) * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
              / Real.sqrt (c * xiEndpointPhase s x)) := by
      have hx1 : Real.sqrt (2 / Real.pi) * ampFourth s x
          = (Real.sqrt c * xiAmplitude s x) * (Real.sqrt (2 / Real.pi)
            / Real.sqrt (c * xiEndpointPhase s x)) := by
        rw [← hratio]
        field_simp
      rw [hx1]
      field_simp
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt c * xiAmplitude s x)]
    have hstep := mul_le_mul_of_nonneg_left hbes
      (le_of_lt (by positivity : (0 : ℝ) < Real.sqrt c * xiAmplitude s x))
    refine le_trans hstep ?_
    have hval : (Real.sqrt c * xiAmplitude s x)
        * (5 / (Real.sqrt (c * xiEndpointPhase s x)
          * Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))))
        = 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
      rw [← hratio]
      field_simp
    rw [hval]
  -- the phase error
  have hphase := abs_cos_phase_sub_le (s := s) (c := c) hs0 hs1 hx.le hc.le
  have hph2 : |Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
      - Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * ampFourth s x
        * (c * (s ^ 2 / 4) * GaloisForLFunctions.HTGeometry.endpointLog x) := by
    rw [← mul_sub, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt (2 / Real.pi) * ampFourth s x)]
    exact mul_le_mul_of_nonneg_left hphase (by positivity)
  -- the amplitude error
  have hamp2 : |Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)
      - Real.sqrt (2 / Real.pi) * ampFourth 0 x
        * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * |ampFourth s x - ampFourth 0 x| := by
    have hfac : Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)
        - Real.sqrt (2 / Real.pi) * ampFourth 0 x
          * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4)
        = Real.sqrt (2 / Real.pi) * (ampFourth s x - ampFourth 0 x)
          * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4) := by
      ring
    rw [hfac, abs_mul, abs_mul, abs_of_pos hT]
    have hcos : |Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x
      - Real.pi / 4)| ≤ 1 := Real.abs_cos_le_one _
    have hnn : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) * |ampFourth s x - ampFourth 0 x| := by
      positivity
    nlinarith [hcos, abs_nonneg (ampFourth s x - ampFourth 0 x), hT.le, hnn]
  -- assemble
  have htri1 := abs_sub_le
    (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))
    (Real.sqrt (2 / Real.pi) * ampFourth s x
      * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))
    (Real.sqrt (2 / Real.pi) * ampFourth 0 x
      * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4))
  have htri2 := abs_sub_le
    (Real.sqrt (2 / Real.pi) * ampFourth s x
      * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))
    (Real.sqrt (2 / Real.pi) * ampFourth s x
      * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4))
    (Real.sqrt (2 / Real.pi) * ampFourth 0 x
      * Real.cos (c * Real.sqrt (x ^ 2 - 1) - c * (s / 2) * radialAngle x - Real.pi / 4))
  linarith [htri1, htri2, hrem, hph2, hamp2]



/-! ## The `s`-dependence of the fourth root -/

theorem ampFourth_pow_four {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    ampFourth s x ^ 4 = 1 / ((x ^ 2 - 1) * (x ^ 2 - s)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hd hn
  have h1 : Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) ^ 2 = (x ^ 2 - 1) * (x ^ 2 - s) :=
    Real.sq_sqrt hP.le
  have h2 : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) ^ 2
      = Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  rw [ampFourth, div_pow, one_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, h1]

/-- **The `s`-dependence of the amplitude is linear.**
`|A_s-fourth-root - A_0-fourth-root| <= s A_0-fourth-root/(x²-s)`, so it is `O(s)` on every compact. -/
theorem abs_ampFourth_sub_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |ampFourth s x - ampFourth 0 x| ≤ s * ampFourth 0 x / (x ^ 2 - s) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have ha : 0 < ampFourth s x := ampFourth_pos hs1 hx
  have hb : 0 < ampFourth 0 x := ampFourth_pos (by norm_num) hx
  have ha4 := ampFourth_pow_four hs1 hx
  have hb4 : ampFourth 0 x ^ 4 = 1 / ((x ^ 2 - 1) * x ^ 2) := by
    have h := ampFourth_pow_four (s := 0) (x := x) (by norm_num) hx
    rw [sub_zero] at h
    exact h
  -- the fourth powers are ordered
  have hpow : ampFourth 0 x ^ 4 ≤ ampFourth s x ^ 4 := by
    rw [ha4, hb4]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith
  have hab : ampFourth 0 x ≤ ampFourth s x :=
    le_of_pow_le_pow_left₀ (by norm_num) ha.le hpow
  -- the difference of fourth powers
  have hdiff4 : ampFourth s x ^ 4 - ampFourth 0 x ^ 4
      = s * (x ^ 2 - 1) / (((x ^ 2 - 1) * (x ^ 2 - s)) * ((x ^ 2 - 1) * x ^ 2)) := by
    rw [ha4, hb4]
    field_simp
    ring
  -- factor the difference
  have hfac : (ampFourth s x - ampFourth 0 x)
      * ((ampFourth s x + ampFourth 0 x) * (ampFourth s x ^ 2 + ampFourth 0 x ^ 2))
      = ampFourth s x ^ 4 - ampFourth 0 x ^ 4 := by ring
  have hden : ampFourth 0 x ^ 3
      ≤ (ampFourth s x + ampFourth 0 x) * (ampFourth s x ^ 2 + ampFourth 0 x ^ 2) := by
    have h1 : ampFourth 0 x ≤ ampFourth s x + ampFourth 0 x := by linarith
    have h2 : ampFourth 0 x ^ 2 ≤ ampFourth s x ^ 2 + ampFourth 0 x ^ 2 := by
      nlinarith [sq_nonneg (ampFourth s x)]
    calc ampFourth 0 x ^ 3 = ampFourth 0 x * ampFourth 0 x ^ 2 := by ring
      _ ≤ (ampFourth s x + ampFourth 0 x) * (ampFourth s x ^ 2 + ampFourth 0 x ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
  -- conclude
  have hb3 : ampFourth 0 x ^ 3 = 1 / (((x ^ 2 - 1) * x ^ 2) * ampFourth 0 x) := by
    have h : ampFourth 0 x ^ 4 = ampFourth 0 x ^ 3 * ampFourth 0 x := by ring
    rw [hb4] at h
    field_simp at h ⊢
    linarith [h]
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ampFourth s x - ampFourth 0 x)]
  have hkey : (ampFourth s x - ampFourth 0 x) * ampFourth 0 x ^ 3
      ≤ ampFourth s x ^ 4 - ampFourth 0 x ^ 4 := by
    calc (ampFourth s x - ampFourth 0 x) * ampFourth 0 x ^ 3
        ≤ (ampFourth s x - ampFourth 0 x)
          * ((ampFourth s x + ampFourth 0 x) * (ampFourth s x ^ 2 + ampFourth 0 x ^ 2)) :=
          mul_le_mul_of_nonneg_left hden (by linarith)
      _ = ampFourth s x ^ 4 - ampFourth 0 x ^ 4 := hfac
  have hkey2 : (ampFourth s x - ampFourth 0 x) / (((x ^ 2 - 1) * x ^ 2) * ampFourth 0 x)
      ≤ s * (x ^ 2 - 1) / (((x ^ 2 - 1) * (x ^ 2 - s)) * ((x ^ 2 - 1) * x ^ 2)) := by
    rw [← hdiff4, ← mul_one_div, ← hb3]
    exact hkey
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hkey2
  have hpos2 : (0 : ℝ) < (x ^ 2 - 1) * ((x ^ 2 - 1) * x ^ 2) := by positivity
  have hscaled : ((ampFourth s x - ampFourth 0 x) * (x ^ 2 - s))
      * ((x ^ 2 - 1) * ((x ^ 2 - 1) * x ^ 2))
      ≤ (s * ampFourth 0 x) * ((x ^ 2 - 1) * ((x ^ 2 - 1) * x ^ 2)) := by
    nlinarith [hkey2]
  have hmain : (ampFourth s x - ampFourth 0 x) * (x ^ 2 - s) ≤ s * ampFourth 0 x :=
    le_of_mul_le_mul_right hscaled hpos2
  rw [le_div_iff₀ hn]
  exact hmain

end GaloisForLFunctions.RHTower

end
