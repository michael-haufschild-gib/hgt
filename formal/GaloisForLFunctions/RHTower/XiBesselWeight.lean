import GaloisForLFunctions.RHTower.XiInverseCoordinate

/-!
# Dunster's Bessel weight and the transport identity

In the phase variable the Liouville–Green amplitude is carried by the weight

`B_s(r) = (X_s(r)² - 1)^{1/4} / (r^{1/2} (X_s(r)² - s)^{3/4})`,

and the transport identity states that the amplitude times the derivative of the inverse coordinate
is `r B_s(r)`.  The identity is exact: the phase `r` cancels against the amplitude's own square root
and the two quarter powers of the amplitude's denominator recombine with the half powers coming from
the reciprocal speed.

The apparent singularity of `B_s` at `r = 0` is not visible here; what is proved is the identity on
the open ray, which is where the substitution lives.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- Dunster's weight in the phase variable, with the fourth roots written as iterated square
roots. -/
def xiBesselWeight (s r : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt ((xiInverse s r) ^ 2 - 1)) /
    (Real.sqrt r * Real.sqrt ((xiInverse s r) ^ 2 - s) *
      Real.sqrt (Real.sqrt ((xiInverse s r) ^ 2 - s)))

/-- **The transport identity.**  The amplitude at the inverse coordinate, times the derivative of
that coordinate, is the phase times Dunster's weight. -/
theorem xiAmplitude_mul_inv_xiSpeed_eq {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    xiAmplitude s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹
      = r * xiBesselWeight s r := by
  have hx1 : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hxi : xiEndpointPhase s (xiInverse s r) = r := xiEndpointPhase_xiInverse hs0 hs1 hr
  set x : ℝ := xiInverse s r with hxdef
  have hu : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hv : (0 : ℝ) < x ^ 2 - s := by nlinarith
  set a : ℝ := Real.sqrt (x ^ 2 - 1) with hadef
  set b : ℝ := Real.sqrt (x ^ 2 - s) with hbdef
  set c : ℝ := Real.sqrt r with hcdef
  have ha : 0 < a := Real.sqrt_pos.mpr hu
  have hb : 0 < b := Real.sqrt_pos.mpr hv
  have hc : 0 < c := Real.sqrt_pos.mpr hr
  set p : ℝ := Real.sqrt a with hpdef
  set q : ℝ := Real.sqrt b with hqdef
  have hp : 0 < p := Real.sqrt_pos.mpr ha
  have hq : 0 < q := Real.sqrt_pos.mpr hb
  have hpa : p * p = a := Real.mul_self_sqrt ha.le
  have hcr : c * c = r := Real.mul_self_sqrt hr.le
  -- the amplitude's denominator is the product of the two quarter roots
  have hden : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) = p * q := by
    rw [Real.sqrt_mul hu.le, ← hadef, ← hbdef, Real.sqrt_mul ha.le, ← hpdef, ← hqdef]
  -- the reciprocal speed
  have hspeed : xiSpeed s x = b / a := by
    rw [xiSpeed, Real.sqrt_div hv.le (x ^ 2 - 1), ← hadef, ← hbdef]
  rw [xiAmplitude, hxi, hden, hspeed, xiBesselWeight, ← hxdef, ← hadef, ← hbdef, ← hcdef,
    ← hpdef, ← hqdef]
  rw [inv_div, ← hpa, ← hcr]
  field_simp

end GaloisForLFunctions.RHTower
