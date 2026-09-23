import GaloisForLFunctions.RHTower.PrimeArchBernsteinMobiusPullback
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# The prime--Gamma specialization of the Bernstein Möbius pullback

For the endpoint source the moment sequence is `m_k = normalizedPrimeArchMoment(k)/R^k`.  Because
the prime--Gamma moment germ is *even*, the ordinary moment germ of that sequence is the same germ
read in the square-root coordinate:

```
M_R(v) = xiCentralMomentGerm(z),   z² = v/R,
```

and the Möbius-pullback law becomes

```
B_R(s,w) = (1-s)^{-1} xiCentralMomentGerm( z ),   z² = s(w-1)/(R(1-s)).
```

Evenness makes the right-hand side independent of the local square-root choice, and the formal
identity `continuedPrimeArchSourceRelativeTrace(z) = -z · normalizedPrimeArchMomentGerm(z)` turns
it into a direct value formula in the analytically continued prime--Gamma trace, with no finite
Bernstein coefficient left in the source expression.
-/

namespace RHTower

noncomputable section

/-- **(9)** The endpoint moment germ in the square-root coordinate. -/
theorem bernsteinMomentGerm_primeArch {R : ℝ} (hR : R ≠ 0) {v z : ℂ} (hz : z ^ (2 : ℕ) = v / (R : ℂ)) :
    bernsteinMomentGerm (radiusNormalizedMoment R normalizedPrimeArchMoment) v
      = xiCentralMomentGerm z := by
  rw [bernsteinMomentGerm, xiCentralMomentGerm_eq_tsum_even]
  refine tsum_congr fun k => ?_
  have hmom : ((normalizedPrimeArchMoment k : ℝ) : ℂ) = xiCentralReciprocalMoment k := by
    rw [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm]
    exact primeArchSourceMoment_eq_xiCentralReciprocalMoment k
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  rw [radiusNormalizedMoment]
  push_cast
  rw [pow_mul, hz, div_pow, hmom]
  field_simp

/-- Evenness: the square-root coordinate may be replaced by its negative. -/
theorem bernsteinMomentGerm_primeArch_neg {R : ℝ} (hR : R ≠ 0) {v z : ℂ}
    (hz : z ^ (2 : ℕ) = v / (R : ℂ)) :
    xiCentralMomentGerm z = xiCentralMomentGerm (-z) := by
  rw [bernsteinMomentGerm_primeArch (v := v) hR hz |>.symm,
    bernsteinMomentGerm_primeArch (v := v) hR (by rw [neg_pow]; simpa using hz)]

/-- **(10)** The prime--Gamma Möbius pullback of the Bernstein pencils. -/
theorem tsum_bernsteinPencil_primeArch {R : ℝ} (hR : R ≠ 0) {s w z : ℂ} (hs : ‖s‖ < 1)
    (hM : Summable fun k : ℕ => |radiusNormalizedMoment R normalizedPrimeArchMoment k|
      * (‖s‖ * ‖w - 1‖ / (1 - ‖s‖)) ^ k)
    (hz : z ^ (2 : ℕ) = s * (w - 1) / ((R : ℂ) * (1 - s))) :
    ∑' n : ℕ, bernsteinCoefficientTransform
        (radiusNormalizedMoment R normalizedPrimeArchMoment) n w * s ^ n
      = (1 - s)⁻¹ * xiCentralMomentGerm z := by
  rw [tsum_bernsteinPencil_eq_mobiusPullback _ hs hM]
  congr 1
  refine bernsteinMomentGerm_primeArch hR ?_
  rw [hz]
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  rcases eq_or_ne ((1 : ℂ) - s) 0 with h | h
  · rw [h]
    simp
  · field_simp

/-- The germ identity that removes every finite Bernstein coefficient from the source expression:
`continuedPrimeArchSourceRelativeTrace(z) = -z · normalizedPrimeArchMomentGerm(z)`. -/
theorem continuedPrimeArchSourceRelativeTrace_eq (z : ℂ) :
    continuedPrimeArchSourceRelativeTrace z = -z * normalizedPrimeArchMomentGerm z := by
  have h := congrFun
    (oddTracePreimage_normalizedTraceMomentGerm_eq
      continuedPrimeArchSourceRelativeTrace continuedPrimeArchSourceRelativeTrace_zero) z
  rw [oddTracePreimage] at h
  rw [← h, normalizedPrimeArchMomentGerm]

/-- Near the centre the endpoint moment germ is the continued prime--Gamma trace. -/
theorem xiCentralMomentGerm_eventuallyEq_source :
    (fun z : ℂ => xiCentralMomentGerm z) =ᶠ[nhds 0]
      fun z : ℂ => normalizedPrimeArchMomentGerm z :=
  (normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm).symm

end

end RHTower
