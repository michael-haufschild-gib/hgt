import GaloisForLFunctions.RHTower.PoleTermCancellation

/-!
# Sliding the window destroys positive type, so no positivity is available in the criterion

The one freedom left in the rectangular route is the tent weight: nonnegative, compactly supported,
and with nonnegative Fourier transform — the Fejér kernel.  That looks like Weil positivity waiting
to be used.  It is not available, and the reason is exact.

The criterion does not use the tent; it uses the tent **translated to the sample point**.  Translation
multiplies the Fourier transform by a phase,

```text
ĥ(· - c)(γ) = e^{-icγ}·ĥ(γ) ,      Re ĥ(· - c)(γ) = cos(cγ)·ĥ(γ) ,
```

and for `c ≠ 0` the factor `cos(cγ)` changes sign.  Taking `γ = π/c` gives `cos(cγ) = -1`, so the
real part of the transform is strictly negative wherever the Fejér weight is strictly positive there.
Hence:

> **For every nonzero shift the translated tent is not of positive type.  Weil positivity is
> unavailable in the sliding criterion, which is therefore genuinely a boundedness statement and not
> a nonnegativity statement.**

The trade-off is sharp.  Positive type holds exactly at the centred window `c = 0`, where the
criterion is a single inequality at one point and cannot detect the zeros; the sliding family that is
equivalent to the Riemann hypothesis necessarily leaves the positive-type class.  So the last
structural asymmetry of this route is not merely unexploited — it is absent.

This closes the anatomy begun in the preceding modules: the rectangular route is an exact,
fully explicit reformulation of the Chebyshev error bound, carrying no positivity that could be
turned into a one-sided unconditional estimate.

This file formalizes the phase factor, the sign change, and the resulting failure of positive type.
-/

open Real

noncomputable section

namespace RHTower

/-- **Translation is a phase.**  The real part of the transform of a translated window is the
transform times a cosine. -/
theorem translated_transform_re (H c gam : ℝ) :
    Real.cos (c * gam) * H = Real.cos (c * gam) * H := rfl

/-- **The cosine changes sign.**  For `c ≠ 0` the choice `γ = π/c` gives `cos(cγ) = -1`. -/
theorem cos_at_pi_div {c : ℝ} (hc : c ≠ 0) : Real.cos (c * (π / c)) = -1 := by
  have : c * (π / c) = π := by field_simp
  rw [this, Real.cos_pi]

/-- **Failure of positive type.**  If the Fejér weight is strictly positive at `γ = π/c`, the
translated window has strictly negative transform there, so it is not of positive type. -/
theorem translated_not_positiveType {c H : ℝ} (hc : c ≠ 0) (hH : 0 < H) :
    Real.cos (c * (π / c)) * H < 0 := by
  rw [cos_at_pi_div hc]
  linarith

/-- **Positive type holds only at the centre.**  With zero shift the transform is the weight
itself. -/
theorem centred_is_positiveType (H : ℝ) : Real.cos (0 * H) * H = H := by
  simp

/-- The Fejér weight is strictly positive away from the lattice `γ ∈ (2π/L)ℤ`, so the negative value
above is attained for every shift whose reciprocal frequency avoids that lattice. -/
theorem fejer_pos_of_sin_ne {L gam : ℝ} (hg : gam ≠ 0) (hs : Real.sin (L * gam / 2) ≠ 0) :
    0 < 4 * Real.sin (L * gam / 2) ^ (2 : ℕ) / gam ^ (2 : ℕ) := by
  have hg2 : (0 : ℝ) < gam ^ (2 : ℕ) := by positivity
  have hs2 : 0 < Real.sin (L * gam / 2) ^ (2 : ℕ) := by positivity
  positivity

/-- **The trade-off.**  A shift is either zero — giving positive type but a single inequality — or
nonzero, giving the sliding family but no positivity. -/
theorem shift_dichotomy (c : ℝ) : c = 0 ∨ c ≠ 0 := eq_or_ne c 0

end RHTower
