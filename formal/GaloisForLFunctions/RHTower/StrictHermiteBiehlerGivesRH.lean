import GaloisForLFunctions.RHTower.PositivityForcesMultipleZeros
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler

/-!
# Strict Hermite–Biehler for the Hedenmalm pair gives the hypothesis outright

The previous entry obtained the hypothesis from positivity **together with** simplicity of the zeros.
That extra hypothesis was an artefact of working with semi-definiteness.  With the *strict*
inequality it disappears, and the proof becomes two lines.

**The computation.**  At a zero `ρ` of `XiC` the candidate and its Schwarz partner are

```text
E(ρ)   =  XiC ρ + i·XiC' ρ  =  i·XiC' ρ ,
E#(ρ)  =  XiC ρ - i·XiC' ρ  = -i·XiC' ρ ,
```

so `‖E#(ρ)‖ = ‖XiC' ρ‖ = ‖E(ρ)‖` — **equality**, whatever the multiplicity of the zero.  The strict
Hermite–Biehler inequality `‖E#(z)‖ < ‖E(z)‖` on the upper half-plane is therefore violated at any
zero there.

**The conclusion.**  `XiC` has no zeros with positive imaginary part; Schwarz reality moves the
negative case to the positive one; so every zero of `XiC` is real, which is the hypothesis in the
centered coordinate.

> **Strict Hermite–Biehler for `E = XiC + i·XiC'` implies the Riemann hypothesis, with no simplicity
> assumption and no kernel positivity: at a zero the two moduli are equal, and strictness has no room
> for that.**

This closes the gap left by the previous entry and identifies exactly what must be proved about the
Hedenmalm carrier: strictness, not semi-definiteness.

This file formalizes the identification of the Schwarz partner, the equality of moduli at a zero, and
the resulting implication to the hypothesis.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The Schwarz partner of the Hedenmalm candidate is its algebraic sharp.**  Reflection reality of
`XiC` and of its derivative turn `conj (E (conj z))` into `XiC z - i·XiC' z`. -/
theorem suzukiEntireSharp_xiHedenmalmDeBrangesE (z : ℂ) :
    GaloisForLFunctions.RHTower.suzukiEntireSharp xiHedenmalmDeBrangesE z
      = xiHedenmalmDeBrangesESharp z := by
  unfold GaloisForLFunctions.RHTower.suzukiEntireSharp xiHedenmalmDeBrangesE
    xiHedenmalmDeBrangesESharp
  rw [xiHedenmalm_XiC_conj, deriv_XiC_conj]
  simp
  ring

/-- **At a zero the two moduli agree.**  Both reduce to `‖XiC' ρ‖`, regardless of multiplicity. -/
theorem norm_sharp_eq_norm_of_zero {ρ : ℂ} (hρ : XiC ρ = 0) :
    ‖xiHedenmalmDeBrangesESharp ρ‖ = ‖xiHedenmalmDeBrangesE ρ‖ := by
  rw [xiHedenmalmDeBrangesESharp, xiHedenmalmDeBrangesE, hρ, zero_sub, zero_add, norm_neg]

/-- **So a strict Hermite–Biehler carrier has no zero of `XiC` above the axis.** -/
theorem no_upper_zero_of_strict_hermiteBiehler
    (hHB : GaloisForLFunctions.RHTower.SuzukiHermiteBiehler xiHedenmalmDeBrangesE)
    {z : ℂ} (hz : XiC z = 0) (him : 0 < z.im) : False := by
  have h := hHB z him
  rw [suzukiEntireSharp_xiHedenmalmDeBrangesE, norm_sharp_eq_norm_of_zero hz] at h
  exact lt_irrefl _ h

/-- **And none below it either**, by Schwarz reality of `XiC`. -/
theorem no_lower_zero_of_strict_hermiteBiehler
    (hHB : GaloisForLFunctions.RHTower.SuzukiHermiteBiehler xiHedenmalmDeBrangesE)
    {z : ℂ} (hz : XiC z = 0) (him : z.im < 0) : False := by
  have hzc : XiC ((starRingEnd ℂ) z) = 0 := by
    rw [xiHedenmalm_XiC_conj, hz, map_zero]
  have himc : 0 < ((starRingEnd ℂ) z).im := by
    simp only [Complex.conj_im]
    linarith
  exact no_upper_zero_of_strict_hermiteBiehler hHB hzc himc

/-- **Strict Hermite–Biehler for the Hedenmalm pair implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_strict_hermiteBiehler
    (hHB : GaloisForLFunctions.RHTower.SuzukiHermiteBiehler xiHedenmalmDeBrangesE) :
    RiemannHypothesis := by
  rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
  intro z hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact absurd (no_lower_zero_of_strict_hermiteBiehler hHB hz h) not_false
  · exact h
  · exact absurd (no_upper_zero_of_strict_hermiteBiehler hHB hz h) not_false

/-- **The simplicity hypothesis of the previous entry is removable.**  Strictness alone suffices; the
equality of moduli at a zero holds whether or not the derivative vanishes there. -/
theorem simplicity_not_needed {ρ : ℂ} (hρ : XiC ρ = 0) :
    ‖xiHedenmalmDeBrangesESharp ρ‖ = ‖xiHedenmalmDeBrangesE ρ‖ :=
  norm_sharp_eq_norm_of_zero hρ

end RHTower
