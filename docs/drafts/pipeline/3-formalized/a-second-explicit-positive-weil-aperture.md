# A second explicit positive Weil aperture

- **ID:** AIP-SECOND-APERTURE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5.4
- **Statement:** An explicit aperture strictly beyond `enlargedWeilFloorAperture` has Weil floor `1/20000`, infinite critical threshold, and positive critical pencils at every positive ratio.

## Theorem

Put `s = weilFloorApertureStep`, `a₁ = enlargedWeilFloorAperture`, and
`a₂ = successorWeilFloorAperture = a₁(1+s)`. Then

\[
a_1<a_2<\tfrac12,\qquad
Q(f)\ge\frac1{20000}\int |f|^2
\]

for every real or complex `C²` test supported in `[-a₂,a₂]`, with the complex
form interpreted as `Re Wζ(f,f)`. Consequently `R₁(2a₂)=⊤`, and every nonzero
test on a window of length at most `2a₂` has a positive critical pencil at every
`R>0`. Every fixed independent finite family inherits positive definiteness along
each critical curve `c_N⁸/log N → R>0`. Also `a*(ζ) ≥ a₂ > a₁`.

## Proof

The definition of `s` gives `s>0`, `s≤1/10`, and, writing `C` for
`onePrimeDilationCoefficient`,

\[
10\log(1+s)+4e^2s+\frac{C}{-\log(s\log2)}\le\frac3{40000}.
\]

Suppose `f` violates the asserted floor. Its energy lies in the low-energy cone
`Q(f)≤∫f²`, and its support lies in `[-1/2,1/2]`. Set `r=1+s` and `g(u)=f(ru)`.
The existing aperture theorem gives `rQ(g)≥(1/8000)∫f²`; the actual prime-two
dilation modulus gives `rQ(g)-Q(f)≤(3/40000)∫f²`. Subtraction yields the claimed
`1/20000` floor, a contradiction. Real and imaginary decomposition gives the
complex statement. Centering gives the half-window floor and the threshold law.
The positive aliasing Gram and the critical-curve limit give the finite-family
consequence. Window positivity gives the onset bound.

## Lean

All module paths below are under `formal/GaloisForLFunctions/`.

| Module | Main declarations |
|---|---|
| `ArithmeticIncidencePositivity/AWeilFloorSurvivesAnotherDilation.lean` | `successorWeilFloorAperture_bounds`, `fullZeroForm_ge_of_support_le_successorWeilFloorAperture`, `zetaZeroConfig_re_W_ge_of_aperture_le_successorWeilFloorAperture` |
| `ArithmeticHodgeTheoryOfDegenerations/EveryCriticalRatioIsPositiveOnALargerWindow.lean` | `exists_larger_window_with_all_critical_pencils_positive`, `eventually_pos_of_le_successor`, `pencilGram_pos_of_le_successor`, `successor_windows_inherit_exact` |
| `WindowVisibilityLaw/TheOnsetExceedsTheEnlargedBase.lean` | `windowPositiveAt_successorWeilFloorAperture`, `enlargedWeilFloorAperture_lt_onsetAperture_zeta` |

Kernel checks pass. Transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. All three programme umbrellas import their new modules.

## Scope

This proves the scalar conclusion of §2.5.4 by continuing the actual one-prime floor.
It does not prove the requested arithmetic mechanism through growing receiving fibres
and literal prime bands. That requirement and the other four questions remain open in
`1-in-progress/review-0411-five-breakthrough-questions.md`.
