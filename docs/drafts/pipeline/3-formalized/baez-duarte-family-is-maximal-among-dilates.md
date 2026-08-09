# Balance is what the detector sees: the Báez-Duarte family is maximal among dilates

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The question

`MellinVanishingCriterion` turned the Nyman--Beurling lane into a template: any family in the carrier whose
Mellin transforms vanish at the detector point of a hypothetical off-line zero inherits the criterion, the
metric form, and the quantitative floor. The obvious first question is whether the Báez-Duarte family can be
*enlarged* — a bigger span is a weaker hypothesis, hence a stronger criterion.

## The answer: no, not within the fractional-part dilates

`RHTower/FractDilateBalance.lean`. Every fractional-part dilate `fractDilate θ : u ↦ {θu}/u` lies in the
carrier (`memLp_fractDilateFun`; the bound `‖{θu}/u‖ ≤ 1/u` needs no cancellation at all). Their transforms:

* `inner_bdDetector_fractDilate` —
  `⟪bdDetector (1−ρ), fractDilate θ⟫ = θ^ρ·(−ζ(ρ)/ρ) − θ/(1−ρ)`.
  Proof: split the ray at `1`, take the corpus's full-ray identity
  `FractionalPartZeta.integral_Ioi_zero_fract_dilate_cpow` and subtract the elementary head
  `integral_Ioc_zero_one_fract_dilate_cpow`, which is `θ/(1−ρ)` because `{θu} = θu` on `(0,1)` for `θ ≤ 1`.
  The head is obtained by reusing the corpus's `integral_Ioc_zero_one_fract_cpow` rather than redoing it.
* `inner_bdDetector_fractDilate_of_zero` — at a zero of `ζ` the ζ-term dies and the head survives:
  `= −θ/(1−ρ) ≠ 0`.  **A single dilate is never annihilated.**
* `inner_bdDetector_sum_fractDilate` — for a finite combination,
  `⟪bdDetector (1−ρ), ∑ cₖ • fractDilate θₖ⟫ = −(∑ cₖθₖ)·(1/(1−ρ))`.
* `not_inner_bdDetector_sum_fractDilate_eq_zero` — hence an **unbalanced** combination (`∑ cₖθₖ ≠ 0`) is not
  annihilated, at any zero.

And `bdGen_eq_fractDilate_sub` exhibits Báez-Duarte's generator as the balanced two-term combination
`fractDilate θ − θ · fractDilate 1`.

So the annihilated part of the dilate span is exactly the balanced part, which is exactly the Báez-Duarte
span. **The Báez-Duarte family is maximal in this class**: you cannot weaken the criterion's hypothesis by
adjoining more dilates, and one hypothetical off-line zero already forces the balance condition — the
obstruction is not an artefact of looking at all zeros at once.

## Consequence for the route

A genuinely different family must come from outside the fractional-part dilates — arithmetic coefficients
(a Möbius-weighted system), or a different kernel entirely. This is a no-go of the useful kind: it prices
the "enlarge the family" idea at zero before anyone spends a session on it, and it says precisely which
degree of freedom is already exhausted (the weighted mass `∑ cₖθₖ`).
