# Exact finite-aperture first-row vanishing — formalized closure

- **ID:** `ccm-exact-finite-aperture-first-row-vanishing-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-exact-finite-aperture-first-row-vanishing.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

General infrastructure (`HTGeometry`, reusable, source-free):

- `GaloisForLFunctions.HTGeometry.ArcoshComparison`
- `GaloisForLFunctions.HTGeometry.IntegralGronwall` — variable-coefficient Grönwall in integral form.

Bessel layer (`RHTower`):

- `GaloisForLFunctions.RHTower.BesselJZeroEnvelope` — `|J₀(u)| ≤ C u^{-1/2}` and
  `|J₀'(u)| ≤ C u^{-1/2}`, by van der Corput.
- `GaloisForLFunctions.RHTower.BesselJZeroODE` — Bessel's equation for the integral representation.
- `GaloisForLFunctions.RHTower.BesselJZeroPhase` — the large-argument phase asymptotic
  `J₀(x) = A x^{-1/2} cos(x − δ) + O(x^{-3/2})`.
- `GaloisForLFunctions.RHTower.BesselJZeroSecondSolution` — a second solution, its envelope, and the
  Wronskian normalisation.

First-row layer (`RHTower`):

- `GaloisForLFunctions.RHTower.CCM.CCMFirstRowStationaryPhase`
- `GaloisForLFunctions.RHTower.CCM.CCMFirstRowVanDerCorputBlocks`
- `GaloisForLFunctions.RHTower.CCM.CCMFirstRowEnvelopeTail`
- `GaloisForLFunctions.RHTower.CCM.CCMFirstRowDunsterModel`
- `GaloisForLFunctions.RHTower.CCM.CCMRadialProlateDefect`
- `GaloisForLFunctions.RHTower.CCM.CCMRadialProlateEndpointLayer`

All twelve are wired into their area umbrellas (`GaloisForLFunctions.RHTower`,
`GaloisForLFunctions.HTGeometry`).

## Audit

The card carries a 700-line Lean status section giving the declaration for every numbered equation;
that section is the clause-by-clause audit and is preserved verbatim in the paper card next to this
certificate. Every one of its 37 Lean gates is checked:

- exact reduction of the stationary equation to the quadratic `(7)`, the root `(8)`, and `(9)` in
  rationalised form;
- `y − 1 ≍ k^{-2}` with explicit absolute constants;
- the weighted first-row sum bound `(18)` from the pointwise two-term bound, and its `o(1)`
  conclusion;
- the `ξ_s` two-sided bracket `(4)` including the improper endpoint integral, and the amplitude half
  `|A_s(x)| ≤ 2^{1/4} x^{-1/2}`;
- the differentiation law `(10)`, the exact speed collapse at the stationary point, the closed form
  of `φ''`, and the `k³` law `(11)` with absolute constants;
- the Bessel envelope and derivative envelope, the envelope tail integral `(16)` with constant `3`,
  and the envelope product bound `(15)` with constant `8`;
- the uniform window bound `|φ''| ≍ k³`, the two off-window bounds `|φ'| ≳ k`, the exact amplitude of
  the leading term with endpoint phases cancelling, and strict concavity of the difference phase;
- the window block of `(13)` — `O(c^{-1/2}k^{-2})` with constant `80` — the two off-window blocks,
  the endpoint layer `(12)` with the exact `(x−1)^{-1/4}` singularity, and the four-way assembly of
  `(13)` with constant `170`;
- the pole-uniform comparison equation of `(14)` solved by `J₀(c ξ_s(x))`, the exact deviation law by
  weighted Wronskian transport and the Abel identity, the Green kernel with its two transport laws
  and algebraic reconstruction, and the pole-uniform comparison estimate for an arbitrary
  perturbation;
- the PSWF-specific input of `(14)`: the actual radial prolate mode solves the comparison equation
  with a defect having only a **simple** pole, `|a| ≤ 40/(x²−1)`, uniformly in the aperture and in
  `0 ≤ s ≤ 1/2`, so the eigenvalue enters only through that range and nothing is imported;
- the total Liouville mass of that defect, `∫_A^B |a|/ξ' ≤ 127` unconditionally, hence a Volterra
  exponent `≤ 254 C²/(cW)` and relative error `1 + O(c^{-1})` in `(14)`;
- equation `(14)` for the actual radial mode — the pole-uniform envelope bound on
  `U = √(x²−1) R / √(ξ/ξ')` with relative factor `exp(O(1/c))` — and `(14)` in approximation form.

## Axioms

`lake env lean` on a scratch file importing all twelve modules and printing axioms for every
non-private theorem (358 declarations generated, private helpers excluded because they are not
addressable across modules): no errors, and no declaration depends on `sorryAx`. Every printed
axiom set is exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

The card's own remaining open gates: the high truncated-divisor weighted radial tail, combination
with the intact Poisson central correction, and the archimedean/true-Weil gap comparison.

## Verification performed

- `lake env lean` on the import + axiom-print scratch file: no errors.
- Umbrella wiring checked for all twelve modules.
