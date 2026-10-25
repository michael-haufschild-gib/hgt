# Arithmetic majorants give Bézout without Riemann–Roch

- **ID:** arithmetic-majorants-give-bezout-without-riemann-roch
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-II source-effectivity audit; original scaling surface.
- **Statement:** Every positive aperture has an arithmetic source cone with Bézout and ampleness on the original pairing, but without RR.

## Exact source

Fix `r>0`, write `C=10+72 exp(r)`, and let `m(f)=integral(f²)` on `realTestsAt r`.
Let `A_r(f)` be the literal Gamma–Lévy–horizon–prime-deficit expression in
`criticalDeficitSourceEnergy`, and put `Q_r(f)=A_r(f)+2 C m(f)`.
Define effectivity by nonnegative fibre degrees and `Q_r(f)≤2 deg_H deg_V`.
The intersection pairing remains the original scaling pairing.

## Dependency-closed proof

[PROVED HERE.] The exact source identity says `A_r(f)=δ(f,f)`. The independently proved
Chebyshev floor says `δ(f,f)≥-C m(f)` for every real compact C² source at this aperture.
Thus `Q_r≥C m≥0`, `δ(f,f)≤Q_r(f)`, and `-δ(f,f)≤Q_r(f)`.
The exact identity and the L² bilinear form show that `Q_r` is genuinely quadratic.

For any real symmetric bilinear form `B` and quadratic form `Q` with
`-Q(v)≤B(v,v)≤Q(v)` for every `v`, apply the upper inequality at `x+t y` and the lower
inequality at `x-t y`. Addition gives
`0≤Q(y)t²-2 B(x,y)t+Q(x)` for every real `t`. Its discriminant is nonpositive, hence
`B(x,y)²≤Q(x)Q(y)`. This argument does not assume positivity of `B`.

Apply this lemma to the source defect and `Q_r`. The exact mixed source-cone criterion
gives Bézout. If `Q_r(f)=0`, the same bound forces every mixed defect with `f` to vanish,
giving ampleness. More strongly, `Q_r≥C m`, with `C>0`, forces `f=0` at zero reserve.
Consequently an effective class orthogonal to the ample class has both fibre degrees zero,
zero source, and hence is the zero class.

RR would require `Q_r(f)≤δ(f,f)` for every source. Subtracting the exact source identity
gives `2 C m(f)≤0`. Every positive aperture has a nonzero compact source with `m(f)>0`,
contradicting this inequality. The obstruction is the strictly positive extra reserve.

## New insight

Independent arithmetic Bézout is available on the original surface once the reserve retains
the full unbounded source energy. A finite L² reserve alone cannot do this. The simultaneous
RR/Bézout problem remains the removal of the extra reserve while preserving its mixed bound.
This construction separates that problem from replacing the intersection pairing.

## Verification

The same aperture cones are convex, pointed and generating. The explicit
bilinear form is `arithmeticMajorantBilinear`; its diagonal is exactly `Q_r`.
The positive quadratic cone laws give zero membership, additive closure,
nonnegative scalar closure and convexity. If both a cycle and its negative
are effective, both fibre degrees vanish; strict ampleness then makes the
cycle zero. Fibre translation gives a difference of two effective cycles
for every cycle.

`ArithmeticMajorantConeGeometry.lean` passed direct check **44990** and all
four transitive audits with only `propext`, `Classical.choice`, and `Quot.sound`:

- `arithmeticMajorantSourceCone_add_closed`
- `arithmeticMajorantSourceCone_convex`
- `arithmeticMajorantSourceCone_pointed`
- `arithmeticMajorantSourceCone_generating`

The module is cleaned, wired and documented.

- Dependencies: `criticalDeficitSourceEnergy_eq_defect`,
  `realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp`,
  `sourceCone_bezout_iff_defect_sq_le`, and the sharp source RR criterion.
- Lean source: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticMajorantsSupplyBezout.lean`;
  direct `lake --old env lean` check passed. The generic majorant, mass floor, mixed
  bound, Bézout, strict ample-zero theorem, and RR obstruction have only
  `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
  The module is wired into its umbrella; no umbrella build was run.
- No new analytic premise, zero-location premise, or numerical experiment.
- No claim that the union of cones with different aperture constants is globally Bézout;
  their mixed-aperture compatibility would need a separate proof.
