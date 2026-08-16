# Route P primitive Gamma--Julia Stokes aperture residue transport

- **ID:** `route-p-primitive-gamma-julia-stokes-aperture-residue-transport`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105I]`
- **Parent:** `route-p-primitive-gamma-julia-log-cofinal-trace-no-go.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesApertureResidueTransport.lean`

## Goal

Turn P-G105H's exact Euler-pole obstruction into literal source-derived Stokes/polar cancellation,
without discarding actual finite matrix incidence.

## Conjecturing loop

### Conjecture 1 — entire promoted prime-depth trace needs singular renormalization

**Falsified and sharpened.** Shift to strictly positive depth. Exact P-G105H formula is bounded by
`(4 log 2)^-1` times corpus's summable higher-valuation prime-log weight. Thus only depth-zero prime
face is singular; positive-depth remainder is ordinarily summable.

### Conjecture 2 — P-G100 four-unit Stokes jump is only analogous to P-G105H residue

**Falsified by exact transport.** For right aperture `d>0`, squared diagonal multiplier

```text
a_d(p)^2 = 32 d log(p) p^(-2d)
```

sends P-G105H depth-zero density to

```text
a_d(p)^2 /(4p) = 8 d log(p) p^(-(1+2d)),
```

exactly corpus's label-faithful oriented Stokes prime term. Coefficient `32=8/(1/4)` is forced;
none is fitted.

### Conjecture 3 — identification holds only after scalar trace summation

**Falsified.** Congruence by `diag(a_d(p_i))` is applied to actual finite P-G186
prime-log-conjugated Gram. Lean proves its real trace equals finite sum of literal transported
Stokes terms. Off-diagonal entries remain in matrix before trace.

### Conjecture 4 — polar cancellation still requires free renormalization

**Falsified.** All-prime transported trace is exactly existing oriented first-trace current.
Adding corpus's explicit higher-valuation plus archimedean polar countercurrent is exactly existing
completed prime--Gamma current. Its right-wall limit is zero, while separate prime and polar limits
are `4` and `-4`.

## Paper proof

P-G105H gives `w(p,0)=1/(4p)`. Multiplication by positive `a_d(p)^2` gives displayed Stokes term
by `p^(-2d)p^-1=p^(-(1+2d))`. Existing prime current summability proves all-prime admission at each
`d>0`.

For higher depths, write `e=k+1`. Then

```text
w(p,k+1)=(1/4)p^{-(k+2)}(k+2)^-3
          <= (4 log 2)^-1 log(p)p^{-(k+2)}.
```

Right side is summable by existing higher-valuation theorem. Finite matrix trace follows by
diagonal congruence, P-G186 exact diagonal, and `sqrt(a_d(p)^2)^2=a_d(p)^2`. Existing completed
current decomposition then gives exact polar identity and zero wall limit. `QED`

## Novelty and anti-theatre audit

This materially repairs P-G105H. It identifies exact Radon--Nikodym transport from literal Route-P
matrix source to literal Stokes current, localizes divergence to one valuation face, and replaces
free scalar counterterm by existing completed-source polar/Gamma current. It also explains P-G100's
four-unit residue as the aperture image of P-G105H's one-quarter harmonic density.

Result remains trace-level. No cofinal polar operator or determinant is constructed. Therefore no
claim is made that P-G105G stability survives completed cofinalization, that determinant divisor is
Xi, or that RH follows.

## Formal status

Lean proves unconditionally:

- positivity of exact aperture multiplier;
- labelwise equality with oriented Stokes prime term;
- all-prime summability and exact total current identity;
- summability of entire strictly positive-depth remainder;
- exact finite trace identity on actual doubly-conjugated P-G186 Gram;
- exact equality of transported-plus-polar trace with completed prime--Gamma current;
- zero right-wall limit after polar cancellation;
- premise-free P-G105I capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Lift scalar polar/Gamma countercurrent to a source-faithful negative operator channel. Prove its
physical child/pivot specialization stays inside P-G105G stable chamber near aperture wall, then
construct locally uniform cofinal determinant preserving completed trace and divisor.

## Higher universal principle

Completion is a two-scale residue transgression. Bulk positive depths are nuclear already. Singular
valuation-one boundary is not subtracted; it is transported by positive aperture density into an
oriented current, then cancelled by a geometrically separate polar channel. This matches finite
Krein architecture: positivity belongs to transported source Gram, negative sign belongs to
completion channel. Mixing them before this split obscures both stability and summability.

## Log

- 2026-08-16 — P-G105I exact source-to-Stokes aperture transport and polar residue cancellation
  paper-proved and formalized.
