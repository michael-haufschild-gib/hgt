# Route U entire root factorization

- **ID:** `route-u-entire-root-factorization`
- **Stage:** 3-formalized
- **Type:** THEOREM / hard-edge normal-family closure and exact root quotient
- **Routes:** U primary
- **Source:** locally uniform squared-angular limit, strong `L²` unit normalization, analytic root extraction

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Result

Let `a_n > 0`, `a_n -> infinity`, and let the squared-angular hard-edge approximants converge
locally uniformly on `C` to `F`. Their only possible pole is `-a_n^2`. On every fixed complex
neighbourhood that pole is eventually absent, so the approximants are eventually holomorphic
there. Therefore `F` is entire.

If the corresponding physical packets converge strongly in real `L²`, and every packet has
squared norm one, then the strong limit has norm one. The already-proved same-subsequence
identification gives

```text
toLp (x -> F(x^2)) = ofRealLp L,
```

so `F` is not identically zero. Hence every physical root `F(r^2)=0` has an exact positive finite
order `m` and a global entire quotient `H` satisfying

```text
m > 0,
H(r^2) != 0,
F(u) = (u-r^2)^m H(u)                for every complex u.
```

The existing bandlimited-source theorem then constructs literal `q in L1 cap L2`, supported in
the open interval `(-C/pi,C/pi)`, and a continuous real-squared profile `G` with

```text
routeURealFourier(q)(w)
  = (w^2-(2 pi r)^2)^m G(w^2)         for every real w.
```

Thus Route U no longer needs an entireness, nondegeneracy, root-multiplicity, continuous-quotient,
or compact-factorization premise at a selected hard-edge root.

## Heavy conjecture loop

### U-E1 — rational approximants cannot yield an entire limit

**Conjecture.** Each squared-angular approximant has a pole, so local-uniform convergence alone
does not supply global analyticity of `F`.

**Attack.** Pole is exactly `-a_n^2`. For a unit ball about any fixed `z`, `a_n -> infinity`
eventually gives `a_n^2 > ||z||+1`; denominator is then nonzero throughout that ball. Mathlib's
locally-uniform limit theorem requires only eventual holomorphy on the local domain.

**Verdict:** false. Escaping singularities imply an entire limit.

### U-E2 — the entire limit may collapse to zero

**Conjecture.** Local-uniform extraction may produce `F=0`, making analytic order infinite and
root division vacuous.

**Attack.** Strong convergence preserves the packet norm one. Same-subsequence representative
identification equates `x -> F(x^2)` with complexified strong limit. If `F=0`, that `L²` class has
norm zero, contradicting norm one.

**Verdict:** false. `F` has a nonzero complex value.

### U-E3 — global squared-root factorization is additional source data

**Conjecture.** Even with an entire nonzero `F` and a root `F(r^2)=0`, Route U must separately
construct a continuous global quotient and multiplicity.

**Attack.** Connected-plane identity theorem rules out local identical vanishing. Full analytic
order extraction gives `(u-r^2)^m` times a quotient analytic on all of `C`, nonzero at the root.
The root equality forces `m>0`. Existing exact normalization transports this factor to literal
compact source.

**Verdict:** false. Quotient, positivity of multiplicity, continuity, and compact factorization are
automatic.

## Higher universal principle

**A hard-edge normal family carries two compactness mechanisms at once: states compactify in
`L²`, while singularities evacuate to infinity in the complex plane.** The first prevents collapse;
the second upgrades local-uniform convergence to entireness. Their conjunction converts a
first-contact root into a globally divisible analytic state. Earlier root-quotient obstruction was
the shadow of treating these mechanisms independently.

Remaining Route-U obstruction is incoming PSD/strictness, or an equivalent source-specific
pre-wall exclusion of nonzero null state. Root quotient and compact admission are closed.

## External novelty audit

Corpus contained separate escaping-pole normality, locally-uniform/strong-`L²` representative
identification, global analytic root extraction, and compact Fourier root division. Search found no
prior theorem composing them into the actual Route-U capstone without entireness or factorization
hypotheses. No external priority claim is made; novelty remains unverified.

## Lean closure

Infrastructure:

- `GaloisForLFunctions.HTGeometry.exists_positive_pow_factor_of_entire_root` in
  `formal/GaloisForLFunctions/HTGeometry/AnalyticRootFactor.lean`.

Route-U module:

- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeEntireRootFactorization.lean`;
- `analyticOnNhd_routeUHardEdge_angularLocallyUniformLimit`;
- `norm_routeUHardEdge_strongLimit_eq_one`;
- `exists_ne_zero_routeUHardEdge_angularLocallyUniformLimit`;
- `exists_positive_entireRootFactor_routeUHardEdge_angularLocallyUniformLimit`;
- `routeUHardEdge_angularLocallyUniformLimit_root_has_literal_compact_factorization`.

Both modified/new leaves passed direct `lake env lean`. Exact leaf builds passed; the Route-U leaf
build replayed cached prerequisite diagnostics after the shared analytic-root `.olean` changed but
did not invoke an umbrella target. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Module is imported by `RHTower.lean`; no umbrella build was run.

## Gates

- [x] 0 -> 1: escaping-pole, zero-collapse, and quotient conjectures attacked
- [x] 1 -> 2: dependency-closed proof and corpus collision audit
- [x] 2 -> 3: direct Lean checks, exact leaf builds, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Log

- 2026-08-16 — Eventual local holomorphy from pole evacuation proved.
- 2026-08-16 — Entire locally uniform hard-edge limit proved.
- 2026-08-16 — Unit norm and global nondegeneracy proved.
- 2026-08-16 — Positive full multiplicity and entire quotient derived at every physical root.
- 2026-08-16 — Actual literal compact-source factorization obtained without factorization premise.
