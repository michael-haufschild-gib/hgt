# Projective Hurwitz 1/42 phase-transition core

- **ID:** `projective-hurwitz-one-over-forty-two-phase-core`
- **Stage:** 3-formalized
- **Type:** FORMALIZATION
- **Scientific status:** `[FORMALIZATION]` of a `[NOVELTY UNVERIFIED]` paper theorem
- **Paper theorem:** `projective-hurwitz-one-over-forty-two-phase-transition`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.HurwitzOrbifoldGap`,
  `GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTailCollapse`

## Formalized surface

`HurwitzOrbifoldGap.lean` proves directly that every ordered integral hyperbolic triangle signature
has rational excess at least `1/42`, that no excess lies strictly between `0` and `1/42`, and that
`(2,3,7)` attains `1/42`.

`NonautonomousProjectiveTailCollapse.lean` combines an abstract positive excess budget with that
scale to prove

```text
degree + 84 <= 84 genus,
```

and proves from the exact `(2,3,7)` fibre counts and Riemann--Hurwitz that

```text
degree = 42(2 genus - 2),
degree + 84 = 84 genus.
```

It also proves that strict ordering by degree is exactly strict ordering by genus in the saturated
phase.

## Deliberate paper boundary

Lean does not yet encode the hypergeometric triangle connection, arithmetic commensurator spans,
or projective Kummer minimality.  Those named geometric inputs remain in the paper theorem rather
than being introduced as axioms.

## Physical/topological meaning

The formal theorem exhibits a genuine discrete gap in integral projective curvature and an exact
surface-capacity equality at its endpoint.  The “phase transition” is static constraint topology,
not dynamics or thermodynamics.

## RH impact audit

The `1/42` density is a sharp falsifier for compact correspondence-based RH architectures that
claim to preserve projective rank.  No RH-sensitive projective connection is constructed.

## Verification

The missing exact object for `HurwitzOrbifoldGap` was built once with its exact module target.
Both touched Lean sources then passed serialized direct leaf compilation.  No umbrella, theorem-
area, full, or self-concurrent build was run.

## Gates

- [x] integral curvature gap formalized
- [x] exact `(2,3,7)` endpoint formalized
- [x] genus threshold and saturation arithmetic formalized
- [ ] triangle uniformization and arithmetic commensurator formalization
- [ ] projective Kummer minimality formalization
