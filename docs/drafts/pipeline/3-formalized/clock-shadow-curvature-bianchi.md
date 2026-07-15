# Clock-shadow curvature obeys an exact descent Bianchi law

- **ID:** `clock-shadow-curvature-bianchi`
- **Stage:** 3-formalized
- **Type:** GENERAL COMPARISON THEOREM / OBSERVABLE-RESOLUTION CURVATURE
- **Scientific status:** `[LEAN-FORMALIZED] [FOUNDATIONAL IDENTITY AND CURVATURE ALGEBRA] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/clock-descent-anomaly.md`
- **Statement:** The failure of source-to-shadow anomalies to commute with clock truncation is
  exactly the curvature of the proposed shadows applied to the higher observation. Shadow
  curvature itself satisfies a three-resolution cocycle law.

## Definitions

For compatible observation spaces `O_1 -> O_0` with truncation `p`, source constraint `S`,
observations `q_i`, and proposed shadows `T_i`, put

```text
alpha_i = T_i q_i-q_i S,                                  (1)
kappa_01 = p T_1-T_0 p.                                   (2)
```

The clock index is observable resolution, not time.

## Bianchi identity

If `p q_1=q_0`, then

```text
p alpha_1-alpha_0 = kappa_01 q_1.                         (3)
```

Thus anomaly incoherence is not an independent error. It is precisely shadow curvature seen by
the source observation.

If source variations realize every value of `q_1`, then

```text
range((p alpha_1-alpha_0)|W)=range(kappa_01).              (4)
```

Every curvature value is therefore realized as an observable-resolution mismatch on an actual
source variation.

## Three-resolution cocycle

For `O_2 -> O_1 -> O_0`,

```text
kappa_02 = p_01 kappa_12+kappa_01 p_12.                   (5)
```

Equation `(5)` is the exact cocycle law required before a calibrated curvature class on the whole
clock tower can be defined.

## Constraint-algebra and gauge laws

For composable pairs of shadows `T=(T_0,T_1)` and `U=(U_0,U_1)`, curvature obeys

```text
kappa(T U)=kappa(T) U_1+T_0 kappa(U).                    (6)
```

Thus curvature is a derivation from the finite source-operation algebra into the cross-resolution
boundary bimodule. Gauge correction is additive:

```text
kappa(T+g)=kappa(T)+kappa(g).                             (7)
```

Finally,

```text
kappa(T)=0  <=>  p T_1=T_0 p.                            (8)
```

So vanishing curvature is exactly finite-shadow compatibility, not merely a sufficient condition.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockShadowCurvature`;
- `clockAnomalyCoherenceDefect`;
- `clockAnomalyCoherenceDefect_eq_shadowCurvature_comp`;
- `range_clockAnomalyCoherenceDefect_domRestrict_eq_range_shadowCurvature`;
- `clockShadowCurvature_add`;
- `clockShadowCurvature_comp_shadow`;
- `clockShadowCurvature_eq_zero_iff`;
- `clockShadowCurvature_comp`.

The module already had a cached object. These declarations were checked with direct source
verification only; no build was rerun.

## Scientific boundary

Noncommuting diagrams, cocycles, and Bianchi identities are parent forms. The candidate research
content is the constrained-HT interpretation: natural finite shadows of a genuinely nonlocal
source need not form a pro-operator, and their curvature can be the thin boundary data erased by
every individual clock cutoff.

## Gates

- [x] two-level curvature defined
- [x] descent Bianchi identity formalized
- [x] exact curvature-range law formalized
- [x] three-resolution cocycle formalized
- [x] gauge-additivity formalized
- [x] constraint-algebra Leibniz law formalized
- [x] zero-curvature/compatibility equivalence formalized
- [ ] calibrated gauge quotient defined
- [ ] nonzero curvature class proved for Gamma
- [ ] self-dual curvature refinement constructed
- [ ] independent novelty/significance audit
