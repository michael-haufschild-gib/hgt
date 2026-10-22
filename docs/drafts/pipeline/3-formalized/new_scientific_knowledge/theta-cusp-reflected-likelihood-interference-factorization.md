# Theta-cusp reflected likelihood-interference factorization

- **ID:** `theta-cusp-reflected-likelihood-interference-factorization`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Date:** 2026-07-23
- **Scientific status:** `[PROVED HERE] [SOURCE-PURE] [NO COMPUTATION] [NOT RH]
  [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../../1-in-progress/theta-cusp-reflected-correlation-angle-concavity.md`
- **Statement:** On every same-half-line reflected chamber, the normalized completed theta-source
  product is exactly the normalized first-atom product times one positive likelihood-partition
  cocycle. Thus every unequal-index obstruction is confined to that cocycle.

## Exact statement

Write

```text
k(x)=thetaCuspFullSource(x),
phi(x)=thetaCuspSourceTerm(x,1),
B(x)=pi*exp(2x)-3/2,
Z(B)=thetaCuspLikelihoodPartition(B).
```

For `0<=t<=u`, put

```text
A=pi*exp(2u),
z=cosh(2t)-1,
p1(u,t)=(1-3A*z/(A-3/2)^2)*exp(-2A*z),
I(u,t)=Z(B(u+t))*Z(B(u-t))/Z(B(u))^2.
```

Then

```text
k(u+t)k(u-t)/k(u)^2 = p1(u,t)*I(u,t).                  (F)
```

Moreover

```text
I(u,t)>0,       I(u,0)=1,       I(u,-t)=I(u,t).        (S)
```

The first factor has strict reflected Riccati contraction by
`theta-cusp-single-atom-reflected-riccati-contraction`. Consequently every possible failure of
completed-source reflected Riccati contraction on this chamber is caused by the likelihood
interference factor `I`, not by any diagonal first-atom geometry.

## Gates

- [x] 0 → 1 in-progress: exact source statement and corpus audit
- [x] 1 → 2 fully-proven: dependency-complete exact proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source theorem, positivity/symmetry/center/action laws,
  umbrella wiring, axiom audit, and lint green
- [ ] 3 → 4 publication-ready: standalone presentation and external priority review

## Dependency-complete proof

The existing positive likelihood spectral measure gives, whenever `B(x)>0`,

```text
k(x)=phi(x) Z(B(x)).                                  (1)
```

For `0<=t<=u`, all three points `u-t`, `u`, and `u+t` are nonnegative. The proved coordinate law
therefore gives

```text
B(u-t)>0, B(u)>0, B(u+t)>0,                           (2)
```

so `(1)` applies at every factor in `(F)`.

Multiplying the instances at `u+t` and `u-t` gives

```text
k(u+t)k(u-t)
 =phi(u+t)phi(u-t) Z(B(u+t))Z(B(u-t)).                 (3)
```

The exact single-atom reflected-product theorem gives

```text
phi(u+t)phi(u-t)=phi(u)^2 p1(u,t).                    (4)
```

The center instance of `(1)` is

```text
k(u)^2=phi(u)^2 Z(B(u))^2.                            (5)
```

Both factors on the right of `(5)` are strictly positive: first-atom positivity follows from
`B(u)>0`, and likelihood-partition positivity follows from its positive Laplace representation.
Division of `(3)` by `(5)`, followed by `(4)`, proves `(F)`.

Partition positivity proves `I>0`. Substitution `t=0` proves `I(u,0)=1`; replacing `t` by `-t`
only swaps its two numerator factors, proving evenness. No limiting argument, summation
interchange, or numerical estimate occurs.

## Hostile audit and classification

1. **No atom sum was re-expanded.** The theorem uses the corpus's stronger fixed-measure Laplace
   factorization, so it does not rediscover the already formalized theta series.
2. **No Riccati sign is claimed for `I`.** A positive partition cocycle can increase under
   unequal-temperature tilting. `(F)` isolates the precise sign still needing proof.
3. **No seam crossing is hidden.** The chamber `0<=t<=u` is exactly where all three likelihood
   coordinates are positive by the existing coordinate theorem. The modular seam remains a
   separate reflected-scattering problem.
4. **No RH leakage.** `(F)` is an identity between explicit source quantities.
5. **Exact obstruction classification.** Diagonal first-atom geometry contributes a certified
   positive Riccati margin; higher-index and unequal-index effects enter only through `I`.

## Novelty boundary

The likelihood spectral measure, modular scattering law, source log-concavity, and atomwise
Riccati contraction already belong to the corpus. Targeted corpus search found no normalized
reflected factorization `(F)`. The audited correlation-angle and Hedenmalm literature does not
state this theta-specific likelihood cocycle. Novelty remains provisional.

## Lean realization

`RHTower/ThetaCusp/ThetaCuspReflectedLikelihoodInterferenceFactorization.lean` formalizes:

- the completed source as first atom times the existing likelihood partition;
- unnormalized and normalized reflected product factorizations;
- strict positivity, center normalization, and evenness of the interference cocycle;
- exact additivity of the completed reflected logarithmic action into its certified atom action
  and interference action.

The module is imported by `RHTower/RiemannHypothesisSOTA2026.lean`. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-23 — extracted from the surviving same-half-line obstruction after single-atom Riccati
  contraction. Promoted directly to Stage 2 because proof is an exact algebraic consequence of
  previously formalized positive likelihood and atom-product laws.
- 2026-07-23 — formalized exact source/partition, normalized cocycle, structural, and logarithmic
  action identities. Promoted to Stage 3 and wired into RHTower frontier umbrella.
