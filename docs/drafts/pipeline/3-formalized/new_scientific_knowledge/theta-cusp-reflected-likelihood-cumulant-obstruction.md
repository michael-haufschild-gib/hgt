# Theta-cusp reflected likelihood cumulant obstruction

- **ID:** `theta-cusp-reflected-likelihood-cumulant-obstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Date:** 2026-07-23
- **Scientific status:** `[PROVED HERE] [SOURCE-PURE] [NO COMPUTATION] [NOT RH]
  [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../../1-in-progress/theta-cusp-reflected-correlation-angle-concavity.md`
- **Statement:** The completed reflected Riccati obstruction on one modular half-line is exactly
  the strict first-atom margin plus one explicit correction determined by the mean, variance, and
  third cumulant of the corpus's fixed positive theta likelihood measure.

## Likelihood cumulants

Let

```text
Z(B)=thetaCuspLikelihoodPartition(B)=1+M_0(B),
M_j(B)=integral s^j exp(-B*s) dmu(s),
```

where `mu` is the already formalized positive higher-likelihood spectral measure. For `B>0`, put

```text
m(B)=M_1(B)/Z(B),
v(B)=M_2(B)/Z(B)-m(B)^2,
kappa(B)=M_3(B)/Z(B)-3*m(B)*M_2(B)/Z(B)+2*m(B)^3.
```

The added `1` in `Z` is the first-atom mass at spectral coordinate zero, so these are exactly the
first three cumulants of the normalized total likelihood state.

Differentiation under the fixed positive measure gives, for every `j>=0`,

```text
M_j'(B)=-M_(j+1)(B).                                  (1)
```

Consequently

```text
(log Z)'=-m,       (log Z)''=v,       (log Z)'''=-kappa. (2)
```

## Source-coordinate jets

Write

```text
B(x)=pi*exp(2x)-3/2,
A(x)=B(x)+3/2=pi*exp(2x),
G(x)=log Z(B(x)).
```

Since

```text
B'=2A,       B''=4A,       B'''=8A,
```

the exact source-coordinate jets are

```text
G'(x)  = -2*A*m,
G''(x) =  4*A^2*v-4*A*m,
G'''(x)= -8*A^3*kappa+24*A^2*v-8*A*m.                 (3)
```

## Reflected interference jets

The formalized likelihood-interference action is

```text
J_u(t)=2G(u)-G(u+t)-G(u-t).
```

Therefore

```text
J_u'(t)   = G'(u-t)-G'(u+t),
J_u''(t)  = -G''(u+t)-G''(u-t),
J_u'''(t) = G'''(u-t)-G'''(u+t).                      (4)
```

No atom-pair double sum remains: all unequal-index interference is encoded by the two tilted
likelihood states at `B(u-t)` and `B(u+t)`.

## Exact Riccati obstruction law

Let `S_1` be the first-atom reflected action and `S=S_1+J_u` the completed reflected action.
For any action `F`, write

```text
R(F)=2*F'*F''-F'''.
```

Pure algebra gives

```text
R(S)
 =R(S_1)+R(J_u)+2*(S_1'*J_u''+J_u'*S_1'').            (5)
```

The first term is strictly positive for `0<t<=u` by the formalized single-atom theorem. Hence the
completed source satisfies reflected Riccati contraction exactly when

```text
R(J_u)+2*(S_1'*J_u''+J_u'*S_1'') >= -R(S_1),          (6)
```

and it is sufficient to prove the left side of `(6)` nonnegative. Substituting `(3)` into `(4)`
turns `(6)` into one explicit inequality involving only `m`, `v`, and `kappa` at the two
temperatures `B(u-t)` and `B(u+t)`.

## Gates

- [x] 0 → 1 in-progress: exact obstruction extracted from formalized likelihood factorization
- [x] 1 → 2 fully-proven: dependency-complete differentiation and algebraic proof
- [x] 2 → 3 formalized: all-moment derivative, cumulant jet chain, reflected jets, margin
  decomposition, source connector, axiom audit, lint green
- [ ] 3 → 4 publication-ready: explicit expanded inequality and external priority review

## Hostile audit

1. **Variance positivity is insufficient.** Strict Hankel positivity proves `v>0`, but `(3)` also
   contains the sign-indefinite third cumulant. The obstruction cannot be discharged by
   log-convexity alone.
2. **No diagonal approximation remains.** `Z` is the complete fixed positive measure already
   proved equal to the full higher tail.
3. **No modular seam is hidden.** `(1)`--`(6)` apply for `B(u-t)>0`, in particular `0<=t<=u`.
   Crossing `u-t=0` requires the separate modular scattering law.
4. **No matrix hypothesis occurs.** The criterion is entirely in source likelihood cumulants.
5. **Exact remaining target.** After the first-atom theorem, only a two-temperature
   mean--variance--skewness inequality can obstruct the same-half-line Riccati law.

## Novelty boundary

Laplace cumulant identities are classical. The new claim is their exact combination with the
theta likelihood spectral measure, reflected source factorization, and Riccati margin. Corpus and
literature searches found no equivalent two-temperature cumulant obstruction for Hedenmalm's
theta source. Novelty remains provisional.

## Lean realization

`RHTower/ThetaCusp/ThetaCuspReflectedLikelihoodCumulantObstruction.lean` formalizes:

- `M_j'=-M_(j+1)` for every tilted likelihood moment;
- mean, variance, and third-cumulant derivative identities;
- literal first three source-coordinate log-partition jets;
- literal first three reflected-interference jets;
- equality with the previously formalized likelihood-interference action;
- exact atom-plus-cumulant action and Riccati-margin decompositions;
- the exact strict-sign equivalence and the unconditional strict conclusion under nonnegative
  cumulant correction.

The module is imported by `RHTower/RiemannHypothesisSOTA2026.lean`.

## Log

- 2026-07-23 — extracted after exact likelihood-interference factorization. Promoted to Stage 2
  because every derivative follows from a fixed positive Laplace measure with already formalized
  all-order exponential moments, and the Riccati split is an exact polynomial identity.
- 2026-07-23 — formalized all-order moment differentiation, cumulant/source/reflected jet chains,
  exact completed action, and exact Riccati obstruction. Promoted to Stage 3 and wired into the
  RHTower frontier umbrella.
