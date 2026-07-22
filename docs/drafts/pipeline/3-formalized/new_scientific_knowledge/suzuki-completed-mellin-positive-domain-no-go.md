# Universal positive-profile completion law and sharp Suzuki Mellin barrier

- **ID:** `suzuki-completed-mellin-positive-domain-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../../1-in-progress/suzuki-terminal-frontier-ledger.md`
- **Statement:** Any positive finite-valued linear completion containing a nonnegative profile and
  all finite coordinate truncations forces its weighted mass to be summable; the critical Suzuki
  Mellin mass is summable exactly for `sigma > 1`.

## Goal

Decide whether the divergent critical Suzuki source can be completed by enlarging the domain of a
positive finite part after the unital cofinal route has failed.  The answer is no on every domain
that contains the completed profile and its finite cutoffs.  This closes the entire positive
finite-valued completion class, not only a chosen regulator.

## Gates

- [x] 0 → 1 in-progress: exact source profile and finite-cutoff connector identified
- [x] 1 → 2 fully-proven: dependency-closed order proof and exact Euler threshold
- [x] 2 → 3 formalized: Lean module built and public declarations axiom-audited
- [ ] 3 → 4 publication-ready: external novelty audit and standalone exposition

## Universal law

Let `w,f : iota -> R` be nonnegative and suppose `sum_i w(i) f(i)` is not summable.  Let `D` be
any real linear subspace of coordinate functions containing `f` and every finite truncation
`f|_F`.  There is no positive linear map `Phi : D -> R` satisfying

```text
Phi(f|_F) = sum_{i in F} w(i) f(i)
```

for all finite `F`.  Indeed, `0 <= f-f|_F`; positivity gives

```text
sum_{i in F} w(i)f(i) = Phi(f|_F) <= Phi(f),
```

uniformly in `F`, contradicting nonsummability of the nonnegative mass.  Moreover every exact
linear extension is unbounded below on the full nonnegative cone of `D`: a finite lower floor on a
cone closed under positive scaling would force positivity.

No order unit, topology, continuity, normality, or regulator hypothesis occurs.

## Exact Suzuki specialization

Define the transported critical profile

```text
f_sigma(p) = exp(-(sigma-1/2) log p).
```

Multiplying by the critical sharp source mass gives exactly

```text
suzukiCriticalSharpPrimeMass(p) f_sigma(p)
  = Lambda(p) exp(-sigma log p).
```

The formal Gamma--Bianchi displacement threshold yields the sharp law

```text
Summable_p [Lambda(p) exp(-sigma log p)]  <->  1 < sigma.
```

Every Gaussian-rational point in the completed left-half RH gate has `sigma < 1/2`, hence no
positive finite-valued domain can contain its Suzuki profile while preserving all exact finite
cutoff values.  Any exact extension is unbounded below on that domain's entire nonnegative cone.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/SuzukiCompletedMellinPositiveDomainNoGo.lean`.

Principal declarations:

- `not_exists_positive_extension_containing_nonsummable_profile`;
- `profile_extension_unboundedBelow_on_coordinate_domain`;
- `suzukiCriticalMellinWeightedPrimeMass_eq_vonMangoldt`;
- `summable_suzukiCriticalMellinWeightedPrimeMass_iff`;
- `not_exists_positive_suzukiCriticalGaussianRatLeftHalfProfile_extension`;
- `suzukiCriticalGaussianRatLeftHalfProfile_extension_unboundedBelow`.

`lake build GaloisForLFunctions.RHTower.SuzukiCompletedMellinPositiveDomainNoGo` passed on
2026-07-22.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Scientific boundary and survivor

This theorem kills every positive completion that assigns a finite completed flux to the actual
left-half profile.  It does not kill a signed canonical finite part whose lower bound is asserted
only on a source-normalized, non-conic family.  The remaining Suzuki frontier is therefore not
another positive-domain construction: it is construction and coercivity of the signed
principal-relative/Burnol anomaly, followed by its connector to the formal RH endpoint.

External novelty has not been audited.  Corpus novelty and class closure are exact.

## Log

- 2026-07-22 — universal law proved, Suzuki mass identified exactly, Lean build and axiom audit
  passed; positive completed-profile branch closed.
