# Route E: incidence-switch parity rigidity

- **ID:** E-INCIDENCE-SWITCH-PARITY-RIGIDITY-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Möbius signs of finite prime products agree exactly for even support symmetric
  difference and are opposite exactly for odd symmetric difference; every valid two-by-two
  incidence switch preserves both receiver signs.

## Goal

Classify which prime-incidence moves can participate in the proposed opposite-Möbius-sign pairing.
This attacks the source-incidence gate before Hall/load estimates: a move family unable to reverse
sign cannot contribute cancellation regardless of its mixing or margin-preservation properties.

## Exact theorem

For finite sets `S,T` consisting of primes,

```text
mu(product S) =  mu(product T)  iff  Even(card(S symmetric-difference T)),
mu(product T) = -mu(product S)  iff  Odd(card(S symmetric-difference T)).
```

The proof is source-exact. Prime factorization gives `mu(product S)=(-1)^card(S)`. The cardinality
identity

```text
card(S)+card(T) = card(S symmetric-difference T) + 2*card(S intersection T)
```

then identifies endpoint-sign parity with move parity.

A standard two-by-two incidence switch has receiver supports

```text
S' = insert q (erase p S),   T' = insert p (erase q T),
```

under `p in S`, `q notin S`, `q in T`, `p notin T`. Both support cardinalities are unchanged, so
both Möbius values are unchanged and neither endpoint is sign-reversing.

## Consequence for proof chain

The contingency-table/switching conjecture fails as a Möbius-cancellation producer. Such switches
may mix configurations inside a fixed parity class and may help estimate unsigned admission, but
they cannot manufacture the required opposite-sign edges. Any useful move must change each paired
receiver's prime-count parity. Since the one-toggle common-spectator mechanism already reduces to
the Route E Hall/load obstruction, the first still-live direct graph is the full odd distance-three
graph, allowing both `0 <-> 3` and `1 <-> 2` toggles. Its multiplicative-cutoff neighborhood
expansion remains unproved.

This is not an RH proof and supplies no unmatched-mass estimate. It removes a false mechanism and
narrows the hard source theorem to odd-toggle expansion.

## Lean formalization

`RouteEIncidenceSwitchParityRigidity.lean` contains:

- `card_add_eq_card_symmDiff_add_twice_inter`;
- `even_card_symmDiff_iff_even_card_add`;
- `moebius_primeProducts_eq_iff_even_symmDiff`;
- `moebius_primeProducts_eq_neg_iff_odd_symmDiff`;
- `card_routeEPrimeSupportSwap` and `routeEPrimeSupportSwap_primes`;
- `routeE_twoByTwo_incidence_switch_preserves_moebius`;
- `routeE_twoByTwo_incidence_switch_cannot_reverse_moebius`.

All statements are dependency-closed finite theorems: their explicit assumptions only say that
the displayed finite supports contain primes and that the displayed switch is valid. No asymptotic
premise, stochastic kernel, column-load estimate, hypothesis about RH, or added axiom occurs.

## Research and failed pivots

Corpus deep search found no existing theorem with this exact prime-support/symmetric-difference
classification. It did recover the existing squarefree-product Möbius law
`GibbsGas.moebius_prod_primes`, the Route E exact column-defect identity, and unrelated incidence
parity infrastructure. Source audit then rejected three proposed pivots:

1. deterministic one-prime pivot: already the one-toggle Hall/load problem;
2. one-to-two fission: existing compression and reservoir counterfamilies leave no source
   mechanism;
3. prescribed-margin two-by-two switching: the theorem here proves every move preserves receiver
   parity.

Broad June--September 2026 arXiv searches on switching, shadows, coupling, expansion, matroids,
transport, hypercubes, and resampling produced no theorem applicable to sparse prime incidence with
nonlinear multiplicative column constraints. Dense contingency-table concentration and generic
switch-chain results do not cross the parity obstruction.

## Gates

- [x] 0 → 1 in-progress: exact source object and noncircular role identified.
- [x] 1 → 2 fully-proven: finite paper proof dependency-closed.
- [x] 2 → 3 formalized: closed Lean theorem, targeted check/build, axiom audit.
- [ ] 3 → 4 publication-ready: not a standalone RH advance; incorporate into Route E obstruction
  classification.

## Final audit

`lake env lean GaloisForLFunctions/RHTower/RouteEIncidenceSwitchParityRigidity.lean` and targeted
module build pass. Module is wired into `RHTower.lean`; no umbrella build is run. Axiom output for
both exact sign criteria and both switch capstones is exactly `propext`, `Classical.choice`, and
`Quot.sound`. No forbidden declaration token occurs.

## Log

- 2026-09-12 — exact parity classification proved and formalized; two-by-two switch route closed;
  full odd distance-three graph retained as next source-expansion target.
