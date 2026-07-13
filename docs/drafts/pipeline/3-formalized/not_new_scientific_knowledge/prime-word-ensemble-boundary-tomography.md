# Boundary jets exactly recover weighted prime-word support strata

- **ID:** `prime-word-ensemble-boundary-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[POSITIVE SOURCE PACKET] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`
- **Consumer:** `../../1-in-progress/prime-source-ramanujan-lift-ihara-limit-rh.md`

## Theorem

Let `S` be a finite set of words over a decidable prime alphabet and let `a_w` be integer weights.
For each word, mark its number `n_w` of distinct letters by

```text
M_(n_w)(t) = n_w (1-t)^(n_w-1),
```

and form the weighted ensemble polynomial

```text
F_(S,a)(t) = sum_(w in S) a_w M_(n_w)(t).
```

Lean proves, for every `r >= 0`,

```text
F_(S,a)^(r)(1)
  = (r+1)(-1)^r r! * sum_(w in S, n_w=r+1) a_w.
```

The prefactor is nonzero over the integers.  Therefore equality of the `r`th boundary jet for two
ensembles forces equality of their weighted support-`r+1` slices, and equality of all boundary jets
forces equality of every positive support-cardinality aggregate.

## Positive content and exact limitation

This upgrades the one-word selector into a lossless finite support-stratified source packet.  A
graph, code, or determinant detour may now consume the complete boundary germ without first
collapsing mixed words to the singleton axis.

The packet is not word-faithful by itself: different words with the same number of distinct labels
are aggregated.  The positive successor is the already formalized squarefree multivariate marker,
which retains the actual support set before the normal boundary derivatives aggregate it.  The
combined packet is

```text
word -> squarefree multivariate support monomial -> weighted boundary germ.
```

Multiplicity and cyclic order still require separate nonbacktracking trace variables.  No graph
realization, Ramanujan bound, determinant limit, or RH conclusion is claimed here.

## Formal certificate

The module proves:

- `primeWordEnsembleDeformation_boundaryJet`;
- `primeWordEnsembleDeformation_boundaryJet_slice`;
- `primeWordSupportWeightSlice_eq_of_boundaryJet_eq`;
- `primeWordSupportWeightSlices_eq_of_all_boundaryJets_eq`.

The exact module builds.  Axiom audits of all four theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] finite weighted ensemble defined
- [x] derivative formula proved
- [x] nonzero-factor cancellation proved
- [x] complete positive-support tomography proved
- [x] exact Lean build
- [x] accepted-axiom audit
