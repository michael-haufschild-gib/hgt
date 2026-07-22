# Completed seam compact-Markov germ capstone

- **ID:** `completed-seam-compact-markov-germ-capstone`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / right-to-left interface closure
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent:** `completed-seam-thorin-subordinator-rh.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedSeamCompactMarkovGermCapstone.lean`
- **Consumer:** `PrimeArchMomentMeasureRH.lean`
- **Statement:** If the ordinary completed seam-moment germ is locally the Markov transform of
  one finite positive measure with compact nonnegative support, that same measure represents every
  normalized prime--archimedean moment. Hence the existing all-degree Hankel capstone proves RH.

## Exact claim

Let

```text
M_src(z)=sum_(n>=0) normalizedPrimeArchMoment(n) z^n
```

be the ordinary source moment germ, and let

```text
K_mu(z)=integral_R 1/(1-x z) dmu(x).
```

Assume `mu` is finite, is carried by a compact interval `[0,R]`, and

```text
M_src = K_mu
```

on a neighborhood of zero. Then for every `n`, differentiation under the integral gives

```text
M_src^(n)(0)=n! normalizedPrimeArchMoment(n)
             =n! integral_R x^n dmu(x).
```

Cancellation of `n!` gives an exact positive moment representation. The already-formalized
theorem `riemannHypothesis_of_primeArchMomentRepresentation` then yields RH.

## Paper proof

Choose `B>0` with `|x|<=B` almost everywhere. On `|z|<1/(2B)`,

```text
|1-xz|>=1-|x||z|>1/2.
```

Therefore every differentiated kernel is uniformly integrable, and

```text
d^n/dz^n (1-xz)^(-1)=n! x^n (1-xz)^(-n-1).
```

Dominated differentiation gives the derivative formula for `K_mu`; compact support also makes
every power integrable. Local equality of the two analytic germs identifies their derivatives at
zero, hence their moments. No Xi divisor, zero location, positivity target, or RH premise enters
the implication.

## Lean closure

The module formalizes:

- the compact Markov kernel and its common integrability disk;
- the one-step derivative law and all-order factorial derivative formula;
- positive convergence radius and coefficient extraction for the ordinary source moment germ;
- exact recovery of the existing normalized continued prime--Gamma germ after the seam-square
  substitution;
- `PrimeArchCompactMarkovGermRepresentation`;
- conversion to `PrimeArchMomentRepresentation`;
- `riemannHypothesis_of_primeArchCompactMarkovGermRepresentation`.

The module is imported by the `GaloisForLFunctions.RHTower` umbrella.

## Scope and hostile audit

- This theorem closes the Markov-to-moment half of open core D of the Thorin card; it does not
  formalize the preceding Thorin-exponent-to-Markov step or construct `mu`.
- Positivity is not renamed: existence of the positive Markov measure remains the load-bearing
  source theorem and is RH-equivalent in the corpus.
- Finite prefixes do not suffice; equality is between analytic germs on a neighborhood.
- Compact support is the seam condition and supplies only legality of dominated differentiation.
- This is interface formalization of known Markov/moment theory, not new mathematical progress on
  the source positivity wall.

## Verification

- [x] `lake env lean GaloisForLFunctions/RHTower/CompletedSeamCompactMarkovGermCapstone.lean`
- [x] `lake build GaloisForLFunctions.RHTower.CompletedSeamCompactMarkovGermCapstone`
- [x] `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in module
- [x] umbrella reachability confirmed by formal lint (global lint has unrelated dirty-tree
      reachability failures)

## Log

- 2026-07-22 -- Codex: selected by backward RH dependency audit, paper-proved, formalized, wired,
  and audited. Producer boundary moved left to the Thorin-exponent-to-Markov wrapper, construction
  of the compact positive measure, and proof of its local identity with the completed source germ.
