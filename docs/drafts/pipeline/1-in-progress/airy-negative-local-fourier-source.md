# Airy negative local-Fourier source

- **ID:** `airy-negative-local-fourier-source`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), proof infrastructure incomplete
- **Source:** Hiroe, Theorem 3.10 and Proposition 3.9; Airy-tower manuscript Claim 4.3
- **Statement:** An Airy characteristic step `R > E`, `β = R + E` is realised by an actual
  algebraic Fourier transformation of a cyclic differential operator/connection whose differential
  rank drops from `R` to `E`; iterating the transformed tail and actual additions reduces every
  Airy tower to rank one.

## Goal

Close the manuscript's only analytic local-Fourier dependency without turning Hiroe's exponent
transition into a certificate.  Build the operator or formal-connection semantics, prove the
Fourier/addition transformations, prove their induced dual Puiseux characteristic law, and then
derive the existing arithmetic reduction theorem from this source.

Knowledge label: `[LITERATURE THEOREM] [NEW LEAN FORMALISATION]`.  This is required infrastructure,
not claimed as new mathematical discovery.  Its role is to make the paper's new Stokes/coarea
results formally dependency-closed.

## Gates

- [x] 0 → 1  in-progress: exact source formula and anti-theatre failure mode isolated
- [ ] 1 → 2  fully-proven: complete paper proof, including operator-to-characteristic bridge
- [ ] 2 → 3  formalized: Lean theorem, direct file check, targeted build, axiom audit
- [ ] 3 → 4  publication-ready: manuscript trace and hostile review accept dependency closure

## Exact open core

1. Construct actual first Weyl algebra/operator semantics over `ℂ`, with coordinate `X`,
   derivation `D`, and proved commutator `D X - X D = 1`.
2. Construct algebraic Fourier automorphism `X ↦ D`, `D ↦ -X`; prove inverse/order-four law and
   preservation of Weyl relation.
3. Construct addition/gauge automorphisms `D ↦ D + h(X)` with explicit inverse.
4. Define cyclic differential modules/operators carrying ramified formal Newton data, not merely
   exponent tuples.
5. Prove the restricted `F^(∞,∞)` Airy step: `β=R+E` changes differential rank `R` to `E`, makes
   the old leading exponent inessential because `E ∣ β`, and preserves the remaining tail.
6. Prove an addition removes the inessential leading term and exposes the next characteristic
   exponent.
7. Iterate on a strict divisor chain and prove termination at actual rank one.
8. Connect this source theorem to `Characteristic.negativeFourier_reduction_package`.

## Approach

Use a free associative algebra on two generators as operator syntax and evaluate it in
`Module.End ℂ (Polynomial ℂ)` by multiplication and differentiation.  This proves the Weyl
commutator semantically.  Construct Fourier and gauge automorphisms on syntax, prove that they
preserve the Weyl relation, then descend them to the Weyl quotient (or an equivalent faithful
normal-form algebra).  Use commutative principal symbols/Newton weights only as invariants of the
actual transformed operators.  The rank-drop theorem must quantify over actual operators/modules;
a transition relation on `(R,β,E)` alone is explicitly insufficient.

On the curve side, Hiroe's `F^(∞,∞)` contact chart is

```text
x = x₁⁻¹ y₁,   y = y₁,
```

so a good parametrisation `x=t^R α(t), y=t^β` becomes

```text
x₁=t^(β-R) α(t)⁻¹,   y₁=t^β.
```

For an Airy step `β=R+E`, source rank is therefore `E`.  This birational calculation will be
formalised as a second semantic model and related to the operator Fourier automorphism; it is not
used as a bare definition of the desired conclusion.

## Anti-theatre gate

Rejected as insufficient:

- defining a datatype constructor named `localFourier` whose fields already contain `R-E`;
- proving only the congruence `β ∣ R+E`;
- citing Hiroe inside prose while Lean sees only natural-number arithmetic;
- proving a generalized-Airy principal-symbol identity without connecting its cyclic module or
  curve germ to the full characteristic tail.

The final theorem must expose an actual operator/connection, actual Fourier/addition maps, and an
independently defined rank/characteristic invariant.

## No-go closure

- **Exact killing theorem/mechanism:** Not falsified. Main risk is that principal-symbol Fourier
  identities see only the first Newton edge and cannot prove preservation of the full tail.
- **Strongest positive survivor:** Even if the full tail bridge fails, the Weyl automorphism,
  semantic commutator, generalized-Airy rank exchange, and curve-contact valuation theorem are
  non-trivial positive source theorems and must be formalized before retiring the route.
- **New insight:** The negative Airy equality `β=R+E` is simultaneously a zero-loop balance law,
  the exponent subtraction in Hiroe's contact chart, and the exchange of derivative/coordinate
  orders under algebraic Fourier transform.  This may be the operator-level shadow of the same
  Galois sheet-pair coarea law.
- **Status:** open; no claim of dependency closure.

## Log

- 2026-08-03 — created in Stage 1 after cyclic and two-orbit sheet-source laws were formalized.
- 2026-08-03 — exact Hiroe formulas checked from source: Definition 2.3, Theorem 2.4,
  Proposition 3.9, Proposition 3.10, and Theorem 3.11 in source numbering.
