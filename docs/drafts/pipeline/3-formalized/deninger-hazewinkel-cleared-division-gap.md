# Hazewinkel cleared-coefficient division gap

- **ID:** `deninger-hazewinkel-cleared-division-gap`
- **Stage:** 3-formalized
- **Type:** FALSIFIED PROOF STEP / THEOREM (Lean)
- **Route:** L — rational-Witt source foundation
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [LITERATURE-PROOF AUDIT] [NOT AN RH PROOF]`
- **Statement:** Hazewinkel Appendix A.2's exponent descent uses a coefficient-algebra closure
  implication that fails: in `ℤ[D,Z]`, `DZ ∈ ℤ[D,DZ]` and `D ∣ DZ`, but `Z ∉ ℤ[D,DZ]`.

## Goal

Prevent the Route-L integral Hankel primeness theorem from being marked paper-closed through an
invalid division step, and replace the missing mechanism by a characteristic-free monic
Gröbner/straightening contraction theorem.

## Exact killing theorem

Let

```text
φ : ℤ[D,Y] → ℤ[D,Z],    φ(D)=D,    φ(Y)=DZ.
```

Then `DZ=φ(Y)` belongs to `range φ`, and `D` divides `DZ` in the ambient polynomial ring. However,
`Z` is not in `range φ`: specialize `D=0`. The composite specialization sends both source
variables to zero, so every element of `range φ` specializes to a constant, whereas `Z`
specializes to the nonconstant variable `Z`.

This is exactly the shape of the printed claim

```text
g ∈ ℤ[low, D·a_(2n)]  and  D ∣ g
  ⇒ g/D ∈ ℤ[low, D·a_(2n)],
```

used to lower the minimal clearing exponent. Ambient Gauss contraction proves only `D ∣ g`; it
does not prove closure of the quotient in the restricted coefficient algebra.

## Strongest positive survivor

The failure identifies the correct missing invariant: **monic normal forms**, not localization or
density. `IntegralMonicGroebnerTransfer.lean` proves:

1. a reduced polynomial in the span of a Gröbner basis is zero;
2. if `R → S` is injective, `B ⊂ R[X]` is monic, and the image of `B` is a Gröbner basis in
   `S[X]`, then membership in the extended ideal contracts to `R[X]`;
3. if the extended ideal is prime, the original ideal is prime.

The proof uses mathlib's well-founded multivariate division algorithm. It assumes no flatness,
torsion-freeness, reducedness, field structure, or characteristic restriction on `R`; monicity is
the complete coefficient-saturation mechanism.

This survivor does not itself close integral Hankel primeness. Remaining instantiation is Conca's
theorem that finite maximal Hankel minors form a monic Gröbner basis, plus finite field primeness.
The parent saturation card therefore correctly remains Stage 1.

## Lean realization

- `RHTower/Deninger/DeningerHazewinkelClearedDivisionGap.lean`
  - `hazewinkelClearedKillPivot_comp_scaledTail`;
  - `hazewinkelCleared_X_one_not_mem_range`;
  - `hazewinkelCleared_division_exits_range` (closed capstone).
- `HTGeometry/IntegralMonicGroebnerTransfer.lean`
  - `MonomialOrder.reduced_mem_span_eq_zero`;
  - `MonomialOrder.mem_span_of_map_mem_span`;
  - `MonomialOrder.span_isPrime_of_map`.

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, computation, or imported RH-equivalent premise is
used. Both modules are wired into their umbrellas.

## Gates

- [x] 0 → 1: exact printed step and counterexample isolated
- [x] 1 → 2: symbolic paper proof and positive replacement mechanism dependency-closed
- [x] 2 → 3: exact Lean theorems; direct foreground checks passed
- [ ] 3 → 4: novelty/literature-response audit and standalone note not pursued

## Log

- 2026-08-13 — hostile audit found division-closure gap in project proof and Hazewinkel Appendix A.2.
- 2026-08-13 — exact symbolic counterexample and monic Gröbner coefficient-transfer survivor
  formalized; card moved directly to Stage 3.
