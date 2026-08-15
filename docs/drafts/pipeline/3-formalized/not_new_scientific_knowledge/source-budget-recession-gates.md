# Source Budget Recession Gates

- **ID:** source-budget-recession-gates
- **Stage:** 3-formalized
- **Lean module:** `formal/GaloisForLFunctions/RHTower/SourceRecession.lean`
- **Paper parent:** `finite-source-normalizations-leave-budget-recession.md`
- **Statement formalized:** If a fixed budget inequality holds along every
  point of a one-sided affine ray, the recession direction is nonnegative on
  every test vector. If it holds along the whole two-sided affine line, the
  recession direction is zero on every test vector.

## Lean Theorems

- `GaloisForLFunctions.source_budget_one_sided_recession_nonnegative`
- `GaloisForLFunctions.source_budget_two_sided_recession_zero`

## Verification

Commands run on 2026-06-24:

```text
cd formal && lake build GaloisForLFunctions.SourceRecession
cd formal && lake env lean GaloisForLFunctions.lean
bash scripts/check_axioms.sh
```

All succeeded. The project axiom audit includes both theorem names and reports:

```text
PASS: Tier A/B elementary theorems axiom-clean (allowed subset of [propext, Classical.choice, Quot.sound]), no sorry (343 theorem outputs audited).
```

Scratch axiom check:

```text
lake env lean /tmp/source_recession_axioms.lean
```

Output:

```text
'GaloisForLFunctions.source_budget_one_sided_recession_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaloisForLFunctions.source_budget_two_sided_recession_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope

This formalizes only the finite-dimensional recession-direction algebra behind
the source-normalization audit. It does not formalize Hermitian forms, Euler
orientation, the completed boundary-Weyl object, Stieltjes/Markov positivity,
or RH.
