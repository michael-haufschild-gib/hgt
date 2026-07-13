# FE-odd reduced quotient blindness

- **ID:** `fe-odd-reduced-quotient-blindness`
- **Stage:** 3-formalized
- **Type:** `[NO-GO]`, `[POSITIVE RESIDUE]`, `[FORMALIZATION]`, not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/FEOddReducedQuotientBlindness.lean`
- **Route:** `../../1-in-progress/fermionic-fe-projector-lefschetz-rh.md`

## Statement

On every critical closed disc of radius `0 < r < 1/2`, the nonzero FE-odd transverse coordinate

```text
u(s) = s - (1-s) = 2s-1
```

belongs to the closed complex span of the paired Euler-unit tangents after deleting any finite set
of primes. Consequently every continuous scalar detector annihilating those cofinite tangents also
annihilates `u`.

Therefore quotienting the FE-odd compact-carrier space by the closed paired-Euler range erases a
nonzero transverse direction unconditionally. An ordinary Hausdorff/reduced cohomology or Banach
quotient of this form cannot retain the divisor residue needed by the fermionic RH route.

## Positive residue

The obstruction identifies the only possible completion defect in this model:

```text
algebraic paired-Euler span  ⊊?  closed paired-Euler span.
```

Since `u` is already in the closure, a live invariant must retain its class modulo the **algebraic**
range, or use a pointed weighted all-prime topology in which the approximating coefficient tails
do not disappear. The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/paired-euler-algebraic-closure-gap.md` proves by
private boundary poles that `u` lies in no finite paired-Euler span. Thus `[u]` is a canonical
nonzero non-Hausdorff residue class rather than an unspecified derived limit.

## Scope

Lean proves closed-span membership, annihilation by all continuous detectors of the cofinite Euler
family, and nonvanishing of `u`. Algebraic-span non-membership is proved on paper in the linked
card but is not yet formalized. No result yet couples the completion-defect class to the Xi divisor.
