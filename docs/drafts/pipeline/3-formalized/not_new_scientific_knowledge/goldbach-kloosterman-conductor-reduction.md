# Exact common-factor reduction of Kloosterman sums

- **ID:** goldbach-kloosterman-conductor-reduction
- **Stage:** 3-formalized
- **Type:** Classical finite arithmetic bridge; no novelty claim
- **Parent:** [composite budget](goldbach-composite-kloosterman-budget.md)
- **Lean:** [KloostermanConductorReduction.lean](../../../../../formal/GaloisForLFunctions/goldbach/KloostermanConductorReduction.lean)

## Exact statements

For actual positive integers q,d, let π be reduction from units modulo
qd to units modulo q, and let κ=#ker π. The module proves

    π is onto,   κ≤d,
    Σ_x f(πx)=κ Σ_y f(y),
    S(dm,dn;qd)=κ S(m,n;q),
    |S(dm,dn;qd)|≤d|S(m,n;q)|.

The last two statements hold for all integer m,n. Positivity is encoded
by the modulus type `ℕ+`; no analytic estimate, conjecture, sign condition
or supplied cancellation premise appears in the theorem statements.

## Paper proof

Unit reduction is onto by the established finite CRT lifting theorem.
Each fibre is a translate of the kernel, so finite regrouping gives the
observation identity. A kernel unit has a fixed residue modulo q. Its
quotient label floor(x.val/q) lies in [0,d); equal labels and equal
residues recover x. Hence κ≤d.

The identity e_(qd)(dz)=e_q(z mod q) descends the phase. Reduction of a
unit commutes with inversion, so both Kloosterman coefficients descend
together. Apply the observation identity to the smaller phase. Taking
norms and using κ≤d proves the final inequality.

This is the common-factor step needed before applying a unit-coefficient
prime-power estimate to an arbitrary Fourier frequency. The finite
gcd cost is preserved; it is not replaced by a coprimality assumption.

## Lean roots and audit

Namespace `GaloisForLFunctions.Goldbach`:

- `kloostermanUnitReduction_surjective`
- `kloostermanLiftMultiplicity_le`
- `stdAddChar_factor_reduction`
- `sum_kloostermanUnitReduction`
- `kloostermanSum_factor_lift`
- `norm_kloostermanSum_factor_lift_le`

Direct check:

    lake --old env lean GaloisForLFunctions/goldbach/KloostermanConductorReduction.lean

Passed from `formal/`, exit 0, without warnings. All six proof closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. Audit log:
`/tmp/hgt-goldbach-conductor-reduction-audit.log`.
Temporary audit directives were removed without changing proof bodies.
The leaf is imported by `goldbach/Main.lean`; the umbrella was not built.
Index regeneration passed. Targeted whitespace, local-link and forbidden-marker
checks are clean. All owned build/search commands terminated; temporary source
audit files and completed-search scratch files were removed, with audit logs retained.

The full composite bound is now formalized in the same leaf. Its
[certificate](goldbach-composite-kloosterman-budget.md) records the new
18-root audit, including all six conductor roots above. Modular-inverse
rectangle discrepancy and centered flat dispersion remain paper-only.
The marked Type II sum and Goldbach remain unproved.
