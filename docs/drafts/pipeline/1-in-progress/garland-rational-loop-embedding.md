# Coefficient-field embeddings of the central loop group

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** Construct the faithful map `LoopSL2 ℚ → LoopSL2 ℝ` from the
  actual rational coefficient inclusion, compatible with center and root groups.

## Dependency and scope audit

The central extension exists over every field. An actual arithmetic quotient
over `ℚ` also needs its faithful inclusion into the real group. Merely having
two group types does not construct that map. Corpus search found the proved
coefficientwise `hahnMapRingHom` in `HahnDilation.lean`; its multiplication law
uses the common support antidiagonal. No central-loop field map was found.
Functoriality of the tame extension is standard, not a novelty claim; compare
Liu, *Eisenstein Series on Loop Groups*, §3.1,
<https://arxiv.org/abs/1103.4212>.

## Dependency-closed paper proof

For a field homomorphism `ι:F→E`, coefficientwise application gives
`ι((∑a_nX^n))=∑ι(a_n)X^n`. The existing Hahn-series construction proves
multiplicativity. Injectivity of a field map preserves vanishing of every
coefficient, hence preserves the Laurent valuation and its integer exponent.
The Laurent residue is the degree-zero coefficient, so residue commutes with
`ι` on valuation-zero units. Applying `ι` to
`(-1)^(mn) a^n b^(-m)` therefore proves

`T_E(ι(a),ι(b)) = ι(T_F(a,b))`.

Apply the Laurent field map to matrix entries and `ι` to the central unit.
The Kubota coordinate commutes with this map because injectivity preserves
the branch `c=0`. Its tame factor consequently commutes as well, proving the
group homomorphism law. Projection and central-coordinate injectivity prove
faithfulness. Entrywise formulas give compatibility with both root groups and
the center. Specializing to the canonical map `ℚ→ℝ` gives the required
rational subgroup of the real central loop group.

## Status

Paper proof recorded. Implementation follows the positive-loop splitting.
This supplies coefficient-field functoriality, not an arithmetic lattice,
Iwasawa decomposition, or Eisenstein convergence theorem.
