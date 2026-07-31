# Finite Anderson recurrence-constraint conversion law

- **ID:** `finite-anderson-recurrence-constraint-conversion-law`
- **Stage:** 3-formalized
- **Type:** LOCAL-HAMILTONIAN REALIZATION THEOREM
- **Date:** 2026-07-31
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/FiniteAndersonRecurrenceConstraintConversionLaw.lean`

## Exact law

Fix any finite Hermitian hopping matrix \(T\), any real onsite potential
\(v_0\), and any \(\varepsilon>0\). There is a real onsite potential \(v_1\)
with
\[
  \operatorname{dist}(v_1,v_0)<\varepsilon
\]
such that the canonical eigenvalue packet of \(T+\operatorname{diag}(v_1)\)
has maximal projective rational rank. Consequently:

1. the temporal-dimension gain from \(v_0\) to \(v_1\) is exactly the
   complete projective recurrence-relation rank at \(v_0\);
2. the projective relation rank at \(v_1\) is zero; and
3. every fixed-time Heisenberg probe satisfies the dimension-free bound
   \[
     \|\alpha_t^{v_1}(O)-\alpha_t^{v_0}(O)\|
     \le 2|t|\varepsilon\|O\|;
   \]
4. every positive full-support replica collision moment at \(v_1\) equals
   its universal permutation floor.

The hopping graph and hopping amplitudes are unchanged. Only onsite
controls vary.

## Formal declaration

- `exists_finiteAnderson_onsite_fullConstraintConversion`.
- `norm_finiteAndersonHamiltonian_sub_eq_onsiteDist`;
- `finiteAnderson_heisenbergEvolution_norm_sub_le_onsiteDist`;

## Verification

The source was compiled to the project cache with:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteAndersonRecurrenceConstraintConversionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/FiniteAndersonRecurrenceConstraintConversionLaw.olean
```

A scratch `#print axioms` audit reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.

## Scope

This theorem closes local-Hamiltonian ensemble transfer for arbitrary
finite fixed hopping matrices. It does not assert thermodynamic-limit
localization, device noise tolerance, or monotonicity of any individual
first-return time.
