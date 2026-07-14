# Prime-chamber dephasing master and Krein--Hamming correspondence

- **ID:** `prime-chamber-dephasing-krein-hamming`
- **Stage:** 1-in-progress
- **Type:** PHYSICS VALUE RELATION / FORMAL BRIDGE
- **Scientific status:** `[BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Physics source:** Z. Chen and X. Hu, *Resource theory of dephasing estimation in
  multiqubit systems*, Phys. Rev. A 108, 032415 (2023), arXiv:2304.14615, especially equation (6).
- **Lean target:** `formal/GaloisForLFunctions/HTGeometry/UniversalPrimeKreinHamming.lean`

## Claim

Represent a finite prime-residue chamber `J` by binary charges

```text
z_J(p) = -1  if p in J,
         +1  otherwise.
```

For two chambers `J,L`, the normalized independent-dephasing master energy of the coherence
`|J><L|` is

```text
E_deph(J,L)
  = (1/4) sum_(p in J triangle L) (z_J(p)-z_L(p))^2
  = #(J triangle L).
```

Thus `E_deph(J,L)=0` exactly when `J=L`.  The same two directed pieces of the symmetric difference
already control the relative prime-residue Pick form:

```text
kappa_+ = #(L \ J),
kappa_- = #(J \ L),
E_deph  = kappa_+ + kappa_-.
```

The physics relation therefore supplies a static positive master energy for the finite
prime-residue cube, while the existing Krein form refines that energy into its two directed
orientation counts.

## Corpus value

1. Completes the finite-set interface left open by
   `prime-residue-krein-hamming-product-law.md`: the generic positive/negative prime packets become
   the actual chamber differences `L \ J` and `J \ L`.
2. Gives the general hypertranscendental prime-residue geometry a quantum-information realization;
   it is not specialized to zeta zeros.
3. Replaces the declared Hamming grading by a positive sum-of-squares constraint energy.
4. Exposes a zero-energy kernel criterion usable by later constraint/Ward consumers: only diagonal
   chamber coherences survive independent dephasing.
5. Directly discharges the finite oriented-carrier positivity premise:
   `universalPrimeOrientedHerglotz_nonneg_iff_dephasingMasterEnergy_eq_zero` identifies global
   Herglotz positivity with zero master energy against the all-positive chamber.  The downstream
   theorem
   `universalPrimeOrientationLimit_coe_finset_nonneg_iff_dephasingMasterEnergy_eq_zero`
   transports the same criterion through the existing finite-to-infinite orientation embedding.

## Verification boundary

The relation is algebraic and source-derived.  During the current no-computation phase the Lean
declarations are manually reviewed but not built, linted, or axiom-audited.  Promotion to stage 3
requires a later targeted check.

## Gates

- [x] primary physics source identified
- [x] exact relation matched to an existing open Lean interface
- [x] no zeta/RH literature used
- [x] paper identity isolated
- [x] Lean source added and manually reviewed
- [ ] targeted Lean verification when computation is permitted
