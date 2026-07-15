# Finite KMS thermofield projector law

- **ID:** `finite-kms-thermofield-projector-law`
- **Stage:** 1-in-progress
- **Type:** PHYSICS VALUE RELATION / LEAN CORPUS STRENGTHENING
- **Source:** thermofield dynamics and the canonical purification of finite Gibbs states

## Statement

For a nonempty finite spectrum with Gibbs probabilities `p_a`, the existing symmetric KMS
half-density kernel

```text
W_ab = exp(-beta*(E_a+E_b)/2) / Z_beta
```

is the rank-one kernel `sqrt(p_a)*sqrt(p_b)`.  It therefore obeys the exact contraction and
marginal laws

```text
W_ab * W_bc = W_ac * p_b,
sum_b W_ab * W_bc = W_ac,
sum_b W_ab^2 = p_a.
```

These are static value identities.  They do not introduce a thermal flow or a new hypothesis.

## Corpus value

The laws are formalized generically in
`formal/GaloisForLFunctions/HTGeometry/FiniteKMSWightman.lean`.  The row-marginal theorem is used
immediately in `FiniteKMSPurityNormalization.lean` to replace the former two-index partition
expansion in the proof that the KMS half-density has unit Frobenius mass.  Every existing finite
KMS, passive-response, thermal-Krylov, prime-log KMS, and Gibbs exposed-face module importing the
generic file can now use the projector law directly.

The projector and purity values also give the exact thermofield linear-entropy relation

```text
sum_(a != b) W_ab^2 = 1 - sum_a p_a^2 = 1 - Z_(2 beta) / Z_beta^2.
```

This is formalized by
`sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity`.  It eliminates an explicit
two-index off-diagonal transition sum in favor of the already-normalized replica scalar.  The
existing Gibbs exposed-face consumer is strengthened immediately: if the zero-temperature
Gibbs state concentrates uniformly on an exposed face of cardinality `r`, then the off-diagonal
thermofield mass converges exactly to `1 - 1/r`.  The corresponding Lean theorem is
`tendsto_offDiagonal_sq_finiteKMSWightmanWeight_neg_energy_exposedFaceCard` in
`GibbsExposedFaceRadicalFlag.lean`.

For independent systems, the same value is compositional rather than additive.  If `L_A` and
`L_B` are their off-diagonal thermofield masses, Lean now proves the exact quantum-information
law

```text
L_(A tensor B) = L_A + L_B - L_A*L_B.
```

This is `sum_offDiagonal_sq_finiteKMSWightmanWeight_tensor`; it follows from the already-proved
purity product without expanding the four-index tensor kernel.

This does not discharge the source-specific prime--Gamma response comparison.  Its useful content
is structural: the bare KMS half-density has only one thermal direction, so additional observable
amplitudes are the sole source of higher-rank transition geometry.

## Physics provenance

The coefficient vector is the canonical thermofield-double purification of a Gibbs state.  See
Y. Takahashi and H. Umezawa, *Thermo field dynamics*, Collective Phenomena 2 (1975), 55--80,
reprinted as DOI `10.1142/S0217979296000817`; T. Barthel, *One-dimensional quantum systems at
finite temperatures can be simulated efficiently on classical computers*, arXiv:1708.09349; and
the explicit canonical-purification formula in Phys. Rev. Lett. 122, 201601 (2019).

## Verification status

- [x] Exact algebra matched to the live finite KMS definitions.
- [x] Generic projector, gluing, and Gibbs-marginal theorem sources added.
- [x] Existing global Frobenius-normalization proof rewired through the marginal theorem.
- [x] Off-diagonal thermofield mass identified exactly with Gibbs linear entropy.
- [x] Identity applied to the existing zero-temperature exposed-face limit.
- [x] Independent-system off-diagonal mass reduced to the two component values.
- [ ] Lean elaboration/build check intentionally not run under the active no-build/no-computation
  constraint.
