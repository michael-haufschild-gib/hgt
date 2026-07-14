# Prime-log universal HT carrier as a finite KMS response limit

- **ID:** `prime-log-kms-response-realization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PHYSICS BRIDGE / OPERATIONAL LEAN VALUE
- **Source:** Bost--Connes multiplicative quantum statistical mechanics; finite-temperature
  spectral/KMS response theory; `PrimeLogHerglotz.lean`; `FiniteKMSWightman.lean`;
  `FinitePassiveResponse.lean`; `UniversalPrimeOrientationLimit.lean`.
- **Statement:** For every bounded prime gauge and every inverse temperature, its prime-log
  Herglotz carrier is the locally uniform thermodynamic limit of explicit finite KMS/Wightman
  passive responses with vacuum-to-prime energy gaps `log p`; the response derivatives converge
  locally uniformly as well. For the fixed universal HT gauge, this KMS net converges to an
  infinite Boolean prime-orientation carrier exactly when that orientation is the canonical
  all-positive one.

## Goal

Replace the previously abstract positive prime-log spectral carrier by an exact finite-dimensional
quantum-statistical realization that can be consumed by the existing constraint-orientation,
upper-end analytic, and Cauchy-jet corpus. The useful content is the exact value relation, its
finite-to-infinite convergence strength, and the selector theorem it supplies for an existing
orientation object.

This theorem does not identify the continued prime--Gamma source used by the RHTower RH gates.
That source comparison remains open.

## Gates

- [x] 0 → 1 in-progress: exact source-pure finite system, response identity, finite-set limit, and
  existing consumers identified.
- [x] 1 → 2 fully-proven: finite KMS normalization, passive-response identity, pointwise and
  locally uniform limits, derivative limit, and orientation-selection proof are complete.
- [x] 2 → 3 formalized: `PrimeLogKMSRealization.lean` builds in the project toolchain; the checked
  declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] 3 → 4 publication-ready: no standalone paper is claimed.

## Physics input

In the Bost--Connes multiplicative dynamics, the integer level `|n⟩` has energy `log n`, since the
time evolution acts with phase `n^(it)`. Therefore the vacuum-to-prime transition has the exact
Liouvillian frequency

```text
E_p - E_1 = log p.
```

This is precisely the pole support of the existing prime-log Herglotz carrier. The construction
uses the standard finite-temperature spectral decomposition: a directed transition contributes a
strictly positive KMS/Wightman thermal weight times the squared observable amplitude, and the
passive response is the Cauchy transform of those transition intensities.

Primary sources:

- Bost--Connes, *Hecke algebras, type III factors and phase transitions with spontaneous symmetry
  breaking in number theory*: <https://doi.org/10.1007/BF01589495>.
- Sarkar--Patra--Menon--Mallik, *Spectral Representation at Finite Temperature*:
  <https://arxiv.org/abs/hep-th/0010062>.

The Lean theorem does not import either physical statement as an axiom. It constructs the finite
Hamiltonians, amplitudes, intensities, and responses explicitly.

## Construction and proof

For a finite prime set `P`, use the state type `Option P`: `none` is the vacuum and `some p` is the
prime level. Set

```text
E(none)   = 0,
E(some p) = log p.
```

The requested carrier weight is the existing positive dyadic weight `primeDyadicWeight u p`.
Because the finite KMS/Wightman transition weight is strictly positive, define the sole nonzero
directed amplitude by

```text
A(some p, none)
  = sqrt (primeDyadicWeight u p / finiteKMSWightmanWeight beta E (some p) none).
```

Its KMS intensity is exactly `primeDyadicWeight u p`. Direct expansion of the finite passive
response then gives

```text
- response_P(z)
  = sum_(p in P) primeDyadicWeight(u,p) / (log p - z)
  = finitePrimeLogHerglotz(P,u,z).
```

Absolute summability of the existing dyadic weights yields convergence along the directed set of
finite prime sets. The already-formalized locally uniform discrete-Cauchy summation theorem upgrades
the limit from pointwise convergence to local-uniform convergence on the upper half-plane. Each
finite response is holomorphic there, so complex Weierstrass convergence gives local-uniform
convergence of the response derivatives.

For the universal gauge, suppose the same finite KMS net converges pointwise to an arbitrary
`universalPrimeOrientationLimit ε`. Uniqueness of limits identifies that carrier with the positive
prime-log carrier on the upper half-plane. Its imaginary part is therefore nonnegative, and the
existing theorem `universalPrimeOrientationLimit_nonneg_iff_allPositive` forces
`ε = fun _ => false`. The converse is the canonical limit theorem itself.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/PrimeLogKMSRealization.lean`.

Principal declarations:

- `primeLogKMSFiniteEnergy_gap`;
- `finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteAmplitude`;
- `neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude`;
- `finiteKMSWightmanResponse_tendsto_primeLogHerglotz`;
- `finiteKMSWightmanResponse_tendstoLocallyUniformlyOn_primeLogHerglotz`;
- `finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn_primeLogHerglotz`;
- `universalFacetOrbitGauge_finiteKMSWightmanResponse_tendstoLocallyUniformlyOn`;
- `universalFacetOrbitGauge_finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn`;
- `universalPrimeOrientationLimit_is_canonicalKMSLimit_iff`;
- `canonicalConstraintOrientationLimit_primeCarrier_is_canonicalKMSLimit_iff`.

## Direct corpus value

1. `UniversalFiniteConstraintCarrier.lean`: the one fixed carrier that realizes every finite
   Stanley--Reisner differential matroid now has an explicit finite KMS thermodynamic realization.
2. `UniversalPrimeOrientationLimit.lean`: the existing all-positive analytic selector is
   strengthened to an exact KMS-response-limit selector; all other Boolean residue orientations
   are excluded for this positive finite KMS net.
3. `UpperEndPrimeLogCarrier.lean`, `UpperEndPrimeLogJets.lean`, and the Cauchy-jet modules: the
   local-uniform value and first-derivative limits supply finite quantum approximants compatible
   with their analytic and differential interfaces.
4. `CanonicalConstraintOrientationLimit`: its prime coordinate now has a direct physical
   admissibility criterion, formalized without adding a new hypothesis.

The result discharges the abstract-realization and finite-to-limit obligations for the universal
HT carrier. It does not discharge the source-specific positivity or response-limit hypotheses in
`RHTower/PrimeArchPassiveResponseRH.lean`, because that file concerns the continued prime--Gamma
source rather than the synthetic universal positive carrier.

## Open source obligation

The KMS amplitude is normalized to reproduce the pre-existing dyadic carrier weight. A stronger
physical result would derive that observable, or a source-equivalent one, from an intrinsic
multiplicative algebra rather than prescribing its matrix element. More importantly for RH, one
must still construct an explicit KMS/passive response net whose limit is the continued
prime--Gamma source, including its coupled sign-changing prime and archimedean contributions. No
claim in this card supplies that comparison.
