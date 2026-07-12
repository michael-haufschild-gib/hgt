# Xi--Hurwitz separated source-packet reconstruction

- **ID:** `xi-hurwitz-separated-source-packet-reconstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The canonical Xi--Hurwitz orientation vector is the Hilbert limit of actual finite
  pairwise-conjugate-separated continued prime--Gamma Cauchy packets, and their exact explicit
  divided-difference energies converge to minus the global orientation energy.

## Formal chain

`XiContinuedCauchyPacketDensity.lean` proves:

```text
arbitrary finite continued Cauchy packet
  -> common vanishing (1+i)-pole perturbation
  -> all z_i != conjugate(z_j)
  -> ell^2 convergence of packet evaluations
  -> exact finite continued prime--Gamma source energy
  -> convergence of source energy to the original Weil Hilbert value.
```

Every algebraic-span vector is also extracted as an actual finitely supported indexed packet.

`XiHurwitzOrientationSeparatedSourceReconstruction.lean` then proves:

```text
exists P_n,
  evaluation(P_n) -> v_Xi,
  sourceEnergy(P_n) -> -E_Xi,
```

where every `P_n` is finite, lies in the genuine continued source domain, and has no pairwise
conjugate collision.  It also proves

```text
RH iff sourceEnergy(P_n) >= 0 eventually
```

for one unconditional existential sequence.

## Boundary

The sequence is extracted through the already-proved closure of the target orientation vector.
It is therefore not yet a source-pure producer.  The remaining mathematical theorem must either
select the packets deterministically from prime--Gamma values or prove eventual nonnegativity for
a source-defined packet class containing the reconstructed sequence.

## Lean certificate

- `RHTower.exists_pairwiseConjSeparatedContinuedCauchyPacketLp_tendsto`
- `RHTower.xiWeilPolarization_indexedCauchyPacket_eq_continuedSource`
- `RHTower.exists_pairwiseConjSeparatedContinuedSourceEnergy_tendsto`
- `RHTower.exists_finsupp_indexedCauchyPacket_eq_of_mem`
- `RHTower.xiHurwitzOrientationEnergy_separatedContinuedSource_reconstruction`
- `RHTower.exists_separatedContinuedSource_sequence_eventually_nonnegative_iff_riemannHypothesis`

## Gates

- [x] paper proof complete
- [x] Lean formalization complete
- [x] exact module builds
- [x] axiom audit
- [ ] source-pure selection or sign producer
- [ ] RH
