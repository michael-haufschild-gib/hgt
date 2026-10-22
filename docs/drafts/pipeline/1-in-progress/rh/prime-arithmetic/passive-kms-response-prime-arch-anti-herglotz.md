# Passive KMS response and the prime--archimedean anti-Herglotz gate

- **ID:** passive-kms-response-prime-arch-anti-herglotz
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [FORMALIZED CONSUMER]`
- **Physics source:** finite-temperature Lehmann/Kubo spectral representation and passivity.

## Transferable value

For nonnegative spectral intensities `I_a` at real frequencies `ω_a`, use the retarded-resolvent
convention

\[
R(z)=\sum_a \frac{I_a}{z-\omega_a}.
\]

Its absorptive value is exact:

\[
\operatorname{Im}R(z)
=-\sum_a \frac{I_a\operatorname{Im}z}{|z-\omega_a|^2}\le 0
\qquad(\operatorname{Im}z>0).
\]

For a finite Hamiltonian, take `ω_ab=E_a-E_b`.  Canonical KMS/Wightman intensities are already
nonnegative, so no separate passivity assumption remains.

The symmetric KMS half-density also has the exact fluctuation--dissipation conversion

\[
2\sinh\!\left(\frac{\beta(E_a-E_b)}2\right)I^W_{ab}
=(p_b-p_a)|A_{ab}|^2.
\]

For a Hermitian amplitude the right side is the commutator spectrum.  Whether or not the amplitude
is Hermitian, multiplication of the FDT-transformed Wightman intensity by the same energy gap gives
the nonnegative dissipative oscillator strength

\[
D_{ab}=(E_a-E_b)(p_b-p_a)|A_{ab}|^2\ge 0
\qquad(\beta\ge0).
\]

This relation is stronger than using `I^W` as an arbitrary positive response weight: it identifies
the exact Gibbs population difference, agrees with the actual commutator for Hermitian amplitudes,
proves dissipative symmetry there, and reindexes odd commutator moments as an ordinary
Stieltjes-positive even moment sequence.

## Corpus application

`PrimeArchAntiHerglotzGate.lean` proves that the continued prime--archimedean source is
anti-Herglotz on the centered upper half-strip only if RH holds.  Therefore a pointwise
thermodynamic limit of canonical finite KMS responses equal to that source trace proves RH.

The value comparison is the open source-facing statement:

```text
finite canonical KMS Lehmann responses
  -> pointwise limit = continuedPrimeArchSourceRelativeTrace
       [OPEN CORE]
  -> upper-half-plane nonpositive imaginary part
       [FORMALIZED]
  -> ContinuedPrimeArchUpperAntiHerglotz
       [FORMALIZED]
  -> RH
       [FORMALIZED EXISTING CONSUMER]
```

`FiniteKMSDetailedBalance.lean` already owned the commutator intensity and its `sinh`/`tanh`
relations; the new work reuses those declarations rather than defining a parallel commutator.
`FiniteKMSFluctuationDissipation.lean` adds the population-difference identity, the positive
energy-weighted transform, and discharges the nonnegative-intensity hypotheses of both
`FinitePassiveResponse.lean` and `ThermalKrylovMoments.lean` from `β ≥ 0` (with Hermiticity only
where identification with the commutator is required).  `PrimeLogKMSRealization.lean` normalizes an explicit
vacuum-to-prime jump amplitude so that its dissipative spectrum is exactly
`primeLogKMSFiniteIntensity`; hence its negative response is exactly `finitePrimeLogHerglotz` for
every `β > 0`.  `PrimeArchPassiveResponseRH.lean` consumes a pointwise limit of these dissipative
responses directly.  The new branch does not prove the source-value convergence.

## Primary physics references

- S. Sarkar, B. K. Patra, V. J. Menon, S. Mallik, *Spectral Representation at Finite
  Temperature*, <https://arxiv.org/abs/hep-th/0010062>.
- G. S. Uhrig, M. H. Kalthoff, J. K. Freericks, *Positivity of the spectral densities of retarded
  Floquet Green functions*, <https://arxiv.org/abs/1808.10199>.
- B. Bradlyn, P. Abbamonte, *Spectral Density and Sum Rules for Second-Order Response Functions*,
  <https://arxiv.org/abs/2404.16144>.
- F. M. Haehl, R. Loganayagam, P. Narayan, A. A. Nizami, M. Rangamani, *Thermal
  out-of-time-order correlators, KMS relations, and spectral functions*,
  <https://arxiv.org/abs/1706.08956>.
- M. Dodelson, C. Iossa, R. Karlsson, A. Zhiboedov, *A thermal product formula*, Appendix A,
  <https://arxiv.org/abs/2304.12339>.

## Gates

- [x] exact finite absorptive identity numerically pre-certified
- [x] exact finite absorptive identity formalized in Lean
- [x] canonical KMS passivity specialization formalized
- [x] thermodynamic-limit anti-Herglotz transfer formalized
- [x] direct RH consumer formalized
- [x] generic finite fluctuation--dissipation identity written in Lean source
- [x] dissipative passivity and ordinary/shifted Hankel hypotheses discharged in Lean source
- [x] exact prime-log dissipative response realization written in Lean source
- [x] direct RHTower dissipative-limit consumer written in Lean source
- [ ] targeted Lean verification of the FDT additions (deferred under the no-build constraint)
- [ ] source-defined response family constructed
- [ ] pointwise source-value convergence proved
