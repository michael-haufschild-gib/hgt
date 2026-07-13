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

## Primary physics references

- S. Sarkar, B. K. Patra, V. J. Menon, S. Mallik, *Spectral Representation at Finite
  Temperature*, <https://arxiv.org/abs/hep-th/0010062>.
- G. S. Uhrig, M. H. Kalthoff, J. K. Freericks, *Positivity of the spectral densities of retarded
  Floquet Green functions*, <https://arxiv.org/abs/1808.10199>.
- B. Bradlyn, P. Abbamonte, *Spectral Density and Sum Rules for Second-Order Response Functions*,
  <https://arxiv.org/abs/2404.16144>.

## Gates

- [x] exact finite absorptive identity numerically pre-certified
- [x] exact finite absorptive identity formalized in Lean
- [x] canonical KMS passivity specialization formalized
- [x] thermodynamic-limit anti-Herglotz transfer formalized
- [x] direct RH consumer formalized
- [ ] source-defined response family constructed
- [ ] pointwise source-value convergence proved
