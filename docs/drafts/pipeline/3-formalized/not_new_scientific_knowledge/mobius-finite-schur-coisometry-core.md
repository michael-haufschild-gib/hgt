# Finite squarefree Möbius channels are exact Schur coisometries

- **ID:** `mobius-finite-schur-coisometry-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean files:**
  `formal/GaloisForLFunctions/RHTower/FiniteSignedChannelCoisometry.lean`;
  `formal/GaloisForLFunctions/RHTower/MobiusFiniteSchurTransfer.lean`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius-signed-coisometry-schur-transfer-law.md`
- **Statement:** Every finite prime aperture has a normalized signed squarefree probability
  channel whose synthesis is an exact coisometry, whose channel projection is idempotent, and
  whose Euler-side transfer product has modulus at most one throughout the closed right half-plane.

## Formalized theorem package

For a finite prime set `S`, real `sigma`, and

```text
q_p=exp(-sigma log p)>0,
```

the module defines

```text
b_p(z)=(1-q_p exp(-(log p)z))/(1+q_p),
tau_S(z)=product_(p in S) b_p(z).
```

Lean proves the local and global Schur bounds

```text
Re z>=0  ->  |b_p(z)|<=1,
Re z>=0  ->  |tau_S(z)|<=1.
```

It also proves the exact prime form

```text
b_p(z)
 =(1-exp(-(sigma+z)log p))/(1+exp(-sigma log p))
```

and the squarefree expansion of `tau_S` over `S.powerset`.

The associated squarefree probability is

```text
P_S(T)=product_(p in T)q_p / product_(p in S)(1+q_p).
```

The finite Euler expansion proves

```text
sum_(T subset S) P_S(T)=1.
```

With signed amplitude

```text
w_S(T)=(-1)^card(T) sqrt(P_S(T)),
```

Lean proves

```text
sum_T |w_S(T)|^2=1.
```

For synthesis and analysis

```text
R_w(f)=sum_T conjugate(w(T))f(T),
R_w^*(c)(T)=w(T)c,
```

the generic finite-channel module proves

```text
R_w R_w^*=I,
(R_w^*R_w)^2=R_w^*R_w,
R_w(R_w^*R_w f)=R_w(f).
```

These identities are then instantiated by `w_S` itself, rather than left behind a normalization
hypothesis.

## Main declarations

- `norm_bernoulliSignedSchurFactor_le_one`
- `bernoulliSignedSchurFactor_prime_eq`
- `finitePrimeSignedSchurTransfer_squarefreeExpansion`
- `norm_finitePrimeSignedSchurTransfer_le_one`
- `sum_finitePrimeSquarefreeProbability`
- `finitePrimeSquarefreeAmplitude_unit`
- `finitePrimeSquarefreeSynthesis_analysis`
- `finitePrimeSquarefreeProjection_idempotent`
- `finiteSignedChannelSynthesis_analysis`
- `finiteSignedChannelProjection_idempotent`
- `finiteSignedChannel_incidence_factorization`

## Boundary of the certificate

This formalizes the complete finite-aperture algebraic and right-half-plane contractive layer. The
cofinal squarefree normalization has since been formalized separately in
`formal/GaloisForLFunctions/RHTower/SquarefreeMoebiusNormalization.lean`, including
`L(mu^2,s)=zeta(s)/zeta(2s)` and the infinite Euler product. The present modules do not construct
the infinite Hardy shift operator or formalize meromorphic contour transport across zeta-zero
poles. Those operations remain the RH-bearing continuation seam in the paper card.

## Gates

- [x] finite Euler and powerset infrastructure reused from `RHProofLab/EulerProductArithmetic.lean`
- [x] exact signed probability normalization formalized
- [x] exact coisometry and projection identities formalized
- [x] local and finite-product Schur bounds formalized
- [x] arithmetic squarefree channel instantiated
- [x] RHTower aggregate import added
- [x] infinite squarefree zeta normalization available in `SquarefreeMoebiusNormalization.lean`
- [ ] infinite Hardy shift-average realization
- [ ] orbit-sensitive meromorphic continuation graph
- [ ] four-unit Xi-source upper bound
