# Hedenmalm spectral orientation classification

- **ID:** `hedenmalm-spectral-orientation-classification`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE / SINGULAR HILBERT--POLYA CARRIER CLASSIFICATION
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `hedenmalm-cyclic-null-form-nonclosability.md`

## Theorem

Let `mu` be a positive Borel measure of temperate growth on the real spectral axis and define

```text
q_mu(u,v)=integral_R hat(u)(t) conjugate(hat(v)(t)) dmu(t)
```

on complex Schwartz space.  For the normalized Hedenmalm theta source `k`, whose Fourier transform
is the centered completed zeta function `Xi`, the following classification holds
unconditionally:

1. `q_mu(k,k)=0` if and only if `mu` is carried by the real zero set of `Xi`;
2. in that case `mu` is exactly the sum of its point masses on the real `Xi` divisor;
3. `q_mu` is the zero form if and only if `mu=0`;
4. under theta nullity, `q_mu` is sequentially closable through ordinary `L^2(R)` if and only if
   `mu=0`;
5. every nonzero theta-null `q_mu` therefore has a dense proper ordinary-`L^2` radical image and
   zero induced ordinary-`L^2` quotient seminorm.

The premise-free capstone is

```text
[q_mu(k,k)=0 and q_mu is sequentially closable through ordinary L^2]
  iff mu=0.
```

The positive carrier law is:

> Every nonzero temperate spectral orientation of the Hedenmalm theta pair is a purely atomic
> real-divisor Hilbert space and is maximally singular relative to ordinary `L^2`.

## Proof route

- The Fourier identity `hat(k)=Xi` converts theta nullity into
  `integral |Xi(t)|^2 dmu(t)=0`.
- Positivity and continuity force the support of `mu` into the closed real zero set of `Xi`.
- That zero set is countable, so support implies the exact atomic decomposition.
- To prove faithfulness of `mu -> q_mu`, use smooth compactly supported spectral bump functions.
  Fourier inversion supplies Schwartz preimages; vanishing of `q_mu` makes every such bump vanish
  almost everywhere for `mu`, forcing the measure support to be empty.
- The exact cyclic-null closure classification then yields the closability equivalence.

## Gates

- [x] prove the converse support-to-nullity implication;
- [x] prove spectral-measure-form faithfulness without an assumed measure-uniqueness interface;
- [x] identify the form radical with the kernel of the Fourier-to-`L^2(mu)` carrier;
- [x] prove the exact theta-null atomic classification;
- [x] prove closability if and only if the spectral measure is zero;
- [x] prove the premise-free null-and-closable cone intersection law;
- [x] exact Lean build and axiom audit;
- [ ] parent-theory and primary-literature audit;
- [ ] assess whether the exact Hedenmalm application passes the significance gate.

## Boundary

This theorem classifies the full temperate spectral-measure class, not every abstract continuous
positive translation-invariant Schwartz form.  The latter converse is the Bochner--Schwartz
representation theorem.  It is standard parent theory but is not currently available in the
formal corpus; no paper claim may silently assume its formalization.

## Formal certificate

The complete proof is in
`formal/GaloisForLFunctions/RHTower/XiThetaSpectralOrientationClassification.lean`. Its headline
declarations are:

- `xiThetaSpectralCarrier_eq_zero_iff`;
- `spectralMeasureForm_mem_leftRadical_iff_carrier_eq_zero`;
- `spectralMeasureForm_eq_zero_iff_measure_eq_zero`;
- `spectralMeasureForm_xiTheta_null_iff_support_realDivisor`;
- `spectralMeasureForm_xiTheta_sequentiallyL2Closable_iff_measure_eq_zero`;
- `spectralMeasureForm_xiTheta_null_and_closable_iff_measure_eq_zero`.

All build exactly and their axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.
