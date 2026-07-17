# Completed prime--Gamma--polar resolved moment colligation

- **ID:** `completed-prime-gamma-resolved-moment-colligation`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** SOURCE-RESOLUTION BRIDGE (Lean), SIGN-INCIDENCE THEOREM
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:**
  - `von-mangoldt-gamma-factorial-normalization-positivity-no-go.md`;
  - `../../1-in-progress/euler-gamma-conormal-markov-dilation-rh.md`.
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaResolvedMomentColligation.lean`

## Theorem

For real `x>1`, define

```text
P_k(x)=m_(2k+1)(x-1)/(2k+1)!,
G_k(x)=2^(-2k-2) gammaBoseMoment(x/2,2k),
R_k(x)=x^(-2k-2)+(x-1)^(-2k-2),
C_k(x)=P_k(x)+G_k(x)-R_k(x),
```

where `m_j` is the cofinal pointed von Mangoldt--Gamma raw source moment.  Lean proves the exact
analytic identity

```text
completedOddLogDerivMoment(x,k)=(-1)^k C_k(x).           (1)
```

This is derived directly from the source decomposition of `xi'/xi`: the Euler `LSeries` is the
cofinal Gamma raw moment, the half-argument digamma derivative is the Gamma/Bose moment, and the
rational completed leg is the polar pair.  No correction is inferred from the target determinant.

Let `H_C`, `H_P`, `H_G`, and `H_R` be the corresponding Hankel matrices.  Lean proves

```text
H_C=H_P+H_G-H_R.                                        (2)
```

The two completion components have genuinely different source realizations:

```text
H_G is positive definite at every finite size,           (3)
H_R is a positive-semidefinite two-atom Gram.             (4)
```

The Gamma proof extracts the even principal submatrix of the positive infinite Gamma/Bose Hankel
clock and applies the forced diagonal half-argument scaling.  The polar proof identifies `H_R`
with the literal two-atom raw Gram whose positive nodes and weights are `x^-2` and `(x-1)^-2`.

Finally, the analytic completed Hankel matrix on the real axis is the complexification of the
alternating diagonal sign congruence of `H_C`.  Applying this sign congruence twice gives `H_C`, so

```text
signed(H_C)>=0  iff  H_C>=0.                             (5)
```

All claims are unconditional.

## RH consequence

The factorial-normalization no-go did not show that completion is absent; it showed that the Euler
leg was being projected before completion.  Equations `(1)--(4)` now give the unique correction
forced by the actual completed source:

```text
factorial Euler + positive Gamma - positive rank-two polar.
```

This identifies the precise remaining RH orientation problem.  Reconstruction, aperture passage,
analytic identification, parity signs, Gamma positivity, and polar Gram realization are no longer
open.  What remains is a source theorem controlling the *coupled signed incidence* in `(2)` under
transport from the absolute-Euler region to the critical center.

Neither `(3)` nor the rank-two bound in `(4)` proves that control.  General finite-negative-index
or Pontryagin-space realization theory allows real sign crossings and generalized zeros of
nonpositive type.  More decisively, the source itself has such crossings: for the polynomial
compression `P=X`, the resolved scalar is `c_2(x)`, and the proved four-crossing law gives
`c_2(1/2)>0`, `c_2(10)<0`, and `c_2(x)>0` eventually.  Thus the completed incidence makes a genuine
negative excursion and returns.  Calling `(2)` a fixed-index colligation is not an RH proof, and
no continuation argument excluding odd real crossings can be true.  A viable producer must act
directly at the critical center, or use a different invariant that remains coercive through these
signed excursions.

## Anti-theatre and novelty gate

The decomposition of `xi'/xi`, Gamma/Bose moment positivity, finite atomic Gram positivity, and
alternating diagonal congruence belong to established parent theories.  The card is therefore not
claimed as new scientific knowledge.  Its significance is exact route purification: it replaces
the false Euler-only normalization arrow by the actual three-leg completed incidence and exposes
the one sign-control theorem still capable of implying RH.

## Lean certificate

Principal declarations:

- `completedOddLogDerivMoment_ofReal_eq_resolved`;
- `completedGammaSpectralHankelMatrix_posDef`;
- `completedPolarPairMoment_eq_twoAtomMoment`;
- `completedPolarPairHankelMatrix_eq_rawGram`;
- `completedPolarPairHankelMatrix_posSemidef`;
- `completedPrimeGammaResolvedHankelMatrix_eq_incidence`;
- `completedPrimeGammaSignedHankelMatrix_eq_congruence`;
- `completedPrimeGammaResolvedHankelMatrix_eq_signedCongruence`;
- `completedPrimeGammaSignedHankelMatrix_posSemidef_iff`;
- `completedOddLogDerivHankelMatrix_ofReal_eq_resolvedSignCongruence`.

Verification:

- exact target build passed;
- axiom audit: `propext`, `Classical.choice`, and `Quot.sound` only;
- no numerical computation;
- no positivity, factorization, Xi-zero, or RH hypothesis used.

## Gates

- [x] exact prime--Gamma--polar scalar resolution
- [x] exact Hankel incidence
- [x] strict Gamma completion positivity
- [x] two-atom polar Gram realization and positivity
- [x] analytic-to-real alternating sign congruence
- [x] positivity equivalence under parity congruence
- [x] finite-index realization rejected as an automatic even-crossing theorem
- [x] odd-crossing sign-transport route falsified by the `P=X` four-crossing law
- [ ] direct critical-center source producer or excursion-stable invariant
- [ ] critical-center positivity
- [ ] RH
