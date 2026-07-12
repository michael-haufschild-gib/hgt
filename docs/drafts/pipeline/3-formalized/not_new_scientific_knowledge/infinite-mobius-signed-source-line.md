# Infinite squarefree Möbius source line and coisometry

- **ID:** `infinite-mobius-signed-source-line`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean file:**
  `formal/GaloisForLFunctions/RHTower/InfiniteMobiusSignedChannel.lean`,
  `formal/GaloisForLFunctions/RHTower/InfiniteMobiusCausalShift.lean`,
  `formal/GaloisForLFunctions/RHTower/InfiniteMobiusShiftAnalysis.lean`, and
  `formal/GaloisForLFunctions/RHTower/InfiniteMobiusLaplaceMultiplier.lean`
- **Upstream:**
  `formal/GaloisForLFunctions/RHTower/SquarefreeMoebiusNormalization.lean`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius-signed-coisometry-schur-transfer-law.md`
- **Statement:** For every real `sigma>1`, the normalized signed squarefree Möbius amplitudes form
  an actual unit vector in `ell^2(N)`. Inner product against this vector is a surjective
  coisometry, its adjoint is the source-line analysis map, and their composition is a contractive
  idempotent projection onto the distinguished all-prime Möbius line.

## Exact arithmetic normalization

Lean defines

```text
mass_sigma(n)=[Squarefree n] n^(-sigma),
Z_sigma=sum_n mass_sigma(n),
P_sigma(n)=mass_sigma(n)/Z_sigma.
```

It proves summability, positivity of `Z_sigma`, normalization

```text
sum_n P_sigma(n)=1,
```

and, using `SquarefreeMoebiusNormalization.lean`, the exact identification

```text
(Z_sigma:C)=zeta(sigma)/zeta(2sigma).
```

## Infinite signed channel

The signed amplitude is

```text
w_sigma(n)=mu(n) sqrt(P_sigma(n)).
```

Lean proves pointwise and globally

```text
|w_sigma(n)|^2=P_sigma(n),
sum_n |w_sigma(n)|^2=1,
||w_sigma||_ell2=1.
```

For an arbitrary unit vector `w` in an `ell^2` carrier it defines

```text
R_w(f)=<w,f>,
R_w^*(c)=c w,
Pi_w=R_w^* R_w.
```

The formal theorems give

```text
R_w R_w^*=I,
Pi_w^2=Pi_w,
R_w Pi_w=R_w,
Pi_w R_w^*=R_w^*,
||R_w f||<=||f||,
||Pi_w f||<=||f||.
```

The coisometry theorem is instantiated with the actual infinite Möbius amplitude, not left behind
a finite cutoff or an abstract normalization hypothesis.

The same normalized amplitudes now define the divisor-resolved logarithmic shift analysis

```text
A_sigma f=(w_sigma(n) U_(-log n)f)_n
  :L2(R)->ell2(N;L2(R)).
```

Lean proves `A_sigma` is a genuine complex-linear isometry. Thus the arithmetic coordinates and
their logarithmic translations coexist in one countable Hilbert carrier before scalar synthesis;
the prime/divisor state is not represented only by its coefficient vector or by a finite sum.

## Main declarations

- `summable_squarefreeMobiusMass`
- `squarefreeMobiusTotal_eq_zetaRatio_re`
- `tsum_squarefreeMobiusProbability`
- `norm_infiniteMobiusSignedWeight_sq`
- `infiniteMobiusSignedWeightLp`
- `norm_infiniteMobiusSignedWeightLp`
- `infiniteSignedChannelSynthesis_analysis`
- `infiniteSignedChannelProjection_idempotent`
- `infiniteSignedChannelSynthesis_projection`
- `norm_infiniteSignedChannelSynthesis_le`
- `norm_infiniteSignedChannelProjection_le`
- `infiniteSignedChannel_incidence_factorization`
- `infiniteMobiusSignedChannel_coisometry`
- `summable_infiniteMobiusShiftTerm`
- `infiniteMobiusShiftAverage`
- `norm_infiniteMobiusShiftAverage_le`
- `infiniteMobiusShiftAnalysis`
- `norm_infiniteMobiusShiftAnalysisValue`
- `additiveTranslationUnitary_hasAELowerSupport_zero`
- `infiniteMobiusShiftAverage_hasAELowerSupport_zero`
- `causalLaplacePairing_additiveTranslationUnitary_neg`
- `causalLaplacePairing_infiniteMobiusShiftAverage`
- `infiniteMobiusLaplaceMultiplier_eq_zetaRatio`

## Route consequence

The arithmetic projection `Pi_omega` in the coupled floor--Möbius route no longer requires a
finite-aperture surrogate: specialize `sigma=1+2omega`. The module also forms the actual absolutely
summable average of logarithmic `L^2(R)` translation unitaries with signed Möbius probabilities and
proves its norm is at most one. Positive logarithmic shifts and their countable average preserve
the zero-threshold causal subspace. On that subspace the Laplace readout has the exact multiplier

```text
tau_sigma(x)=zeta(2sigma)/
  (zeta(sigma) zeta(sigma+pi*x)),       sigma>1, x>0.
```

This completes the causal arithmetic channel. Decisively, it is only the reciprocal-zeta factor
in the absolutely convergent half-plane. No orbit-sensitive meromorphic continuation through the
charged graph, no floor-discrepancy coupling, and no contour-jump estimate is proved.

## Gates

- [x] squarefree real mass summability and positivity
- [x] exact zeta-quotient total mass
- [x] normalized all-prime probability
- [x] signed amplitude realized in `ell^2(N)`
- [x] unit norm and exact coisometry
- [x] idempotent contractive source-line projection
- [x] RHTower aggregate import
- [x] infinite logarithmic `L^2` signed translation average and contraction
- [x] divisor-resolved logarithmic shift analysis as an `ell^2(N;L^2)` linear isometry
- [x] causal zero-threshold restriction
- [x] exact reciprocal-zeta Laplace multiplier
- [ ] Xi-pointed charged continuation graph
- [ ] four-unit boundary estimate
