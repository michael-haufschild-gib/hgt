# TG actual mixed-prime cubic principal coefficient

- **ID:** TG-C5-CUBIC-PRINCIPAL
- **Stage:** 3-formalized
- **Route:** TG
- **Module:** `RHTower.PrimeBurnolMixedCubicPrincipal`
- **Parent:** `../1-in-progress/tg-mixed-reflection-collision-counterterm.md`
- **Next operator test:** `../1-in-progress/tg-confluent-cofinal-counterterm.md`

## Exact source theorem

For every finite injective prime-depth packet and every real theta grade a, let c(k) be the
literal L2 Gram of all original columns at clocks k and -k. The original-sector projections are

```
p=[[I,0],[0,0]],
q=[[U,V],[V,I-U]],
U=diag(thetaVisibility(a,p_i)^2),
V=diag(thetaVisibility(a,p_i)*thetaContrast(a,p_i)).
```

Set `C(r,q,p)=(r-p)^3-(r-q)^3-(q-p)^3`, and retain the complete weighted source cubic

```
tau(k)=Tr(c(k)*C(c(k)^-1 q c(k),q,p)).
```

With `G=M_0` and `K=M_2-M_1 G^-1 M_1` from the literal confluent moment Gram, Lean proves

```
lim_(k->0,k!=0) k^2 tau(k) = -Tr(G K^-1 (U-I/2) G V).
```

This theorem has no unproved invertibility, projection, convergence, or arithmetic hypothesis.
Injective finite labels are bundled as an embedding. It holds for every real theta grade,
including zero, and the limit is two-sided. All cross-prime and inverse-Gram terms remain.

## Proof chain

1. The actual `sech/tanh` identity proves theta projection idempotence.
2. Continuity of the desingularized Gram's determinant and its nonzero value at collision
   give eventual punctured invertibility of the actual parity Gram.
3. The existing checked single-inverse cubic trace formula separates one inverse-dependent
   term from a polynomial term. The latter vanishes after multiplication by k squared.
4. The audited inverse pole, together with continuity of the source Gram, gives the full
   block limit. Matrix multiplication yields the stated Schur-inverse coefficient exactly.
5. A concrete Hadamard unit conjugates the original source Gram and both original-sector
   projections to the parity data. Conjugation preserves the inverse, cubic associator and
   weighted trace, identifying the limit with the original literal source current.

## Frontier contribution and limits

The previous result gave only the matrix inverse pole. This result computes the actual
theta-weighted source cubic coefficient and verifies its source-coordinate provenance.
It supplies a precise, prime-mixing counterterm for testing Gamma cancellation.

Only the leading second-order coefficient is proved here. Subtracting it is not claimed to
leave a bounded remainder; the mixed first-order term and finite part remain open. No cofinal
operator bound, actual Gamma cancellation, source-to-Hardy identification, or RH result follows.

The live cofinal test uses the corpus's single-prime depth density. Canonical dual vectors may
force the new coefficient to diverge as packets grow; the exact proposed argument and its
rank-one charge-escape survivor are recorded on the next card, not asserted as Lean results.

## Audit

- Production `lake --old env lean -o ... PrimeBurnolMixedCubicPrincipal.lean`: exit 0, no warnings.
- New leaf wired into RHTower umbrella; no full or umbrella build.
- Separate `lake --old env lean /tmp/...` audit checks all seven public theorem axiom sets:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Corpus index regenerated. Lint exits 1 on eleven unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMPrimeDeficitEulerPositiveRigidity, CCMRetainedChainKernelLower,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. The new TG leaf is not reported.
- Scoped tracked-file whitespace check passes. Owned temporary files cleaned; no owned build
  or search process remains running.
