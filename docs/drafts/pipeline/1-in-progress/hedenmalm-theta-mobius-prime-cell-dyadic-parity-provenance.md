# Hedenmalm--theta Möbius prime-cell dyadic parity provenance

- **ID:** P-G52
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN SOURCE-CLEAN
- **Source:** P-G51 alternating current; existing full primitive Gamma/co-Poisson prime-power source; corpus dyadic valuation/parity channel
- **Statement:** Squarefree Route-P cell is exact valuation-parity Markov image of full geometric prime-valuation source, with strict data-processing equality precisely at saturation.

## Goal

Decide whether P-G51's alternating prime-power signs are artificially chosen or forced by a
source-defined reporter.  Required certificate must retain prime-power depth labels, identify
discarded information exactly, and characterize equality without inserting Xi-zero data.

## Gates

- [x] 0 → 1 in-progress: source parity reporter and exact dyadic descent identified
- [x] 1 → 2 fully-proven: termwise incidence, convergent currents, Hellinger factorization, strict equality case
- [ ] 2 → 3 formalized: umbrella build, lint, and axiom audit green
- [ ] 3 → 4 publication-ready: merge with critical-normal-cone theorem and external novelty audit

## Labelwise parity boundary `[PROVED HERE]`

Let `P_{p,n}(s)` be existing primitive Gamma/co-Poisson source at depth `p^{n+1}`.  Define actual
odd/even valuation boundary

\[
 (\partial_{\rm par}P)_{p,n}
 =P_{p,n}-2\,1_{2\mid n+1}P_{p,n}.
\tag{1}
\]

Since `P_{p,n}=-(n+1)^{-1}p^{-(n+1)s}`,

\[
 \boxed{
 (\partial_{\rm par}P)_{p,n}=(-1)^nP_{p,n}=A_{p,n}.
 }
\tag{P-G52a}
\]

Thus P-G51 alternating source is canonical parity incidence, not fitted sign data.

For real `σ>0`, full geometric current and parity current are

\[
 P_p(\sigma)=\log(1-p^{-\sigma}),\qquad
 S_p(\sigma)=-\log(1+p^{-\sigma}).
\]

Both arise as convergent labeled primitive series, and

\[
 \boxed{S_p(\sigma)=P_p(\sigma)-P_p(2\sigma).}
\tag{P-G52b}
\]

This is exact dyadic coboundary underlying Bose--Fermi/parity factorization.

## Hellinger data-processing factor `[PROVED HERE]`

For positive endpoint rates `σ,τ`, write

\[
 G_p^{\rm geo}(\sigma,\tau)=
 \frac{(1-p^{-\sigma})(1-p^{-\tau})}
 {(1-p^{-(\sigma+\tau)/2})^2},
\]

\[
 G_p^{\rm par}(\sigma,\tau)=
 \frac{(1+p^{-(\sigma+\tau)/2})^2}
 {(1+p^{-\sigma})(1+p^{-\tau})}.
\]

Direct dyadic factorization gives

\[
 \boxed{
 G_p^{\rm geo}(\sigma,\tau)
 =G_p^{\rm par}(\sigma,\tau)
  G_p^{\rm geo}(2\sigma,2\tau).
 }
\tag{P-G52c}
\]

The parity factor at `σ=1+xε`, `τ=1+zε` is exactly literal P-G45 squarefree Route-P prime cell.
If `σ≠τ`, doubled geometric factor lies strictly in `(0,1)`, so

\[
 G_p^{\rm geo}(\sigma,\tau)<G_p^{\rm par}(\sigma,\tau).
\]

Sharp equality law is

\[
 \boxed{G_p^{\rm geo}=G_p^{\rm par}\iff\sigma=\tau.}
\tag{P-G52d}
\]

At free-energy level, P-G51 log-Gram is exact cofiber of geometric second differences at rates
`σ` and `2σ`.

## Conjecture loop verdict

### Conjecture P-G52.A

P-G51 alternating current may be formal sign choice with no positive source reporter.

**Killed.** `(P-G52a)` is exact valuation-parity incidence, while `(P-G52c)` realizes its positive
Markov/Hellinger channel and prices all discarded information.

### Strongest positive survivor

Route-P squarefree cell is canonical parity quotient of full prime-valuation experiment.  Parity
data processing is strict at every finite nonneutral cell, and equality itself is saturation.
Corpus already proved local parity/residual probability, amplitude, Weyl, mean, and variance
factorizations in `EulerSquarefreeDyadicFockLocal.lean`; those are parent results, not novelty here.
New content is coefficient-exact identification with existing primitive Gamma/co-Poisson current,
its labeled convergent log current, and its literal Route-P log-Gram/equality weld.  Exceptional
Xi-reporter landing remains open.

### Surviving obstruction

Markov data processing or source provenance supplies inequality in correct direction but does not
force equality.  Globally, higher dyadic valuation factors can become asymptotically invisible in
critical normal cone, explaining why parity retains complete limiting geometry without annihilating
finite transverse rate.  Missing producer must force exact sufficiency, not merely asymptotic
sufficiency or another fidelity comparison.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellDyadicParityProvenance.lean
```

Key declarations:

- `squarefreeGammaCoPoissonPrimePowerTerm_eq_parityBoundary`;
- `hasSum_geometricGammaCoPoissonPrimePowerTerm`;
- `squarefreeGammaCoPoissonPrimeCurrent_eq_geometric_dyadicCoboundary`;
- `geometricPrimeValuationGramSq_eq_parity_mul_doubled`;
- `squarefreePrimeParityGramSq_eq_squarefreeMobiusPrimeCellGramSq`;
- `geometricPrimeValuationGramSq_mem_Ioo_zero_one`;
- `geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq`;
- `geometricPrimeValuationGramSq_eq_squarefreePrimeParityGramSq_iff`;
- `log_squarefreePrimeCell_eq_geometric_dyadicCofiber`.

## Next hard gate

Exploit exact-sufficiency characterization.  Test whether completed Gamma/co-Poisson reporter has a
source-defined reverse channel on actual Xi fibres.  A genuine reverse Markov recovery would force
equality in `(P-G52c)` and hence saturation.  Reject any reverse kernel whose existence is merely
equivalent to chosen endpoint equality or whose transition probabilities depend on zero locations.

## Log

- 2026-08-12 — proved canonical parity incidence, dyadic current coboundary, exact Hellinger
  factorization, strict data processing, and equality iff saturation.
