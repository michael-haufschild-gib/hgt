# Hedenmalm--theta Möbius prime-cell squarefree current

- **ID:** P-G51
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN SOURCE-CLEAN
- **Source:** P-G48 grade-one co-Poisson complement; P-G50 source-realized Gamma window; full existing primitive prime-power current
- **Statement:** Alternating all prime-power Gamma/co-Poisson source sums to squarefree local current, whose exact second difference is literal Route-P prime-cell log-Gram.

## Goal

Determine whether omitted prime-power grades convert P-G49's conservative three-channel law into
a coercive saturation identity.  Preserve every prime-power label through convergence and use only
the existing primitive Gamma/co-Poisson source.

## Gates

- [x] 0 → 1 in-progress: source-pure alternating prime-power reporter and exact target identified
- [x] 1 → 2 fully-proven: complete labeled convergence proof and exact log-Gram identity
- [ ] 2 → 3 formalized: umbrella build, lint, and axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Full alternating current `[PROVED HERE]`

For prime `p`, grade `n≥0`, and real `σ>0`, take the existing primitive source at `p^{n+1}`:

\[
 A_{p,n}(\sigma)
 :=(-1)^n\,
   \operatorname{CoPoisPrim}(p^{n+1},\sigma)
 =\frac{(-1)^{n+1}}{n+1}p^{-(n+1)\sigma}.
\tag{1}
\]

Then the label-preserving series converges absolutely and

\[
 \boxed{
 \sum_{n\ge0}A_{p,n}(\sigma)
   =-\log(1+p^{-\sigma})=:S_p(\sigma).
 }
\tag{P-G51a}
\]

This is exactly negative logarithm of squarefree local Euler factor.  It is not a fitted
counterterm.

For source endpoint rates

\[
 \sigma_x=1+x\varepsilon,\qquad
 \sigma_z=1+z\varepsilon,\qquad
 \sigma_y=1+\frac{x+z}{2}\varepsilon,
\]

literal prime cell is

\[
 G_p=\frac{(1+p^{-\sigma_y})^2}
 {(1+p^{-\sigma_x})(1+p^{-\sigma_z})}.
\]

Consequently

\[
 \boxed{
 \log G_p=S_p(\sigma_x)+S_p(\sigma_z)-2S_p(\sigma_y).
 }
\tag{P-G51b}
\]

When all three rates are positive, `(P-G51b)` is itself sum of labeled second-difference terms

\[
 \sum_{n\ge0}
 \bigl(A_{p,n}(\sigma_x)+A_{p,n}(\sigma_z)-2A_{p,n}(\sigma_y)\bigr)
 =\log G_p.
\tag{2}
\]

No interchange over primes, unlabelled analytic continuation, or zero-dependent parameter enters.

## Conjecture loop verdict

### Conjecture P-G51.A

Higher prime-power grades supply missing positive or negative remainder that makes P-G49 budget
coercive.

**Killed.** Full alternating source absorbs remainder exactly into `(P-G51b)`.  There is no local
residual after all grades are restored.

### Strongest positive survivor

Route-P Euler defect is exactly conservative free-energy curvature of independently existing
Gamma/co-Poisson primitive.  P-G48's positive grade-one complement was truncation remainder, not
new saturation energy.  This identifies higher universal principle behind P-G41--P-G50:
Hellinger/Julia/Gamma identities are different scalarizations of one squarefree logarithmic
second-difference current.

### New obstruction

Full source law measures strict log-convexity but cannot force equality: for every nontrivial cell,
`log G_p<0`.  Remaining producer must be nonlocal across primes, introduce a signed polarization,
or impose a global annihilation law.  Any further local positive completion is now ruled out as a
route to saturation.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellSquarefreeCurrent.lean
```

Key declarations:

- `squarefreeGammaCoPoissonPrimePowerTerm_eq`;
- `one_LSeries_term_prime_pow_real`;
- `hasSum_squarefreeGammaCoPoissonPrimePowerTerm_real`;
- `hasSum_squarefreeGammaCoPoissonPrimePowerTerm`;
- `log_bernoulliMidpointGramSq_eq_squarefreeCurrentSecondDifference`;
- `log_squarefreeMobiusPrimeCellGramSq_eq_squarefreeGammaCoPoissonSecondDifference`;
- `hasSum_squarefreeGammaCoPoissonPrimePowerSecondDifferenceTerm`.

## Next hard gate

Test whether exact local currents admit a nonlocal prime-pair polarization whose off-diagonal
energy has forced sign and diagonal equals `-log G_p`.  Kill immediately if tensor/product
factorization reduces it to another tautological sum of local convexities.

## Log

- 2026-08-12 — proved full alternating prime-power sum and exact label-preserving local log-Gram
  second-difference law; higher-depth coercive-remainder conjecture killed.
