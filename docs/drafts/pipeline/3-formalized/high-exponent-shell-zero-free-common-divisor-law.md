# High-exponent shells have a zero-free multiplier and the full Xi divisor

- **ID:** `high-exponent-shell-zero-free-common-divisor-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[RH SOURCE THEOREM]`
- **Scientific status:** `[PROVED] [PROOF VALUE ONLY] [NOVELTY NOT EVALUATED BY REQUEST]`
- **Parents:**
  - `not_new_scientific_knowledge/mfree-moebius-ladder-carrier-bridge.md`
  - `../2-fully-proven/mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `../2-fully-proven/squarefree-fixed-current-right-half-ward-localization.md`
  - `new_scientific_knowledge/scalar-ht-persistent-clock-character-law.md`
  - `new_scientific_knowledge/charged-scalar-core-fixed-current-torsor.md`

## Statement

For `m>=1`, let

```text
a_m(n)=1_((m+1)-free)(n)-1_(m-free)(n).                 (1)
```

Thus `a_m(n)=1` exactly when the largest exponent in the prime factorization of `n` is `m`.
The supports of `a_m` and `a_k` are disjoint when `m!=k`.  On `Re s>1`, its Dirichlet series is

```text
S_m(s)=sum_(n>=1)a_m(n)n^(-s)
      =zeta(s)H_m(s),
H_m(s)=1/zeta((m+1)s)-1/zeta(ms).                       (2)
```

For every integer `m>=12`, `H_m` is holomorphic and zero-free on

```text
Re s>1/2.                                                (3)
```

Consequently, if

```text
c_infinity(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2,
X_m(s)=c_infinity(s)S_m(s)=Xi(s)H_m(s),                 (4)
```

then `X_m` and `Xi` have exactly the same strict right-half divisor, with the same
multiplicities.  Equivalently,

```text
-2X_m'(s)/X_m(s)
 =-2Xi'(s)/Xi(s)-2H_m'(s)/H_m(s),                       (5)
```

and the second term in `(5)` is holomorphic on `Re s>1/2`.  Every high-exponent shell therefore
has the same strict anti-causal Hardy profile `ell_E` as the completed zeta source.

Each shell is also a positive four-unit source.  For `sigma=1+epsilon`, define

```text
P_(m,sigma)(n)=a_m(n)n^(-sigma)/S_m(sigma),
H=log n,
kappa_(m,sigma,t)=[Pi_(m,sigma),2Q_t-I].                (6)
```

Then, for every fixed `m>=12`,

```text
epsilon log n  ->  Exp(1)             in W_1,
epsilon E|H-H'| -> 1,
epsilon integral_0^infinity
  ||kappa_(m,sigma,t)||_HS^2 dt ->4.                    (7)
```

The arithmetic supports in `(6)` are pairwise disjoint across `m`, so the corresponding
incidence kernels occupy mutually orthogonal Hilbert--Schmidt blocks before any fixed-current
quotient is taken.

## Zero-free proof

The denominators in `H_m` are nonzero on `Re s>1/2`, since `Re(ms)>1` for `m>=12`.  It is therefore
enough to prove that

```text
D_m(s)=zeta(ms)-zeta((m+1)s)                             (8)
```

does not vanish there.  Write `sigma=Re s>1/2` and split off the `n=2` term:

```text
D_m(s)
 =2^(-ms)(1-2^(-s))
  +sum_(n>=3)n^(-ms)(1-n^(-s)).                         (9)
```

The leading term satisfies

```text
|2^(-ms)(1-2^(-s))|
 >=2^(-m sigma)(1-2^(-sigma)).                          (10)
```

After division by `2^(-m sigma)`, the tail is at most

```text
sum_(n>=3)(2/n)^(m sigma)(1+n^(-sigma))
 <=64 sum_(n>=3)(n^(-6)+n^(-13/2)).                     (11)
```

Here `m sigma>6`.  Since

```text
sum_(n>=3)n^(-6)
 <=3^(-6)+integral_3^infinity x^(-6)dx
 =8/3645
```

and `n^(-13/2)<=3^(-1/2)n^(-6)`, the right side of `(11)` is strictly less than

```text
64(1+1/sqrt(3))8/3645
 <4096/18225
 <1/4
 <1-1/sqrt(2)
 <1-2^(-sigma).                                         (12)
```

The tail in `(9)` is therefore strictly smaller than the leading term.  This proves `(3)` by
Rouche's elementary one-term domination, pointwise throughout the half-plane.

## Critical four-unit proof

The real number

```text
H_m(1)=1/zeta(m+1)-1/zeta(m)                             (13)
```

is positive.  Hence `(2)` has a simple pole at `s=1` with positive residue `H_m(1)`.  Uniformly
for `u` in compact subsets of `Re u>-1`,

```text
S_m(1+epsilon(1+u))/S_m(1+epsilon) ->1/(1+u).           (14)
```

This is the Laplace transform of `Exp(1)`.  Differentiating the Laurent expansion at the real
axis gives convergence of the first scaled moment to `1`; Laplace convergence plus first-moment
convergence gives `W_1` convergence.  Applying it to two independent copies yields the middle
limit in `(7)`.  The projection-commutator identity

```text
||[Pi,2Q_t-I]||_HS^2
 =8 P(H<=t)P(H>t)                                       (15)
```

and `integral P(H<=t)P(H>t)dt=E|H-H'|/2` give the last limit.

## Prime-two asymptotic and HT meaning

The same domination is uniform on every closed half-plane `Re s>=1/2+delta`.  As `m->infinity`,

```text
H_m(s)
 =2^(-ms)(1-2^(-s))(1+o_delta(1)).                      (16)
```

Thus a high shell is source-locally a large clock translation of the odd-integer zeta source,
while its completed logarithmic current retains the entire Xi divisor.  The affine translation
`2^(-ms)` becomes only the boundary constant `m log 2` after taking a logarithmic derivative and
does not alter the strict anti-causal profile.

This is a concrete fixed-current phenomenon: infinitely many disjoint positive clock sectors can
have asymptotically one-prime local geometry while carrying one common global HT divisor current.
Meromorphic continuation is therefore discontinuous in the coefficient/clock topology that makes
the shell sectors orthogonal.

## Attack on the anti-causal Ward estimate

The theorem supplies infinitely many orthogonal four-unit inputs with the same desired output
`ell_E`.  This gives a sharp anti-theatre test for a proposed Ward codifferential.

If one bounded linear row operator on the orthogonal shell sum sent every limiting shell curvature
to the same vector `ell_E`, then for `N` shells its value on their normalized sum would grow like
`sqrt(N) ell_E`; boundedness would force `ell_E=0`, hence RH.  However the identical argument
already applies to the nonzero incoming pole vector `2e^(-t/2)`.  Therefore a row operator that
collapses every shell clock to the common pole cannot be bounded unconditionally.

**Strengthened no-go.**  Artificially adjoining the shell label and then taking a scalar
codiagonal is not an RH proof.  The weighted-codiagonal dichotomy in
`not_new_scientific_knowledge/high-shell-codiagonal-closability-dichotomy.md` proves more than
unboundedness: a scalar shell row is closable exactly when its weights are square-summable, in
which case it is already bounded.  The unit-weight row which erases the common fixed-current label
is therefore nonclosable.  It cannot be repaired by declaring an unspecified closed domain.

**Positive successor.**  A viable anti-causal Ward construction must keep the arithmetic shell
label through the pole cancellation and take the fixed-current quotient only on an
operator-valued multiplication graph.  A scalar unbounded row is excluded even as a closable
operator.  Equation `(3)` guarantees that no shell-specific right-half divisor is introduced for
`m>=12`; equation `(16)` gives a prime-two-dominated cofinal family on which a uniform graph
estimate can be attacked.  Failure of such uniformity is now localized to the fixed-current
quotient, not to Gamma completion, source energy, shell orthogonality, or an auxiliary divisor.

## Proof verdict

The theorem produces an infinite, pairwise-disjoint positive test family whose completed currents
have no auxiliary strict right-half divisor.  It does not prove RH: the tempting bounded
codiagonal is already impossible for the known nonzero incoming Euler-pole vector.  The surviving
use is the prime-two-dominated cofinal test family for the single closed fixed-current graph.

## Lean certificate

All five card claims that carry a proof — `(1)`–`(5)`, `(7)`, `(13)`, `(16)` — are formalized
unconditionally.  Every listed theorem builds with no warnings and `#print axioms` returns exactly
`propext, Classical.choice, Quot.sound`.

Modules (all imported by their theorem-area umbrella):

- `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellCriticalClock.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellSourcePole.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellClockMoments.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellClockMeasure.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellGiniEnergy.lean`
- `formal/GaloisForLFunctions/HTGeometry/ExponentialClockTotalEnergy.lean`

| Card item | Lean name |
|---|---|
| `(1)` shell indicator, largest exponent `= m` | `RHTower.shellIndicator`, `RHTower.shellIndicator_eq_one_iff` |
| disjoint supports | `RHTower.shellIndicator_eq_zero_of_ne` |
| smallest member of the shell | `RHTower.shellIndicator_two_pow` |
| `(2)` `S_m(s) = zeta(s)H_m(s)` | `RHTower.LSeries_shellIndicator` |
| `(3)` zero-free multiplier on `re s > 1/2`, `m >= 12` | `RHTower.riemannZeta_natCast_mul_sub_succ_mul_ne_zero`, `RHTower.shellMultiplier_ne_zero` |
| `(16)` prime-two domination | `RHTower.norm_riemannZeta_diff_sub_shellHead_le`, `RHTower.le_norm_shellHead` |
| `(4)` common strict right-half divisor with `Xi` | `RHTower.analyticOrderAt_mul_shellMultiplier`, `RHTower.analyticOrderAt_riemannZeta_mul_shellMultiplier`, `RHTower.analyticOrderAt_completedRiemannZeta_mul_shellMultiplier`, `RHTower.riemannZeta_mul_shellMultiplier_eq_zero_iff` |
| `(5)` log-derivative split | `RHTower.logDeriv_riemannZeta_mul_shellMultiplier` |
| `(13)` `H_m(1) > 0` | `RHTower.shellMultiplier_one_eq_ofReal_pos`, `RHTower.shellResidue_pos` |
| arithmetic source, nonnegative, positive | `RHTower.shellMellin_eq_tsum`, `RHTower.shellMellin_nonneg`, `RHTower.shellMellin_pos` |
| simple pole at `sigma = 1`; pole factorisation | `RHTower.tendsto_shellMellin_residue`, `RHTower.shellSource_eq_of_ne_one` |
| `(14)` `Exp(1)` clock, Laplace form | `RHTower.tendsto_shellCriticalClockLaplace` |
| `(14)` `Exp(1)` clock, weak-convergence form | `RHTower.charFun_shellClockProbabilityMeasure`, `RHTower.tendsto_charFun_shellClockProbabilityMeasure`, `RHTower.tendsto_shellClockProbabilityMeasure` |
| shell clock moments | `RHTower.ofReal_shellLogMoment`, `RHTower.tendsto_shellLogMoment_one`, `RHTower.tendsto_shellLogMoment_two` |
| `(7)` `epsilon E|H - H'| -> 1` | `RHTower.tendsto_shellGapProbabilityMeasure`, `RHTower.tendsto_integral_abs_shellGapProbabilityMeasure` |
| `(7)` four-unit incidence energy | `RHTower.tendsto_shellRelativeClockEnergy` |
| `(7)` four-unit projective-Fisher energy | `RHTower.tendsto_shellClockVariance`, `RHTower.tendsto_shellProjectiveFisherEnergy` |
| `Exp(1)` totals (class invariants) | `GaloisForLFunctions.HTGeometry.tendsto_exponentialCutMass_atTop`, `..._exponentialCutOverlap_atTop`, `..._exponentialCutEnergy_atTop` |

The prime-two domination is quantitative and sharper than the card's prose: for `m >= 12` and
`re s > 1/2`,

```text
| (zeta(ms) - zeta((m+1)s)) - (2^(-ms) - 2^(-(m+1)s)) |
   <= 2^(-m re s) (512/5)(3^(-6) + 4^(-6) + 1/2500)  <  2^(-m re s) (21/100),
| 2^(-ms) - 2^(-(m+1)s) |
   >= 2^(-m re s) (29/100).
```

so the `n = 2` term strictly dominates the entire tail, pointwise on the half-plane.

## Reuse audit

Built on existing tree infrastructure, no duplication:

- `RHTower.MFreeLadder`: `MFree`, `mFreeIndicator`, `LSeries_mFree_eq_riemannZeta_div` — the whole
  `(2)` factorisation;
- `RHTower.ZetaLogDerivResidue`: `zetaResidueUnit`, `analyticAt_zetaResidueUnit` — the analytic
  unit at the zeta pole, reused verbatim for `U_m = G·H_m`;
- `RHTower.GammaInvGrowth`: `HilbertSchmidt.tsum_reciprocal_square_tail_le` — the reciprocal-square
  tail used in the sixth-power tail bound;
- `HTGeometry.CriticalClockSourceUniversality`: `criticalClockLaplace`,
  `tendsto_criticalClockLaplace_of_simplePole`, `exponentialCutMass/Overlap/Energy`;
- `RHTower.MobiusCriticalClockWeakConvergence`: `squarefreeMobiusCriticalClockParameter`,
  `mobiusCriticalExponentialProbabilityMeasure`,
  `charFun_mobiusCriticalExponentialProbabilityMeasure`,
  `mobiusCriticalExponentialGapProbabilityMeasure` — the universal limit laws;
- `RHTower.MobiusIncidenceClockGiniFisherFourUnit`:
  `tendsto_integral_abs_of_weak_of_uniform_sq` and the three Laplace-gap moment facts.  These four
  were `private`; they are general (the first uses nothing about the measures beyond a uniform
  square bound) and are now public, which is the only edit made to that module;
- `RHTower.EulerFisherCurvature`: `summable_abs_log_natCast_pow_mul_rpow_neg`;
- mathlib: `zeta_eq_tsum_one_div_nat_cpow`, `summable_one_div_nat_cpow`,
  `riemannZeta_ne_zero_of_one_lt_re`, `analyticOn_riemannZeta`, `analyticOrderAt_mul`,
  `LSeries_iteratedDeriv`, `ProbabilityMeasure.tendsto_of_tendsto_charFun`,
  `Summable.tsum_lt_tsum`.

## Gates

- [x] exact shell indicator and Dirichlet series
- [x] disjoint arithmetic supports
- [x] zero-free multiplier on `Re s>1/2` for every `m>=12`
- [x] exact common strict right-half divisor with `Xi`
- [x] critical `Exp(1)` clock and four-unit incidence energy
- [x] prime-two asymptotic on closed strict half-planes
- [x] bounded-codiagonal shortcut rejected using the incoming pole
- [x] scalar codiagonal strengthened from unbounded to nonclosable
- [x] proof contribution evaluated without a novelty gate
- [x] every proven card claim formalized in Lean, unconditional, axiom-clean
- [ ] construct a shell-label-preserving closed Ward graph
- [ ] prove a uniform relative estimate through pole cancellation
- [ ] RH

## Log

- 2026-07-26 — formalized: zero-free law, prime-two domination, divisor identities, positive
  residue, `Exp(1)` critical clock in both Laplace and weak-convergence form, clock moments,
  four-unit incidence and projective-Fisher energies.  Card moved to `3-formalized`.
