# EDQ harmonic cutoff selection and the complete tail

Status: completed finite diagnostic; no numerical result enters Lean.
The fixed prediction reverses in two of four bands. The gcd-selected cutoff
has a strictly larger later tail in three bands, including one where its
complete energy is smaller. No asymptotic inequality or RH conclusion is
established or refuted by these finite comparisons.

## Frozen question

The [all-gcd head theorem](../../3-formalized/edq-gcd-head-subpower.md) controls
the total corrected-head remainder by every positive cutoff power. Its
retained polynomial is

`P(N)=A_N*sum_r |K_r(N)|`, where `A_N=sum_(k<=N)k/(k+1)` and
`K_r(N)=sum_(d,e<=N,gcd(d,e)=r)mu(d)mu(e)/(d*e)`.

In each of four fixed bands, S selects the least numerical minimizer of
`N*H(N)^2`, with `H(N)=sum_(d<=N)mu(d)/d`. Independently, G selects the least
numerical minimizer of P(N). The parameter-free prediction was that G has
no greater complete raw residue energy than S in every band. The entire
scan through 1023 is archived, not only its selected cutoffs.

The actual source and energy are

```
F_N(k) = sum_(d<=N) mu(d)*(k mod d)/d,
E(N)   = sum_(k>=1) F_N(k)^2/[k(k+1)].
```

This is the full source used in the preceding Gram work. It includes the
initial range and every later coordinate. The protocol, bands, selectors,
0.005 analytic tail allowance and 120-second execution limit were frozen
before the RunPod computation. No bands, thresholds or precision were
changed after seeing results.

## All four comparisons

| Band | S cutoff | G cutoff | S full energy interval | G full energy interval | Prediction |
|:---|---:|---:|:---|:---|:---|
| [64,127] | 77 | 78 | [1.035755973,1.040755925] | [1.159816287,1.164816239] | Reversed |
| [128,255] | 154 | 190 | [1.038664519,1.043664498] | [1.169433093,1.174433081] | Reversed |
| [256,511] | 390 | 266 | [1.038271156,1.043271152] | [1.030281832,1.035281826] | Supported finitely |
| [512,1023] | 859 | 571 | [1.036372321,1.041372320] | [0.981034346,0.986034345] | Supported finitely |

The intervals include the analytic omitted infinite tail. A separate 1e-7
floating-point sensitivity margin was used for classification; all four
full-energy comparisons remain separated with that margin. This is not
certified interval arithmetic or a formal Lean counterexample.

The corresponding G-minus-S differences locate the improvement or loss:

| Band | Head energy difference | Later-tail difference interval |
|:---|---:|:---|
| [64,127] | +0.113277133 | [+0.005783229,+0.015783133] |
| [128,255] | +0.121375849 | [+0.004392745,+0.014392714] |
| [256,511] | -0.006198206 | [-0.006791114,+0.003208876] |
| [512,1023] | -0.062873033 | [+0.002535059,+0.012535057] |

In the final band, G lowers the head enough to lower total energy despite
its larger complete tail. The third band's tail ordering is unresolved;
no finer computation was run.

## Exact identities and proof boundary

The literal initial source is `F_N(k)=k*H(N)-1` for 1<=k<=N. Consequently
its squared head energy is exactly

`H(N)^2*A_N - 2*H(N)*sum_(k<=N)1/(k+1) + 1 - 1/(N+1)`.

The linear unit-source cross term matters for finite rankings. The G
cutoffs in the two reversed bands have negative H; the positive H at
N=571 lowers its head relative to N=859. This explains the recorded head
differences through an exact identity. It does not predict the full tail's
sign or ordering.

Only the strict finite selector-dominance prediction fails here. In
particular, this test does **not** refute a full-energy upper bound in terms
of P(N), with a constant or a subpower allowance: such a bound would not
imply that minimizing P minimizes the actual energy. The already formalized
positive survivor is the all-gcd subpower remainder and its variation
comparison. Both remain intact. No RH route is retired.

The direct bound attempt also retains its gap. If
`J_q=sum_(q|d,d<=N)mu(d)/d`, then `K_r=sum_l mu(l)*J_(rl)^2`, and hence
`sum_r |K_r|<=sum_q tau(q)*J_q^2`. The available inverse-log envelopes for
H(N), including `Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow`,
leave a cutoff divided by a logarithmic power after squaring and multiplying
by A_N. Completing the coprime columns does not provide the missing power
saving. An actual estimate for the retained coefficients and complete tail
is still required.

## Method and verification

The finite K scan uses the exact coefficient-update identity

`K_r(N)-K_r(N-1)=2*(mu(N)/N)*sum_(d<N,gcd(d,N)=r)mu(d)/d
                 + [r=N]*mu(N)^2/N^2`.

Selected cutoffs were independently checked using the full divisor inversion
from the squares J_q^2. The smallest runner-up gaps were 2.02886e-8 for S
and 0.00253211 for G; the archived scan is numerical, not an exact rational
optimization certificate.

For the complete energy, integer divisor increments and their cumulative
sums are formed exactly in signed 64-bit arrays. Their range is checked
against overflow. Only the final harmonic subtraction and weighted energy
use long-double arithmetic. The infinite-tail bound uses the literal
centered-residue inequality

```
|F_N(k)| <= B_N,
B_N = (1/2)*sum_(d<=N)|mu(d)|*(1-1/d)
      + |(1/2)*sum_(d<=N)mu(d)*(1-1/d)|,
sum_(k>T) F_N(k)^2/[k(k+1)] <= B_N^2/(T+1).
```

Centering is only an algebraic bound here; no uniform-period average replaces
the actual energy. Each T is chosen before summation to make its analytic
allowance at most 0.005.

Validation discrepancies:

- Full scan reconstruction `sum_r K_r=H^2`: at most 4.38e-20.
- Direct residue evaluation versus accumulated source: at most 1.36e-12.
- Exact closed-head formula versus weighted source: at most 2.17e-19.
- Independent selected-cutoff harmonic variation agreed within 1e-12.

Eight independent energy jobs ran on RunPod, with one thread per native
pool, Python 3.8.10, NumPy 1.24.4, and 63-bit long-double mantissa. Total
experiment wall time was 0.77751 seconds. Largest finite prefix was
13,460,275; all eight prefixes together contained 24,896,646 coordinates.
Analysis also ran on RunPod. Source, frozen protocol, full results, scan,
logs, analysis and hashes are archived here. No Lean file or build was added
for this diagnostic. The frontier map was not edited.
