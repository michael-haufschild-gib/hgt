# Integer-start Möbius windows from the actual spectral head

- **ID:** twin-prime-integer-start-moebius-window
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE; classical deduction
- **Lean:** `formal/GaloisForLFunctions/twin-prime/IntegerStartMoebiusWindow.lean`
- **Source:** `RHTower/Sieve/MoebiusAveragedMeanSquareAllLengths.lean`,
  `DyadicMeanSquareTail.lean`, and the twin-prime coupled-centering input audit.
- **Statement:** Uniformly for integer lengths `log N <= l <= N`, the mean square
  of the actual Möbius sums over `(t,t+l]`, `N <= t < 2N`, is `o(N l^2)`.

## Exact claim

There is a real sequence `B(N) -> 0` such that, for every sufficiently large
integer `N` and every integer `l` with `log N <= l <= N`,

`sum_(N<=t<2N) |sum_(t<n<=t+l) mu(n)|^2 <= B(N) N l^2`.

No cancellation estimate is a premise of the Lean theorem. The
length restrictions specify its geometric range. The spectral input below
comes from an existing proved source, with its arithmetic inputs discharged.

## Corpus and parent-theory audit

The older formalized short-interval card correctly distinguishes reciprocal
fibres from integer starts. A later corpus development proves more than that
card uses: `eventually_integral_head_le_budget` controls the plain Möbius
polynomial at height `M/sqrt(h)`, for every growing `h <= sqrt(x)`.
Its displayed analytic arguments are supplied by
`exists_top_high_bound` and
`exists_setIntegral_disc_normSq_logPoly_moebius_le_rate`, exactly as in
`averagedMeanSquare_moebius_of_tendsto`. The actual majorant tends to zero by
`tendsto_headBudget`. Merely citing the reciprocal-fibre conclusion would
not justify the present claim; the proof uses this stronger spectral input.

Corpus lexical search for `dyadicMeanSquare` found finite Gallagher and
mean-square transfer bounds, but no unconditional Möbius limit for this
integer-start object. Source statements and proofs were inspected.

**Verdict: BRIDGE / classical deduction.** This is a transfer of the existing
Möbius short-interval mechanism, not new scientific knowledge. The general
short-interval theorem is already in the checked
[Matomäki–Radziwiłł–Tao source](https://arxiv.org/pdf/1503.05121v3).
No claim of novelty attaches to the certificate.

## Dependency-closed paper proof

Put `h=log N`, `M=floor(4N+h)`, and

`I_N = integral_(|w| <= M/sqrt(h))
 |sum_(1<=n<=M) mu(n) exp(2 pi i w log n)|^2 dw`.

Apply the existing spectral-head construction with
`x=(4N)^2` and `hh(x)=log(sqrt(x)/4)`. This function tends to infinity
and is eventually at most `sqrt(x)`. The two proved arithmetic inputs
listed above discharge the head theorem. Its majorant tends to zero,
so `I_N/M^2 -> 0`. All changes of cutoff are exact: `sqrt(x)=4N`
and `hh(x)=h` for positive `N`.

For sufficiently large `N`, `h>=1` and `4N<=M<=5N`. Fix
`h<=l<=N`. The polynomial includes every summand of every required
window. Take the Gallagher cut `G=M/(3l)` and height
`T0=M/sqrt(h)`. Then `G>=1` and `G<=T0`.
The proved affine-from-head inequality bounds every larger spectral
window by `alpha T+I_N`, where

`alpha=(5 pi/2)M+(5e/2)M^2/T0`.

For every real `Y>=N`, its logarithmic window width
`delta=log(1+l/Y)` satisfies `0<delta<=l/N<=6l/M`.
The proved Gallagher dyadic-tail bound and `headBudget_le`, applied
with length `3l` and height multiplier `3l/sqrt(h)`, therefore give

`integral_E |logWindowSum_mu(delta,u)|^2 du <= l^2 E_N`

for every measurable or arbitrary set `E`, where

`E_N=270/h+180/sqrt(h)+81 I_N/M^2`.

Indeed the normalized head budget is bounded by
`270/l+180 sqrt(h)/l+81 I_N/M^2`, and `l>=h` gives the displayed
majorant. Thus `E_N>0` eventually and `E_N->0`.

Set `epsilon=sqrt(E_N)` and `K=ceil(1/epsilon)`. Eventually
`0<epsilon<=1`, `K epsilon>=1`, and `K<=2/epsilon`.
Bernoulli's inequality gives `(1+epsilon)^K>=2`; the logarithmic
bound gives `(1+epsilon)^K<=exp(K epsilon)<=exp(2)<9`.
These blocks cover exactly the required range of starting points.
Apply the proved `dyadicMeanSquare_le_gen` with the actual
Gallagher bound `l^2 E_N`. Its conclusion, divided by `N l^2`, is
at most

`36 E_N/epsilon + 36 (epsilon+1/l)^2`.

Here `log(1+epsilon)<=epsilon` pays the discretization error.
Since `1/l<=1/h<=E_N` and eventually `E_N<=sqrt(E_N)`, this is at most

`36 sqrt(E_N)+144 E_N`.

That expression tends to zero and is independent of `l`, proving
the exact claim, including all integer endpoints. The finite receiver
is `dyadicMeanSquare mu l N (2N-1)`.

## Scope

This closes an unmodulated integer-start receiver transfer. It does not give the additive-frequency supremum
needed by the rough-shift centering argument. Nor does this qualitative
rate give that argument's prescribed power saving in `L`. Its length
range `l>=log N` also does not cover `D<log Y`, which is allowed when
the centering statement puts only a lower bound on `Y`. These are three
separate obligations; closing the unmodulated transfer does not close
any of them. It also does not bound a
fixed-shift Möbius correlation, uniform affine correlations, or prime-pair
mass. Those remain open. The new Ramaré cofactor theorem is not required
for this particular transfer; the later multirange spectral head already
handles the plain polynomial.

## Lean certificate

The foreground leaf command passed:

`lake --old env lean GaloisForLFunctions/twin-prime/IntegerStartMoebiusWindow.lean`

All four capstones passed transitive `#print axioms` audits with exactly
`[propext, Classical.choice, Quot.sound]`:

- `TwinPrime.tendsto_integerWindowHead_div`;
- `TwinPrime.tendsto_integerWindowError`;
- `TwinPrime.tendsto_integerWindowRate`;
- `TwinPrime.eventually_dyadicMeanSquare_moebius_le_integerWindowRate`.

No analytic premise or limit increase was introduced. The final theorem
has no assumption binders; its eventual conclusion specifies the length
range. The leaf is imported by `twin-prime/Main.lean`; the umbrella was
not compiled. Temporary axiom-print commands were removed after the
successful audit without changing proofs.

Lexical corpus search returns the principal capstone. Seven owned
source/card files passed whitespace, relative-link and applicable
forbidden-directive checks. All sixteen owned search/PDF/code scratch
files were removed; all owned compile and search processes terminated.

## Gates

- [x] Exact object, normalization, uniformity and endpoint proof.
- [x] Corpus and parent-theory audit; no novelty claim.
- [x] Dependency-closed paper deduction from proved inputs.
- [x] Unconditional Lean certificate and transitive axiom audit.

## Log

- 2026-10-23 — Located the later all-length spectral head while testing
  the fixed-determinant route; completed the integer-start transfer proof.
  Twin-prime infinitude remains unproved.
- 2026-10-23 — Full leaf and all four capstone axiom audits passed.
  This advances the formalized receiver interface, not the scientific
  frontier or the proof of twin-prime infinitude. The next analytic
  work must retain the actual two-row arithmetic and its normalization.
