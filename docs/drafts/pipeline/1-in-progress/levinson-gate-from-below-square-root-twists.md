# Levinson's gate from the two-main-term twisted moment

- **ID:** A111
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Produce an unconditional positive critical-zero proportion through the
Levinson detector using mollifier length `T^θ`, `θ<1/2`.

## Proved analytic reduction

`exists_linearDetector_main_remainder_bound` in
`MultiscaleMollifiedZetaField/TheDetectorMomentErrorsAreSmall.lean` proves
that the actual tapered detector integral equals `detectorThreeMomentMain`
up to `C T^(7/8)`, uniformly for `q∈[T,2T]`,
`1/T≤d≤min(r,1/40)`, `1<N≤T^θ`, `0≤λ≤1`, and `λ log N≤1`.
One common taper has width `T^a`, `0<a<1`.

For `F=ζΨ`, `G=λζΨ′`, `H=F−G`, and `q_J(d)=∫W|J(1/2−d+it)|²`,
the exact identity is

`∫W|(ζ+λζ′)Ψ|² = q_H − (λ/2)(q_F′−q_G′+q_H′) + (λ²/4)q_F″`
`+ λ∫W′ Im(F conj G) + (λ²/4)∫W″|F|²`.

The moment jets differentiate displacement with all coefficients frozen.
Their errors have arbitrary power saving. Thin-strip Weyl bounds and
edge-supported taper derivatives give the stated `T^(7/8)` remainder.
The exact identity, derivative transfer, and remainder passed Lean checks.
See `3-formalized/linear-detector-three-moment-remainder.md`.

## Proved arithmetic reduction

The shifted gcd form has an exact Euler correction and harmonic Möbius
model. Absolute triple-fibre weights have a common summable majorant;
the correction has limiting unit mass. Every normalized correction jet
has a Cauchy majorant, and positive-order jets vanish along every bounded moving-centre sequence.
See `3-formalized/shifted-selberg-euler-factorization.md`.

For `P∈C²`, `P(0)=0`, the normalized power-shifted Möbius transform tends
to `P′(u)−vP(u)`, uniformly on `δ≤u≤1` and compact `v` intervals.
It is uniformly bounded on the full cutoff interval. This compact uniform
statement passed Lean in `TheShiftedMobiusProfilesConvergeUniformly`.
See `3-formalized/smoothed-mobius-tests-and-power-shifts.md`.

## Remaining arithmetic and gate

The required general profile limit, with `L=log N`, is

`L Σ μ(h)μ(k)(hk)^(v/L) gcd(h,k)^(1+c/L)/(hk)`
`  ·P(log(N/h)/L)P(log(N/k)/L)`
`→ ∫₀¹ exp((c+2v)t)[P′(1−t)−vP(1−t)]² dt`.

Only polynomial profiles of degree at most two and the first two
frozen-coefficient displacement jets are needed. At the detector point,
`(v,c)=(u,−2u)` or `(−u,2u)`, so both diagonal exponentials cancel.
Existing polynomial harmonic moments suffice. The linear-profile
constants are predicted to be `1−u+u²/3` and `1+u+u²/3`.

Harmonic endpoint control, profile-product replacement, and fixed-row
polynomial limits are formalized, including convergent moving shifts.
Remaining obligations: summation over all correction pairs; exact arithmetic jet
identities; analytic main-term asymptotics; insertion into
`RHTower.levinsonReciprocalLogMeanSquareGate_of_dyadicLaw` and the proved
count receiver. Details: `shifted-selberg-euler-correction.md`.
No detector gate from these inputs is yet claimed.

## Low-height split and scalar choice

The dyadic receiver uses one mollifier for every block down to height 20.
Take length exponent `θ=13/50` and split exponent `α=53/100`:
`θ/α=26/53<1/2`, while `θ+(11/8)α=791/800<1`.
A thin-strip Weyl bound for the detector then makes the initial segment
`O(U^(791/800))`; larger blocks admit the proved short twisted moment.
The detector Weyl bound and the resulting bound `C B² N A^(11/8)` for
coefficients satisfying `|b_n|≤B n^(σ−1/2)` have Lean proof drafts.
Their checks and the block assembly remain required.

For `R=13/10`, exact integration of Young's linear scalar predicts
`c(13/50)<18/5<exp(13/10)`, hence a positive proportion.
`TheShortLevinsonMollifierHasAPositiveScalarMargin` contains the full proof
draft using rational bounds on `exp(13/20)`; Lean check pending.

The receiver fixes coefficients before choosing its nearby abscissa.
Using coefficients at `d_U=R/log U` instead of `d=R/log T₂` changes each
coefficient by relative size `O((d−d_U)log N)=O(1/(U log U))`.
Its detector-energy effect must be bounded explicitly; the matched-shift
remainder theorem alone does not discharge this obligation.
