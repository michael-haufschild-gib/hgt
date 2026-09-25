# Damped exact flux: full Fourier compatibility

Status at registration: unrun. Numerical guidance only; no output is a Lean premise.

## Question and relation to the proof

The RH target remains the sign of every center-mixed polynomial form. Can an exponentially
damped, exactly zero-integral center correction produce nonnegative Fourier kernels at every
center? This tests a sufficient certificate for the whole hierarchy, rather than another finite
Hankel rank. The earlier single-flux transition protocol remains paused and unrun.

Write `P_x(t)=Φ(x+t)Φ(x-t)`, `p_x=P_x/Φ(x)^2`, and `ℓ=log Φ` for the literal complete
theta source. For aperture `a`, the existing Lean flux is `F_a(r)=r² sinh(ar) Φ(r/2)²`.
Use the full derivative of `exp(-λr)F_a(r) C(t)`, where `C(0)=0`; omitting the damping
derivative would lose the exact zero integral. The normalized corrected kernel is

```
p_x(t) + h_(a,λ)(x) C(t),
h_(a,λ)(x) = exp(-2λx)[2+2ax coth(2ax)+2xℓ'(x)-2λx],
h_(a,λ)(0) = 3.
```

If `W(x,b)=∫ p_x(t) cos(2bt)dt`, a real correction transform `c(b)` requires
`W(x,b)+h(x)c(b)≥0` at every center. Thus, at each frequency,

```
sup_(h>0)(-W/h) ≤ inf_(h<0)(-W/h).                           (1)
```

For a positive-coefficient center `x+` and negative-coefficient center `x-`, the equivalent
division-free test is `M=(h+ W- - h- W+)/(h+ - h-)≥0`. The sign and location of a
robust violation for the actual complete source are not supplied by the existing corpus.
Passing sampled tests does not construct a correction: all centers, all frequencies, regularity,
and `C(0)=0` still need proof. The aperture is fixed in this diagnostic, not in the RH target.

Tail reasoning already rejects slow damping as a useful scalar repair: fixed-frequency
`W(x,b)` is of order `exp(-x)` whereas `h(x)` is of order
`-x exp(-2(λ-1)x)`. For `1<λ≤3/2`, (1) forces `c(b)≤0` at every frequency; an
integrable correction transform with zero total mass is then zero. This is a paper observation,
not a new Lean theorem or a numerical input. Test only faster damping.

## Frozen design

- Aperture `a=1/4`; damping `λ∈{7/4,2,3,5}`.
- Centers `x=j/80`, `0≤j≤160`; frequencies `b=k/4`, `0≤k≤192`.
- Evaluate the literal source with its positive-half-line atom formula and even reflection.
  Use stable logarithms, not cancellation-prone source values in the tails.
- Two independent quadrature/truncation settings: Gauss–Legendre on `[0,4]`,
  512 nodes/7 atoms and 1024 nodes/14 atoms. The transform is twice the cosine integral.
- Exclude centers with `|h|<10^-10` from the division-based search. For each damping, select
  the most negative division-free margin among pairs chosen by the sharp sampled bounds (1).
- A provisional conflict must exceed `max(10^-12,100 times the observed two-setting
  quadrature discrepancy)` in absolute margin. This threshold is a diagnostic, not a certified
  error bound.
- Confirm only those selected conflicts using independent mpmath integration at
  60 digits/10 atoms and 90 digits/18 atoms, over `[0,4]` split into intervals of length `1/4`.
  Recompute source slopes and flux coefficients at both precisions. No rank/frequency/grid expansion.
- Runpod only; at most 12 processes; BLAS/OpenMP threads set to one. Hard wall-time cap180s.
  Download script, JSON results, and log. Record elapsed time and numerical disagreement.

## Decisions

1. Confirmed negative margin: the tested scalar damping has incompatible centers at that
   frequency. Examine the center pair analytically and seek a correction allowing displacement
   and center to interact. No claim about untested damping rates or RH follows.
2. No robust sampled conflict: keep the candidate undecided. Attempt an analytic construction
   or obstruction; do not automatically enlarge the scan or claim positivity.
3. Precision disagreement, timeout, or only sub-threshold values: inconclusive. Do not turn
   numerical signs into a theorem or proceed to a longer run.

Follow `docs/meta/scientific-method.md`. This experiment changes which explicit certificate is
worth an analytic attempt; it does not replace that attempt.
