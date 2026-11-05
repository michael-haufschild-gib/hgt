# Real-weight camera and local count transfer

- **ID:** real-weight-camera-and-local-count-transfer
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A40.

## Target

Extend the local moment camera to real coefficients with absolute Lorentzian
mass, retaining its aperture and explicit error. Transfer local weighted counts
to positive on-line mimics by band-limited interval majorants.

## Available inputs

`exists_local_slow_pair` constructs windows from the carrier count, independently
of coefficient values. `tsum_far_le` already handles arbitrary complex coefficients
with summable absolute Lorentzian mass. `weighted_discMoment_readout_slow` combines
these inputs without an integer lower bound on a nonzero coefficient.

## Count distinction

The isolating product uses the number of distinct support points. A weighted
count alone cannot provide that number without a positive lower bound on atom
weights. The proposed sharp example is the simple lattice
`{1/2 + πik/L}`, with weight `1/(2L)` per point: for `L≥a`,
`W_simpleHalfLatticeConfig` gives the same normalized form `∫f·conj(g)` at
aperture `a`, while the number of points in a fixed interval grows with `L`.
Formalize this distinction alongside the weighted transfer; it does not refute
transfer of weighted mass.

## Majorant construction to verify

For a smooth compactly supported bump `b`, use `K(t)=|b̂(t)|²`.
Convolve the indicator of `[x−R,y+R]` with `K`, then divide by
`∫_[−R,R] K`: the result majorizes `[x,y]` and is nonnegative elsewhere.
Its Fourier support stays within twice the aperture of `b`, so equality of
window images transfers its integral to the source configuration. The strip
envelope must retain a leading coefficient arbitrarily close to one.

Write `F=b̂`, with `b` supported in `[-ε,ε]`. A candidate envelope is

`E(x)=(1+ε)|F(x)|²+(1+1/ε)∫_{-1/2}^{1/2}|F′(x+iy)|²dy`.

The vertical fundamental theorem of calculus, Cauchy–Schwarz and Young's
inequality give `|F(x+iv)|²≤E(x)` for `|v|≤1/2`. Plancherel gives

`∫E≤[1+ε+(ε+ε²)e^ε]∫|F|²`.

Indeed, the differentiated transform has source `itb(t)e^{-yt}`, whose
squared norm is at most `ε²e^ε` times that of `b`. The coefficient tends to
one as `ε→0`; enlarging `R` makes the central integral approach the full
energy. This derivation still requires Lean verification.

For a source with interval mass at most `D·length+C`, Fubini then bounds
the integrated envelope by `(D·length+C)∫E`. For ζ, use the multiplicity
count on `|γ−T|≤3T/4`. If the target interval lies in `[T/2,3T/2]` and `T≥8R`, every exterior zero is farther
than `T/8` from each modulation point. Sixth-order transform decay and
the Lorentzian mass bound give a uniform tail `B=320 C_b²e^ε`.
Its integral is `B·length`; a sufficiently large `log(T/2π)` absorbs it
in any reserved density slack. This leaves the sharp coefficient
`θ/(2π)` for every `θ>1`, with an additive `A log(T/2π)` term.

## Lean obligations

`weighted_discMoment_readout_slow` passes Lean and its transitive axiom audit
uses only the three standard axioms. It chooses one pair of windows uniformly
for all complex coefficients with summable absolute Lorentzian mass.
`weighted_discMoment_readout_rvm_explicit` also passes with the same explicit
`cameraMomentHeight` and the same standard axioms. The sharp multiplicity
count on `|γ−T|≤3T/4`, the vertical energy estimate, absolute convergence
of weighted images, and their positive on-line Fourier-energy identity also
pass with standard axioms. Fourier normalization, interval majorants,
weighted count transfer and the lattice example remain under verification.
Final direct source audits and umbrella wiring remain.
