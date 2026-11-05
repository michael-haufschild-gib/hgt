Route WD (Ward / collision / window energy) has three branches that reach RH, and in each the remaining step is one unproved estimate. Everything below is the status quo of the Lean corpus at b9ea120c82.

## Branch 1: long mollifiers (the only branch with a proved RH landing).
Prove, for arbitrarily large exponents θ, a bound ∫_1^T |ζ(½+it) M(½+it)|² dt ≤ C_θ T^K along an unbounded sequence of heights T, with a fixed K, where M has length X ≤ T^θ, bounded coefficients |b_d| ≤ B, and prefix cancellation: the Dirichlet coefficients of ζM vanish for 2 ≤ n ≤ X₁ with X₁ ≥ T^{3θ/4}. The truncated Möbius mollifier M_X = Σ_{d≤X} μ(d) d^{−s} qualifies, so the Möbius form of the estimate suffices.

The bound must be uniform in the sense that K does not grow with θ. The trivial bound grows like T^{θ+1}, so genuine cancellation at length far beyond T is required. No upper bound for any mollified second moment at length T^θ with θ > 1 exists in the corpus.

The integral must start at height 1, not at T. Dyadic bounds ∫_T^{2T} ≤ CT with prefix cancellation to T^{θ₁}, θ₁ > ½, only give eventual quasi-RH: all but finitely many zeros have depth < 1/(2θ₁) + ε, and the finite exceptional set is not controlled as θ₁ grows.

Or: A bounded or subpolynomial dyadic defect for the linear Möbius taper μ(d)(1 − log d/log y) - but not the sharp Möbius truncation.


## Branch 2: inner caps and the window integer.    

Prove Laplace integrability of the inner-cap flux at every exponent on every Burnol window and every polynomial stage. The flux equals the off-line generating function Σ m_ρ e^{(ρ−½)t} plus bounded plus L² terms, so this statement is "no off-line zero in the window" verbatim. The missing input is a source-side bound on the caps from the Euler or theta source, not an estimate of the caps themselves.

Prove the collision charge is below 2, or the window index is 0, at every resolution for the full source. 

Equivalent forms: a matrix-complete positive residual with sub-unit integer trace on every disc, or bounded unweighted right-port L² norm on every window. Each is RH restated; no arithmetic ceiling for the index exists.

## Branch 3: Hecke defect and sectoriality.

Prove that one constant bounds the dyadic unit-window readings (min, mean, sup, C²) of the log-scale Hecke defect at every height and scale. One dyadic constant is RH; fixed-scale bounds give only an inverse-log corridor.

Prove growing-prefix sectoriality of the theta prefixes with index below 2 at all heights; fixed prefixes have critical-line zeros above their cusp horizon.

## What the density branch cannot do.

100% clustering and D_win are sub-RH landings. Moment → 1 at length exp(o(T)) gives clustering; excess K₀/log T at length exp(c log²T) gives D_win. Neither reaches RH, because sparse off-line zeros survive both.

## Constraints every WD proof must respect (proved impossibilities).
- No polynomial-length mollifier: the second moment is at least (1 + 1/(8+6θ))T at length T^θ.
- No mollifier below length exp(log²T/(6K₀)) for the excess K₀/log T; moment → 1 forces log N/log T → ∞.
- No argument using only upper bounds for ζ on lines: it proves itself for ζ(s)(1 − cp^{−s}), which has a zero lattice at any width.
- No L^p or log⁺ detector at scale V/log V, and no critical-line proportion or exponential depth-tail rate, reaches D_win.
- No size-only heat or coefficient repair below the saddle ½/log X.