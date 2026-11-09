# Gaussian observation boundary of an exceptional layer

- **ID:** ELT-GOB
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** review-0911/obstacles-summary.md §2.10, observation-scale question
- **Statement:** Exponential damping has a mode boundary `a(Re ρ−σ)/2=π/4`; after finite exceptional subtraction the complete prime-current error vanishes at every positive exponential speed.

## Objects

`K(y,w)=½Γ(w/2)y^(−w/2)`, `s=σ+it`, `y=e^(−at)`,
`r(ρ,σ,a)=a(Re ρ−σ)/2−π/4`.
The current is the full infinite von Mangoldt sum minus its continuum.
Its normalized continued finite part is `e^(−y)(A(s)−ξ′/ξ(s))`.

## Proof [PROVED HERE]

1. For fixed ρ and σ, put `z=(ρ−s)/2`. Once `t≥|Im ρ|+2`,
   `1≤|Im z|=(t−Im ρ)/2≤t`. The corpus's arbitrary-strip Gamma and
   reciprocal-Gamma bounds give

       |K(e^(−at),ρ−s)| ≤ C t^N e^(rt),
       |K(e^(−at),ρ−s)^(−1)| ≤ D t^M e^(−rt).

   Indeed the damping norm is exactly `e^(at(Re ρ−σ)/2)` and the
   Gamma exponential is `e^(−πt/4)e^(π Im ρ/4)`. Constants absorb
   the fixed ordinate. They are independent of a. Gamma and the complex
   power are nonzero at these heights. Thus `r<0` gives decay; `r>0`
   gives norm tending to infinity. No assertion about magnitude at `r=0`
   follows from these polynomial bounds.

2. Failure of AAL supplies finite F and `½≤θ<σ<1` with every omitted
   zero left of θ. Its complete error is bounded by
   `C(y+y^p)(1+log t)`, `p=(σ−θ)/2>0`, throughout the high strip.
   At `y=e^(−at)`, `a>0`, this is at most
   `Ct(e^(−at)+e^(−apt))` for `t≥1`, which tends to zero independently
   of the observation abscissa in `[σ,1]`. This retains the infinite tail.

3. If every member of F has negative r, their finite sum tends to zero.
   Subtract it from step 2: the prime-minus-continuum current passes to
   its normalized continued finite part at that exponential speed.

4. Let β be the largest real part in F; `σ<β<1`. Choose `β<b<1` and
   `a=π/(2(b−σ))`. Every retained zero has negative r, while the pole
   `ρ=1` has positive r. Thus the actual infinite-current passage in
   step 3 coexists with a divergent Gaussian pole mode.

5. The complete raw-current expansion is

       ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s)
         − K(y,1−s) + Σ_{ρ∈F} K(y,ρ−s) → 0.

   The corpus's germ bound, applied to `1−s`, gives
   `|e^(−y)/(1−s)+E(y,1−s)−K(y,1−s)|≤4y` for `Im s≥1`,
   `Re s≤1`, `0<y≤1`. Add this to step 2 and use
   `A−ξ′/ξ=−ζ′/ζ−1/(s−1)`. The rational terms cancel exactly.
   A finite height cutoff and the horizontal gap make the strip zero-free,
   so this identity uses no additional zero-free assumption. The expansion
   holds uniformly in its observation abscissa at every positive exponential speed.

## Mathematical consequence and limits

Inverse-height passage does not license arbitrary joint limits. Exponential
observations distinguish the pole from the exceptional layer. The finite
subtraction gives a valid infinite-current formula at every exponential speed;
the individual mode bounds identify when a discarded term can grow.
No conclusion about cancellation among several growing modes is asserted.
These laws neither repel zeros nor replicate them.

## Formalization

`formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGaussianObservationBoundary.lean`.
`formal/GaloisForLFunctions/ExceptionalLayerTheory/ThePrimeCurrentAtExponentialScales.lean`.
Lean check and transitive axiom audit pending.
