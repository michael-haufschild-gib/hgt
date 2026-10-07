# Exact interval phase of the canonical measure

## Status and scope
Paper proof below is a bridge, not a quantization producer. No half-integrality is concluded. The main WP04 conjecture remains open. The mathematical parent is Stieltjes inversion; novelty is not claimed for the inversion theorem.

## Statement
Let `hW : WeilPositiveFull lam`, let μ be `boundaryMeasure hW`, and let Φ be `weilContinuation hW`. For η>0 put

`K(η,a,b,r) = arctan((b-r)/η) - arctan((a-r)/η)`.

For a<b and μ{a}=μ{b}=0,

`lim_{η→0+} ∫_a^b Re Φ(1/2+η+it) dt = π μ((a,b])`.

Consequently the doubled reflection phase

`exp(4i ∫_a^b Re Φ(1/2+η+it) dt)`

converges to `exp(4πi μ((a,b]))`. A single full-Lebesgue-measure endpoint set works for all intervals: the complement of the countable atom set of μ. No atomic decomposition, boundary regularity, meromorphic continuation or prescribed zero support is assumed.

## Dependency-closed paper proof
1. Existing canonical Poisson representation gives
   `Re Φ(1/2+η+it) = ∫ η/(η²+(r-t)²) dμ(r)`.
   Existing weighted integrability gives `∫(1+r²)⁻¹ dμ<∞` and local finiteness.
2. All integrands are nonnegative. Tonelli on [a,b] and the derivative of arctangent give
   `∫_a^b Re Φ = ∫ K(η,a,b,r) dμ(r)`.
3. For r≠a,b, `K→π 1_(a,b)(r)` as η→0+, by the two infinite-end limits of arctangent. At either endpoint the limit is π/2; endpoint nullity therefore removes exactly these two exceptions.
4. Uniform integrable domination: set R=|a|+|b|+1 and restrict 0<η≤1. If |r|≤2R, then `0≤K≤π≤π(1+4R²)/(1+r²)`. If |r|>2R, every t∈[a,b] obeys |r-t|≥|r|/2 and r²≥1. Thus
   `η/(η²+(r-t)²) ≤ 4/r² ≤ 8/(1+r²)`.
   Integration gives `K≤8(b-a)/(1+r²)`. The sum of the two displayed bounds dominates globally and is μ-integrable.
5. Dominated convergence gives `∫K→π μ((a,b))=π μ((a,b])`. Continuity of the complex exponential gives the phase limit.
6. Every locally finite Borel measure on ℝ is sigma-finite and has countably many positive singleton masses. Its atom set is Lebesgue-null. This supplies the common endpoint set, independent of a,b and η.

## Why this does not pay quantization
The computed phase is a limit of an open vertical-segment phase, not the winding number of a supplied closed nonvanishing arithmetic loop. Its limit need not be 1. Calling it a monodromy invariant does not supply trivial monodromy. The exact remaining obligation is an arithmetic identity making these limiting doubled reflection phases equal 1 on the common endpoint set.

## Candidate audit
- Single-valued-square conjecture: still open for actual canonical source, with no proof supplied by Herglotz positivity.
- Attempt to infer it from integer-support Fourier/quasicrystal theorems: not justified. The opened Favorov paper starts with unit masses/zero multiplicities and bounded Dirichlet spectrum; it does not derive those hypotheses for μ. Verdict for that inference: CIRCULAR.
- Positive survivor: exact canonical interval phase above. Verdict: BRIDGE / classical parent theory; useful normalization and domain identification, not claimed significant new scientific knowledge.

## Next conjecture
After this bridge, attack whether the actual integer-supported arithmetic continuation forces the limiting doubled reflection phase to be trivial. Competing possibility: a surviving natural-boundary phase. Any proposed closing loop must be constructed from the arithmetic source and shown to represent the displayed interval quantity.

## Endpoint extension and radial traces

For arbitrary a<b, the same domination gives the endpoint-inclusive limit

`π μ((a,b)) + (π/2) μ{a} + (π/2) μ{b}`.

The endpoint-inclusive theorem is now compiled in `WeilWorkQuantizationEndpointPhase.lean`. All three terms are finite by local finiteness. This supplies a finite phase at every height, rather than only almost everywhere.

Let P be the holomorphic primitive of Φ on `Re s>1/2`, normalized by P(2)=0. Conjugation symmetry of Φ and uniqueness of the normalized primitive give P(conj s)=conj P(s), so P is real on the real interval `(1/2,∞)`. Along a vertical line, differentiation gives `d Im P(σ+it)/dt = Re Φ(σ+it)`. The endpoint formula therefore gives a finite radial limit of Im P at every height, including zero and negative heights by real-axis normalization and interval reversal.

Positivity gives `d exp(Re P(σ+it))/dσ = exp(Re P(σ+it)) Re Φ(σ+it) ≥ 0`. Thus this modulus has a finite nonnegative right-hand limit at the critical line: it is bounded below by zero and bounded above by any fixed interior value. The identity `exp P = exp(Re P) exp(i Im P)` gives a complex radial limit at every height. A sequence of interior vertical lines proves the trace measurable; conjugation symmetry passes through the radial limit. None of these steps asserts continuity of the trace on the boundary or analytic continuation across it.

The radial construction passed scratch Lean and its promoted direct leaf audit in `WeilWorkQuantizationRadialBoundary.lean`. These are classical analytic prerequisites for the finite-irregular-remainder candidate in `FINITE-REMAINDER.md`; they do not themselves force half-integer masses. A parallel current corpus module also constructs an almost-everywhere trace; see EVIDENCE.md for the overlap and exact difference in endpoint scope.
