# The receiver's Abel boundary at one is admitted

- **ID:** receiver-abel-boundary-at-one-is-admitted
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** review-2610 B3.2(c); the unattained zero-abscissa branch
- **Statement:** For every 0<ε<1/2, the actual receiver profile damped at c=1/2−ε belongs to L². Its nearby Abel Grams converge to the finite boundary Grams. If Θ=1, this is the actual zero frontier.

## Goal

Determine the actual endpoint state when the zero abscissa equals one. Local
absence of poles does not determine whether total Abel mass is finite or
divergent. Prove the positive endpoint admission and its exact limiting kernel
from the arithmetic reciprocal-zeta estimate, without assuming a zero-free
strip or receiver growth at the endpoint.

No contribution is credited. First audit whether this is already supplied by
the existing half-damping admission or causal Hardy limits. A routine transport
of those results does not meet the research goal. The scientific consequence,
if new, must be the correct actual-source endpoint classification in B3.2(c),
not an improved exponent or a negative statement about a proof method.

## Gates

- [x] Well-posed actual source and potential arithmetic input identified.
- [ ] Corpus novelty and significance audit completed.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean formalization, individual source check, and transitive axiom audit.

## Evidence and approach

`RHTower.Sieve.exists_norm_invZeta_contour_le` bounds the reciprocal on the
line Re s=1 by a logarithmic power. This is stronger at that boundary than the
strict-half-plane reciprocal estimate used in the new energy theorem.

At c=1/2−ε the symbol has numerator ζ(1−ε+it), shifted denominator ζ(1+it),
and a factor 1/(1−ε+it). Combine the existing vertical zeta growth estimate
with the reciprocal logarithmic bound to seek an integrable squared majorant,
uniform on approaching lines. Handle the removable centering singularity at
s=1 by the existing divided-difference proof. Hardy–Laplace uniqueness should
then identify the same actual receiver at the endpoint.

If endpoint L² admission is proved, multiplication by exp(−e u) converges
strongly in L² as e decreases to zero. This gives convergence of every shifted
Abel Gram and, once positivity of the diagonal is established from the actual
receiver, convergence of normalized Grams to its boundary correlation kernel.
The statement itself is unconditional in ε; Θ=1 only identifies this fixed
line with the actual frontier.

Known leads to inspect before claiming novelty:

- `CriticalWienerConvolutionsPreserveTheReceiver.receiverBounded_pmPowerDamped_half`
  gives receiver admission at ε=1/2, by the earlier discrete-energy producer.
- `PMPowerDampedMobiusDiscreteEnergy.exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le`
  reduces to `PMPowerDampedMobiusEndpoint.memLp_pmPowerDampedFermiSource_half`.
  That proof uses finite Abel summation of raw-prefix energy with arbitrary
  logarithmic savings, then Fatou. Its stated theorem covers damping ε≥1/2;
  it does not state the proposed tilted-profile admission for 0<ε<1/2.
- `MobiusCenteredSchurBoundary` already proves strong critical Hardy limits
  for different centered reciprocal and floor-remainder multipliers.
- `TheCenteredReceiverSymbolIsHardy` and `TheReceiverEnergyGrowthAtTheZeroAbscissa`
  currently use a strict distance from the zero frontier.

## More direct endpoint route to verify

Full Hardy admission on another half-plane may be unnecessary. The proved
energy bound already admits the actual profile at c=1/2−ε+e for every e>0,
since Θ≤1. Its spectral symbol is the centered quotient on Re s=1−ε+e.
Seek a uniform integrable square majorant for 0<e<ε/2, using a reciprocal
bound uniform on Re s≥1 and elementary zeta growth at Re s≥1−ε>1/2.
Plancherel gives a uniform bound for the actual damped profiles. Pointwise
convergence and Fatou then give endpoint L² admission directly, preserving
the same source throughout. The ε<1/2 margin absorbs logarithmic factors.

For the Gram limit, endpoint L² admission makes the product of two translated
profiles integrable. The extra damping factors are at most one on the
positive support. Dominated convergence gives each Gram limit without needing
endpoint L¹ admission. Verify these inputs and the exact majorant before
marking the paper proof complete.

Split the endpoint admission proof by Θ<1 or Θ=1. In the first branch,
c=1/2−ε is strictly above the actual frontier, so the existing energy estimate
already gives L² admission. Only Θ=1 needs a new boundary estimate; there the
new closed-frontier module supplies the compact majorant and symbol identity.
For large |t| the intended uniform estimate is
`|Qε(1−ε+e+it)| ≤ C |t|^(ε−1) log(|t|)^K`,
whose square is integrable for ε<1/2. The uniform reciprocal bound and the
literal numerator-growth theorem must still be read and checked in Lean.

The sharper scientific target is the full probability limit. Define
`Q0(y)=centeredReceiverSymbol ε (1−ε+iy)` and
`Cε=∫ℝ|Q0(y)|²dy`. Prove `0<Cε<∞` and, for every bounded continuous w,

`[∫ℝ|Gε(c+e+iy)|²w(y)dy]/[∫ℝ|Gε(c+e+iy)|²dy] → ∫ℝ|Q0(y)|²w(y)dy/Cε`,

with c=1/2−ε. A global integrable majorant would give this directly by dominated
convergence, with no tail assumption. At Θ=1 this identifies the actual
frontier state as an absolutely continuous probability measure. Prove diagonal
positivity from the literal source or a nonzero boundary-symbol value; do not
insert it as a premise. This explicit state, together with endpoint admission,
is the proposed positive result to audit for significance.

The exact uniform reciprocal input is now located and read:
`RHTower.norm_inv_riemannZeta_shift_le` in `ZetaShiftedLineBound.lean` gives
`|1/ζ(1+e+it)| ≤ (26/zetaLowerA) log(|t|)^7` for 0<e≤1 and |t|≥9,
by taking ω=e/2. The already checked receiver core gives the uniform numerator
bound `|ζ(s)| ≤ A(1+|Im s|)^(5/16)` for Re s≥1/2 and large height. Absorb
the seventh logarithmic power into `(1+|t|)^(1/8)` and divide by |s| to obtain
the same integrable square-majorant exponent −9/16 as in the strict Hardy
proof. This avoids a new elementary numerator estimate.

## Status

Research lead only. The effective-pole classification remains the current
formalization task; finish and audit it before implementing this conjecture.
