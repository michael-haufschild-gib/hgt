# Finite-clock cancellation in the actual processed source

- Owner: resumed clock/source research task.
- Type: THEOREM, formalized; source-level partial result, not an RH proof.
- Lean: `formal/GaloisForLFunctions/RHTower/MobiusDivisorTruncatedMomentCancellation.lean`,
  `RHTower.mobiusDivisorContinuousHead_finite_clock_cancellation`.
- Frozen statement: for every finite prime core `P` and every real `X > 1`,
  `∫ x in (0,X], mobiusDivisorContinuousHead P x / x^3 > 0`, with one
  comparison constant `1/48` against the unprocessed primitive, independent
  of both `P` and `X`. The comparison holds for every real `X`, and strict
  positivity holds if and only if `1 < X`.
- Source evidence: the continuous head is the exact finite Möbius dilation of
  the nonnegative unit source, including every integer/clipped sample. The full
  inverse-cube moment has a uniform positive Euler product; the finite-clock
  primitive has not been supplied by that factorization.

## Whole-route test

| Corpus fact | What the theorem adds |
| --- | --- |
| Full signed moment has a core-uniform positive margin. | Retain the moving upper time boundary instead of integrating it away. |
| Fixed-core head cancels its square-root main term. | A sign uniform in the core, without taking a separate cutoff limit for each core. |
| Pair renewal retains signed cross-scale terms. | A positive primitive for one source only; multiplication by the second signed source remains uncontrolled. |
| Delayed bounded-half-weight helpers cannot repay arbitrary debt. | This theorem does not repair that obstruction or produce an exhaustive funded history. |

The hard RH gate remains boundedness of the actual logarithmic-clock action.
Inverse-cube positivity alone is not that bound. The theorem is a partial
source-sign result; it does not supply cancellation in the critical action.

## Paper attack

Write `J(X)=∫_(0,X] U(x)/x^3`, where `U` is the actual nonnegative unit head.
Exact dilation gives the processed primitive
`Σ_(d|∏P) μ(d)d^(-3/2)J(X/d)`. Since `J` is nonnegative and increasing,
the unit term survives and every negative term is bounded by its full coefficient
times `J(X)`. The required nontrivial numerical-free analytic step is a uniform
bound below one for the total odd-parity divisor weight. The rational margin
uses finite Euler products and a symbolic p-series comparison. Both the margin
and the finite-clock theorem are now Lean-certified.

The paper comparison closes with `1/48`:

1. For `a(n)=sqrt(n)/n²`, symbolic telescoping gives
   `a(n+1) ≤ 2/sqrt(n)-2/sqrt(n+1)` for `n ≥ 1`. The first nine nonzero
   terms sum to at most `2`; hence `Σ a(n) ≤ 8/3`.
2. Finite geometric Euler expansion gives `B(P)=∏_(p∈P)(1-a(p)) ≥ 3/8`.
3. For a core containing `2`, write `A(P)=∏_(p∈P)(1+a(p))`.
   Then `A(P)B(P)=∏(1-a(p)²) ≤ 1-a(2)² = 7/8`, so `A(P) ≤ 7/3`.
4. The odd-parity mass is `(A(P)-B(P))/2 ≤ 47/48`. Adding prime `2` only
   increases odd-parity mass, so this holds also for cores omitting `2`.
5. In the actual truncated primitive the unit contribution is `J(X)`;
   every negative contribution is bounded in magnitude by its coefficient
   times `J(X)`, and the other even contributions are nonnegative. Thus the
   signed primitive is at least `J(X)/48`, for every core and cutoff.
6. The actual unit source is positive on `(1,2)`, so `J(X)>0` whenever `X>1`.

This uses the literal inverse-cube moment weight, not the RH-bearing critical
weight. At the latter weight the corresponding absolute divisor envelope is
not summable. Consequently this proof does not transfer to the critical
clock action or to a product with an arbitrary sign-changing dilated head.

## Audit

- Scratch verification: `lake env lean /tmp/hgt-clock-cancellation.lean` passed.
- Final audit: `lake build GaloisForLFunctions.RHTower.MobiusDivisorTruncatedMomentCancellation`
  passed. The new module is imported by `GaloisForLFunctions/RHTower.lean`;
  no umbrella or full build was run.
- Public theorem's `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
  No added axioms, `sorry`, numerical experiments, or native computation.
- `scripts/formal_tools.py index` passed.
- Repository lint did not pass: four unrelated modules were reported unreachable:
  `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMobiusSourceTransport`.
  The last already has direct umbrella imports. These diagnostics do not name
  the new module; this audit does not certify the entire repository.

## Remaining hard problem

The proof wins by controlling the total negative divisor mass in the summable
inverse-cube moment. It does not construct compensating mixed-source terms at
the critical weight. Thus the critical cancellation request remains incomplete.
The next attack must retain the signed cross-scale product and its actual clock
weight throughout the prime-insertion/cutoff recurrence; another absolute-mass
bound at a stronger decay rate would not advance that gate.

## Facts / failed attacks

- The finite-clock sign is uniform in both the finite prime core and the real
  cutoff, without a core-dependent onset. The source-birth boundary `X = 1` is sharp.
- The exact truncated dilation identity keeps `J(X/d)`; replacing it with the
  complete moment loses the moving-boundary issue that this theorem resolves.
- An odd-mass estimate proves this noncritical sign but leaves critical mixed
  cancellation untouched. No RH consequence is claimed.
- Existing sparse all-cutoff reserve histories already change cores indefinitely;
  repeating their construction would leave prescribed-prime exhaustion untouched.
- Generic pointwise contraction is not justified by homothety: the copied field
  preserves its parity sector and the larger-cutoff background remains present.
- A pointwise exponential compensator for the spectral insertion factor is an
  analytic target only. No actual prime packet realizing it with the required
  norm and cutoff control has been constructed; do not add it as a producer.
- Deep search results are suggestions, not verification. The first broad mixed-source
  query returned generic inner-product structure, not an arithmetic cancellation law.
