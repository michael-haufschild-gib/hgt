# Paid cutoff growth from the current source clock

Owner: critical-clock product task. RH and exhaustive payment remain open.

## Closed producer [BRIDGE]

`MobiusDivisorPaidCutoffInterval.lean` proves
`eventually_exists_mobiusDivisorInitialClockPayment_cutoff_interval`.
For the literal initial core and `M = 14*(b+1)*N`, actual fresh-prime batches
pay every original integer cutoff `M <= L <= M + sqrt(sqrt M)`.
The endpoint retains a positive quadratic reserve after paying the original
two-coordinate energy. Every intermediate batch prefix also has complete
weighted energy control throughout this interval. The theorem has no payment,
correlation, source-sign, or energy-bound premise.

## Corpus facts

- The full prime-insertion clock identity already cancels the positive
  copied self-square against the removed prime-labelled mass; its remaining
  terms are the complete signed correlation and a negative logarithmic square.
- The current-clock producer pays `delta M^2` using actual fresh primes.
- Literal channel cutoff increments equal the square-root clock increment
  times `mu(d) * primeFreeDivisorDefect(M/d)`.
- The divisor defect has an unconditional `24 sqrt(n)` bound, and the corpus
  has the square-root reciprocal sum bound. Grouping by arbitrary processed
  labels cannot increase the total absolute increment.

## New verified facts

- Literal channel increment: `|D(M+1,d)-D(M,d)| <= 12/sqrt d` for `d>=1`,
  including inactive channels. For any label set and arbitrary processed core,
  the total absolute fibre change is at most `24*(L-M)*sqrt L`.
- Complete weighted energy satisfies
  `W(P,L) <= (1+e)*W(P,M) + (1+1/e)*(1+log L)*(24*(L-M)*sqrt L)^2`.
  Both cutoffs are represented on the larger squarefree support; newly active
  coordinates and their self-squares are included, not discarded.
- If `W(P,M) <= C*M^2*(1+log M)` and `L-M <= sqrt(sqrt M)`, the increase is
  at most `(C+2304)*M^2*(1+log(2*M))/sqrt(sqrt M)`.
  Dividing by `M^2` tends to zero. The threshold depends on `C` and the desired
  payment fraction, not on the processed core or its cardinality.
- The actual initial-clock producer supplies the energy bound uniformly for
  all its batch prefixes. Half its quadratic reserve pays the cutoff interval;
  half remains at the endpoint. The cutoff radius tends to infinity.

## Whole-route test

Local simultaneous core/cutoff control is now an actual producer. Its cutoff
radius grows in original integer-clock units; its helper child quotients remain
bounded. It is not a growing-child-depth producer.

The batch length is the minimum of the three window cardinalities minus one;
this is not the total pool cardinality and does not prove pool exhaustion.
The existing producer requires the whole candidate pool to be fresh, so its
reuse on partially processed windows is not supplied by the local result.
No successive fresh-pool schedule follows. The earlier depth obstruction
still requires growing child quotients to pay inherited omitted-prime debt.
Finite-depth cancellation constants still lack the quantitative dependence
needed as the active field grows. Thus exhaustive current-clock payment,
completion, bounded critical action, and RH remain unproved.

## Verification

Scratch `lake env lean` passed. All five public declarations use only
`propext`, `Classical.choice`, and `Quot.sound`; no added axioms or computational
certificates. The module is wired into `RHTower.lean`. Named leaf build passed
without leaf warnings; existing dependency warnings were replayed. Index passed.
Global lint remains blocked by the same four unrelated unreachable modules:
`ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
`XiHeatCassiniWoldJointDepthMöbiusSourceTransport`. Whitespace audit passed.
