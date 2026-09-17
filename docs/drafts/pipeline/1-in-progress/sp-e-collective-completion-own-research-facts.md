# SP-E collective-completion facts

- `CCMFUSuzukiMobiusDivisorDilationChannels` proves that the literal SP-E
  half-order Abel source is one *joint* signed Möbius-dilation sum.  Its
  collapsed-kernel theorem explicitly rules out obtaining cofinal gain by
  estimating dilation channels separately; no decomposition that first
  bounds dyadic/dilation pieces can be a producer.

- `MobiusDivisorDilationMeanUniformCoreNoGo` proves that even the fixed core
  `{2}` has unbounded one-prime renewal cost.  Uniform local insertion and
  independent averaging are therefore not candidate completion mechanisms.

- `MobiusDivisorTerminalCoreExistence` proves an unconditional endpoint
  statement stronger than a middle-prime capacity claim: for every positive
  quadratic tolerance, cofinally many actual cutoffs admit a state that has
  processed every prime outside two signed macroscopic windows and whose
  complete successor envelope is below that tolerance times the cutoff
  square.  Thus the remaining issue is a bounded *path* to this state, not
  existence of a low-envelope terminal state.

- In the terminal windows, primes are isolated after the required quotient
  core.  `MobiusDivisorSignedPrimeBatches` gives an exact scalar ordering for
  any chosen isolated pool under the larger of its two endpoint energies.
  This cannot by itself close SP-E: the unknown full endpoint remains the
  signed Abel/RH-bearing quantity.

- Conjecture/failure loop: an unbounded-memory dyadic reconstruction was
  considered as a possible cross-scale moderator.  It factors through the
  individual dilation/error-difference channel, so the first fact above
  excludes it before any new Lean statement is written.  The next live
  candidate must give a simultaneous changing-core path law, not a dyadic,
  scalar, or channelwise estimate.

- Formalized exact structural obstruction: retained arity energy has the
  literal all-source pair expansion
  `sum_(d,e) 1_(pf(d) triangle pf(e) subset P) |pf(d) \\ P| C_d C_e`.
  For disjoint labels its summand is identically zero at every processed core:
  before the labels can interfere its indicator is zero, and once they can,
  the surviving label is empty.  Thus any proof based only on accumulated
  arity/copy cost is mathematically unable to control the primitive coprime
  cross sector.  The Lean theorem is stronger: every additive label-pair
  potential with zero weight on an empty remaining label has this blindness.
  This formalizes the paper-level sector separation and its universal
  extension; it does not prove the needed joint signed cross bound.

- Literature audit: Harper's 2025 survey, [arXiv:2512.23681](https://arxiv.org/abs/2512.23681),
  obtains better-than-square-root effects for *averages* of multiplicative
  character sums by deterministic-to-random moment transfer.  Its indicated
  Möbius short-interval consequence assumes GRH and the Ratios Conjecture.
  It supplies neither an unconditional estimate for one literal signed
  Möbius--divisor source nor the labelled endpoint/seam control required by
  SP-E, so there is no literature theorem to import as a proof here.
