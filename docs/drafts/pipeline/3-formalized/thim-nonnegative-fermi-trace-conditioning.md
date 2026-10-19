# Nonnegative coefficients and selected Fermi trace conditioning

- **ID:** thim-nonnegative-fermi-trace-conditioning
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../3-formalized/thim-full-trace-valuation-depth-stability.md`
- **Statement:** The quadratic depth obstruction persists when every divisor
  coefficient is nonnegative. Cancellation between coefficient signs is not
  necessary for poor conditioning of the complete selected trace.

## Scope and counting

This strengthens the same physical observability package. It is not a separate
contribution count. No external novelty claim, numerical experiment, or RH
consequence is asserted.

## Exact family

Let L>=1, H=2^(L+1), B=2^L. Let c_L be the signed ramp from
`FermiDyadicRampAndQuadraticTraceLoss.lean`. Set

`c_L^+(d) = c_L(d) + B * 1_(d=H)`.

Its equivalent explicit coefficients are

- `c_L^+(2) = 2*L`;
- `c_L^+(2^j) = 2^(j-1)*(L-j)` for 2<=j<=L;
- zero elsewhere.

Every coefficient is nonnegative; all subtraction in these formulas is real.
Telescoping gives total coefficient sum B. The range L=1 has just c(2)=2.

## Audited paper proof

Write s for the signed ramp sieve, s+ for the modified sieve. Linearity gives
`s+(n) = s(n) + B*1_(H divides n)`. Whenever H divides n, every column of the
signed ramp is active and its positive and negative contributions cancel,
so s(n)=0. Thus `s+(n)^2 >= s(n)^2` for every n, and consequently

`P(c_L^+) >= P(c_L) >= L*(L+1)*(2*L+1)/12`.

The added column has zero odd readings. At an even sieve index n its selected
reading changes by

`D(n) = B*(2*1_(H divides n) - 1_(H divides 2*n))`.

Nested divisibility gives `D(n)^2 = B^2*1_(2^L divides n)`. Setting n=2j and
reindexing j=2^(L-1)*t yields its complete selected energy

`Q_delta = (H^2/4) * sum_(t>=1) q(H*t) <= 1/2`,

where q(n)=1/(n(n+1)). The estimate follows termwise from
`H^2*q(H*t) <= 2*q(t)` for H,t>=1 and the existing total pronic mass 1.
For each reading, `(a+b)^2 <= 2*a^2+2*b^2`; summability then gives

`Q(c_L^+) <= 2*Q(c_L)+2*Q_delta <= 4*L+1 <= 5*L`.

Therefore

`((L+1)*(2*L+1)/60) * Q(c_L^+) <= P(c_L^+)`.

For L>=2, the first selected even jump is exactly 4, hence Q>=4/5. For L=1
it is 2, hence Q>=1/5. These facts make the lower ratio nonvacuous. Together
with the verified general upper estimate, these establish the same
quadratic growth order inside the nonnegative cone.

## Existing work and dependencies

- `sieveSeq_nonneg_of_nonneg_weight` and
  `sieveSeq_le_of_dvd_of_nonneg_weight` already exist in
  `NonnegativeWeightEndpointOrderAndCalibratedDefect.lean`; source and olean
  checked. Nonnegative observation/state-order equivalences are also prior art.
- Lexical `sieveSeq nonnegative`: 5 hits, all inspected. `Fermi positive
  coefficients`: 1 hit, from this programme's earlier theorem about positive
  observation indices, not coefficient signs. `sieveSeq linear`: 11 hits,
  inspected; none supplies this cone obstruction.
- Deep query `nonnegative divisor coefficients selected Fermi boundary energy
  coercivity long dyadic valuation ramp`: completed; 20 source arguments and
  20 candidate statements inspected. Suggested mean-square and dyadic-frame
  ingredients concern different objects and remain unverified as a route here.
- Reuse existing THIM multiples reindex and RHTower pronic mass. The signed
  ramp lower/upper theorem has passed source and axiom verification. This
  stronger cone theorem has now passed source and public-axiom verification.
- The endpoint estimate now reuses `RHTower.Sieve.sum_inv_sq_le_two` from
  `RHTower/Sieve/SquarefreeHarmonic.lean`. Its source, compiled artifact and
  scratch name probe passed. The broader finite-set variant was found by
  corpus search, then its smaller interval dependency was selected.
- Classical finite-chain Hardy theory is already recorded on the parent card;
  an abstract ramp inequality alone is not new mathematics.

## Gates

- [x] Precise stronger conjecture recorded before further formalization.
- [x] Initial corpus audit and dependency identification.
- [x] Complete paper audit, including finite-to-total comparison using the
  established summability of every finite-horizon sieve and selected trace.
- [x] Exact unconditional Lean theorem, source/axiom audits, umbrella wiring.
- [x] Global generated lint after the concurrent umbrella was completed.
- [ ] Significance and external novelty qualification.

## Log

- 2026-10-18 — Removing the signed ramp's last negative endpoint exposed this
  stronger conjecture. It is not asserted by the existing source-audited upper bound.
- 2026-10-19 — `FermiNonnegativeDyadicRampTraceObstruction.lean` now contains the
  explicit nonnegative family, endpoint comparison, cubic lower energy,
  linear selected-energy bound, positivity, quadratic lower loss, and the
  nonnegative-cone no-go. First source audit found a cast mismatch and an
  unsimplified zero inequality; both were corrected. A second audit found two
  incorrect named arguments to `Nat.cast_nonneg`; typed positivity proofs fixed
  those. The third source audit passed without diagnostics. All seven public
  declarations passed the separate `/tmp` axiom audit, using only `propext`,
  `Classical.choice`, and `Quot.sound`. The leaf is wired and index regeneration
  passed. `scripts/formal_tools.py lint --check-generated` failed solely because
  concurrent `BiScaleUncertainty.FiniteHorizonPositiveCoercivity` is unreachable
  from its own umbrella. That other work is preserved. The last clean global
  gate remains the preceding six-leaf checkpoint. Lean proves strict positivity
  of the selected energy; the explicit first-cell numerical bounds above remain
  paper results.
- 2026-10-19 — The concurrent BiScale umbrella now imports its new leaf. Fresh
  index regeneration and `scripts/formal_tools.py lint --check-generated` both
  passed. This completes the seventh-leaf formalization gate; the whole
  observability package still has no qualified novelty count.
