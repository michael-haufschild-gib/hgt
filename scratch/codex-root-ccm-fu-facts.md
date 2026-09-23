# CCM--FU fact log (root)

- The RH-bearing CCM--FU action is equivalent in the corpus to uniform boundedness of the
  critical Mertens-deviation variation action; source-free Gamma/harmonic terms already have a
  uniform budget.
- New, Lean-checked: for every integrable source `f`, the exact combination
  `3 T₂ + Σ_{j<N} T_{j+3} - (N+3) T_{N+3}` equals the finite causal slab ledger
  `3 B₂ + Σ_{j<N} (j+4) B_{j+3}`, with `T_a = ∫_(a,∞) f`, `B_a = ∫_a^(a+1) f`.
  For `f=E/t²`, this removes all future Mertens tails before any estimate.
- Consequence under investigation: remaining cancellation is finite and couples each local
  Chebyshev slab to endpoint terms; generic tail convergence cannot resolve it.
- New, Lean-checked: the literal shifted critical factorial prefix satisfies
  `Σ_{j≤N}(Λ(j+3) - (j+3) log((j+3)/(j+2))) = psiRemainder(N+3) + D_N`,
  where `D_N = (N+3) - (N+3) log(N+3) + log((N+2)!) + log 2` is deterministic.
  Thus factorial/Volterra cancellation transports, but cannot remove, terminal Chebyshev error.
- New, Lean-checked: on every physical Suzuki aperture, the endpoint-free minus completed
  outgoing quantile characteristic has zero quadratic pairing with every actual head, while its
  zero-clock coefficient equals `criticalMellinCompletedError(2a) - 2(1-exp(-a))`.  Therefore
  terminal completed error has a source-bearing null gauge direction; quadratic Gamma--Slepian
  head coercivity alone cannot control it.  Any viable bridge must use a non-null cross-boundary
  observable.
- New, Lean-checked: literal matched-quantile Lorentz current is zero unless both endpoints are
  prime powers. The ambient adjacent-slope cone escape therefore does not refute a
  source-support-sensitive graph wall; remaining obstruction is cofinal resistance on
  prime-power pairs carrying nonzero current.
- New, Lean-checked: finite Lorentz graph resistance equals exactly its sum over active
  prime-power-pair edges. Thus zero-atom geometry is absent before any cofinal estimate; the
  remaining resistance problem is intrinsically a completed prime-power problem.
- New, Lean-checked no-go: literal Lorentz graph resistance obeys
  `R_K ≥ (criticalMellinAtomWeight 2 / 2) *
  (ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2)` and hence tends to `+∞`.
  Therefore no uniform raw-resistance Cauchy wall can close the signed CCM source. This does not
  transfer to a certificate that first deletes dissipation-null edges.
- New, Lean-checked: replacing each Lorentz resistance by zero precisely when its literal
  singular dissipation is zero preserves the exact current-square factorization and gives a
  finite Cauchy wall with effective resistance `R_eff ≤ R_raw`. Hence raw-resistance divergence
  is not a no-go for the source-active graph. Open datum is cofinal control of `R_eff`, or a
  completed terminal cancellation of its charged edges.
- New, Lean-checked: `R_eff(K)=0` iff literal Lorentz graph dissipation is zero, equivalently
  the matched--quantile displacement is constant on every active prime-power vertex of the head.
  Therefore the effective wall deletes no physical coercive direction and has no new null gauge;
  remaining cofinal obstruction lives on the existing active relative-offset quotient.
- New, Lean-checked: on each distinct active prime-power pair, literal Lorentz dissipation is
  zero iff their matched--quantile displacements are equal. Hence every active vertex with
  displacement different from the base prime `2` retains its full raw base-edge cost after
  null-edge deletion.
- New, Lean-checked: effective finite graph resistance is at least
  `(criticalMellinAtomWeight 2 / 2)` times the critical-Mellin mass of prime powers where
  `ccmActualHeadOutgoingNodeError n + ccmActualHeadMatchedPolarUpperExcess n` differs from its
  `n=2` value. This is an exact source-faithful lower envelope, not a generic Cauchy estimate.
- Current precise frontier: either this completed-source mismatch mass diverges cofinally, which
  rules out a uniform effective-resistance graph wall, or a uniform effective wall forces a
  cofinally massive exact level set of completed outgoing error plus retained endpoint channel.
  Corpus presently supplies neither a divergence proof nor a lawful cancellation of that level
  set; proving/refuting this alternative is the relevant next hard problem.
- No-go verified against existing Lean: the unconditional DLV result gives only
  `delta_n / sqrt(n) -> 0`, which is compatible with any fixed base displacement, and the exact
  adjacent increment is an unoriented matched-cell overlap/gap. Hence neither relative decay nor
  a monotonicity argument can prove divergence of the mismatch mass. The positive covariance
  Abel kernel is cutoff-history dependent; Lean already rules out replacing it by a fixed local
  gap coefficient. Any next producer must act on the all-history prime-power admission law.
- New, Lean-checked: every literal strict-cross current has the denominator-free exact split
  `current² = displacementDebt * debtConjugateGeometry`, where the first factor is the actual
  ordered quadratic debt already retained by the source hard core. The resulting finite Cauchy
  wall is therefore the strongest direct attempt to pay that debt by a positive factorization.
- New, Lean-checked no-go: the conjugate geometry has a fixed-base lower envelope proportional
  to `Σ Λ(n)/√n` and tends to `+∞`. Thus no uniform Cauchy producer with literal displacement
  debt as one entire positive factor can close Route O/CCM-FU. The surviving requirement is a
  genuinely signed, all-history prime-power admission mechanism; neither raw resistance nor
  debt-positive factorization can supply it.
- New, Lean-checked: the Route-P terminal parabolic orbit, normalized by the reciprocal of
  `4 * actual prime-power mass * (sqrt(K+3)-1)`, converges in `Fin 4 → ℝ` to the fixed vertical
  null flag `(0,0,-1,0)`. This gives a canonical singular terminal boundary despite the forced
  connection height tending to `-∞`. Its limit carries no signed prime-power history by itself;
  the ordered two-Julia graph pairing and its cofinal signed control remain open.
- New, Lean-checked: across any interval `m<n` with no intermediate prime-power atom,
  equal matched--quantile displacement forces the exact resonance
  `4(n-m)=(c_m+w_m/2)(w_m+w_n)`, where `c_m` is the literal matched centroid and
  `w_j=Λ(j)/sqrt(j)`. For prime endpoints `p<q`, the same resonance gives
  `q-p ≤ log p + (log p)^2/(2p)` once `p≥exp(2)`, and
  `log p-(q-p) ≤ log p*(q-p)/(4p)` without that cutoff. These are source-specific
  necessary conditions for an active displacement level set, not RH or a cofinal signed bound.
- Paper argument, Lean-open: the two bounds above and `log p≤p` force
  `|(q-p)-log p|≤(log p)^2/(2p)` for resonant consecutive active primes.
  On `[X,2X]`, their integer gap takes only `O(1)` values; for each value,
  `p` lies in an `O(log² X)` interval around its exponential. Thus there are
  `O(log² X)` resonant prime--prime active edges. Proper prime powers in the
  block number `O(sqrt X log X)`, while PNT gives `≫X/log X` primes. Path-run
  counting therefore yields `≫X/log X` noncoherent prime vertices and
  `≫sqrt X` completed-source mismatch mass. By the already Lean-proved base-edge
  envelope, the effective-resistance wall diverges. The quantitative counting,
  prime-density link, and resulting no-go are not yet formalized; do not mark
  the subroute retired before those Lean proofs are closed.
- New, Lean-checked: the exact resonant adjacent-prime gap satisfies
  `|(q-p)-log p|≤(log p)^2/(2p)` once `p≥exp 2`. The correction tends to zero.
  Since odd primes have even integer gaps, no equal-displacement adjacent
  odd-prime active pair can start in the logarithmic band
  `2t+1≤log p≤2t+1+1/4` when that correction is below `1/4`.
  The corresponding exponential-window theorem is also Lean-checked.
- Corpus correction: `RHTower.tendsto_primeCounting_ratio` proves the
  unconditional prime-counting asymptotic, contrary to the stale comment in
  `PrimeMassWindow.lean`. Thus odd-centered multiplicative windows have
  abundant primes; no new PNT infrastructure is needed. This offers a
  simpler parity-window route to effective-resistance divergence than
  counting all near-integer resonances in dyadic blocks. The bridge from
  prime density through proper-power separators to actual mismatch mass,
  and its cofinal divergence, remain Lean-open. None of this supplies the
  signed CCM-FU source bound or RH.
- New, Lean-checked finite active-path law: if no adjacent prime-labeled
  vertices are both coherent, then
  `primeCount ≤ 2*mismatchCount + nonprimeCount + 1`.
  The proof uses literal adjacency, not a probabilistic independence
  heuristic. Specialization to the ordered actual prime-power path in the
  odd-centered windows is still open, as are quantitative prime/proper-power
  counts in that path.
