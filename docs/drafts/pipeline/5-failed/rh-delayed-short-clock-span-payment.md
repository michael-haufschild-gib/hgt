# Delayed short-span helper batches cannot repay inherited clock debt

- **ID:** rh-delayed-short-clock-span-payment
- **Owner:** critical-clock product task
- **Stage:** 5-failed
- **Type:** FALSIFIED (the short-span repayment candidate only)
- **Source:** [own fact log](../1-in-progress/rh-exhaustive-clock-continuation-facts.md)
- **Statement:** After fixing a short delayed logarithmic window, increasing helper count and depth does not pay every actual omitted-prime debt on the eventual cutoff tail.

## Goal

Test whether replacing isolated helper pairs by arbitrary dense batches in
one delayed prime window can close paid exhaustive continuation. The full
RH goal and constructions using older helpers or wider spans remain open.

## Gates

- [x] Source-pure candidate; actual finite prime cores, omitted primes and clock energy.
- [x] Complete paper proof below; no open source estimate.
- [x] Lean proof, standard-axiom audit and named leaf build passed.

## No-go closure

- **Exact mechanism:** The existing source debt producer requires positive
  reciprocal-prime mass for half repayment. Interval Mertens controls the
  mass of the entire permitted window, even when every prime is selected.
- **Positive survivor:** For every nonempty even-cardinality prime core P
  and every N, actual witnesses r>N, delta>0, kappa>0, T>0 satisfy
  `K(P+r)=K(P)+2*delta`. For every tau>=T and every finite helper set S with
  `tau<log(p)<=(1+kappa)*tau`, the complete coefficient energy satisfies
  `K(P+r+S)>K(P)+delta`. Moreover, one common eventual integer-cutoff tail
  works for all such S:
  `W(P+r+S,M)-W(P,M)>=delta*M^2*(1+log(M))`.
  The full mixed source terms and original logarithmic clock weight remain
  in W. There is no bound on helper cardinality or inverse-square-root mass.
- **New insight:** A fixed delayed window has a positive residual debt,
  regardless of helper cardinality. Its finite-clock onset still depends
  on that window. Moving windows tau=tau(M) are not excluded by this
  quantifier order; a uniform onset needs a separate finite-counting proof.
- **Scope:** This is a restriction on helper timing, not an RH
  counterexample or a proof that every exhaustive construction fails.

## Dependency-closed paper proof [PROVED HERE]

1. `exists_mobiusDivisorClockDelayedInsertionProducer` produces an actual
   prime r, delta>0 and eta>0, with `K(P+r)=K(P)+2*delta`. After a source
   threshold, `K(P+r+S)<=K(P)+delta` forces
   `sum_{p in S} 1/(p+1)>eta` whenever every helper clock exceeds tau.
2. For nonempty S set m=min(S), a=m-1 and b=max(S). Every p is prime,
   so m>=2 and m<=2a. Hence `log(a)>=tau-log(2)` and
   `log(b)<=(1+kappa)*tau`. The entire helper set lies in
   `primesLE(b) \ primesLE(a)`.
3. Interval Mertens gives
   `sum_{p in S} log(p)/p <= log(b)-log(a)+mertensIntervalConst`.
   Since `tau/(p+1)<=log(p)/p`, including the empty-set case yields
   `tau*sum 1/(p+1)<=kappa*tau+C`, where
   `C=log(2)+mertensIntervalConst>=0`.
4. Choose `kappa=eta/4` and
   `T=max(sourceThreshold,1,4*(C+1)/eta)`. The preceding inequality forces
   reciprocal mass at most eta for tau>=T. This contradicts half repayment
   and proves the strict positive coefficient gap, uniformly over S.
5. Every S in the window belongs to the finite powerset of the primes at
   most `floor(exp((1+kappa)*tau))`. For each such S the proved full clock
   limit is `W(Q,M)/(M^2*(1+log(M))) -> K(Q)`. The strict coefficient gap
   gives the stated positive finite-clock lower bound. Intersecting these
   finitely many eventual tails produces one tail valid for every S.

## Audit

Verified theorem:
[`RHTower.exists_mobiusDivisorLogClockSpanDebt`](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorDelayedClockSpanDebt.lean).

`lake env lean /tmp/hgt-clock-span.lean` and
`lake build GaloisForLFunctions.RHTower.MobiusDivisorDelayedClockSpanDebt`
both passed without new-leaf warnings. The axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into
`RHTower.lean`; no full or umbrella build ran. Corpus index refresh passed.
Repository lint reports four unrelated umbrella-reachability errors;
none concerns this leaf. Owned processes exited and scratch files were removed.

## Separate moving-window upgrade

[Uniform finite-clock debt](../3-formalized/rh-moving-helper-clock-debt.md)
now provides the separate finite-counting argument required above.
`exists_mobiusDivisorMovingClockSpanDebt` produces one cutoff M0 before
all window positions tau, giving the lower bound for every M>=M0 and
every tau>=T simultaneously. Its unchanged-cofactor argument preserves
the original weight and counts multiples of only the actual helpers.
This stronger theorem still does not exclude broader helper sets or prove
paid exhaustive continuation.
