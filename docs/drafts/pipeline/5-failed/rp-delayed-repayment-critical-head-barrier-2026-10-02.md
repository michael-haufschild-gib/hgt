# RP: delayed net repayment forces a critical head spike

- **ID:** RP-27
- **Stage:** 5-failed
- **Type:** FALSIFIED (uniformly budgeted delayed repair; not Route RP or RH)
- **Source:** Route RP; `MobiusDivisorInheritedPrimeInsertionProducer`, physical finite-core Mellin identity, and uniform local source regularity.
- **Candidate under test:** Repair an actual inherited omitted-prime debt arbitrarily late while retaining one bound on the prepared core's critical action at every later cutoff.
- **Novelty:** Corpus extension; external novelty unaudited.

## Hard problem and scope

The native RP floor requires joint signed cancellation. RP-26 deletes the complete product region but leaves its complementary source and smooth term unpaid. A proposed way to assemble the remaining cancellation is delayed preparation by fresh prime helpers followed by insertion of an omitted prime. Existing corpus theorems can reverse the marginal insertion sign, but distinguish that operation from net repayment of the old debt. Their necessary reciprocal-prime mass bound did not itself imply an actual energy spike.

The present argument supplies that missing implication. It applies to every sufficiently late helper set, with no cardinality, upper prime window, inverse-square-root mass, or phase restriction. It does not exclude a construction that couples the active core to its current cutoff and avoids these later fixed-core excursions. It is not an RH falsification.

## Positive survivor: reciprocal Euler moment stability

Let H_P(x) be the literal `mobiusDivisorContinuousHead P x`. Define

    I(P) = integral_0^infinity x^(-5/2) H_P(x) dx.

Absolute physical Mellin convergence at s=3/2 and the exact finite-prime multiplier give

    I(P) = I(empty) * product_{p in P}(1-1/p) > 0.

The source I(empty) is positive because the actual unit head is nonnegative and strictly positive on (1,2). This is not a postulated source sign for processed heads.

If H_P=H_Q on x<=X, X>=1, and |H_P(x)|<=C*x, |H_Q(x)|<=D*x on x>X, then

    |I(P)-I(Q)| <= 2(C+D)/sqrt(X).

Proof: the exact difference is its tail integral beyond X; bound its integrand by (C+D)*x^(-3/2) and integrate. This is a positive stability law for the reciprocal Euler density in the critical head norm.

For disjoint fresh helpers S with p>X, exact source locality gives H_(P union S)=H_P on x<=X, while Euler factorization and 1-u<=exp(-u) give

    I(P) * (1-exp(-sum_{p in S}1/p)) <= 2(C+D)/sqrt(X).

Thus a fixed positive reciprocal mass is incompatible with arbitrarily late admission under a fixed linear envelope for the prepared head.

## Literal discrete head spike

Suppose the retained head square obeys

    selectionFibre(M,Q,empty)^2 <= K*M^2  for every integer M>X.

For x>X put N=ceil(x). The corpus's uniform local regularity gives

    |H_Q(x)-H_Q(N)| <= 24*sqrt(N),

and the exact integer weld identifies H_Q(N) with the retained source fibre. Since N<=2x,

    |H_Q(x)| <= 2*(sqrt(K)+24)*x.

The fixed parent has its existing square-root envelope, hence a linear envelope on x>=1. Fix eta>0 and K>=0. The positive number I(P)*(1-exp(-eta)) then exceeds the preceding tail ceiling at every sufficiently large admission horizon X. Consequently every fresh disjoint helper set with sum 1/p>=eta forces some integer M>X with

    selectionFibre(M,P union S,empty)^2 > K*M^2.

The full retained source energy is at least this head square. The argument therefore proves more than growth in unprocessed fibres or growth of a sufficient upper-bound constant: the literal prepared head itself exceeds the critical budget.

## Actual inherited debts

The corpus produces, over every even nonempty inherited prime core P and beyond every prescribed prime threshold, an actual omitted prime r and delta,eta>0. Its asymptotic fixed-core energy coefficient at insert(r,P) exceeds the old coefficient by 2*delta. Every sufficiently delayed helper family achieving half repayment requires

    eta < sum_{p in S}1/(p+1) <= sum_{p in S}1/p.

Choose the delay beyond both the new head-spike threshold and every prime of insert(r,P). The helpers are then disjoint from that parent. The positive stability law forces a later integer M>exp(tau) at which the prepared retained head square exceeds K*M^2. This holds for every proposed K, with the deadline chosen before the helper set.

## No-go closure

- **Exact obstruction:** Arbitrarily delayed successful net half repayment cannot preserve one all-later-cutoff critical head budget, even with unrestricted helper mass.
- **Strongest positive survivor:** Positive exact reciprocal Euler moment, its quantitative tail stability law, and an unavoidable later spike in the actual retained head for every fresh helper family of fixed positive reciprocal mass.
- **What changes:** Marginal insertion sign control cannot be promoted to uniformly budgeted delayed net repayment. The surviving construction must coordinate prime admission and current cutoff; asymptotic sign reversal after a remote preparation does not supply that coordination.
- **Limit:** Neither the native history floor nor RH is proved or falsified. No general impossibility of timely signed assembly follows.
- **Status:** Dependency-closed paper proof and Lean formalization complete. `RoutePReciprocalHeadMoment.lean` (323 lines, seven public theorems) and `RoutePDelayedRepaymentHeadBarrier.lean` (78 lines, one public theorem) both passed foreground `lake --old env lean <leaf> -o <olean>` audits with exit 0 and no diagnostics. All eight public theorem axiom lists, checked in a separate `/tmp` audit, are exactly `[propext, Classical.choice, Quot.sound]`. Both leaves are wired once into the RHTower umbrella; no umbrella build ran. Global lint fails on twelve unrelated unreachable modules; neither leaf is flagged.

## Log

- 2026-10-02 — Formulated actual-energy conjecture, proved moment stability, strengthened the conclusion to the retained head itself, and checked the base production leaf.
- 2026-10-02 — Specialized to the actual inherited-debt producer; both final leaf audits and all eight axiom audits passed. Retired only the delayed uniform-budget mechanism, retaining the positive exact moment and stability law. Timely simultaneous core/cutoff assembly remains the next hard problem.
