# Wall 13: exact cycle-detection order

- **ID:** BSU-W13-MINIMAL-CYCLE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** BiScaleUncertainty; no RH work.
- **Statement:** for the constructed smooth seed and every gap T>2, opposite nonzero copy amplitudes first become visible at closed-product order floor(T)+1.

## Exact theorem

Construct the literal smooth bump b with inner radius 1/4 and outer radius 1/2. Its autocorrelation h is positive exactly on (-1,1), zero at and outside the endpoints, and has positive mass and normalized polar moment.

For every T in (2,infinity), a in R and natural n, set f_a(u)=b(u)-a*b(u-T). Then

    exists l : List R,
      length(l)=n and sum(l)=0 and
      product(h_f_-a(x), x in l) != product(h_f_a(x), x in l)
    iff a!=0 and T<n.

`SharpCycle.detects_iff` proves this classification, including zero amplitude and every integer boundary. `detects_iff_floor`, `firstOrder_detects_iff` and `lower_orders_agree` give the exact first order floor(T)+1. All support, smoothness, positivity and moment inputs are established for the actual constructed source; no analytic estimate is assumed.

At a=exp(-T/2), `sharp_polar_pair` constructs smooth compact sources f,g with equal positive mass, normalized polar moment zero for f and strictly positive for g, and the same exact detection threshold. More precisely, the positive moment equals twice the seed's normalized polar moment.

## Dependency-closed paper proof

1. The bump is nonnegative and positive exactly for |u|<1/2. If |x|>=1, nonzero b(u)b(u+x) would imply |x|<=|u|+|u+x|<1. If |x|<1, the integrand is positive at u=-x/2; continuity, nonnegativity and compact support make its integral strictly positive. Exponential-moment factorization gives a positive polar moment.
2. At gap T>2 the correlation has three disjoint open packets, centered at 0 and +/-T. Reversing a multiplies the packet value by (-1)^c, where c is its integer packet index. Every nonzero factor has strict packet error |x-c*T|<1.
3. For a nonempty nonzero closed product of length n and total packet charge Q, summing the strict errors gives |Q|T<n. A distinguishing product has Q!=0, so T<=|Q|T<n. Zero factors and empty lists cannot distinguish signs.
4. For n>T, choose one lag T-T/n and n-1 lags -T/n. Their sum is zero; every packet error has magnitude T/n<1. Exactly one factor is outer, the rest central. For a!=0 all factors are nonzero and total charge is one, so reversing a negates the product. Endpoint n=T fails because the seed correlation vanishes there.
5. Substitute a=exp(-T/2) in the proved distant-copy polar formula. The minus copy is polar-neutral; the opposite copy has normalized moment 2*normalizedPolarMoment(b)>0. Their masses coincide.

## Lean package

Namespace: `GaloisForLFunctions.BiScaleUncertainty.SharpCycle`.

- `UnitCorrelationBump.lean`: literal seed, exact open correlation support, positive mass and polar moment; 14 public declarations.
- `StrictCopyCycleCharge.lean`: actual separated source, packet sign law, strict error and order obstruction; 12 public declarations.
- `SharpCycleDetectionOrder.lean`: explicit detector, exact classification, first order and polar-distinct pair; 15 public declarations.

All files are under `formal/GaloisForLFunctions/BiScaleUncertainty/` and imported exactly once by the field umbrella. Parents include the [closed-cycle obstruction and complete recovery package](wall13-closed-cycle-order-obstruction.md) and `DistantCopyPolarTopology.lean`.

## Corpus and verification evidence

- Prior corpus searches `/tmp/bsu-wall13-cycle-threshold-search.json` and `/tmp/bsu-wall13-minimal-order-frontier.json` each inspected all 20 candidate and 20 source statements. They supplied related support/correlation parents, not the exact sharp-order theorem. Semantic coverage unmeasured; background refresh incomplete. No exhaustive absence or novelty claim.
- Installed API probe `/tmp/bsu_wall13_sharp_api.lean` passed. No numerical experiments, added axioms, heartbeat increases or full builds.
- Each leaf passed `lake --old env lean` with an explicit output file. Final named-leaf audit `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SharpCycleDetectionOrder.lean` passed with empty `/tmp/bsu-wall13-sharp-final.log`.
- Complete public-signature and axiom audit: **41/41 declarations, 32 theorems and 9 definitions**, all using only `[propext, Classical.choice, Quot.sound]`. Scratch `/tmp/bsu_wall13_sharp_axioms.lean`; output `/tmp/bsu-wall13-sharp-axioms.log`; source hashes and export list `/tmp/bsu-wall13-sharp-manifest.json`.
- Successful leaf logs: `/tmp/bsu-wall13-unit-bump-resumed.log`, `/tmp/bsu-wall13-strict-charge-r2.log`, `/tmp/bsu-wall13-sharp-order-r2.log`. All empty. Every leaf retained its checked source hash through the audit.
- Index refresh passed; documented lexical search discovers the classification and polar-pair capstones. Logs `/tmp/bsu-wall13-sharp-index.log` and `/tmp/bsu-wall13-sharp-index-search.json`.
- Global lint at this checkpoint exited 1: four concurrent, unrelated unwired leaves (`ClampedPrimeLogResummation`, `CompactAutocorrelationPolarMoment`, `FactorialBiNullPolarSign`, `FactorialRampDiagonalIdentity`) and 381 existing large-file warnings. No lint error belongs to this package. Log `/tmp/bsu-wall13-sharp-lint.log`.
- Both field READMEs and the walls ledger match their starting hashes; scoped whitespace checks passed. Earlier interrupted checks were not counted as validation. No commit or push performed.

## Mathematical boundary and next conjecture

The result gives a sharp relationship between spatial separation and the order of signed correlation information. It proves neither a sharp Gram-determinant threshold nor full-Gram recovery for arbitrary sources, stable recovery, a coercive energy bound, or a compatible transfer between pointwise and Bochner cones. **Wall 13 remains open; the broader all-walls goal remains active.**

Next: [sharp Gram-determinant detection order](../1-in-progress/wall13-sharp-gram-order.md). The proposed equally spaced sample configuration gives a chordless cycle; the determinant difference should reduce to two oriented cycles, equivalently to a triangular cofactor after expanding the endpoint rows. This successor is a conjecture awaiting Lean verification.
