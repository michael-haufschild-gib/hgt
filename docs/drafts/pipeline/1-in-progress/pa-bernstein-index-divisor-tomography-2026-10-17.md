# PA Bernstein index measures recover the dominant divisor

Status: CANDIDATE 15, NOT COUNTED. Paper mechanism and attacks recorded below.
Lean formalization and final significance audit pending. Goal remains 14/100.

## Exact proposed result

Fix the actual PA endpoint radius R and its real source-defined Bernstein
coefficients b(n,i). If an off-line Xi zero exists, let B>1 be the maximal
amplitude of the actual normalized reciprocal-square coordinates
u_q=xiZeroCopyReciprocalSquare(q)/R. Existing corpus results supply a finite
nonempty complete maximal packet D and a strict complementary amplitude
bound beta<B. Aggregate equal coordinates before taking any norm:

    U = {u_q : q in D},
    C_u = sum_(q in D, u_q=u) xiZeroCopyReciprocalSquare(q),
    p_u = |u|/(|u|+|1-u|),
    kappa_u = bernsteinAffineRowHalfOrderConstant(u)>0.

The new target is the coefficient-index measure, at this ONE fixed radius:

    nu_n = sqrt(n)/(B^2)^n * sum_(i=0)^n |b(n,i)|^2 delta_(i/n),
    nu_infinity = sum_(u in U) |C_u|^2 kappa_u delta_(p_u).

Prove weak convergence of the finite positive measures, equivalently the
displayed weighted-sum limit for every continuous real test on [0,1]. Prove
the corresponding limit for interval windows whose boundaries avoid all
p_u. The total limiting mass is positive, so normalization gives convergence
of the probability distributions obtained from the actual source packets.

Then prove exact reconstruction, rather than stopping at concentration:

    Re u = [1+B^2(2p_u-1)]/2,
    (Im u)^2 = B^2 p_u^2 - (Re u)^2.

At fixed B, equality of p values is equivalent to equality of coordinates up
to complex conjugation. Thus the support of nu_infinity recovers precisely
the maximal reciprocal-square divisor modulo conjugation. Recover B from
the already established nth-root growth of total source purity.

For the actual source, let N_u be the number of multiplicity-counted copies
in the reciprocal-square fibre. Then C_u=R*u*N_u. Conjugation preserves the
complete maximal packet and gives N_conj(u)=N_u. Since B>1, Im u is nonzero,
so a limiting atom at p has weight

    W_p = 2 R^2 B^2 p^2 N_u^2 kappa_u.

Consequently its observed weight determines N_u uniquely as a positive
integer. Claim only reciprocal-square fibre multiplicity unless the further
conversion to a single Xi zero's multiplicity is separately proved.

The theorem is a conditional branch of an unconditional source-divisor law:
no existence of an off-line zero is asserted, and no source positivity,
admission, simple-zero assumption or spacing hypothesis is assumed. The
actual source supplies the finite packet and every required separation.

## Why this may meet the requested bar

PA knows each fixed coefficient index is eventually nonnegative, while its
possible obstruction lies at growing indices. Existing scalar purity
asymptotics show growth but do not locate it in the coefficient packet. The
proposed measure converts that unresolved growing-order direction into a
canonical finite positive observable that reconstructs dominant divisor
coordinates and multiplicities from actual source coefficients.

This is not a new RH equivalence or a claim to prove PA's missing sign. A
mere variance bound, total-energy asymptotic or generic weak-limit helper
would not be counted. Count only if the full actual-source reconstruction
and independent significance survive final comparison.

## Local-corpus comparison

- `BernsteinAffineRowDiagonalAsymptotic`: sharp unweighted half-order limit
  for one row; no coefficient-index distribution.
- `FiniteBernsteinCoordinatePacketAsymptotic`: finite maximal packet total
  energy with exponentially gapped mixed terms; no test-weighted limit.
- `AtomicBernsteinMaximalPacketAsymptotic` and
  `XiBernsteinPurityHalfOrderAsymptotic`: transfer total energy to the full
  actual source, including the infinite complementary packet.
- `ScaleCovariantBernsteinPurityJet` and `...PurityJacobian`: recover source
  moments by varying the scale and observing a whole polynomial jet.
  This target fixes the scale and uses index-resolved large-degree energy.
- `ScaleCovariantBernsteinAbelTomography` and `...GibbsCorollary`: scalar
  amplitude, Abel radius, transverse envelope, and scale jets. Inspected
  conclusions do not identify the weak index measure and its atomic weights.
- `XiSourceEntropySeparatedSourceReconstruction`: a different Weil/source
  orientation vector; no Bernstein index measure.
- Weil log-shift midpoint/edge binomial results transfer probability
  concentration to another actual route, but specialize to the symmetric
  binomial profile. The present occupation parameter is arbitrary p_u.
- Mathlib `Analysis/SpecialFunctions/Bernstein` provides proved positivity,
  total probability and exact variance. Do NOT use
  `Probability/Distributions/Binomial.variance_of_hasLaw_binomial`, whose
  declaration in this toolchain is `proof_wanted`.

A documented deep whole-corpus search for the exact localization/recovery
mechanism covered 61,578 Lean files and 1,084,600 declarations. It was partial
because final judging returned malformed JSON, with semantic coverage not
measured. Returned L1/purity inequalities and generic variance names do not
prove this target. Direct searches and the comparisons above remain necessary;
no exhaustive semantic or external novelty claim.

## Dependency-closed paper proof

1. **One affine row is a tilted binomial row.** For u!=0,1 set
   a=|u|, b=|1-u|, B_u=a+b and p=a/B_u. Then

       |choose(n,i) u^i (1-u)^(n-i)| / B_u^n
         = choose(n,i) p^i (1-p)^(n-i) = P_(n,p)(i).

   These weights lie in [0,1], sum to one, and satisfy
   sum_i (i/n-p)^2 P_(n,p)(i)=p(1-p)/n for n>0.

2. **Squared rows still concentrate.** Since P^2<=P,

       sqrt(n) sum_i (i/n-p)^2 P_(n,p)(i)^2
         <= p(1-p)/sqrt(n) -> 0.

   The total mass sqrt(n) sum_i P^2 tends to kappa_u by the existing sharp
   diagonal theorem. For any bounded continuous g on [0,1], split the sum
   into |i/n-p|<delta and its complement. On the first, continuity makes
   |g(i/n)-g(p)| small; on the second, the second moment divided by delta^2
   controls the mass. This proves both the weighted mass limit and

       sqrt(n) sum_i P^2 |g(i/n)-g(p)|^2 -> 0.

   Bounded tests continuous only at the finitely many p_u also work, which
   includes interval indicators whose boundaries avoid those points.

3. **Mixed modes vanish with test weights.** The existing strict mixed-mode
   gap proves sqrt(n)/B^(2n) sum_i r_u(n,i) conj(r_v(n,i))->0 for u!=v.
   Subtract g(p_u) times this unweighted expression. Cauchy--Schwarz bounds
   the remainder by the square root of the error energy in step 2 times
   the square root of the normalized v-row energy. The first tends to zero,
   the second has a finite limit. This works even if p_u=p_v, so conjugate
   modes cannot interfere with the limiting positive atomic weights.

4. **Finite packet.** Expand |sum_u C_u r_u|^2 and pass to the limit in the
   finite double sum. Step 2 gives the diagonal entries; step 3 kills every
   off-diagonal entry. The limit is sum_u |C_u|^2 kappa_u g(p_u).

5. **Infinite actual source.** The exact existing decomposition writes the
   source packet as its finite aggregated maximal packet plus a remainder
   with l1 norm <=A beta^n. The main packet has l1 norm <=M B^n.
   For |g|<=G, the weighted energy difference is at most

       G [2 M A (B beta)^n + A^2 beta^(2n)].

   Multiplication by sqrt(n)/B^(2n) makes both terms vanish since beta<B.
   Thus no truncation, summability or zero-tail hypothesis is left unproved.

6. **Source-defined finite measure and probability law.** Finite sums of
   nonnegative weighted Dirac masses define nu_n. Continuous tests give weak
   convergence on the compact interval. Its limiting mass L is the existing
   strictly positive maximal-packet constant. Division by total mass
   therefore gives the normalized probability limit. Early zero packets may
   be defined separately; they do not affect the limit. For the actual PA
   source, its nonzero zeroth moment also excludes zero total packet energy.

7. **Coordinates and multiplicities.** The identities |u|=Bp and
   |1-u|=B(1-p) imply the two real equations above. Equal B,p therefore force
   equal real parts and equal squared imaginary parts, hence u=v or conj(v).
   Every maximal coordinate is nonreal because real actual coordinates are
   positive and inside the calibrated interval, so their amplitude is one.
   The actual conjugation equivalence on XiZeroCopy preserves amplitude,
   hence preserves D by the strict complementary gap. Its restriction gives
   a bijection between conjugate fibres. Their coefficients are R*u*N_u
   and its conjugate; their kappa values coincide. Adding exactly these two
   positive contributions yields W_p. Every factor outside N_u^2 is known
   and positive, and squaring is injective on positive natural numbers.

## Attacks and boundaries

- Taking the strong limit of total energies alone does not imply this weak
  measure law; weighted mixed terms need step 3.
- Summing individual copy energies before aggregating coordinates gives the
  wrong multiplicity dependence. Aggregate first; fibre weights are squared.
- p alone cannot distinguish u from conj(u). State and prove that exact
  ambiguity, rather than claiming full complex phase recovery.
- Different maximal coordinates can have the same p. Step 3 still removes
  cross terms; geometry says this collision is exactly conjugation.
- The fixed-index eventual-positivity theorem does not contradict interior
  concentration at i about p*n.
- Do not claim the RH branch has the same finite-packet law: under RH B=1
  and there may be infinitely many maximal coordinates, without this gap.
- No numerical experiment, RH proof, external novelty, or finite-prefix
  decision procedure is claimed.

## Formalization plan

Verify the Mathlib probability/variance APIs in /tmp. Formalize the normalized
binomial square concentration, weighted mixed-mode transfer, actual complete
packet specialization, finite-measure/test law, and exact fibre recovery in
small leaves. One owned Lean process, normal heartbeats, no umbrella build.
Then audit every new named public declaration, exact signatures and source
definitions, fingerprints and import wiring; run index and both lint modes.
Final significance comparison precedes any contribution count.

## Formal progress

- `HTGeometry/FinitePacketSecondMomentConcentration.lean` added and compiled
  with `lake --old env lean -j 1 -o ...`. Three public lemmas: bounded local
  quadratic modulus, squared test-error convergence, weighted test convergence.
  Index types may vary with degree; tests need continuity only at the centre.
  This is a helper, not a separately countable result.
- Mathlib Bernstein probability and variance checked in `/tmp`; both use only
  standard axioms. The row occupation/concentration and weighted pairing
  arguments are being developed in owned `/tmp/hgt-root-cr15-*` scratches.
- Actual source specialization, divisor recovery, final axiom/import/lint
  audits and significance decision remain open. Verified goal count: 14/100.
- `RHTower/BernsteinAffineRowIndexConcentration.lean` and
  `HTGeometry/FinitePacketWeightedPairing.lean` now pass targeted compilation
  with their objects written. The first proves the exact binomial modulus,
  vanishing normalized index variance and both weighted single-row limits.
  The second proves weighted mixed-pair transport without requiring distinct
  concentration points. Neither is counted separately.
- `RHTower/BernsteinOccupationRigidity.lean` contains the exact coordinate
  formulas and conjugation ambiguity; its final targeted check is pending.
  Finite-packet assembly and bounded-test tail transfer remain in scratches.
