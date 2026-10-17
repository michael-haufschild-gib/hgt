# PA Bernstein index measures recover the dominant divisor

Status: FORMALIZED. Contribution 15, counted once. Verified count: 15/100
when the user cleared the goal. All 15 leaves and the complete public
axiom/signature audit pass; repository-wide lint limitations are recorded below.

## Exact result

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

The new observable is the coefficient-index measure, at this ONE fixed radius:

    nu_n = sqrt(n)/(B^2)^n * sum_(i=0)^n |b(n,i)|^2 delta_(i/n),
    nu_infinity = sum_(u in U) |C_u|^2 kappa_u delta_(p_u).

The finite positive measures converge weakly. More strongly, the displayed
weighted-sum limit holds for every bounded real test continuous at the finite
set of occupation points. Every measurable window whose frontier avoids
these points has the corresponding mass limit. Actual source energy is
positive in every degree, and the normalized probability measures converge
weakly to the normalized positive divisor measure.

Exact reconstruction follows:

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

The principal theorem has no premises and states RH or the complete
source-divisor law above:
no existence of an off-line zero is asserted, and no source positivity,
admission, simple-zero assumption or spacing hypothesis is assumed. The
actual source supplies the finite packet and every required separation.

## Significance

PA knows each fixed coefficient index is eventually nonnegative, while its
possible obstruction lies at growing indices. Existing scalar purity
asymptotics show growth but do not locate it in the coefficient packet. The
proved measure converts that unresolved growing-order direction into a
canonical finite positive observable that reconstructs dominant divisor
coordinates and multiplicities from actual source coefficients.

This is not a new RH equivalence or a claim to prove PA's missing sign. A
mere variance bound, total-energy asymptotic or generic weak-limit helper
is not counted separately. The full actual-source reconstruction supplies
one structural result after the comparison and audits below.

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
   therefore gives the normalized probability limit. The actual PA source
   has positive total packet energy in every degree: its positive zeroth
   moment and the Bernstein partition identity imply this by Cauchy--Schwarz.
   The probability law normalizes unscaled packet energy, including degree zero.

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

## Formal verification

Principal declaration:
`RHTower.primeArchEndpointBernstein_index_divisor_tomography`, in
`formal/GaloisForLFunctions/RHTower/XiBernsteinIndexDivisorTomography.lean`.
Its audited statement is premise-free: RH or the full superunit alternative.

All 15 leaves passed targeted `lake --old env lean -j 1 -o ...` compilation.
A single /tmp audit imported the final root and checked all 76 named public
axiom lists, all 63 theorem/lemma signatures, and all 13 definitions. Exit 0;
no diagnostics; every axiom list contains only `propext`, `Classical.choice`,
`Quot.sound`. The finite packet leaf's compilation emitted nonfatal `ring`
advice; its complete signatures and axiom lists passed the final audit.

All source fingerprints below match their audited files; every object exists
and is newer than its source; every module is imported exactly once in its
area umbrella. No forbidden declaration token occurs in these leaves, and
all 76 declarations appear in the generated API index. No umbrella build or
heartbeat increase was used.

The index command completed and was refreshed after concurrent source changes.
Normal lint and generated-file lint both exited 1. The final generated-file
check reports 22 concurrent modules outside this contribution as unreachable,
plus stale `formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md`; it also reports
381 existing size warnings. The concurrent module set changed between checks,
so another index regeneration is not represented as a stable global pass.
There is no diagnostic against these 15 leaves. Foreign modules were neither
edited nor wired to conceal the repository-wide failure.

Final unreachable modules (all prefixed `GaloisForLFunctions.`):

- `RHTower.OddSectorGroundCompleteDivisors`
- `RHTower.OddSectorGroundDivisionCalculus`
- `RHTower.OddSectorGroundDivisionEigenvectors`
- `RHTower.OddSectorGroundDivisionOperator`
- `RHTower.OddSectorGroundOriginInterpolation`
- `RHTower.OddSectorGroundSpectralQuotient`
- `HTGeometry.CoerciveCompactSpectralVanishing`
- `HTGeometry.CompactFormNegativeCapacity`
- `HTGeometry.CompactPositiveFormGap`
- `HTGeometry.FiniteRankTraceDeterminant`
- `HTGeometry.HolomorphicRieszFamily`
- `HTGeometry.OuterSpectralContinuation`
- `HTGeometry.QuasiCompactSpectralCircle`
- `HTGeometry.RieszProjectionPowerCalculus`
- `HTGeometry.SymbolicHolderSpace`
- `HTGeometry.SymbolicLevelSpaces`
- `HTGeometry.SymbolicRuellePollicottBounds`
- `HTGeometry.SymbolicShiftSpace`
- `HTGeometry.SymbolicTraceSplitting`
- `HTGeometry.SymbolicTransferBounds`
- `HTGeometry.SymbolicTransferHolomorphy`
- `HTGeometry.SymbolicTransferOperator`

Audited source fingerprints (SHA-256):

| Module | Public declarations | SHA-256 |
|---|---:|---|
| `HTGeometry.FinitePacketSecondMomentConcentration` | 3 | `189a9ae3c359b092afe49f76fa8ee3c1233233d1da0c1ebb3908b2647bab46dd` |
| `HTGeometry.FinitePacketWeightedPairing` | 2 | `9d621f6db200c56893ba8e8e407eaab00362a86ab24b935073c1cb105d798726` |
| `HTGeometry.FiniteRealAtomicMeasure` | 6 | `5cfdf91bc9b6dbed284be90e20744e3853e0c39a7cbf524a5d8233b44ff3cd6f` |
| `RHTower.BernsteinAffineRowIndexConcentration` | 10 | `b559b878bae685e0e55735a4834563dab155b15afb5982c2935c0fcbf6cba444` |
| `RHTower.BernsteinOccupationRigidity` | 5 | `cee88403952fdad7b9a2eca130ef3f22eaa69d8ed9e0db9fcdbc9937dd997215` |
| `RHTower.FiniteBernsteinPacketIndexAsymptotic` | 6 | `468b0c0247ddf88fcf54cc273811b7cbc64cbf0a1d0269c03b5f79a883fe49f5` |
| `RHTower.FiniteComplexPacketWeightedPerturbation` | 2 | `b50601c3370ee0d3b7bfd87502a70cab044bc1d41dc033760a9d5c908a56a9a9` |
| `RHTower.AtomicBernsteinPacketIndexAsymptotic` | 2 | `0c0fae5c75bfd481d907e0b0eff64ae6fc52d8da1b3d3046598d205b4f445ebf` |
| `RHTower.XiBernsteinOccupationFibres` | 9 | `7934ee8f29197164bfaa762bb44cca2a0bce9fee675335a2f777add3522edc40` |
| `RHTower.XiBernsteinOccupationWeights` | 5 | `bf6737780b2ff74e7b07a41574e0a54b08a037be4e1cc17d916417c9b4aeb3e3` |
| `RHTower.XiBernsteinIndexAsymptotic` | 4 | `feaa2e6aa56c969073d4996fa8f8d785e46af12ae611688cf0a45c0345708f43` |
| `RHTower.XiBernsteinIndexNormalization` | 7 | `ab316ee6fabb0b2e2af051e80a640a6b3ccfac5631696245da98d940c01c45cb` |
| `RHTower.XiBernsteinIndexMeasures` | 7 | `1d39cb1f8d6b9062ddd691976ff10a63a45ac01d75af347c86f43ab738a8cda0` |
| `RHTower.XiBernsteinIndexProbability` | 7 | `182bcff43561e28daf5c8840b150df0a1688f49cc1868e26f7ff93338b1e37c4` |
| `RHTower.XiBernsteinIndexDivisorTomography` | 1 | `d428be398c6f388cae6a5dd885c2ee0488eb4396881113c400d4d2078a603ae3` |

## Significance and boundary audit

The structural result is fixed-scale inverse observation of the complete
dominant reciprocal-square divisor from the actual source's coefficient
indices, including its multiplicities. The new information is absent from a
scalar purity limit and from moment recovery requiring variation of the
radius. Weighted mixed terms are an essential obstacle: coincident occupation
points do not permit an inference from the unweighted pairing limit alone.

Cross-route inputs are concrete: PA's exact atomic source and strict maximal
packet gap; Deninger's multiplicity-exact conjugation equivalence; the proved
binomial probability/variance law and finite pairing concentration; and the
actual theta-Gibbs positive zeroth source moment for all-degree probability
normalization. No additional source positivity or admission is assumed.

The whole reconstruction is counted as ONE verified result. The 76 public declarations, including 13 definitions, are supporting
parts, not separate contributions. No count for the variance estimate, weak
topology packaging, probability normalization, or the growth-rate bridge.

The conclusion identifies only the complete dominant packet in the superunit
alternative, modulo conjugation. It does not recover subdominant off-line
coordinates, supply a finite truncation decision procedure, identify a single
Xi-zero multiplicity with its reciprocal-square fibre cardinality, prove the
RH branch has a finite maximal packet, or establish PA's missing source sign
or Sonin susceptibility representation. External novelty is unassessed; local
comparison coverage and its partial semantic search are recorded above.
