# Test whether quartet surgery preserves every finite marked monodromy image

- **ID:** RH-XIQFM-20261007
- **Stage:** 1-in-progress
- **Parent:** `../3-formalized/xi-marked-finite-monodromy.md`
- **Status:** finite-divisor extension proved on paper below; Lean implementation begins with analytic inputs; full monodromy endpoint remains unformalized; novelty not certified

## Exact candidate

Reuse the corpus's centered quartet gauge with a=1/6,b=1, normalized at0:

    P(s) = (((s-1/2)-1/6)^2+1)*(((s-1/2)+1/6)^2+1),
    P(0) = 130/81,
    F(s) = xi(s)*P(s)/P(0).

F has the actual known off-line quartet 1/3±i,2/3±i, reflection and real
structure, endpoint normalization F(0)=F(1)=1/2, and positive real values.
Test whether EVERY finite real-slope marked family F(s)*exp(-a*s) has the
same finite-group image classification Delta_A as actual Xi, and the same
discrete normal closure. If proved, this would precisely limit conclusions
based solely on those image invariants. It would not equate arithmetic
source identities, individual labeled loops, divisor locations or all jets.

## Mechanism requiring audit

All added roots lie in the critical strip. For Re(s)>1,
Re(P'/P)=sum_r Re(1/(s-r))>0, so the existing far-right lower bound on
Re(xi'/xi) also bounds Re(F'/F). Polynomial multiplication preserves the
needed real-axis superexponential growth; the half-plane Schottky argument
should give nonzero marked values arbitrarily far right. The logarithmic
inverse-disk proof should then apply to F. It has simple Xi zeros at high
critical heights outside the finite added quartet. These are the exact
inputs to the now-audited packet/finite-image proof. They must be discharged
for F, rather than recorded as permanent hypotheses of the endpoint.

## Corpus and scope audit

Query `Xi polynomial multiplier off critical line zeros logarithmic derivative
inverse islands monodromy`, budget90, partial=false, inventory68272; all20
candidate and20 source statements inspected. Crucial existing result:
`RHTower/CompactOpenKolchinWardChargeEscape.lean` lines1--180 read. The corpus
already constructs normalized escaping quartet gauges, proves entire and
hypertranscendental structure, both symmetries, added off-line zeros and
exact rational logarithmic corrections. Its later declaration inventory
also includes preservation of the full differential shift matroid and fixed
Ward mass. Reuse this family; do not claim a new quartet countermodel.

`HypertranscendentalQuartetWardIndex` declaration inventory identifies an
important boundary: quartet surgery changes the endpoint logarithmic
derivative, with an exact nonzero source-weighted Ward term. Lines205--339
have now been read: positivity of the explicit weight proves the derivative
changes even after constant normalization. Thus finite monodromy invisibility concerns that
observation only, not equality of the actual arithmetic source or its
endpoint derivative. The finite-image extension itself remains unproved.

Known infrastructure: `XiPolynomialLeftFactors` imports the actual generic
`HTGeometry/SchottkyHalfPlaneGrowth.lean`; use it rather than an invented
half-plane API. `XiLogarithmicIslands` uses HalfPlaneLogarithm and
HolomorphicExpandingInverse. No existing source module has been modified
for this candidate. Finish its dependency-closed paper and external audits
before starting implementation.

## Stronger exact statement and dependency-closed paper proof

Let r_1,...,r_n be arbitrary nonzero complex numbers, with repetitions allowed,
including the empty list. Set Q_r(s)=product_j(1-s/r_j) and F_r=xi*Q_r.
For every finite set A of real slopes define the actual source
U_r,A={s:F_r(s)≠0 and F_r(s)exp(-a*s)≠-1 for every a in A}, based at0.
Since F_r(0)=1/2, every target coordinate is based at1/2. Let mu_r,A be the
induced map to Gamma_A=product_a pi_1(C\{0,-1},1/2), and Delta_A the subgroup
with common zero winding. Claim: every homomorphism f from Gamma_A to any
finite group satisfies f(image mu_r,A)=f(Delta_A), and
normalClosure(image mu_r,A)=Delta_A. The concrete normalized quartet above
is one instance. This parametrization covers normalized nonzero polynomials
whose value at0 is1 by complex factorization; that identification is not
required for the first formal endpoint.

1. **Exact logarithmic correction.** Outside the finite list of roots,
   Q_r'/Q_r=sum_j 1/(s-r_j). For Re(s)>max_j Re(r_j), every summand has
   nonnegative real part. Q_r is entire and nonzero there. Existing actual
   Xi bounds therefore give Re(F_r'/F_r)≥B uniformly on a sufficiently far
   right half-plane, for every real B. Empty products cause no exception.
2. **Growth and actual value occurrence.** On the real ray x≥2 max_j|r_j|,
   |x-r_j|≥x-|r_j|≥|r_j|, hence |Q_r(x)|≥1. For any tilt a, an exponential
   ray bound for F_r exp(-a*s) on any shifted ray would bound tilted Xi on
   its terminal part. Existing xi_superlinear_ray_above contradicts this
   directly (discarding a finite initial interval). If any nonzero value w
   were omitted on a far-right half-plane, both0 andw would be omitted;
   SchottkyHalfPlaneGrowth would supply that impossible exponential bound.
   Thus every w≠0 occurs arbitrarily far right.
3. **Logarithmic inverse islands.** Choose Re(F_r'/F_r)-a≥1 beyond T≥R.
   Choose b with Re(b)>T+2M+2 and F_r(b)exp(-a*b)=1 by step2. Integrate
   F_r'/F_r-a on the half-plane, normalized to0 atb. The scalar ODE gives
   exp(P)=F_r exp(-a*s). Re(P')≥1 and the existing expanding inverse-disk
   theorem give h on B(0,M), Re(h)>R and F_r(h(w))exp(-a*h(w))=exp(w).
   No assertion about bounded inverse singular values or global tracts is used.
4. **Separated packets.** For b≠a, the ratio of two marks at h(w) is
   exp((a-b)h(w)). On a bounded logarithmic disk and sufficiently far-right
   island this makes each other mark uniformly inside or outside the unit
   circle. Closed logarithmic lifts of a finite packet with zero winding
   therefore realize the selected target packet while all other coordinates
   contract. This is precisely the proof in XiMarkedLoopPackets, with F_r
   replacing xi and step3 replacing its one analytic input.
5. **Source topology and common winding.** F_r and each F_r exp(-a*s)+1
   are entire and nonzero as functions (at0 they equal1/2 and3/2). Their
   zero sets are countable. The complement U_r,A is path connected by the
   same plane-minus-countable-set theorem as XiMarkedSourceSpace. Connecting
   the island base once to0 yields a common conjugator for each finite packet.
   All coordinate zero windings agree because exp(-a*s) has a global logarithm.
6. **Primitive actual winding.** Choose an unconditional simple critical Xi
   zero at height exceeding every |r_j|, using exists_high_simple_critical_xi.
   Q_r is nonzero there, so F_r has order1. A sufficiently small circle avoids
   all other F_r zeros and every auxiliary divisor, and has winding1.
   Transport to0 gives surjectivity onto the common winding integer.
7. **Exact images.** The finite common-conjugator packet lemma puts the image
   of every coordinate zero-winding kernel into f(image mu_r,A). Their product
   has the same inclusion. Subtract an actual element with the required common
   winding using step6; the remainder lies in that product kernel. This proves
   finite-image equality. For normal closure, conjugation can be removed
   directly, giving the same argument without finiteness. The reverse
   inclusions follow from step5. Empty A gives the trivial group.

## Hostile audit, positive survivor, and literature boundary

This does not prove discrete-image equality, equality of individual marked
loops, equality of kernels of the source maps, or equality of the arithmetic
source. It cannot relocate or remove an existing Xi zero: it only inserts
finitely many zeros. The positive survivor is the exact common-winding
classification, stable under every finite normalized divisor insertion;
endpoint source weights remain capable of detecting such insertions.
No generic analytic premises may remain undisclosed on the F_r endpoint.
Root nonvanishing is structural data needed for normalization, not an RH
assumption. Repeated roots and empty root/mark families must be covered.

Corpus query `finite polynomial divisor dressing Xi marked finite monodromy
image invariance` completed with partial=false, 68273 inventoried files,
20 candidate and20 source statements inspected. Coverage was a slightly older
snapshot and refresh reported background_indexer_running; applicability must
be checked in Lean. No matching finite marked-image invariance theorem found.
The existing ShiftOrbitMassObstruction.logDeriv_prod_sub supplies the exact
finite-product correction, avoiding duplicate algebra.

External primary check: Marinov--Veselinov, arXiv:2602.09253v1, Theorem1.1
and §§1--3 concern inverse-branch monodromy of elementary meromorphic functions
with infinitely many critical values. This does not establish our simultaneous
marked-source image theorem. Eremenko--Lyubich1992 §2 needs bounded inverse
singular values for global logarithmic tracts; those hypotheses are not assumed
here. These checks separate scopes; they do not certify scientific novelty.

Sources: https://arxiv.org/html/2602.09253v1 and
https://www.numdam.org/item/AIF_1992__42_4_989_0.pdf.

## Working log

- 2026-10-07 resumed after explicit goal continuation. Previous paused turn
  was a status restatement (no progress); current goal state verified active.
- Preserve all previously audited Xi leaves. Implement new finite-divisor
  analytic inputs first, then reuse/generalize the packet infrastructure.
  No numerical experiments, full builds, admissions or heartbeat changes.
