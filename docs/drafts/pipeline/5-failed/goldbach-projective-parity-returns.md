# Integral-return cost of projective parity transport

- **ID:** goldbach-projective-parity-returns
- **Stage:** 5-failed
- **Type:** FALSE coverage conjecture; sharp finite survivor formalized
- **Source:** Cycle 11's matrix μ(T−mn), Cycle 12's arithmetic parity reflection, and the RH programmes' incidence/holonomy mechanisms.
- **Goal:** test whether fixed projective symmetries can pair a substantial part of the balanced matrix before estimating its signed covariance.

## Previous turn classification

Progress: the actual RH source's damping-parity law and finite two-scale
Goldbach criterion were formalized and axiom-audited. That changes the
available representation but proves no all-even positivity estimate. The
original unconditional Goldbach goal remains active and unchanged.

## Proposed cancellation mechanism

Write T−mn=n(T/n−m). The difference kernel on rational coordinates has
an exact projective transformation law. For

    g(x)=(ax+b)/(cx+d),       Δ=ad−bc≠0,

transform both m and T/n. In the original coordinates this gives

    m'=(am+b)/(cm+d),
    n'=T(cT+dn)/(aT+bn),
    T−m'n'=TΔ(T−mn)/((cm+d)(aT+bn)).                 (1)

All denominators in (1) are required to be nonzero. Extending Liouville to
nonzero rationals by numerator/denominator parity turns the prefactor
into a determinant sign and one sign for each coordinate. This suggests
using several transformations as common signed symmetries of the matrix.
The Möbius version would additionally have to retain both squarefree masks.

The necessary coverage conjecture was: a polylogarithmic family of fixed
nondiagonal projective transformations, with integer representatives of
polynomial height in T, can have integral returns on a positive proportion
of a balanced integer rectangle. Here both side lengths are at least T^δ
for fixed δ>0. Transformations may depend on T, but not on an individual
edge. No cancellation conclusion was assumed from coverage alone.

## Attack: exact denominator constraint

If m' is integral, t=cm+d is nonzero and t divides am+b. Hence

    t | a(cm+d)−c(am+b)=Δ.                           (2)

When c≠0, the map m↦t is injective. Thus every finite integer set S has
at most 2τ(|Δ|) integral return points, independently of the size or
location of S. The bound is sharp: x↦D/x returns at exactly the nonzero
signed divisors of D, of which there are 2τ(|D|).

For the column coordinate the representing coefficients are

    (a',b',c',d')=(Td,cT²,b,aT),       Δ'=T²Δ.

Therefore, if b≠0 and TΔ≠0, the column return count is at most
2τ(|T²Δ|). The two coordinates are independent, so their joint return
set is the Cartesian product of the two return sets.

Consequently any nondiagonal transformation has joint return count at most

    2τ(|Δ|)|U|                 when c≠0,
    2τ(|T²Δ|)|S|               when c=0 and b≠0.       (3)

Restrictions that also keep the transformed points inside the original
rectangle can only decrease these counts.

If b=c=0, then m'=(a/d)m and n'=(d/a)n, so m'n'=mn. These diagonal
transformations preserve the arithmetic argument itself and supply no
new sign change of λ(T−mn).

## Why the coverage conjecture fails

For representatives of polynomial height, |Δ| and |T²Δ| are polynomial
in T. The elementary divisor estimate τ(r)≤C_η r^η for each η>0 makes
both divisor counts T^{o(1)}. Summing (3) over (log T)^K transformations
covers at most

    (log T)^K T^{o(1)} max(|S|,|U|)
      = o(|S||U|),

since min(|S|,|U|)≥T^δ. This is uniform over the chosen matrices. Thus
the necessary dense-return conjecture is false. Allowing more arithmetic
maps or maps depending on individual points is a different route; it is
not ruled out by this argument.

For completeness, the divisor estimate needs no cancellation input.
For large primes p with p^η≥2, e+1≤2^e≤p^{ηe}. For each of the finitely
many smaller primes, (e+1)p^{−ηe} is bounded by the convergent series
Σ_{e≥0}(e+1)p^{−ηe}. Multiplication over prime powers gives C_η.

## Positive survivor and next obligation

- **Exact survivor:** sharp finite return bound (2)–(3), its Cartesian-product
  form for the original bilinear coordinates, and equality for inversion.
- **New insight for this attempted route:** the projective parity law lives
  naturally on rational incidence. Returning to the integer rectangle has
  a determinant-divisor cost. The diagonal maps avoiding that cost leave
  T−mn unchanged. A common rational symmetry cannot be treated as a common
  integer symmetry without paying this return set.
- **Paper status:** finite survivor has a dependency-closed proof above.
- **Lean status:** the finite return cap, sharp inversion classification,
  transformed column determinant, bilinear numerator identity and family
  coverage cap are checked in
  [ProjectiveIntegralReturns.lean](../../../../formal/GaloisForLFunctions/goldbach/ProjectiveIntegralReturns.lean).
  Exact statements and proof are on the
  [formalized survivor card](../3-formalized/not_new_scientific_knowledge/goldbach-projective-integral-returns.md).
  No analytic premise or placeholder was added.
- **Novelty:** elementary method audit and bridge, not a claim of new scientific
  knowledge. Corpus search found projective actions and parity gauges, but
  no inspected declaration giving this integral-return bound.

The signed Möbius covariance remains unproved. A next projective attempt
would need an explicitly counted arithmetic correspondence or an adaptive
family with controlled multiplicity and retained squarefree masks. It
cannot reuse the falsified fixed-family coverage premise.

## Second-pass audit and closure

The scope of retirement is the fixed-family dense-return premise above,
not all projective or correspondence methods. The strongest finite
survivor is sharp and attained by inversion, rather than merely a renamed
failure statement. Its two-coordinate and family forms retain the exact
determinant costs needed by the original arithmetic matrix.

Replacing a common map by a homogeneous action avoids division but moves
the target to (cm+d)(aT+bn). Normalizing back to the fixed target restores
the same denominators. That change cannot silently replace a targetwise
estimate by a target average.

Simple sign switching also supplies no matrix norm saving by itself:
the inspected `TwinPrime.determinantUnitPairingValues_moebius_eq_parity`
and `determinantFourCycle_moebius_eq_parity` preserve all unit-ball tests
and cancel row/column gauges around cycles. Any next holonomy argument
must estimate the residual arithmetic cycle signs, not the removable gauges.

Direct leaf compilation and six axiom-closure audits passed with only
`propext`, `Classical.choice`, `Quot.sound`. Audit log:
`/tmp/hgt-goldbach-projective-returns-audit.log`. No new analytic cancellation
estimate or scientific novelty is claimed. The original Goldbach goal
remains active.
