# Uniform remainder between compensated interior martingale and half energy

- **ID:** BVI-UNIFORM-INTERIOR-REMAINDER-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / corpus and paper audit
- **Parent:** `bvi-interior-martingale-coercive-contraction-2026-10-18.md`

## Exact proposed statement and relation to the full goal

For every positive damping epsilon, seek a finite constant C(epsilon),
independent of T, such that

    |2*M_int(epsilon,T) + 2*c_int(epsilon)*H_comp(T) - E(epsilon,T)|
      <= C(epsilon).

The corpus currently supplies this residual as o(log T). This conjecture
would upgrade that remainder to O(1). It is NOT the requested strict
contraction: with this result, strict contraction is quantitatively
equivalent to a uniform bound on the actual energy. No claim of that bound
is made. A coefficient-one identity alone cannot prove this conjecture;
the new input must bound its two signed arithmetic remainder terms.

## Existing source inputs

- `pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget`
  decomposes E into the active-deleted diagonal remainder, twice the
  predecessor-peak remainder, and twice the compensated interior bracket.
- `CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget` already has
  uniform single-divisor harmonic remainders under log-weight summability,
  and the o(log T) residual statement.
- `ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds` already
  has the progression remainder and first-hit suppression. Directly
  summing absolute two-modulus harmonic remainders may lose small damping.
- The corrected natural-cutoff head/tail bridge retains a nonnegative
  conditional-tail variance. Its identity alone gives no upper bound for
  that variance. Existing observation recovery likewise gives finite
  injectivity, not uniform physical-Gram conditioning.

## Corpus correction: reuse the existing successive truncation proof

`RHTower/PMAdjacentDivisorCorrelation.lean` already proves the adjacent
mean by two successive dominated limits, using the proved bounds
`0 <= pmPowerDampedDivisorCoeff epsilon n <= 1`. This makes a new
weighted-divisor second-moment theory unnecessary for this target.
The source statements and proof bodies were inspected; Lean API and axiom
checks remain to be run for this continuation.

Write `c_e(a)=mu(a)*a^(-e)`, `Z_e=sum_{a>=1} a^(-1-e)` and
`T_e(A)=sum_{a>A} a^(-1-e) <= A^(-e)/e` for A>=1. For N>=1,
let Q(N) be the normalized mean of `F_e(n+1)*F_h(n)`, and let Q_inf be
the existing `pmAdjacentDivisorDensity e h`. With integer A,D>=1:

    |Q(N)-Q_inf|
      <= (1+Z_e)*T_h(D) + (2*D+Z_h)*T_e(A) + A*D/N.

The five terms are obtained without losing the bounded full field:

1. Truncate the outer divisor d at D only. The finite-mean tail is at
   most T_h(D), since the full F_e lies in [0,1] and the count of d-multiples
   is floor(N/d). The density tail is at most Z_e*T_h(D).
2. On each retained outer divisor, truncate the inner a at A. Its finite
   mean tail is at most 2*T_e(A), since the adjacent incidence count is
   at most floor((N+1)/a). The outer absolute head mass is at most D.
   The corresponding density tail is at most Z_h*T_e(A).
3. Every retained compatible pair has one CRT residue class, hence
   count discrepancy at most 1. Incompatible pairs have zero count and
   density. Each coefficient has absolute value at most 1, giving A*D/N.

Choose A=ceil(N^(1/2)), D=ceil(N^alpha),
alpha=e/(4*(1+e)). Then 0<alpha<1/4 and alpha<=e/4. Using
ceil(x)<=2*x for x>=1 gives a positive power saving with

    delta = min(alpha*h, e/4, 1/4) > 0.

Thus `|sum_{n<=N} (F_e(n+1)*F_h(n)-Q_inf)| <= K*N^(1-delta)`.
Abel summation bounds the centered harmonic sum by
`K*(1+sum_{n>=1} n^(-1-delta))`. The corpus already contains
`HTGeometry.abel_bound_of_partialSum_le`; its exact indexing and public
API must be checked before reuse.

For the active-deleted diagonal, the corpus already supplies the exact
single-divisor expansion of F_e*F_(1+e) and
`abs_pmShiftedExponentSecondCoeff_le`, bounded by `d(n)*n^(-e)`.
Existing divisor-square and log-square Dirichlet summability imply its
log-weight summability; the existing uniform divisor-harmonic bound then
applies. The remaining terms are individual F_e and F_(1+e) fields.

All shifts and terminal terms cost finite constants because these fields
are bounded. Use the actual source normalization:
`H_comp(T)=H_T-2*T/(T+1)` for T>=1, and its proved difference bound <=2.
The predecessor coefficient is the exact combination
`(F_e(n+1)*F_e(n)-F_e(n+1)*F_(1+e)(n)
  +rho_e*(F_(1+e)(n)-F_e(n)))/2`.
Its density is precisely the existing predecessor drift formula.
Combining both uniform remainders with the existing canonical energy
identity proves the proposed O(1) residual on paper. Formalization still
needs the quantitative truncation estimate and its actual-coefficient
specializations; none is being assumed as an analytic premise.

## Earlier candidate, superseded by corpus reuse

Let F_epsilon(n)=sum_{d|n} mu(d)*d^(-epsilon), n>=1, and let F_D truncate
that divisor sum to d<=D. For positive tau, define the nonnegative divisor
majorant B_tau(n)=sum_{d|n} d^(-tau).

1. Candidate uniform second-moment estimate:

       sum_{n<=N} B_tau(n)^2
         <= N * sum_{d,e>=1} d^(-tau)*e^(-tau)/lcm(d,e)
         <= N * Z(1+tau)^2 * Z(1+2*tau).

   Here Z(s)=sum_{k>=1} k^(-s), not an assumed analytic input. Expand the
   finite divisor square, count multiples by floor(N/lcm), and write
   d=g*a,e=g*b with g=gcd(d,e). Drop the coprimality restriction only in
   this nonnegative majorant. All series on the right converge for tau>0.

2. For d>D>=1, d^(-epsilon)<=D^(-epsilon/2)*d^(-epsilon/2). Therefore
   the divisor tail has mean square O_epsilon(D^(-epsilon)), uniformly
   in N. Cauchy-Schwarz gives an O_epsilon(D^(-epsilon/2)) error in a
   normalized shifted correlation. This keeps the physical shift and
   does not replace an incomplete progression by a complete period.

3. The finite head correlation has the actual CRT density and error at
   most D^2/N, using the existing exact incidence count. Its density tail
   is controlled by absolutely convergent reciprocal coefficient series.
   With D=floor(N^(1/4))+1, the normalized error is bounded by a positive
   power of N, for every epsilon>0.

4. A genuine positive-power mean error would make the harmonic centered
   correlation remainder uniformly bounded by Abel summation. Apply this
   only after checking the exact predecessor-peak and diagonal formulas,
   including all shifts and endpoint terms. The target does not use the
   harmonic-difference expression from the original programme quotation.

The second-moment route above remains an alternative paper argument. It
is not needed after locating the existing bounded-field proof. The full
strict contraction remains the parent objective after this step.

## Verification plan

- [ ] Inspect rich corpus candidate lemmas and source arguments, freshness,
  and exact applicability.
- [ ] Close the paper proof or record the exact failure and survivor.
- [ ] Formalize only the missing result, preserving existing definitions.
- [ ] Check original leaf, every public axiom closure, umbrella wiring,
  generated index and lint; clean owned scratch.
- [ ] Return to the remaining strict-contraction problem; do not mark the
  parent complete on this auxiliary result.

## Lean checkpoint

The exact adjacent mean, divisor progression mean, divisor-square and
log-square summability, shifted coefficient bound, existing uniform
divisor-harmonic remainder, Abel bound, and Abel increment summability
were imported and checked in `/tmp/bvi-uniform-remainder-api-2026-10-18.lean`.
The one owned process (18588) exited 0; all eight axiom queries returned
only `propext`, `Classical.choice`, and `Quot.sound`. Log:
`/tmp/bvi-uniform-remainder-api-2026-10-18.log`.

The first missing arithmetic specializations are being proved in
`/tmp/bvi-uniform-active-deleted-2026-10-18.lean`: actual coefficient
log-weight summability and uniform same-node harmonic remainders.
No new repository Lean source has been written yet. Scratch is pending
verification; it is not a completed theorem claim.
