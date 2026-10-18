# Uniform remainder between compensated interior martingale and half energy

- **ID:** BVI-UNIFORM-INTERIOR-REMAINDER-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM / dependency-closed paper proof and checked Lean 4
- **Parent:** `../1-in-progress/bvi-interior-martingale-coercive-contraction-2026-10-18.md`
- **Session:** Completed started Lean work; further research paused at user request.

## Exact statement and relation to the full goal

For every positive damping epsilon, there is a finite constant C(epsilon),
independent of T, such that

    |2*M_int(epsilon,T) + 2*c_int(epsilon)*H_comp(T) - E(epsilon,T)|
      <= C(epsilon).

This upgrades the prior corpus residual from o(log T) to O(1). It is NOT the requested strict
contraction: with this result, strict contraction is quantitatively
equivalent to a uniform bound on the actual energy. No claim of that bound
is made. The new input bounds both signed arithmetic remainder terms;
the coefficient-one identity is used only after those bounds are proved.

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
The source statements and proof bodies were inspected. Eight reused APIs
passed the scratch API/axiom audit; only `propext`, `Classical.choice`, and
`Quot.sound` occur. The log is currently
`logs/bvi-asymmetric-adjacent-truncation-2026-10-18-reused-axioms.txt`.

Further corpus reuse removes the proposed new counting proof:
`ChineseRemainderBezoutPeriodicityAndSawtoothDefect` already proves
`abs_bezoutSawtoothDefect_le_one`, the sharp unit discrepancy for each
positive modulus pair. Its quadratic finite-prefix expansion can be
extended to two coefficient families and unequal cutoffs. The existing
`pm_divisor_average_eq_tsum` supplies the exact floor-count formula needed
for mean absolute truncation tails, without exposing any private helpers
in `PMAdjacentDivisorCorrelation`. No RHTower source change is needed.
The unused weaker counting draft was archived and removed.

The latest broad mean-tail search had partial semantic coverage and
mostly unrelated hits. A narrowed lexical search for
`"sievedDivisorSum" tail` returned seven hits, all inspected, including
the positive-index bridge and exact truncated LCM Gram. None of those
seven statements supplies the mean L1 tail estimate. The completed
formalization therefore derives that estimate directly from the existing
divisor-average identity. This is a bounded search finding, not a claim
that no such theorem exists anywhere in the corpus.

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

### Formalization shortcut: transfer the bound through the existing limit

The existing `tendsto_pm_adjacent_divisor_mean` avoids a separate formal
estimate of the double-series density tail. For each fixed A,D, the finite
truncation error is bounded by

    B(A,D) = T_h(D) + 2*D*T_e(A)

at every positive horizon. The sharp CRT defect gives convergence of the
truncated mean to its finite coprime density. Passing this bound to the
limit yields `|Q_inf - finite_density(A,D)| <= B(A,D)`. The same inequality
holds for every A,D, so they may subsequently depend on the horizon N.
The triangle inequality gives the alternative quantitative bound

    |Q(N)-Q_inf| <= 2*T_h(D) + 4*D*T_e(A) + A*D/N.

This has the same positive-power consequence below. It uses only the
already-proved adjacent limit, the finite mean L1 tails, and the existing
unit CRT defect; no new premise about an infinite density series is needed.

An elementary half-exponent moment suffices for formalization, avoiding
a separate integral estimate for p-series tails. Write

    U_e(A) = sum_{d>A} |mu(d)|*d^(-1-e),
    K_e = sum_{d>=1} |mu(d)|*d^(-1-e/2).

The existing reciprocal summability theorem at e/2 makes K_e finite.
For d>A>=1, factor `d^(-e)=d^(-e/2)*d^(-e/2)` and use monotonicity
of the negative power to obtain `U_e(A)<=K_e*A^(-e/2)`. In the
alternative bound replace T by U, choose

    alpha = e/(8*(1+e)),
    A = ceil(N^(1/2)), D = ceil(N^alpha),
    delta = min(alpha*h/2, e/8, 1/4).

Then delta>0, and the bound is at most
`(2*K_h+8*K_e+4)*N^(-delta)`. This weaker but explicit positive exponent
is enough for the same Abel argument and O(1) remainder. Both choices
are dependency-closed paper arguments; the half-exponent version is the
implemented Lean argument.

Choose A=ceil(N^(1/2)), D=ceil(N^alpha),
alpha=e/(4*(1+e)). Then 0<alpha<1/4 and alpha<=e/4. Using
ceil(x)<=2*x for x>=1 gives a positive power saving with

    delta = min(alpha*h, e/4, 1/4) > 0.

Thus `|sum_{n<=N} (F_e(n+1)*F_h(n)-Q_inf)| <= K*N^(1-delta)`.
Abel summation bounds the centered harmonic sum by
`K*(1+sum_{n>=1} n^(-1-delta))`. The corpus already contains
`HTGeometry.abel_bound_of_partialSum_le`; its exact indexing and public
API were checked before reuse in the adjacent compensated-bound leaf.

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
identity proves the O(1) residual. The quantitative truncation estimate,
actual-coefficient specializations, and final assembly are formalized.
Original-source and public axiom audits passed for every leaf.
No analytic premise is assumed.

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

## Verification

- [x] Inspect rich corpus candidate lemmas and source arguments, freshness,
  and exact applicability.
- [x] Close the paper proof or record the exact failure and survivor.
- [x] Formalize only the missing result, preserving existing definitions.
- [x] Check original leaf, every public axiom closure, umbrella wiring,
  generated index and lint; clean owned scratch. Lint retains one unrelated
  root-module placement error, documented below; no owned-leaf finding.
- [ ] Remaining strict contraction is open. Further research is paused at
  user request; this auxiliary result does not complete the parent.

## Lean checkpoint

The exact adjacent mean, divisor progression mean, divisor-square and
log-square summability, shifted coefficient bound, existing uniform
divisor-harmonic remainder, Abel bound, and Abel increment summability
were imported and checked in `/tmp/bvi-uniform-remainder-api-2026-10-18.lean`.
The one owned process (18588) exited 0; all eight axiom queries returned
only `propext`, `Classical.choice`, and `Quot.sound`. Log:
`logs/bvi-uniform-active-deleted-2026-10-18-reused-axioms.txt`.
The completed scratch input is archived in the matching search archive.

The diagonal paper proof is now recorded in
`bvi-uniform-active-deleted-compensated-remainder-2026-10-18.md`.
New repository leaf `UniformActiveDeletedCompensatedRemainder.lean` has
250 lines and five public theorems, with one umbrella import. Scratch
checks found one implicit-argument mismatch and two shadowed addition
lemma applications; these were corrected. The original-source check is
complete: session 21412 exited 0 with no diagnostics and emitted both
compiled artifacts. Final public audit (18267) passed for all five public
theorems and thirty mathlib name probes. Index refresh passed; lint reports
only the unrelated `TransHorizonIncidenceMechanics.lean` placement error
and existing warnings. Thirty completed scratch files were archived and
removed. The exact certificate is in the diagonal child card and manifest.

Further corpus/source inspection found the stronger existing result:
`abs_bezoutSawtoothDefect_le_one`, in
`ChineseRemainderBezoutPeriodicityAndSawtoothDefect.lean`. That source
also provides the exact finite correlation decomposition and its L1-square
remainder bound. The unrun constant-two draft was archived in
`logs/bvi-adjacent-superseded-count-draft-2026-10-18.tar.gz` and removed.
Do not reimplement this count estimate.

The public `RHTower.pm_divisor_average_eq_tsum` gives the mean L1 divisor
tail directly, by applying it to the nonnegative tail coefficients and
bounding floor(x/d)/x by 1/d. Thus the two-cutoff proof can avoid the
private weighted-average helpers entirely; no helper visibility edits or
new RHTower exports are needed. Use existing `sievedDivisorSum`,
`truncatedSieveWeight`, and their positive-index `sieveSeq` bridge.

The key product split is

    F_e(n+1)*F_h(n) - F_e,A(n+1)*F_h,D(n)
      = F_e(n+1)*(F_h(n)-F_h,D(n))
        + (F_e(n+1)-F_e,A(n+1))*F_h,D(n).

The first full field is bounded by 1; the truncated second field by D.
Mean L1 tails therefore give T_h(D)+2D*T_e(A). Passing this bound through
the existing adjacent limit, as detailed above, avoids a separate density
tail proof. The bilinear-prefix query completed; all twenty candidate
statements and twenty source arguments were inspected. Its proposed plan
does not establish the desired bound. The scratch proof extends the
existing finite-head identity to unequal cutoffs and coefficient families.

The quantitative truncation assembly is now formalized in
`AsymmetricAdjacentDivisorTruncation.lean`: the exact two-cutoff estimate,
its cutoff-size corollary, and the half-exponent reciprocal tail bound.
Original source (68346), all three public axiom closures, and twenty
mathlib name probes (82766) passed. The leaf is wired once and indexed;
lint has three unrelated errors and no finding in this leaf. Thirty-two
completed scratch files were archived and removed. Exact proof/certificate:
`bvi-asymmetric-adjacent-divisor-truncation-2026-10-18.md`.

The combined positive power-rate and exact compensated-kernel scratch
passed (85594, exit 0). Its promoted leaf is
`UniformAdjacentDivisorCompensatedRemainder.lean`. Original source (96521)
and public axiom/API audit (4141) passed; all twelve completed scratch
files were archived and removed. Certificate:
`bvi-uniform-adjacent-compensated-remainder-2026-10-18.md`.

A further live corpus search found the exact existing conversion
`sum_Icc_pred_compensated_add_sum_pronicSeq_eq` in
`ActivePairMartingaleDissipationAndShiftedTotientReduction.lean`.
The new assembly reuses that identity, not a new kernel-shift proof.
For 0<=F<=1, the pronic correction and terminal mean each lie in [0,1].
Thus conversion of the single-field harmonic remainder costs at most 2.
The completed assembly uses this, the two adjacent compensated bounds,
the exact predecessor-drift formula, and the canonical energy budget.
It also states the quantitative equivalence between strict contraction
and bounded actual energy. This equivalence does not prove either side.
The full O(1) residual and the exact equivalence passed scratch Lean
(84274, exit 0, no diagnostics). Promoted leaf
`UniformRenormalizedInteriorEnergyRemainder.lean` has 182 lines and four
public theorems:

- `exists_pmPowerDampedDivisor_compensated_bound`
- `exists_pmPredecessorPeak_compensated_bound`
- `exists_pmBezoutInterior_compensated_energy_bound`
- `pmInterior_strict_contraction_iff_bounded_energy`

Original-source audit (50797) exited 0 with no diagnostics and emitted
fresh `.olean` and `.ilean` artifacts. Public axiom/API audit (36525)
exited 0: all four closures use only `propext`, `Classical.choice`, and
`Quot.sound`; all three mathlib name probes passed. The umbrella imports
the leaf exactly once. Index refresh (21581) passed and indexed retrieval
(63549) returned all four public theorems.

Formal lint (89068) exited 1 with 381 existing warnings and one unrelated
error: `research leaf module at package root: TransHorizonIncidenceMechanics.lean; move it into an owned theorem area`.
No finding names this leaf. This is not a global lint pass.

Source SHA256:
`5f1909c7d34a04bde6f6aff6e8bb92f354dc98818fe42516e54947e31848d49d`.
Certificate: `logs/bvi-uniform-interior-remainder-2026-10-18-manifest.json`.
Raw source, axiom, index, indexed-API and lint logs share that prefix.
Four proof scratch files and eight completed corpus-search results were
archived, hash-verified, and removed from `/tmp`; archives are
`logs/bvi-uniform-interior-remainder-2026-10-18-proof-scratch.tar.gz` and
`logs/bvi-uniform-interior-remainder-2026-10-18-search.tar.gz`.

Strict contraction and the equivalent uniform actual energy bound remain
open. Started Lean work, wiring, and documentation are complete. Further
research is paused at the user's explicit request.
