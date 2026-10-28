# Residue horizon charges on all gcd strata

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** RAPT characters at the horizon; BVI arithmetic-progression harmonic remainders
- **Count:** uncounted; unit-residue special case is existing baseline; only the all-gcd-strata extension remains prospective

## Revised target and baseline

The original unit-residue target is already proved in
`RenormalizedArithmeticPotentialTheory/TheHorizonCountertermIsBlindToResidueClasses.lean`.
Its module statement, residue Gram endpoint, step-profile expansion, and polar
survival endpoint were inspected. In particular,
`exists_abs_atomicWeilForm_unitClassProfile_sub_le` covers arbitrary signed
unit-class profiles with independent integer cutoffs, with the sharper
harmonic-minimum error. This special case cannot count as new work.

The remaining proposed target is the full gcd-stratum counterterm stated below,
including non-unit residues, cross-stratum error control, and the exact leading
energy cost of the non-unit-invariant part of a fixed periodic profile. Its
significance and novelty still need audit; it is not automatically a separate
contribution merely because it generalizes the existing unit result.

## Corpus leads checked

- `RAPT/MertensTheoremInResidueClasses.lean` proves, for every positive modulus
  and unit r, `classMertensSum q r y=log(y)/phi(q)+O_q(1)` unconditionally.
  Its exact character orthogonality and principal/nonprincipal estimates were read.
- `BVI/ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds.lean`
  proves `abs_progressionHarmonicSum_succ_sub_harmonic_div_le` and
  `abs_progressionHarmonicSum_succ_sub_log_div_le`. Its full harmonic-remainder
  section was read: a two-sided reciprocal sandwich supplies the bound with
  no analytic premise. Conversion to arbitrary integer horizons remains to prove.
- `BVI/DilationSuccessorSectorHarmonicClassification.lean` uses the progression
  remainder to isolate a harmonic mode after exact periodic block decomposition.
- The existing character-gauge horizon theorem treats one real character gauge,
  not arbitrary independently truncated unit-class profiles.
- Corpus queries for unit-residue horizon counterterms and harmonic progression
  remainders found these inputs and the programme's open question, not the target.

## All-gcd-strata classification, still unproved

For all residue classes modulo q, group polar charges by `gcd(n,q)=d`, for d|q.
The candidate counterterm is

`sum_(d|q) [q/phi(q/d)] * ell_d(x)^2`.

Each gcd stratum has density `phi(q/d)/q`. This suggests counterterm rank equal
to the number of divisors of q, with unit-residue mixing inside each stratum and
only lower-order interaction between distinct strata. That interaction estimate
is a separate mathematical obligation, not a supplied premise. Audit this
stronger conjecture before adopting it; do not count a rank-one special case
and a general classification as separate contributions without a distinct advance.

The stronger-target novelty search surfaced
`RHTower/CCM/CCMRationalZModUnitInvariantMobius.lean`, read in full. It already
proves that unit orbits are exactly gcd strata and gives their canonical Mobius
decomposition. That orbit classification is baseline, not proposed novelty.
It supplies the finite algebraic carrier; the missing result is its identification
with the actual prime horizon divergence, including all independent cutoffs.

No dependency-closed paper proof or Lean implementation of the all-gcd-strata extension yet. The full-prime spectral-exhaustion package remains the active formalization task.

## Mechanism to audit

For unit classes a,b, split the rectangular prime Gram into its two oriented
multiples sums. Their exact inner sums are the residue Mertens sums for b/a
and a/b. After the bounded Mertens remainders, the two leading terms are

`(1/phi(q)) sum_(m<=min(A,B),m=a mod q) log(B/m)/m`
`+(1/phi(q)) sum_(n<=min(A,B),n=b mod q) log(A/n)/n`.

The progression harmonic discrepancy is bounded; summation by parts should
therefore leave O_q(log N) error under the logarithmic weight. The main terms
combine to `log(A)log(B)/(q phi(q))`. This matches the proposed product of the
two actual harmonic charges up to the same error. The downward half must be
reindexed as a second multiples sum: a residue-restricted divisor sum cannot
be replaced pointwise by `log(n)/phi(q)`.

For a common gcd stratum d, dilation n=d*k reduces the classes to units mod
q/d, with the prime Gram scaled by 1/d. This gives coefficient q/phi(q/d).
Between distinct strata, a nonzero prime-kernel entry must have ratio p^j for
a prime p dividing q. Its Mangoldt weight divided by p^j has a bounded geometric
sum, suggesting O_q(log N) cross terms. These exact reindexings and bounds are
still obligations. The existing gcd-orbit theorem supplies the classification
only; the horizon interpretation is the proposed new result.

The needed weighted discrepancy has a corpus tool:
`BVI/OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError.lean`,
`abs_sum_range_mul_antitone_le` (statement and proof inspected). Apply it to
the harmonic discrepancy sequence `(1_(n mod q=a)-1/q)/n` and the nonnegative
decreasing weight `max(log(B)-log(n),0)`. A bounded harmonic prefix discrepancy
then costs only O_q(log B), uniformly in the smaller cutoff. The uniform
logarithmic harmonic sum is already handled by `HTGeometry/LogHarmonicFinitePart`.
This supplies a concrete route for the two elementary asymptotics named in
RAPT section 9.3 without introducing a new analytic hypothesis.

A substantive consequence of the full gcd-stratum counterterm would classify
fixed periodic pole profiles by their energy scale. For q-periodic a, let R_q a
be its average over each unit orbit, equivalently each gcd stratum modulo q.
The proposed full counterterm and the ordinary harmonic periodic mean would give

`(log(N)*sum_(n<=N)a(n)^2/n-P_N(a/sqrt(n),a/sqrt(n)))/(log N)^2
 -> mean_q((a-R_q a)^2)`.

Indeed the gcd charge on stratum d is asymptotic to
`log(N)/q * sum_(r mod q,gcd(r,q)=d)a(r)`, and its coefficient
q/phi(q/d) gives exactly mean_q((R_q a)^2). Subtract from mean_q(a^2).
For nonzero a, a positive right side forces normalized energy to diverge
linearly with log N. If a is unit-invariant, finite divisor-to-Ramanujan
inversion expresses it in conductors dividing q, and the already proved
prime quasimodes give its finite weighted adjunction-energy limit.
This would identify the entire fixed-periodic bounded-energy carrier, including
an exact leading cost for its complement. It belongs to the same proposed
horizon classification, not another contribution count.

This is a quadratic-form assertion. A compressed leading form alone does not
give a full-vector residual estimate or eigenvalues for the nonradial modes;
no such operator or spectral upgrade is claimed. Arbitrary independent cutoff
control remains part of the main conjecture and must still be proved.

The later targeted search also returned `TheArchimedeanPlacePaysTheArithmeticPoint.lean`.
Its joint-germ definitions and counterterm statement were inspected. They concern
a periodic Abel/Cauchy germ and its matched arithmetic-point coupling, rather
than the literal spacing-scale Weil matrix. That finite periodic orthogonality
and matched-rank-one mechanism are baseline for the separate full-Weil candidate.
