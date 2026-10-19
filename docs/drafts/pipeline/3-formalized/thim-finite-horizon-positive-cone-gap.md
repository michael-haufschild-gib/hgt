# Odd-trace centering and the finite-horizon positive-cone gap

- **ID:** thim-finite-horizon-positive-cone-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Sharp physical conditioning](../3-formalized/thim-sharp-physical-fermi-asymptotic.md)
- **Statement:** The signed and nonnegative physical inverse constants have the same leading asymptotic but can differ at a fixed horizon; a native coefficient shift gives an exact odd-trace centering law.

## Goal and counting

Test the stronger conjecture `K_N = K_N^+` for every `N>=2`. The shared
`4/pi^2` asymptotic does not imply this. The dependency-closed paper refutation is
`K_3^+ < K_3`, with an exact centering law as positive survivor. Both are now
formalized. This is an extension of C1, not a separate contribution: it refines
C1's signed/nonnegative comparison through classical centering and a
two-variable Rayleigh maximum. Its native finite-horizon conclusion is useful,
but does not warrant an independent count. Programme count remains **1/100**.

## Prior-work audit

Before this card, a deep search for positive-cone equality of the physical
inverse recovered the existing coefficient restriction/finite-dimensional
sieve space, the current Fermi transport, and general cone statements.
All 20 candidate statements, 20 source arguments, and the proposed two-step
ingredient set were reviewed. Its finite-tail equivalence construction does
not preserve the finite divisor carrier or either physical energy, so it
does not settle this problem. The exact lexical query `sieveSeq centering`
returned no hits; that is not absence evidence. A focused native odd/even
coefficient-shift query recovered `sieveSeq_unitShiftWeight` in
`RadicalCheckpointSignRigidityAndGaugeLaw.lean` and the coefficient-agreement
lemma in `ActiveSawtoothPowerSamplingAndCalibratedRecovery.lean`.
Their source was checked. The current paired shift reuses the unit-shift law.
Further searches recovered the existing bounded-sieve estimate, summability
under pronic weights, and exact shifted reciprocal-pronic tail. All 20+20
candidate/source rows in each query were reviewed. The older BiScale parity
lift is an exact signed residue-row construction, not a physical inverse
ratio or positive-cone optimum theorem.

Two additional focused searches, `tsum even odd sum split natural` and
`sieve energy pronic gram coefficient lcm infinite sum`, returned 20 candidate
lemmas and 20 source arguments each; all returned statements were triaged.
Following `DQPTBernoulliBound.lean` and
`DirichletLMixedAdditiveEvenIndexLaw.lean` recovered mathlib's
`tsum_even_add_odd`, so the parity decomposition will reuse that theorem.
The source of `EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound.lean`
was checked: its rank-one centering removes a von Mangoldt functional from
the **prefix discrepancy** Gram form. It is relevant prior centering work,
but does not assert simultaneous changes of these two physical trace energies
or a signed/nonnegative inverse-constant gap. The classical projection algebra
is not claimed as new here. Both searches reported complete retrieval runs,
but compiler coverage is mostly source-only, pending, or stale; this audit
does not establish global priority or exhaustive semantic absence.

## Paper argument for the positive survivor

Write `P=P_N(c)`, `Q=Q_N(c)` for the existing complete pronic energies.
For `N>=2`, set

`c_t(d)=c(d)+t*(1_(d=2)-1_(d=1))`.

The sieve response is unchanged at every even integer and decreases by `t`
at every odd integer. Consequently every selected even jump `J(4m+4)` is
unchanged. Both physical energies change only in their common odd sector.
Put

`T = sum_(n>=1, n odd) 1/[n(n+1)] > 0`,

`A_N(c) = sum_(n>=1, n odd) sieveSeq N c n/[n(n+1)]`.

These sums converge: the fixed-horizon sieve response is bounded, and the
pronic reciprocal series telescopes. Expanding the common odd square gives

`P_N(c_t)=P-2t*A+t^2*T`,
`Q_N(c_t)=Q-2t*A+t^2*T`.

Thus `P-Q` is an exact invariant of this native coefficient direction. At
`t*=A/T`, both energies lose `A^2/T`. If `P>Q`, the centered selected energy
is positive: otherwise complete-trace stability would make the centered
sieve energy zero too, contradicting the invariant. Completion of the
square therefore proves unique maximization of `P_N(c_t)/Q_N(c_t)` at `t*`.
The exact gain is

`P_N(c_t*)/Q_N(c_t*) - P/Q = (P-Q)*A^2/[T*Q*Q_N(c_t*)]`.

For nonnegative coefficients the admissible shift interval is
`[-c(2),c(1)]`, while `A>=T*c(1)`. Hence the best nonnegative shift, when
`P>Q`, is `t=c(1)`. Equality `A=T*c(1)` holds exactly when every admitted
odd coefficient beyond 1 vanishes. Any signed maximizer with ratio above 1
has `A=0`; a nonnegative signed maximizer must have every admitted odd
coefficient zero. This is a classification of a necessary extremal condition,
not an assertion that all even-supported inputs are extremizers.

## Paper refutation at horizon three

For positive integers `d`, define the convergent positive series

`E_d = sum_(n>=1) 1/[d*n*(d*n+1)]`.

The native shift reduces any nonnegative candidate of ratio above 1 to
`c(1)=0`, preserving nonnegativity. Write the remaining coefficients
`c(2)=a`, `c(3)=b`. Direct divisibility gives

`P=E_2*a^2+2*E_6*a*b+E_3*b^2`,
`Q=E_4*a^2+2*E_12*a*b+(E_3-E_6+E_12)*b^2`.

The ratio on `a,b>=0`, `a+b=1` is continuous with strictly positive
denominator, so it attains its maximum. Homogeneity and the shift reduction
identify that maximum with `K_3^+`; inputs of ratio at most 1 cannot enlarge
it because the pure `a` input has ratio at least `10/3`.

Let `R=E_2/E_4`. The following exact rational comparisons avoid evaluation
of any logarithmic or special-function constants:

1. Termwise, `E_d/E_(2d)>=4-2/(d+1)`, so `R>=10/3` and
   `E_6/E_12>=26/7`.
2. Retain the first term of `E_4` and bound each remaining term, `n>=2`,
   by `1/[16*n*(n-1)]`. The latter tail telescopes to `1/16`, giving
   `E_4<=1/20+1/16=9/80`.
3. Also
   `4E_4-E_2 = sum_(n>=1) 1/[2n(2n+1)(4n+1)] >= 1/30`.
   Therefore `R<=100/27<26/7<=E_6/E_12`.
4. `E_6<=E_3/2` gives `E_3/(E_3-E_6+E_12)<=2<R`.

The derivative numerator at `(a,b)=(1,0)` in the positive `b` direction is
`2*(E_6-R*E_12)>0`. Equivalently, a sufficiently small positive `b` makes
the exact quadratic difference `P-R*Q` positive. Thus the cone maximum is
strictly greater than `R`, and both coordinates of a cone maximizer are
positive: either endpoint has ratio at most `R`.

For that maximizer, the odd mean is `b*(E_3-E_6)>0`. Its real centering shift
creates a negative coefficient at 1 and increases the coefficient at 2,
preserves every even sieve reading and selected even jump, and strictly
improves the physical ratio. The centered selected energy stays positive.
Its ratio is an admissible signed ratio, proving `K_3^+<K_3`.

## No-go closure and final certificate

- **Failed stronger claim:** exact equality of the signed and nonnegative
  constants at every horizon.
- **Paper killing mechanism:** strict horizon-three cone gap above.
- **Strongest current positive survivor:** exact common odd-energy centering,
  invariant `P-Q`, unique orbit optimizer, and nonnegative extremal restriction.
- **Status:** the algebra audit checked the common odd-energy shift, all four
  rational series comparisons, positivity of the reduced denominator, the
  compact interval normalization, and strictness of the centering improvement.
  The paper proof is dependency-closed. All four leaves below passed named
  source/olean checks without diagnostics. All 48 public declarations passed
  import axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`.
  All leaves are imported by the THIM umbrella; index regeneration and
  `scripts/formal_tools.py lint --check-generated` passed.
- **Retirement:** [universal finite-horizon cone equality](../5-failed/thim-universal-physical-cone-equality.md)
  is closed with the exact positive survivor and strict counterexample both
  proved on paper and in Lean.
- **Counting:** C1 extension; no new independent contribution.

| Leaf in `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/` | Public declarations | Result |
|---|---:|---|
| `FermiOddTraceCenteringAndExtremalRestriction.lean` | 27 | Common quadratic shift, invariant, unique orbit optimum, odd-support restriction |
| `FermiDilatedPronicMassAndRationalBounds.lean` | 12 | Exact pronic sums and rational comparisons |
| `FermiHorizonThreePhysicalGram.lean` | 7 | Actual horizon-three energy matrices and odd mean |
| `FermiFiniteHorizonPositiveConeGap.lean` | 2 | Interior positive-cone extremizer and `K_3^+ < K_3` |

The first final generated-file check found stale `LEAN_API.md` and
`LEAN_OVERVIEW.md` while other work was changing the shared tree. Regenerating
the index and rerunning the gate passed. No full or umbrella build was run.

## Log

- 2026-10-19 — Created after the all-horizon sharp physical limit was formally
  closed. No numerical experiments or empirical conjecture fitting used.
- 2026-10-19 — `/tmp/thim-fermi-odd-centering.lean` is checking the paired
  coefficient shift, common odd mass/mean, and exact changes in both complete
  physical energies. This is scratch verification, not a promoted theorem.
- 2026-10-19 — The centering survivor passed scratch verification and was
  promoted to `FermiOddTraceCenteringAndExtremalRestriction.lean` (491 lines).
  Its named source/olean check passed with no diagnostics. Besides the exact
  common quadratic, it proves the orbit ratio gap, admissible nonnegative
  shift interval, odd-coefficient equality classification, unit-removal ratio
  bound, and odd-support restriction on nonnegative signed extremizers.
  It is wired. All 27 public declarations passed the import axiom audit with
  only standard axioms. Index regeneration and `lint --check-generated` passed.
  Exact pronic comparison and compact-cone arguments remain scratch.
- 2026-10-19 — Exact pronic comparisons passed scratch axiom checks and the
  named source/olean check in `FermiDilatedPronicMassAndRationalBounds.lean`
  (205 lines), with no source diagnostics. This reuses the existing bounded
  pronic summability, telescoping tail, and mathlib parity decomposition.
  The leaf is wired; its final import audit is included in the next scratch
  check. Horizon-three formulas, compact maximization, and the strict gap are
  being checked together. They are not yet certified or counted.
- 2026-10-19 — The full scratch proof of
  `fermiPhysicalInverseConstant_three_strict_cone_gap` passed, including
  `fermiHorizonThree_positive_extremal_exists`, with standard axioms only.
  `FermiHorizonThreePhysicalGram.lean` (183 lines) now passes its named
  source/olean check without diagnostics and is wired. The compact-max proof
  is being cleaned of tactic diagnostic output before final promotion.
  The candidate remains uncounted pending its final certificates and
  significance decision.
- 2026-10-19 — Final gap leaf passed its named source/olean check with no
  diagnostics. Final nine-declaration import audit for the Gram and gap leaves
  passed with standard axioms only. Index regeneration and generated-file lint
  passed. Promoted this card to formalized; retired universal cone equality
  with its formal positive survivor. Significance audit bundles the result
  into C1, retaining the qualified count of 1/100.
