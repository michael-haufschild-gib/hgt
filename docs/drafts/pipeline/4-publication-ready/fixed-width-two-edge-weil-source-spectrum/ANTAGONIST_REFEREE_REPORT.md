# Antagonist referee report

Manuscript: **Fixed-Width Weil Tomography for the Riemann Xi Divisor: Exact Prime--Gamma
Realization and Negative-Mass Spectrum**

Standard applied: skeptical referee at a renowned general mathematics/science journal, not a
friendly project reviewer.

Date: 2026-07-27

## Executive assessment

Initial verdict: **major revision**.

Revised verdict after route-vitality audit: **reject at the requested significance threshold**.

The central theorem is correct-looking and quantitatively sharper than a bare RH equivalence, but
its information flows from the continued Xi divisor through an exact explicit formula to a family
of classifiers. No independent source estimate, positivity theorem, operator limit, or divisor-free
producer consumes the classification. It therefore describes false-RH behavior without advancing
the missing implication that an active RH route must prove.

Exact finite prime--Gamma realization does not repair this defect. It gives a source-side expression
for each detector value, but the theorem that this expression has the required sign or growth is
still precisely RH. The manuscript is useful as a specialist tomography/classification paper, not
as community-scale progress toward RH and not as a no-go theorem for CCM, Hilbert--Pólya, Weil
positivity, or another famous route.

## Round-one objections

### 1. Is this only another RH equivalent?

**Objection.** A sign criterion alone would be insufficient for a broad journal. It could be a
repackaging of Weil positivity.

**Required answer.** State and prove information not exhausted by the endpoint equivalence:

- exact one-sided exponent for every horizontal zero-free half-plane;
- exact negative-part Dirichlet abscissa;
- exact cumulative negative-mass threshold;
- cofinal two-sided oscillation below every false-RH transverse exponent;
- individual completeness for generic smooth profiles.

**Resolution.** Manuscript now makes this classification, not the binary sign criterion, the
central theorem. Exact results terminate in named Lean declarations.

### 2. Smooth robustness was stated too weakly

**Objection.** “All profiles” class-wide equivalence obscured a stronger theorem latent in the
argument.

**Required answer.** Determine whether one fixed generic profile is individually complete.

**Resolution.** Two unconditional Lean corollaries were added:

- `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_nonneg`;
- `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_eventually_bddBelow`.

Paper now states that every individual member of a dense residual profile set is an RH-complete
detector.

### 3. Hidden extremal-zero assumption

**Objection.** Arguments using
`delta_* = sup Re(w)` often silently choose a rightmost zero.

**Required answer.** Make proof work if supremum is not attained.

**Resolution.** Shifted-zeta pole tomography treats every zero separately. Landau step chooses a
real convergence coordinate strictly below `1 + delta_*`; contradiction uses supremum only.
Manuscript explicitly records this. Lean theorem uses `sSup`, not a maximizing zero.

### 4. Multiplicity cancellation

**Objection.** Infinite sums of shifted zeta functions can cancel poles, especially at repeated Xi
zeros.

**Required answer.** Prove exact local order and residue with multiplicity.

**Resolution.** Completed numerator has order `m - 1` at a zero of multiplicity `m`, while
off-support terms have order at least `m`. Quotient therefore has a simple pole with residue
`m A_L(w)^2`, nonzero by half-plane nonvanishing. Paper and Lean both retain this calculation.

### 5. Sharp-window regularity

**Objection.** A discontinuous rectangle cannot be inserted into a smooth Weil criterion without
proof.

**Required answer.** Either smooth it with controlled limit or prove sharp formula directly.

**Resolution.** Paper defines zero-side polarization by an absolutely convergent divisor sum and
proves the source formula by contour exhaustion. Vertical edge, Gamma integral, Fourier inversion,
and finite autocorrelation support are addressed directly. Barner specialization is acknowledged;
no general explicit-formula novelty is claimed.

### 6. Source circularity

**Objection.** “Prime--Gamma source” is meaningless progress if Xi zeros are embedded in its
definition.

**Required answer.** Audit definitions.

**Resolution.** `g_L(n)` contains only a finite von Mangoldt autocorrelation and completed
Gamma--polar integral. Divisor appears only in proved equality. Claim trace records source purity.

### 7. The tempting source bound is circular

**Objection.** Critical cumulative bound could be advertised as a prospective RH proof while
the theorem shows it is equivalent to RH.

**Required answer.** Separate proved classification from missing endpoint estimate.

**Resolution.** Manuscript states explicitly that
`O_epsilon(X^(1+epsilon))` is identified as RH, not independently proved. No unresolved estimate
is included among conclusions.

### 8. False strict bound on transverse supremum

**Objection.** Individual zeros satisfy `Re(w) < 1/2`, but their supremum may equal `1/2`.

**Resolution.** Corrected `0 < delta_* <= 1/2`.

### 9. Totalized logarithm at zero

**Objection.** Lean's real logarithm is totalized; paper mathematics must not use `log 0`.

**Resolution.** Paper defines logarithmic samples only for positive integers. Formal theorem is
stronger and includes Lean's totalized zero case, but no paper argument uses it.

### 10. Literature collision and priority

**Objection.** Weil, Yoshida, Bombieri, Suzuki, Connes--Consani, CCM, Barner, and recent Groskin
work cover nearby ground.

**Required answer.** Identify exact boundary using current primary sources.

**Resolution.** Literature section concedes all parent mechanisms. Full-text and targeted searches
through July 2026 found no statement combining:

- one arbitrarily fixed translated two-edge profile geometry;
- logarithmic integer sampling;
- cofinal lower and two-sided power divergence;
- exact finite prime--Gamma coefficient;
- negative abscissa and cumulative exponent recovering every horizontal Xi bound;
- individual completeness for a residual smooth profile set.

Search absence is not proof of priority. Manuscript requires independent specialist priority
review and does not claim otherwise.

## Correctness review

### Analytic chain

- Divisor summability: classical zero count supplies reciprocal-square and reciprocal-`3/2`
  convergence.
- Edge fold: algebraic identity is exact; discarded channel is uniformly summable for fixed width.
- Carrier: ordinary Dirichlet series and shifted-zeta continuation use locally normal sums.
- Pole support: multiplicity-safe and noncancelled.
- Landau: applied only after finite deletion and explicit nonnegative correction.
- No-go assumptions: no rightmost zero, gap, simplicity, or numerical verification.
- Explicit formula: sharp contour proof; finite support follows from autocorrelation.
- Cumulative theorem: positivity plus Abel summation; not claimed independently novel.
- Smooth theorem: Baire intersection of complements of proper closed kernels.

No correctness blocker remains in paper architecture. Final axiom and module build must include the
new individual-profile corollaries.

## Significance review

The manuscript does not meet the requested RH significance criterion.

1. It compresses a broad positivity framework to explicit fixed-width scalar detectors.
2. It replaces a binary equivalent by a quantitative failure law.
3. It makes detector values finite on the prime side.
4. It proves residual individual completeness for smooth profiles.

Those are mathematically substantive classifier results. They do not supply the missing sign,
nonnegativity, convergence, or spectral-realization theorem. They also do not exclude a natural
published route: fixed-width scalar tomography is a chosen diagnostic layer, not a compulsory
architecture of CCM or Hilbert--Pólya. The direct consumer audit found only further equivalences,
abscissa classifications, and packaging theorems. No theorem uses this classification to establish
a new zero-free region or another unconditional arithmetic consequence.

Accordingly, the result may interest specialists in explicit formulae and RH equivalences, but an
honest general-journal referee cannot call it high-interest progress toward an RH proof.

## Round-two route-vitality audit

The expanded corpus does not rescue the paper.

- The cofinal Sonin carrier theorem can adapt a shell depth to arbitrary moving vectors and preserve
  their codiagonal to a prescribed vanishing scale. Its Xi specialization reconstructs an
  already-known continued source trace. It does not construct the anti-causal divisor column and
  does not prove the four-unit nonexpansive estimate required by the live CCM incidence problem.
- The clock-splitting theorem recovers an omitted diagonal collision with vanishing added energy.
  It has no downstream consumer proving a sign, a source-to-divisor contraction, or a zero-free
  region.
- The scalar critical-clock blindness theorem is a valid no-go for arguments using only the
  four-unit critical clock budget. Published CCM does not reduce to that scalar datum, so this is
  an internal route filter, not a CCM death theorem.
- The complete-carrier obstruction in the Deninger/Hilbert lane is Hellinger--Toeplitz folklore:
  an everywhere-defined symmetric operator on a Hilbert space is bounded. It cannot support a
  novel famous-route no-go.

These facts answer the decisive question negatively: the present synthesis encodes true terminal
knowledge and useful internal diagnostics, not a theorem with a live edge into the unresolved
source-producing step.

## Closed rejection gates

- [x] Current primary-literature attack
- [x] Exact claim trace
- [x] Sequential targeted `lake env lean` checks
- [x] Repository formal lint
- [x] Initial standard-axiom audit
- [x] PDF compilation and sampled visual inspection
- [x] Direct downstream-consumer audit
- [x] Comparison with live CCM source-incidence obligation
- [x] Comparison with expanded Sonin, clock-splitting, and Deninger corpus
- [x] General-journal significance challenge

No final build or publication promotion is warranted. Retire this manuscript from the active
candidate set unless the corpus later supplies an independent source theorem that consumes its
classification.
