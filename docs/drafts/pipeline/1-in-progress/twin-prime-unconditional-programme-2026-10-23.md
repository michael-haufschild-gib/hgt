# Unconditional twin-prime programme

- **ID:** twin-prime-unconditional-2026-10-23
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** user attachment `170605ee-4345-4eed-9981-4feb5812e448/pasted-text-1.txt`
- **Statement:** For every natural number `N`, there exists `p > N` such that `Nat.Prime p` and `Nat.Prime (p + 2)`.

## Goal and completion gate

Prove the statement unconditionally in Lean. Supporting identities, reductions,
bounded-gap results, and failed-route audits do not satisfy this goal.
All directly related Lean belongs in `formal/GaloisForLFunctions/twin-prime/`,
with its own umbrella. No analytic assumptions, new axioms, placeholders,
computational certificates, or raised elaboration limits. Compile leaf modules
only with `lake --old env lean GaloisForLFunctions/twin-prime/<Module>.lean`.

- [x] 0 → 1: exact target and research constraints recorded.
- [ ] 1 → 2: dependency-closed paper proof of twin-prime infinitude.
- [ ] 2 → 3: unconditional Lean theorem, successful leaf audit, axiom audit.
- [ ] 3 → 4: independently audited paper and certificate.

## Internal frontier: inspected evidence

Corpus searches precede mathlib searches. Initial queries:

- `twin prime conjecture infinitude prime pairs parity obstruction`
- `"twin prime"` (lexical, uncapped modules)
- `additive shifted correlation of von Mangoldt prime pairs at fixed gap`
- `Liouville parity cancellation shifted primes sieve`

The exact phrase search surfaced only
`weightRamanujanCoeff_parityTwin_prime`, in
`TransHorizonIncidenceMechanics/ParityPairAtHalfDamping.lean`.
This concerns a parity-conjugated arithmetic weight, not twin primes.
Inspected theorem `parityPair_at_half_damping` asserts equal Ramanujan
coefficient amplitudes but different accumulated receiver-energy behavior.
Thus diagonal spectral statistics alone can lose relevant arithmetic signs.
It is a methodological warning, not a proof of an additive prime correlation.
No twin-prime infinitude theorem has been located by these searches.

## External frontier: primary sources checked

1. [Polymath8b, 2014](https://arxiv.org/abs/1407.4897), Theorem 1.4:
   unconditional bounded gaps of at most 246; gap 6 under generalized EH.
   Section 8 discusses parity-twisted weights and explicitly calls its general
   barrier discussion partly heuristic. It is not a theorem excluding all
   possible future methods.
2. [Stadlmann, 2026-08-31](https://arxiv.org/abs/2608.31126): preprint claims
   a bound of 240. Abstract checked; full proof not audited here.
3. [Lü–Wang–Wu, 2026-10-14](https://arxiv.org/html/2610.20242v1),
   Theorem 1: preprint claims `sum_{p≤x} μ(p+2) = o(π(x))`.
   Theorem 2 concerns signs among squarefree shifted primes. Statements
   inspected. Relevant determinant-energy proofs in §§4--5 and
   Appendix A, plus the character--Mellin input, were subsequently
   checked for the marked-average deduction. This is a scoped source
   audit, not a formal verification of the entire paper or its ancestry.
   These statements do not themselves assert twin-prime infinitude.
4. [Wang–Yi, 2026-10-12](https://arxiv.org/abs/2610.16394): abstract reports
   a dynamical extension of two-point Chowla, citing a recent proof of that
   case. Abstract checked only; no such result is assumed in Lean.
5. [Smith, 2025](https://arxiv.org/abs/2511.14810): a prime-pair distribution
   conjecture implies twin primes. An unproved prime-pair input cannot be
   imported as a premise of the requested theorem.

## Research direction

Use the corpus's separation of amplitudes from signed arithmetic data to
identify an exact signed quantity that detects primes rather than all numbers
of one factor-count parity. Audit any new cancellation theorem at its actual
weight, modulus range, and error scale before transferring it to a sieve.

**[OPEN CORE]** No unconditional estimate giving a positive unbounded supply
of prime pairs at the fixed shift 2 has yet been proved here. In particular,
unrestricted cancellation of `μ(p+2)` cannot simply be restricted to numbers
whose least prime factor grows with the counting scale.

## Research protocol

Each exact conjecture gets a corpus/literature attack and a verdict:
`FALSE`, `CIRCULAR`, `REDISCOVERED`, `BRIDGE`, `INSIGNIFICANT`, or
`SURVIVES PRELIMINARY ATTACK`. Prove its exact surviving statement on paper
before Lean. Failed routes require a positive-survivor audit and, when a
nontrivial survivor has a closed proof, formalization of that exact theorem.
Do not count an equivalent reformulation as a solution or new knowledge.

## Current audit and continuation

- Current source-specific obstruction and positive survivor:
  [relative residue matching](../2-fully-proven/twin-prime-residue-matching-boundary.md).
  An explicit bounded second row exactly saturates the actual
  Liouville correlation on separated prime-shift residue classes.
  Its relative mass is eventually at least `1/(20 log(2D))`,
  uniformly in arbitrarily large complete-block horizons. Thus
  the arbitrary-row centering theorem cannot be strengthened
  to the required relative normalization. The sharp finite norm
  has a complete paper proof and is under Lean verification.
  The actual two-row affine target remains open; any successful
  relative proof must retain both arithmetic rows.
- Current certified transfer:
  [integer-start Möbius windows](../3-formalized/twin-prime-integer-start-moebius-window.md).
  The later all-length spectral-head source controls the plain
  Möbius polynomial. A complete paper argument transfers it to
  `o(N l^2)` uniformly over integer lengths `log N<=l<=N`, using
  a shrinking geometric partition and paid endpoint errors.
  This is a classical deduction, not a new scientific claim.
  The additive-frequency supremum, centering's quantitative rate
  and full length range, relative affine correlation, and positive
  prime-pair mass remain unproved. The complete leaf passed;
  all four capstone audits contain only standard foundational
  axioms. The own umbrella is wired; it was not compiled.
  Verification: lexical corpus search returns the principal
  capstone. All seven owned source/card files passed whitespace,
  relative-link, and applicable forbidden-directive checks.
  Temporary axiom-print commands and all sixteen owned scratch
  files were removed. No unchanged earlier leaf was rebuilt.
- Current certified removal of damping:
  [cofactor rectangles](../3-formalized/twin-prime-cofactor-damping-removal.md).
  On every selected subset of `[2,X]`, `ZW<=X` and the explicit
  clock `epsilon=(1+log(X+2))^-6` give normalized error at most
  `6/(1+log(X+2))`. The same clock approximates the actual
  projected prime-pair average with error at most
  `8/(1+log(X+2))^3`. All five new capstones passed the leaf
  check and standard-axiom audits; no analytic premise was added.
- Verification of this batch: corpus indexes regenerated; the
  principal damping-removal capstone is returned by lexical
  search. All eight owned source/card files passed whitespace,
  relative-link and applicable forbidden-proof-directive checks.
  The existing umbrella import is intact; no umbrella was built.
  Audit directives and all 28 owned search/PDF scratch files were
  removed. Unchanged earlier Lean checks were not repeated.
- Current analytic deduction:
  [coupled-residue centering](../2-fully-proven/twin-prime-coupled-residue-centering.md).
  Keeping the shift-dependent congruence inside one Fourier
  expansion avoids a modulus loss. A paid square-divisor
  truncation extends the argument to Möbius against any
  unit-bounded second row. This is a paper deduction from the
  checked short exponential-sum theorem; it is not Lean-certified.
- Further certified analytic deduction:
  [uniform Ramaré cofactor](../3-formalized/twin-prime-ramare-weighted-cofactor-cancellation.md).
  A positive smooth-divisor convolution transfers the existing
  signed Möbius prefix rate to `mu(n)/(omega_P(n)+1)`, uniformly
  for designated primes below `exp((log X)^beta)`, every fixed
  `beta<1`, and Mellin frequencies up to every fixed `X^kappa`,
  `kappa<1`. The tail moment is proved by a finite Euler product;
  no unproved distribution input enters the Lean proof.
  Six capstones now pass the leaf and transitive axiom audits;
  only standard foundations occur. Its stronger finite form
  separates the frequency horizon from the prime cutoff and
  reaches frequencies close to the cofactor length. The own
  umbrella is wired. Additive-window assembly remains open.
  Verification: the cleaned leaf passed again; corpus indexes
  were regenerated. Owned source/card whitespace and relative
  links passed, as did the forbidden-proof-directive check.
  Temporary axiom-print commands and all 36 owned search scratch
  files were removed. No umbrella or unrelated leaf was built.
- Precise remaining uniformity question:
  [fixed determinant, growing coefficients](twin-prime-fixed-determinant-uniformity.md).
  Canonical reduced intercepts put the actual cofactor faces on
  intervals starting at zero. Fixed determinant four does not
  remove the growing progression modulus. The estimate still
  needed is relative to the actual affine sample count; a
  full-interval normalized rough-shift bound does not provide it.
  A direct prime-stripping operation now identifies a closed
  family of reduced primitive frames with the same determinant,
  exact parameter normalization and a square-divisor error at
  most `T/p^2+1`. This suggests working on the frames directly.
  Its sign reversals admit the gauge `lambda(ac)`, so no decay
  is inferred from the transport identity alone. The uniform
  estimate for the actual source remains the next research test.
- Current analytic result:
  [balanced CRT compensation](../2-fully-proven/twin-prime-balanced-crt-compensation.md)
  has a complete paper bound `O(Y^(2-1/400))` for `Y^2<=X<=4Y^2`,
  using the checked classical inverse-phase theorem and explicit
  smoothing/tail bounds. This analytic input is not Lean-certified
  here; no conditional Lean surrogate was introduced.
- Current certified compensation:
  [axis and cofactor identities](../3-formalized/twin-prime-compensated-damping-coefficients.md)
  remove the inverse damping loss and transfer the coefficient
  cost to `log m`. Unit-cofactor terms vanish exactly, including
  both faces of the physical pair expansion. Ten capstones passed
  the leaf and foundational-axiom audits without analytic premises.
- Current certified boundary:
  [full-height CRT kernel](../3-formalized/twin-prime-full-height-crt-boundary.md)
  is exactly the shift; an explicit positive odd block has
  normalized period-transfer defect at least `1/20`. Five
  capstones passed their leaf and foundational-axiom audits. The
  [uniform full-height extension](../5-failed/twin-prime-uniform-full-height-crt-transfer.md)
  is closed with this positive survivor, while actual Möbius
  compensation remains available across the decomposition.
- Current verification: both changed leaves passed and all fifteen
  new capstone axiom audits contain only standard foundations.
  The new umbrella import is wired; no umbrella was built. Index
  regeneration passed and both new principal capstones are returned
  by corpus search. Ten owned source/card files passed whitespace
  and relative-link checks. No forbidden proof directive or temporary
  axiom-print command remains in the changed Lean leaves.
- Next source-specific target:
  [nonunit cofactor dispersion](twin-prime-nonunit-cofactor-dispersion.md).
  Retain the complete truncated Möbius dilation and its mixed
  terms. Unit cancellation does not justify termwise estimates
  for every remaining face. The actual squared Fourier transform's
  shift-two coefficient still lacks the required bound. The new
  SAEI path theorem was inspected; its gauge and packing data
  have not been constructed for this source and are not assumed.
- Completed RH-language synthesis:
  [twelve-programme reformulation](twin-prime-rh-language-reformulation.md).
  All requested READMEs read and selected source statements checked.
  The common source is the existing damped Möbius divisor response;
  twin pairs select its gap-two mixed derivative after squarefree
  projection. The source's prime-resolving diagonal is pre-crossover,
  so fixed-damping dissipation cannot simply be transferred to it.
- New certified quantitative bridge:
  [physical damping diagonal](../3-formalized/twin-prime-damped-pair-diagonal.md).
  At the explicit schedule `epsilon=log^(-4)(X+h+2)`, the projected
  divisor pair average differs from the actual prime-pair log average
  by at most `1/log(X+h+2)` and tends to zero. All five capstones
  have no proposition-valued premises and passed standard-axiom
  audits. This supplies no positive lower bound.
- New certified sign diagnostic:
  [complex determinant parity bridge](../3-formalized/twin-prime-determinant-parity-bridge.md).
  Entry conjugation preserves all finite unit-ball tests and every
  conjugated four-cycle, for arbitrary complex weights. All four
  capstones passed standard-axiom audits. The actual shifted parity
  correlations remain to be estimated.
- User-requested supporting work:
  [RH--twin-prime pair-kernel bridge](../3-formalized/twin-prime-rh-pair-kernel-bridge.md).
  The existing RH square-window correlation criterion and exact
  twin-prime tail detection can read one von Mangoldt pair kernel.
  Paper proof and all five Lean capstone audits passed.
  A sharper formalized deduction shows that deleting the explicit twin
  slice leaves this RH growth criterion unchanged, because every
  individual lag already has a uniform subpower bound. This
  establishes a common arithmetic representation and its precise
  limitation, not an equivalence between the two conjectures.
- Completed finite audit:
  [proper-divisor mark boundary](../3-formalized/twin-prime-divisor-mark-transfer-boundary.md).
- Active analytic target:
  [centered root distribution](twin-prime-centered-root-distribution.md),
  following the [signed cubic roughness attack](twin-prime-signed-cubic-roughness.md).
- Current mechanism test:
  [mark-preserving root average](../2-fully-proven/twin-prime-mark-preserving-root-average.md).
  The finite modulus-average bound avoids a power loss in the number
  of moduli. Its elementary weighted cofactor energy is bounded on paper
  with exponent independent of the number of marks. Both averaged
  Type I terms now have paper proofs using the classical maximal
  Möbius progression theorem, with coprimality and truncation errors
  checked. The paper deduction is now assembled from the cited
  Type II energy theorem, whose relevant proof was inspected.
  Its unconditional Lean formalization and all removal steps
  remain open.
- Earlier exact analytic test:
  [cofactor sampling energy](twin-prime-cofactor-sampling-energy.md).
  Splitting root divisors between selected labels and cofactors
  exposes a missing `1/d` density if consumed selections are
  treated separately. This pointwise strengthening remains open,
  but is unnecessary for the partial-layer application.
- New paper deduction:
  [partially consumed marking groups](../2-fully-proven/twin-prime-partially-consumed-mark-energy.md).
  Aggregating consumed selections first gives a bounded
  modulus-dependent cofactor weight. Existing energy then controls
  every Type II layer retaining sufficiently many selected groups.
  Layers retaining too few groups, including full consumption,
  and removal of the marks remain open. Its
  [finite modulus-energy step](../3-formalized/twin-prime-root-modulus-energy.md)
  is formalized and axiom-audited; the analytic theorem is not.
- Current hard endpoint:
  [fully consumed signed determinant sum](twin-prime-consumed-mark-determinant.md).
  Exact equation `mn-qh=-2` retains two Möbius factors and all
  arithmetic coefficients. Classical determinant estimates need
  smooth variables that have not been supplied. The positive
  empty-label energy has a
  [formalized order-`X` lower bound](../3-formalized/twin-prime-semiprime-energy-lower-bound.md),
  uniform in all cutoffs below the factor scale. The
  [unsigned shortcut is closed](../5-failed/twin-prime-unsigned-empty-label-energy.md);
  its missing logarithmic saving cannot simply be conjectured.
- Second completed finite audit:
  [cubic dilation classification](../3-formalized/twin-prime-cubic-dilation-classification.md).
  Its exact set equality identifies nontrivial cubic rough edges as prime
  dilations of twin pairs. This does not count or produce such edges.
- Main requirement audit: corpus research done; current primary sources
  inspected at stated scopes; three failed routes have formalized positive
  survivors. Dependency-closed paper proof of infinitude **missing**;
  unconditional Lean infinitude theorem **missing**; main goal **not achieved**.
- Scientific audit: no new number-theoretic knowledge established. The
  formalized identity is known mathematics. The hard analytic estimate
  remains the research target; no theorem is declared by replacing it with
  a premise. Next cycle must attack that estimate rather than produce
  further equivalent definitions or routine wrappers.
- Verification: all five owned research leaves passed their
  leaf checks and capstone standard-axiom audits. The own umbrella
  and root import are wired; neither umbrella was built. Indexes
  were regenerated and the latest RH deletion capstone is returned
  by the corpus search. All 21 owned source/card files passed
  whitespace and relative-link checks. Global lint still reports
  unreachable modules, research leaves at package root, and stale
  `LEAN_API.md`/`LEAN_OVERVIEW.md` during concurrent work; no global
  pass is claimed. All owned research scratch files were removed.
- Latest structural batch: the RH pair-kernel criterion, exact
  twin-prime tail criterion, pair partition, uniform lag bound,
  and RH criterion after deleting twins are certified in
  `RHPairKernelBridge.lean`. This completes the user's supporting
  bridge request, not the unconditional twin-prime goal. The
  shared aggregate growth class does not supply the missing
  fixed-gap positivity estimate.
- Latest verification: both additional leaves, `DampedPairDiagonal`
  and `DeterminantParityBridge`, passed foreground checks and all
  nine capstone axiom audits. Both imports are wired; the umbrella
  was not built. Corpus indexes regenerated. Owned source/card
  whitespace, relative links, and forbidden-proof-directive checks
  passed. Earlier unrelated global lint findings are not claimed
  resolved. Temporary audit directives and owned research scratch
  files removed.

## Log

- 2026-10-23 — Read full task and repository rules. Existing unrelated edits
  left intact. Began primary-source and corpus audit; twin-prime goal remains
  unproved. October 2026 shifted-prime cancellation claims require audit at
  their precise scope before selecting a route.
- 2026-10-23 — Closed the nonempty-divisor-mark transfer route. Exact finite
  energy minimum and signed decomposition formalized in
  `TwinPrime.exists_divisorMark_minimum` and
  `TwinPrime.twinMass_eq_signed_residual_difference`; no extra analytic
  premises, no new axioms, leaf compile and capstone axiom audits passed.
  See [survivor](../3-formalized/twin-prime-divisor-mark-transfer-boundary.md)
  and [failed transfer](../5-failed/twin-prime-nonempty-divisor-mark-transfer.md).
  This is a known finite identity, not new scientific knowledge or a proof
  of the target. Next attack: signed cancellation on polynomially sifted
  shifted primes, with the exact divisor and residue dependence retained.
- 2026-10-23 — Direct rough-graph transfer failed at its label/height
  interface; positive cubic-edge classification formalized and audited.
  Mathlib-only leaf passed with standard foundational axioms. No new
  scientific knowledge claimed. Recovered Murty–Vatwani's author-hosted
  PDF and checked the centered distribution theorem and omitted moving
  endpoint in the switched tail. Next exact target and operator obligations
  recorded in `twin-prime-centered-root-distribution.md`. Infinitude remains
  unproved; neither completion gate is checked.
- 2026-10-23 — Refined the new target to odd squarefree moduli, since the
  switched coefficient is `μ(e)`. Recorded the exact nonprincipal-character
  correction and dual cofactor sum, retaining `qh-mn=2`, the centered term,
  coprimality, and individual endpoints. These are research reductions,
  not new analytic estimates. The next work is the signed determinant
  estimate itself; no further elementary detector wrapper is needed.
- 2026-10-23 — Expanded the actual centered cofactor Gram expression.
  Its diagonal is manageable; the signed off-diagonal and centering
  remain open. Shared label factors require an extra divisibility
  condition beyond the determinant equation. Checked the corpus's
  exact Kloosterman Fourier collapse and current fixed-modulus bounds;
  no matched frequency localization was established.
- 2026-10-23 — Started a distinct analytic test with moduli coprime to
  the marking primes. Derived its positive-energy transfer cost and
  proved the elementary `tau(h)^2` energy bound on paper with logarithmic
  exponent `17`. Recorded a maximal-endpoint Fourier reduction and a
  coprimality reduction for prospective Möbius Type I estimates. These
  do not prove the marked prime-sum estimate or the main conjecture.
  No new scientific result or additional Lean theorem claimed. Existing
  Lean audits were not rerun because their sources were unchanged.
- 2026-10-23 — Checked the exact Möbius Bombieri–Vinogradov
  statement in Murty–Vatwani (2018), Proposition 3. Proved the
  uniform-coprimality extension and root-averaged Type I estimate
  on paper, using smaller Vaughan cutoffs. Both truncation errors
  are controlled by divisor multiplicity rather than the number
  of moduli. Signed Type II energy and removal of marks remain
  open; no twin-prime theorem or new Lean result claimed.
- 2026-10-23 — Completed the marked-average paper deduction,
  including source-level energy audit and full precision accounting.
  Moved its card to `2-fully-proven`; this records a deduction from
  cited analytic theorems, not a formal certificate for those
  theorems. Lean formalization remains open. Mark removal and
  moduli consuming marks remain the arithmetic obstacles to the
  unmarked target. No scientific novelty or twin-prime proof claimed.
- 2026-10-23 — Closed partially consumed Type II layers on paper
  by aggregating consumed selections before Cauchy--Schwarz.
  The previously proposed pointwise sampling estimate is stronger
  than this application needs. Recorded the exact residual layers.
  Found pinned external Lean source for the shift-1 determinant
  method in Plasma AI's `erdos-408`; version and shift differences
  prevent treating it as an already verified dependency here.
- 2026-10-23 — Formalized the finite modulus-energy inequality
  with weights depending on both modulus and cofactor. The
  fourth-power capstone passed the leaf compile and standard-axiom
  audit. This certifies finite transfer only, not the signed
  arithmetic energy or the requested infinitude theorem.
- 2026-10-23 — Closed the unsigned empty-label shortcut with an
  explicit prime-product lower bound. The full positive survivor
  is formalized using the corpus's unconditional PNT, with no
  new analytic premise. The signed determinant endpoint remains open.
- 2026-10-23 — Completed the user-requested RH--twin-prime bridge.
  Both are expressed through one von Mangoldt pair kernel; the
  fixed-lag bound and deletion criterion precisely identify the
  aggregate criterion's limitation. All five capstone axiom audits
  and the leaf check passed. Neither conjecture is proved.
- 2026-10-23 — Completed the quantitative damping diagonal and
  complex parity certificates. Both leaf checks and all nine capstone
  axiom audits passed, without any analytic premise. This batch is
  **progress on the requested bridge**, not a proof of infinitude or
  a claim of new number-theoretic knowledge. The exact next analytic
  target is the source-specific signed finite-horizon/period defect
  at shrinking damping. A balanced CRT Fourier attack now retains
  the inverse-residue phases and physical endpoint factor explicitly;
  no varying-modulus cancellation bound or tail compensation has
  been proved. Main completion gates remain unchecked.
- 2026-10-23 — Obtained a balanced-block paper estimate from a
  checked classical theorem. Certified both exact compensations
  and the full-height boundary: two leaf checks, fifteen capstone
  audits, standard foundational axioms only. The generic full-height
  extension fails, but the actual source cancels its unit faces
  algebraically. The next core is growing nonunit cofactors and
  their mixed terms. No new number-theoretic result beyond the
  literature, source-specific saving, lower prime-pair mass, or
  infinitude theorem is claimed. No difficulty was replaced by
  an unproved Lean premise. Main completion gates stay unchecked.
- 2026-10-23 — Certified uniform cofactor damping removal and
  compatibility with the prime-pair observable: five new capstones,
  standard foundational axioms only. Audited the fixed-form
  two-point proof's coefficient dependence and derived a uniform
  coupled-residue rough-shift estimate, including its Möbius
  version, on paper. This removes a centering loss but not the
  fixed-shift arithmetic core. No scientific novelty or infinitude
  claimed. Further work must establish the missing relative
  progression or aggregate cofactor saving, rather than add
  another equivalent detector or an assumed analytic interface.
- 2026-10-23 — Completed the uniform Ramaré-weight paper bound
  after checking the actual corpus coefficient. Existing damped
  contour theorems retain a prime-set correction; the new
  convolution argument pays a positive smooth tail separately.
  This is a classical-method bridge, not new number-theoretic
  knowledge or a fixed-shift prime-pair estimate. Next formal
  target is this exact uniform bound, without a premise asserting
  its arithmetic input. No requested infinitude gate is complete.
- 2026-10-23 — Certified the uniform Ramaré-cofactor theorem,
  including its stronger finite two-scale bound: six capstones,
  standard foundational axioms only. Moved its card to
  `3-formalized` and wired the own umbrella. This continuation
  is **progress**, not completion. No new scientific knowledge
  beyond classical methods is claimed. Checked the scope of
  the uniform cofinal first-moment theorem and retained the
  missing second row explicitly. Derived a native affine
  prime-stripping representation preserving determinant four
  and reduced intercepts; its relative-normalization estimate
  remains unproved. No analytic premise or interface replaces
  that estimate. The infinitude gates remain unchecked.
