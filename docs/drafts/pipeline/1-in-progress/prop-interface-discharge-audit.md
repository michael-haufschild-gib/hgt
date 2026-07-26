# Prop-interface discharge audit: HTGeometry, HilbertMetric, RHTower

- **ID:** prop-interface-discharge-audit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** loop mandate — audit the three owned areas for undischarged hypotheses / `Prop` interfaces
- **Statement:** every `Prop` interface consumed as a hypothesis in `HTGeometry`, `HilbertMetric`,
  `RHTower` is either (a) produced by an unconditional or corpus-discharged theorem, (b) proved
  unsatisfiable with an exact obstruction plus a satisfiable structural replacement, or (c) recorded
  as a genuinely open analytic input with its named open core.

## Goal
Remove silent conditionality from the three owned theorem areas.  A `Prop` interface that no
theorem in the corpus ever concludes is either an undischarged premise (recoverable) or a vacuous
one (fatal to every consumer).  Both cases must be resolved explicitly.

## Audit instrument (reproducible)
A Lean metaprogram over the whole environment, not a text grep.  For every project theorem it
records the head symbol of each `Prop`-valued binder and of the conclusion, using a
**non-reducing** `forallTelescope` (a reducing telescope unfolds a `Prop` def in the conclusion and
loses the producer, which is why index/grep searches under-report producers).

- script: `scratchpad/AuditAll.lean` pattern — import `GaloisForLFunctions.MainTheorems`,
  `forallTelescope`, emit `module|theorem|propHypHeads|conclHead`, plus every project
  `Prop`-valued `def`/`inductive`.
- corpus size measured 2026-07-26: 71 232 project theorems, 1 721 project `Prop`-valued
  definitions.
- result: **258** project `Prop` interfaces are consumed as a hypothesis inside the three areas and
  concluded by **no** theorem anywhere in the corpus.  Ranked worklist:
  `prop-interface-discharge-worklist.md` (next to this card).

## Worklist status
- HilbertMetric full-CCR layer (`IsFullCCRMatrixTuple`, `IsCommutingFullTuple`,
  `IsInvariantFullCompression`) — **in progress**, see below.
- 255 remaining entries — untouched.

## Finding 1 — the finite full-CCR interface is unsatisfiable
`IsFullCCRMatrixTuple T : ∀ i j, T i * (T j)ᵀ = δᵢⱼ • 1 + (T j)ᵀ * T i` on
`Matrix (n ⊕ m) (n ⊕ m) ℝ`.  Taking `i = j` and the trace, `tr (T Tᵀ) = tr (Tᵀ T)` forces
`tr (1) = 0`, i.e. `Fintype.card (n ⊕ m) = 0`.  So for `Nonempty I` the interface holds only on the
empty space: every `CCRPowerConcavity` theorem carrying it is vacuous in positive dimension.
This is the finite-dimensional CCR obstruction (Wintner/Wielandt) in exact matrix form.

## Structural replacement (satisfiable, keeps every downstream theorem)
The proofs only ever read the relation on the **upper-left block**.  Replace by
`IsBlockCCRMatrixTuple T : ∀ i j a b, (T i * (T j)ᵀ) (inl a) (inl b) = (δᵢⱼ • 1 + (T j)ᵀ * T i) (inl a) (inl b)`.
Then, under `IsInvariantFullCompression T`:
`IsBlockCCRMatrixTuple T ↔ IsCCRCompletion (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)`,
and `IsFullCCRMatrixTuple T → IsBlockCCRMatrixTuple T`, so the existing statements are corollaries.
Non-vacuity is then inherited from the already-proved Gaussian coherent completion
(`GaussianJetPositivity.exists_gaussianCoherentCCRCompletion`,
`gaussianCoherentCompression_commutes`) via `T i = Matrix.fromBlocks (A i) (B i) 0 0`.

## Gates
- [x] 0 → 1  in-progress: audit instrument built, worklist ranked
- [ ] 1 → 2  fully-proven on paper for each worklist entry touched
- [ ] 2 → 3  formalized: Lean module per finding, `lake build` green, lint PASS
- [ ] 3 → 4  n/a (infrastructure card)

## Log
- 2026-07-26 — created in 1-in-progress; audit instrument built; 258 undischarged interfaces found;
  finding 1 (finite full-CCR unsatisfiable) proved on paper with structural replacement.
- 2026-07-26 — finding 1 formalized and closed.  `HilbertMetric` is now free of undischarged
  interfaces (3 of 3 resolved).
  - `GaloisForLFunctions/HilbertMetric/CCRFiniteBlockObstruction.lean` (new):
    `card_add_card_eq_zero_of_isFullCCRMatrixTuple`, `isEmpty_of_isFullCCRMatrixTuple`,
    `not_isFullCCRMatrixTuple`, `not_exists_isFullCCRMatrixTuple`,
    `blockCCRTuple_isInvariantFullCompression`, `blockCCRTuple_isBlockCCRMatrixTuple`,
    `exists_invariantBlockCCRTuple_of_isCCRCompletion`, `unitModeLeakage_isCCRCompletion`,
    `blockCCRTuple_zero_isCommutingFullTuple`, `exists_invariant_commuting_blockCCRTuple`,
    `isFullCCRMatrixTuple_empty_and_isBlockCCRMatrixTuple_inhabited`,
    `exists_gaussianCoherentInvariantBlockCCRTuple`.
  - `CCRPowerConcavity.lean`: added `IsBlockCCRMatrixTuple`,
    `IsFullCCRMatrixTuple.isBlockCCRMatrixTuple`, `isBlockCCRMatrixTuple_iff_isCCRCompletion`;
    the seven consumer theorems now take `IsBlockCCRMatrixTuple T` and
    `IsCommutingCCRCompression (fullCCRCompressionBlock T)` in place of the two unsatisfiable /
    stronger full-matrix hypotheses, so each is strictly stronger than before and non-vacuous.
  - `#print axioms` on every new capstone: `[propext, Classical.choice, Quot.sound]`.
  - `lake build GaloisForLFunctions.HilbertMetric` green.
- 2026-07-26 — audit instrument corrected.  The first pass used a reducing `forallTelescope`, which
  unfolds a `Prop` def in the conclusion and therefore lost producers; it also matched only the
  outermost conclusion head, so existential producers such as `semSplitData_exists` were missed.
  The corrected instrument scans every project constant occurring at any depth in each `Prop`
  binder and in the conclusion.  Undischarged count drops from 258 to **50**.
- 2026-07-26 — `HTGeometry.PointFiniteFacetFamily` realized
  (`GaloisForLFunctions/HTGeometry/PointFiniteFacetWitnesses.lean`): automatic for finite families
  and over a finite vertex set, automatic for pairwise disjoint families, with the infinite disjoint
  edge family `{2k, 2k+1}` on `ℕ` as an explicit infinite witness.  The point-finiteness premise is
  removed from the universal-source Stanley--Reisner constraint law in two forms — over every finite
  vertex set, and on the infinite edge geometry.
- 2026-07-26 — `HTGeometry.IsConstantMvPolynomial` discharged
  (`GaloisForLFunctions/HTGeometry/NonconstantMvPolynomialWitnesses.lean`): constancy is exactly
  vanishing total degree, giving checkable nonconstancy criteria and unconditional coordinate-family
  instances of disjoint-block algebraic independence and of the iterated Krull-dimension drop.
- 2026-07-26 — `HTGeometry.ErlangRecoveryAdmissible` (the largest entry, 23 consumers) discharged
  (`GaloisForLFunctions/HTGeometry/ErlangBoundedSource.lean`).  All seventeen analytic fields are
  proved for the class `ErlangBoundedSource f f' M` (globally bounded value and derivative):
  - the three kernels are `erlangPowKernel ε k c s = s ^ k · exp (-s / ε) / c`, whose half-line
    integrability is a Gamma moment (`integrableOn_erlangPowKernel`);
  - bounded measurable sources integrate against them (`integrableOn_erlangPowKernel_mul`);
  - the far boundary is exponential decay (`tendsto_erlangPowKernel_mul_atTop`), the near boundary is
    continuity (`tendsto_erlangPowKernel_mul_nhdsGT`);
  - differentiation under the integral is dominated by kernel × derivative bound
    (`hasDerivAt_erlangPowKernel_integral`, via
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
  Consequences: `erlangRecoveryAdmissible_of_boundedSource`,
  `erlangAverageThree_exact_recovery_of_boundedSource`, and the premise-free sine instance
  `erlangAverageThree_exact_recovery_sin` — the identity `(1 - εD)³ R = f` with no analytic premise.
- 2026-07-26 — `RHTower.SuzukiAllAngleRealZeros` discharged
  (`GaloisForLFunctions/RHTower/SuzukiAllAngleWitnesses.lean`).  The all-angle quantifier over the
  unitary circle collapses: `A z + u E z = 0` has a unimodular solution `u` exactly when
  `‖A z‖ = ‖E z‖`, so
  `SuzukiAllAngleRealZeros A E ↔ ∀ z, z.im ≠ 0 → ‖A z‖ ≠ ‖E z‖`
  (`suzukiAllAngleRealZeros_iff_norm_ne`).  The Cayley powers `((z-i)^n, (z+i)^n)`, `n ≠ 0`, satisfy
  the criterion because `i` and `-i` are equidistant from `z` only on the real axis; they are
  Schwarz-reflected, so `suzukiHermiteBiehler_addI_pow`,
  `norm_suzukiLivsicQuotient_cayleyPow_lt_one`,
  `norm_suzukiLivsicQuotient_cayleyPow_le_lineCayley` and `suzukiHerglotz_cayleyPow_im_nonneg`
  hold with no interface premise.
- 2026-07-26 — `PeriodicFrom` discharged
  (`GaloisForLFunctions/HTGeometry/PeriodicFromWitnesses.lean`): the residue extension
  `n ↦ v (n % p)` is periodic from index `0` for every `p` and unimodular whenever `v` is, together
  with constants, later starting indices, and closure under sums, products and scalars.  The
  periodicity premise is removed from `exists_periodicGeometric_leastLevelPolynomial_eq_zero` and
  `exists_periodicGeometric_targetLevelPolynomial_eq_zero`, whose conclusions now hold for the phase
  family of every sequence read modulo the period.
