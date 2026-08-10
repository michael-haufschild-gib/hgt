# Universal-law-field stage 2→3 sweep — frontier

Standing task: formalize each card in `docs/drafts/pipeline/2-fully-proven/universal-law-field`
unconditionally in Lean, oldest file-mtime first, then promote it to `3-formalized`.

## Promotion protocol (per card)

1. Tick the `2 → 3` gate (or flip `[NO LEAN]` → `[LEAN CERTIFIED]` in `Status`) and append a
   `## Lean certification status … COMPLETE` section to the paper card.
2. `git mv` the card to `docs/drafts/pipeline/3-formalized/universal-law-field/`.
3. Write the `<card>-formalized.md` companion next to it.
4. Append a row to `2-fully-proven/universal-law-field/_LEAN-CERTIFICATION.md`.
5. Append an entry to `docs/drafts/pipeline/_stage2-to-3-ledger.md`.
6. Wire the module into `GaloisForLFunctions/HTGeometry/UniversalLawField.lean`, then **always**
   finish with `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Certified so far (modules in `GaloisForLFunctions/HTGeometry/`)

ULF-CTX-1, ULF-IRR-1, ULF-TORS-1, ULF-FILL-1, ULF-DOCT-1, ULF-ENDP-1, ULF-BULK-1, ULF-MATCH-1,
ULF-DGLU-1, ULF-FLUX-1, ULF-MOORE-1, ULF-INV-1, ULF-MPE-1, ULF-LSW-1, ULF-IPE-1, ULF-MSQ-1,
ULF-EIR-1, ULF-A2R-1, ULF-ACTION-1,
ULF-TOEPLITZ-1 `ConstitutiveToeplitzDefectIndex`,
ULF-DEFECT-1 `ConstitutiveBalancedDefectZeroIndex`,
ULF-EXPDIM-1 `ConstitutiveExperimentalDimension`,
ULF-BIALG-1 `ConstitutiveMonoidBialgebraHopfEnvelope`,
ULF-IPKMS-1 `ConstitutiveInvariantPositivityKMSWall`,
ULF-TRLC-1 `ConstitutiveTimeReversalLikelihoodCocycle`,
ULF-PAFP-1 `ConstitutivePolarAmplitudeFisherPhase`.

41 files remain in stage 2 (a concurrent agent adds cards).  Next by mtime:
`hidden-history-elimination-forces-positive-kernel-and-purification-gauge-law.md` (12:32:24).

## Reusable corpus — do NOT rebuild

- `ConstitutiveToeplitzDefectIndex`: ℂ unilateral shift on `lp (fun _:ℕ => ℂ) 2` (coordinate
  reindexings, adjoint, defect projections, ranks, index, compact-perturbation rigidity).
- `ConstitutiveBalancedDefectZeroIndex`: `WithLp 2 (H × H)`, `pairOp`, `adjoint_pairOp`,
  signed-defect cancellation.
- `ConstitutiveInvariantPositivityKMSWall`: **`continuous_of_isClosed_graph`**, `basisVec`,
  `toeplitzGibbsState`, abstract KMS-exchange lemmas.
- `ConstitutiveTimeReversalLikelihoodCocycle`: **`klDiv_map_measurableEmbedding`**,
  **`measurableEmbedding_graph`**, **`klDiv_compProd_right`**, **`klDiv_map_le`** (data processing),
  `jointLaw`, ±1-walk recurrence, SLLN bridge.
- `ConstitutivePolarAmplitudeFisherPhase`: `ampNormSq`/`ampInner`/`fsSpeedSq`, `polarAmp`,
  `polarTangent`, `hasDerivAt_polarAmp`, the Fubini–Study decomposition, `phaseLoop`,
  `velMean`/`velVar`, `berryHolonomy`, and **`polarEquiv`** (projective ≃ simplex × phase torus).
- `ConstitutiveMonoidBialgebraHopfEnvelope`, `ConstitutivePositiveResponse`,
  `ConstitutiveStabilityWall`, `ProjectiveQuantumFisherValue` / `QuantumGeometricTensorGram`
  (projective Gram tangent energy, Berry curvature value),
  `HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness` (namespace has **no**
  `GaloisForLFunctions` prefix).
- mathlib lacks: Fredholm **index** theory, C*-algebra K-theory, Calkin algebra, C*-dynamical
  systems / KMS states, Markov-chain recurrence, closed-graph continuity, `klDiv` data processing.
- mathlib **has**: `MeasureTheory.llr` (+`neg_llr`, `exp_neg_llr`); `InformationTheory.klDiv`
  (**namespace matters**) with `toReal_klDiv_of_measure_eq`, `klDiv_eq_zero_iff`,
  `klDiv_compProd_eq_add`, `klDiv_eq_lintegral_klFun_of_ac`; `MeasureTheory.toReal_rnDeriv_map`
  (pushforward RN derivative **is** a conditional expectation); `Measure.disintegrate`;
  `Kernel.rnDeriv_eq_rnDeriv_measure`; `ProbabilityTheory.strong_law_ae`;
  `AddMonoidAlgebra.instBialgebra`, `LaurentPolynomial.instHopfAlgebra`, `IsGroupLikeElem.isUnit`.

## Traps

- **Umbrella name collisions are invisible to `lake env lean`** — only the umbrella build sees them.
- `TangentSpace I x` is a non-reducible def to `E`; instance search will not unfold it.
- Prefer `abbrev` for subtype wrappers (`FullAmp`): a `def` breaks subtype coercion in `show`/`rw`.
- `rw [f]` fails for a function-valued `def` (`ampProb`); use `show` to unfold.
- `AddMonoidAlgebra k M` is not elaboration-transparent to `M →₀ k`; `AddMonoidAlgebra.lift R A M`
  puts the **target `A` before `M`**.
- `WithLp p V` uses `.ofLp` / `WithLp.toLp`.
- `omit … in` must precede the docstring.
- A `def` producing a measure needs an explicit `instance` for `IsFiniteMeasure` before it can be
  used in a statement requiring one.
- `setLIntegral_congr_fun` wants `Set.EqOn`; use `lintegral_congr_ae` + `ae_restrict_of_ae`.
- Deprecated (the lint gate fails on warnings): `push_neg`;
  `ContinuousLinearMap.{add,sub,smul,one}_apply`; `isUnit_of_mul_eq_one`.
- `Int.induction_on` via `induction … using … with` rejects `hz/hp/hn`.
- `Measure.isProbabilityMeasure_map` / `Measure.isFiniteMeasure_map` are namespaced.

See `mem:universal-law-field/parity-contextuality-lean-layer-2026-08-09` and siblings.
