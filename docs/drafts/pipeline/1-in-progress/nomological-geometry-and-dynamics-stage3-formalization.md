# Nomological geometry and dynamics Stage-3 formalization

- **Stage:** 1 — in progress
- **Started:** 2026-08-09
- **Scope:** Every paper-proved theorem in every current card under
  `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/`.
- **Completion gate:** Exact Lean statements, unconditional proofs, umbrella imports, per-file
  elaboration, formal lint, targeted final builds, axiom audits, and card moves to Stage 3.

## Card audit

| Card | Exact mapping | Lean status | Final audit |
|---|---|---|---|
| critical Euler/Mass/Weil/Stokes shadow | mapping | pending | pending |
| Dirichlet Maurer--Cartan Mellin orbit | `DirichletMaurerCartanMellinOrbitLaw` covers the exact Dirichlet derivation, Möbius--von-Mangoldt contraction, Kähler inverse law, Mellin algebra automorphism, full coefficient derivative via both complex components, both gauge equations, Julia orbit, pure gauge, and one-parameter curvature; `UniversalDeRham` constructs the canonical `Ω¹ → Ω²` differential from `I/I²`, proves descent, and gives `d(a db)=da∧db`; the card module proves the literal universal Maurer--Cartan equation | complete; both modules and `HTGeometry` umbrella build; exhaustive theorem axiom audit has only standard foundations; forbidden-declaration scan clean | moved to `docs/drafts/pipeline/3-formalized/dirichlet-maurer-cartan-mellin-orbit-law.md` |
| Euler prime-orbit prolongation/recurrence/polar/cofinal | mapping | pending | pending |
| finite law-relation wall synchronization/phase loss | mapping | pending | pending |
| framed two-boundary phase fibre/history separation | mapping | pending | pending |
| half-density Route-L odd Weil connection weld | mapping | pending | pending |
| Hurwitz monodromy closure/resonance rank | mapping | pending | pending |
| marked half-character duality/soldering/cofinal obstruction | `MarkedHalfCharacterDualityLaw` covers marked augmentation and its naturality/scaling, categorical unit/pair Morita equivalence plus strict-representative mismatch and literal vanishing `H¹`, exact complex-unit Cartan/duality/soldering/energy identities, dual orientation loss, hostile off-unit-circle witness, deck parity, one-loop cocycle, free-history relation curvature and neutral descent, continuous and Laurent-algebraic root no-sections, and literal continued-Hurwitz realization; `MarkedHalfCharacterCofinalDiagonalInverseLaw` covers exact physical Xi residue/Gamma comparison and its nonzero coefficient, rank-energy identity `(20)`, all of Theorem 7.1, explicit quotient kernel, noninjectivity and surjectivity, exact prime `ell^1` boundedness iff via Banach--Steinhaus, plus the algebraic noncanonical-splitting boundary; `MarkedHalfCharacterCompactActionLaw` covers exact compact recurrence, endpoint/winding non-determination, root parity, positive energy integral, sharp absolutely-continuous action/equality rigidity, Fubini--Study normalization, rotor-core relations, and magnitude/parity non-determination | complete; all three modules and both umbrellas build; exhaustive theorem axiom audit has only standard foundations; no stale process | moved to `docs/drafts/pipeline/3-formalized/marked-half-character-duality-soldering-and-cofinal-diagonal-inverse-obstruction-law.md`; global lint reachability failure is unrelated pre-existing umbrella debt documented in card audit |
| multiple-Gamma period-action three-shadow | mapping | pending | pending |
| multiple-Gamma three-face cofinal wall | mapping | pending | pending |
| native observer descent/effectivity/non-determination | mapping | pending | pending |
| odd Euler comb tempered admission wall | mapping | pending | pending |
| perfect defect motive five-shadow | mapping | pending | pending |
| polarized exactness horizon/relative Connes phase | `ParachainConnesComparisonLaw` covers Theorem 4.1; `PolarizedExactnessHorizonRelativeConnesPhaseLaw` covers exact dual-number sign/conormal laws, all of Theorem 3.1, general power-series `mu_m` phase, exact Smith classification/contraction for every finite free factorization of `X`, noncontractible doubled `(X,X)`, literal relative/source cohomology and Theorem 4.2, field-horizon regularity/all-module projectivity, exact completed energy ideal `(E)=(X²)`, periodic residue resolution, residue nonprojectivity/projective dimension `⊤`, and doubled-horizon nonregularity; `PolarizedExactnessHorizonSourceSpecialization` identifies the literal trace-one ordinary-prime Xi residue with `(q-1)c`, proves `c≠0`, the exact vanishing criterion, and actual positive source-energy factorization | partial; both clean modules wired into `HTGeometry`/`RHTower`; literal Verdier singularity-category object/zero-category realization and final five-item trichotomy audit remain | pending |
| positive observer covariance/HT/compact resolvent | mapping | pending | pending |
| restricted history completion/polynomial saturation | mapping | pending | pending |
| Route-L odd current/Suzuki/Mass reconstruction | mapping | pending | pending |
| source-normal Hochschild/Maurer--Cartan clock curvature | `SourceNormalClockCurvatureLaw` covers Theorem 2.1 pointwise and on arbitrary finite Hochschild one-cycles, literal Kummer prime-period non-erasure, Theorem 3.1 generically and on the exact `dilUnit` multiplier simplex with its normalized trace, Theorems 3.2/3.4, Corollary 3.3, global analytic and formal-`ℚ` logarithmic linearization, an explicit off-neutral raw-curvature/log-flat hostile witness for Corollary 3.6, exact actual Riemann source laws and literal product-trace realization `(4.3)`, exact critical-line classification of the prime quadratic representative, physical Xi prime residue `(4.2)`, and Theorem 5.1 | implementation coverage complete; direct elaboration and targeted module build pass; exhaustive own/supporting axiom audit has only standard foundations; forbidden-declaration scan clean | umbrella audit currently blocked only by unrelated concurrently edited `RHTower/ProlateTwoBranch.lean`; Stage-3 move waits for clean umbrella rerun |
| split-prime Euler class/inverse-monodromy no-go | `ParachainConnesComparisonLaw` covers inverse scalar totalization | partial | pending |
| Tate fracture obstruction/Bianchi/amplitude | `TateFractureObstructionBianchiAmplitudeLaw` covers exact ordered Maurer--Cartan weights, literal `H²` extension obstruction, `O₂`/`O₃` and indeterminacy, strict conjugation, explicit `O₂=0`/`O₃≠0` witness, bundled typed bidegree composition, finite-amplitude cutoff and terminality, cofinal unbounded-amplitude converses, standard totalization linear equivalence and zero quotient boundary, and positive Hilbert no-go | complete; module and `HTGeometry` umbrella builds pass; exhaustive axiom audit has only standard foundations; no stale process | moved to `docs/drafts/pipeline/3-formalized/tate-fracture-obstruction-bianchi-amplitude-law.md`; global lint reachability failure is unrelated pre-existing umbrella debt documented on card |
| universal Hausdorff observer rank transmutation | mapping | pending | pending |
| weighted history action/infinite completion boundary | mapping | pending | pending |

## Owned new Lean modules

- `formal/GaloisForLFunctions/HTGeometry/ParachainConnesComparisonLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/PolarizedExactnessHorizonRelativeConnesPhaseLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/DirichletMaurerCartanMellinOrbitLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/UniversalDeRham.lean`
- `formal/GaloisForLFunctions/HTGeometry/MarkedHalfCharacterDualityLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/MarkedHalfCharacterCompactActionLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateFractureObstructionBianchiAmplitudeLaw.lean`
- `formal/GaloisForLFunctions/RHTower/MarkedHalfCharacterCofinalDiagonalInverseLaw.lean`
- `formal/GaloisForLFunctions/RHTower/PolarizedExactnessHorizonSourceSpecialization.lean`
- `formal/GaloisForLFunctions/RHTower/SourceNormalClockCurvatureLaw.lean`

## Open core

Map every numbered paper theorem to an existing exact declaration or a genuine missing declaration.
No card may move until every proved assertion is represented and the hostile-boundary statements are
preserved as explicit non-implication/counterexample theorems where the card proves them.
