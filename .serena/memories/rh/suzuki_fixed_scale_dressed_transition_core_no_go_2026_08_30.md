# Suzuki fixed-scale dressed transition-core class kill (2026-08-30)

Route: `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY` -> eventual lower semibounded rectangular Ward defect -> `riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow` -> RH.

Formal result: `GaloisForLFunctions.RHTower.SuzukiFixedScaleDressedTransitionCoreNoGo` proves the transition-core Ward defect still tends to `-∞` after subtracting any uniformly upper-bounded correction, then instantiates this with the sum of fixed-source-scale aperture-dressed wall light, marked halfgap, and scalar holonomy Schur budgets. Closed theorem `RHTower.no_fixedScaleDressed_transitionCore_WardProducer` rules out every fixed positive source scale, fixed scalar marked/Schur coordinates, and arbitrary positive moving aperture sequence as an eventually lower-semibounded Ward producer.

Core scaling law: `naturalCauchyEnergy <= transitionCore`; raw natural Cauchy Ward defect tends to `-∞`; fixed-scale full dressed budget has an aperture-independent ceiling. Even the most favorable subtraction sign cannot repair the defect.

Positive survivor: any viable Suzuki assembly must use signed atomic-continuous relative renormalization, cutoff-growing/non-scalar cross-channel transport, or growing channel rank with collective cancellation.

Audit: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.SuzukiFixedScaleDressedTransitionCoreNoGo` passed; five key declarations use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import present. Global lint recognizes new module; global failure only from unrelated pre-existing unreachable modules.

Card: `docs/drafts/pipeline/3-formalized/suzuki-fixed-scale-dressed-transition-core-no-go.md`.