# Route R physical Bockstein all-finite Kunneth non-erasure — 2026-08-13

Created and umbrella-wired `RHTower/RouteRPhysicalBocksteinHomologicalNonErasure.lean`. It defines the literal physical Bockstein class in the genuine signed Kummer cyclic/Hochschild quotient, proves its regulator is the existing physical dilation defect, and classifies representative boundary membership and every retained target-linear image: zero iff mate gain is 1 iff `Re rho = 1/2`.

Extended from tensor square to every finite tensor power using `TensorPower`/`PiTensorProduct`. Product regulator reads `physicalDefect^n`; every tensor power, including degree zero, is nonzero off line; every positive-degree power is zero iff `Re rho = 1/2`.

Defined `RouteRFiniteKunnethPhysicalBocksteinAnnihilator` with nonzero coefficient, positive degree, off-line divisor, and source exactness. Proved `routeR_no_finiteKunnethPhysicalBocksteinAnnihilator`. Added this as a discharged constructor of `RouteRPrepolarIntrinsicAnnihilator` in `RouteRPrepolarTerminalNoGo.lean`.

Verification: `lake env lean GaloisForLFunctions/RHTower/RouteRPhysicalBocksteinHomologicalNonErasure.lean` green; final targeted `lake build GaloisForLFunctions.RHTower.RouteRPrepolarTerminalNoGo` green; axiom audit of product-regulator, tensor-power classification, finite-Kunneth no-go, and terminal theorem gives only `[propext, Classical.choice, Quot.sound]`; no forbidden declarations or stale Lean.

Scientific verdict: finite coefficient-faithful ordinary Kunneth/cyclic-Hochschild powers cannot supply Route R annihilation. Surviving core is genuinely non-Kunneth and source-selected: source-specific collective compactness/singular Xi factorization of fixed `(2,3)` Stokes–Sonin receiver or loss-zero physical Cauchy landing of fixed inverse-log Fisher vector. This is not RH and not full Route-R death.