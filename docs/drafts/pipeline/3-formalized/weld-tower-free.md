# The finite completed weld is tower-free: RH_{2^k} carried by no finite piece of ξ's Euler–Γ product

- **ID:** weld-tower-free
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** bottom-up composition of EulerTruncationRigidity + PrimeDivisorAtomsNoGo + Bottcher.HolomorphicBranch + KummerObstruction
- **Statement (delivered):** `[PROVED HERE]` On the convex (hence simply connected) right half-plane, a nonvanishing analytic function has a single-valued analytic 2^k-th root (`exists_pow_root_of_analyticOn_nonvanishing`). Applied:
  - `archimedeanFactor_pow_root`: the archimedean generator `π^(−s/2)Γ(s/2)` (the ∂_s side) has an unconditional free 2^k-th root tower on Re s > 0.
  - `completedLocalFactor_pow_root`: **the finite completed weld `archimedeanFactor · eulerPartial P` (the ∂_s×{σ_p} weld) has an unconditional free 2^k-th root tower on Re s > 0** — through the wall Re s=1 and across the strip, no divisibility condition.
  - `completed_weld_tower_free_but_xi_tower_costs`: sharpened dichotomy — the finite weld's tower is free unconditionally; ξ's 2^k-th root on Re s>1/2 exists only under hole-order divisibility (= RHLadder k).
- **Lean:** `RHTower.{archimedeanFactor_pow_root, completedLocalFactor_pow_root, completed_weld_tower_free_but_xi_tower_costs, exists_pow_root_of_analyticOn_nonvanishing, isSimplyConnected_rightHalfPlane}` in `formal/GaloisForLFunctions/RHTower/WeldTowerFree.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green.

## What was new (method: bottom-up)
EulerTruncationRigidity had the Euler side's free tower; PrimeDivisorAtomsNoGo had the archimedean factor's nonvanishing and the weld's UNIT-ness (order 0 at points) — but NOT the archimedean side's tower nor the weld's tower. The step from "nonvanishing" to "single-valued 2^k-th root on the whole simply-connected Re s>0" (trivial monodromy around ANY loop, not just order-0 at points) via `Bottcher.exists_differentiableOn_pow_eq` is the missing composition. The assembled statement — the finite completed ∂_s×σ_p weld is tower-free, so the RH_{2^k} monodromy obstruction is carried by NO finite piece of the completed Euler–Γ product and is purely emergent in the P→∞ limit — is stated by no file and localizes the obstruction precisely. Mission-central (the weld is the ∂_s/{σ_p} frontier); "constraint not flow" (the only link to ξ's conditional tower is the limit flow).

## Log
- 2026-07-07 — created directly in 3-formalized (bottom-up harvest → composition → Lean).
