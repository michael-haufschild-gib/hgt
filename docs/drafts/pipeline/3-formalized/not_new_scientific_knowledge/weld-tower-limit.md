# The product tower survives the P→∞ limit past the wall; reclaiming the strip is RH

- **ID:** weld-tower-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** composition of WeldTowerFree + SeamReciprocity.completedSeam_eq + RiemannTower/UPlaneLadder coherent-tower machinery
- **Statement (delivered):** `[PROVED HERE]` The finite completed weld is tower-free on Re s>0 (WeldTowerFree). Its P→∞ completed limit is `completedRiemannZeta = archSeam·seamDirichlet` (completedSeam_eq); both limiting factors are nonvanishing only past the wall (archSeam on Re>0, seamDirichlet=ζ on Re>1), so:
  - `completedZeta_coherentTower_beyondWall`: completedRiemannZeta has an unconditional coherent infinite Kummer tower on Re s>1 — the product tower survives the limit, but only past the wall.
  - `xi_coherentTower_beyondWall`: ξ (entire, zero-free on Re≥1) likewise, unconditional on Re>1.
  - `rh_iff_xi_coherentTower_rightHalf`: **RH ⟺ ξ has a coherent tower on Re s>1/2** — reclaiming the strip is exactly RH.
  - `weld_tower_survives_to_wall_extends_iff_rh`: packaged. The free-tower region contracts from Re>0 (finite weld) to Re>1 (completed limit); the last stretch across the strip is RH.
- **Lean:** `RHTower.{completedZeta_coherentTower_beyondWall, xi_coherentTower_beyondWall, rh_iff_xi_coherentTower_rightHalf, weld_tower_survives_to_wall_extends_iff_rh, exists_pow_root_of_analyticOn_nonvanishing_convex, coherentTower_of_analyticOn_nonvanishing_convex}` in `formal/GaloisForLFunctions/RHTower/WeldTowerLimit.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green, warning-free.

## What this is
Answers the edge the finite-weld tower-freeness opened: does the product tower survive the P→∞ boundary? Yes — on Re s>1 (the limit contracts the free region by exactly the strip), via the product of the two surviving free-tower factors (completedSeam_eq). The clean RH-characterization `RH ⟺ ξ coherent-tower on Re>1/2` locates the whole obstruction in the continuation across the strip: free through the wall unconditionally, extends across the strip iff RH. Bottom-up: assembled from completedSeam_eq + WeldTowerFree + the coherent-tower iff; stated by no single file.

## Log
- 2026-07-07 — created directly in 3-formalized (composition of the surviving free factors + coherent-tower iff).

## Update: the threshold law (unifies both σ-endpoints)
`xi_coherentTower_iff_zeroFree_halfPlane (σ)`: for EVERY real σ, ξ admits a coherent infinite Kummer tower on {Re s > σ} ⟺ ξ has no zero with Re s > σ. The coherent-tower obstruction on any open half-plane is exactly its zero-set. Corollaries: `xi_coherentTower_gt_one` (σ=1, unconditional) and `rh_iff_xi_coherentTower_gt_half` (σ=1/2, ⟺ RH). This single parametrized theorem subsumes both the unconditional survival past the wall and the RH-iff — the free tower survives down to the first zero and no further. Axiom-clean.
