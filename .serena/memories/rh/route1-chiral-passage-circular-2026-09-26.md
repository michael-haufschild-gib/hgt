# Route 1 (sub-quantum chiral passage) is CIRCULAR — 2026-09-26

- Card: docs/drafts/pipeline/5-failed/route1-sub-quantum-chiral-passage.md; facts: docs/drafts/pipeline/1-in-progress/route1-chiral-passage/facts.md
- Kill 1 (holomorphic rigidity, Lean): zero-free approximants exp∘G_k converging on an open anchor, with boundary Im G_k bounded in L¹ mod constants ⇒ limit zero-free on the disc. BBM turns bounded H^{1/2}(S¹;S¹) phase energy into that L¹ bound. So κ₋=κ₊ always for anchored passages, and the κ₋ ≤ B_base budget is idle.
- Kill 2 (explicit formula, paper): logDeriv Φ_x − logDeriv ξ = ½Σ_ρ Γ((ρ−s)/2)(πx)^((s−ρ)/2) + O(x). The passage converges exactly on Re s>Θ and fails diffusely at rate x^(−(β−σ)/2). Step 2 ⟺ RH (the classical ψ-bound in Gaussian form).
- Lean: GaloisForLFunctions.RHTower.AnchoredPhasePassageRigidity. Theorems: schwarz_difference_formula, norm_sub_le_of_boundary_im_oscillation, ne_zero_of_anchored_boundaryArgOscillation_bounded, riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded. Axioms clean.
- Lesson: holomorphic readers have no sub-quantum regime. The integer changes only through divergence, so budgets must bound growth exponents, not quanta. Do not rebuild chiral-corona or κ₋ closures (RPGT.12/.21/.23).
