# q62 for real pairs via the hole-free-tip pigeonhole route

- **ID:** q62-pigeonhole-tip-rigidity-real-pairs
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, conditional on two named Props)
- **Source:** open-problems/04 (answered) + the root-limit pigeonhole repair of the Step-3 hole gap
- **Statement:** For real `−2 < c₂ < c₁ < 0`, the Böttcher coordinates `φ_{c₁}, φ_{c₂}` are
  algebraically independent over `ℂ(z)`, conditional on exactly two Props: the Schoenflies
  exterior collar at `imagTip c₁` and `SmoothPieceRigidity c₁ c₂`.

## Goal
The first *nonexceptional both-connected* q62 pair class. Every step of the chain is
machine-checked (`Bottcher.q62_phiMero_independence_real_pair`,
`Q62TipRigidityCapstone.lean`, axiom-clean); the two remaining Props are classical paper
mathematics (Jordan-curve collar for hyperbolic Julia sets; smooth-piece Julia rigidity),
tracked as formalization epics — no open mathematics remains anywhere in the chain.

## Gates
- [x] 0 → 1  in-progress: well-posed; chain fully wired in Lean
- [ ] 1 → 2  fully-proven: discharge the collar Prop and the rigidity Prop on paper-complete
      writeups (04-answer supplies the collar's paper proof; rigidity is classical Fatou/E–vS)
- [ ] 2 → 3  formalized: collar epic (#124) + rigidity epic (#118) in Lean
- [ ] 3 → 4  publication-ready

## Approach
Assume a bivariate relation. (1) It propagates by the identity theorem from the far field
through the unbounded component `W` of `ℂ ∖ (K₁ ∪ K₂)` — `pair_relation_at_escape_point`,
using the global basin branches and `connectedComponentIn`. (2) The hole-free tip
(open-problems/04, ANSWERED for this class: `z₀ = i·√(β₁+c₁)`, Janiszewski/collar + imaginary
escape ray) makes every `J₁`-point of a small ball a limit of relation-carrying `W`-points —
`HoleFreeTip`, `holeFreeTip_of_collar`, `holeFreeTip_frontier_approach`. (3) The root-limit
lemma (Bolzano–Weierstrass, **no branch coherence**) plants a modulus-one root of the fibre
polynomial at every such Julia point — `holeFreeTip_modulus_one_supply`. (4) The minimal
separable relation has a far-field witness (A3) that countable-avoidance moves onto `J₁`
inside the ball — uncountability from `perfect_frontier_of_perfect`, the **two-ray**
perfect-frontier theorem (no empty-interior hypothesis, no Jordan curve theorem). (5) The IFT
branch family + Baire pigeonhole put a relatively open `J₁`-piece inside the modulus-one
locus of one branch — `exists_relOpen_smooth_piece_of_holeFreeTip`. (6) `SmoothPieceRigidity`
forbids that piece; degree-0 relations die on the germ bridge —
`noRelation_phiMero_of_holeFreeTip_of_rigidity`. Assembly over the Mandelbrot placement with
unconditional connected-side transcendence: `q62_phiMero_independence_of_monodromy_tip_rigidity`.

Adversarial audit notes: (i) the exceptional-partner trap of the first 03-answer is excluded
(both `c_i ∈ (−2,0)` are in `M ∖ {0,−2}` by `real_mem_mandelbrot` + interval arithmetic);
(ii) the tip-height monotonicity used for tip separation holds only on `(−2,0]` — it fails on
`(0,1/4]`, so this class cannot naively extend past `c = 0`; (iii) the rigidity Prop carries
the full branch-family data (analytic coefficients, separability, pointwise-distinct root
branches) so that its discharge is genuinely possible — continuity alone would make the Prop
refutable by a constant function.

## Log
- 2026-07-02 — created directly in 1-in-progress: the whole chain formalized and axiom-clean
  in one session (RealSliceDynamics, ImaginaryAxisTip, TipWApproach, PairComponentPropagation,
  FrontierPerfectGeneral, TipSmoothPiece, HbothconnAssembly, Q62TipRigidityCapstone);
  open-problems 03 answered vacuously (exceptional partner), restated as 04, answered for
  this class the same day.
