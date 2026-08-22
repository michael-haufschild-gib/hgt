# Hodge coercivity and global dynamics in two-field edge-cochain systems

- **ID:** hodge-edge-cochain
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Moses Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field Edge-Cochain
  Systems with MHD-Type Cancellation*, arXiv:2608.19360v1 [math.DS], 19 Aug 2026
- **Statement:** On a finite two-step cochain complex, the divergence-free edge space admits the
  Poincaré-type estimate needed for dissipativity iff its harmonic 1-cochain space is trivial; under
  that condition the MHD-type two-field system has an exact energy identity, a global semiflow, an
  absorbing ball and a compact global attractor, and in the noncoercive case the
  harmonic-decoupled interaction produces invariant affine fibres with fibre-wise attractors.

## Goal
Complete unconditional Lean formalization of every numbered result of the paper, together with the
reusable analytic infrastructure the corpus did not own (bounded-Lipschitz global ODE existence,
continuation by cut-off, uniform positivity of a homogeneous form on a subspace).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the paper supplies complete proofs; the continuation step of Lemma 2 was
      re-derived because mathlib has only local Picard–Lindelöf)
- [x] 2 → 3  formalized: 61 audited declarations, all `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Modules
`formal/GaloisForLFunctions/HTGeometry/HodgeEdgeCochain/`

| File | Content |
|---|---|
| `Coercivity.lean` | (1), Lemma 1, (2), **Theorem 1**, the `V₀` companion with the attained `λ₊`, the projector characterisation (`P²=P`, `P*=P`, `d₀*P=0`, normal-equation form of the Moore–Penrose formula), §2.1 modal decay, and non-vacuity models |
| `Interaction.lean` | (4) `IsCancelling`, (9), closure under linear combination and orthogonal restriction, (8), (10), **Proposition 1** (abstract skew-family form and the explicit `D(a)J + JD(a)` realization on `EuclideanSpace`), **Remark 1** in sharp form |
| `Energy.lean` | **Theorem 2** (12), the integrated identity (15)–(16), §4.1 mean dissipation, (13)–(14) **Proposition 2**, **Theorem 4**, the absorbing estimate and absorption time of **Theorem 3**, (11) with the paper's `C_J = 16‖J‖` |
| `GlobalExistence.lean` | **Lemma 2**: `exists_solution_of_bounded_lipschitz` (reusable), the cut-off continuation, `exists_isSolutionOn_Icc`, `exists_isSolutionOn_Ici`, `isSolutionOn_unique` |
| `Attractor.lean` | the semiflow (`orbit_add`, `continuous_flow`) and **Theorem 3**: `energyBall_mapsTo`, `exists_absorbing`, `attractor_nonempty`, `isCompact_attractor`, `isInvariant_attractor`, `attractor_attracts` |
| `HarmonicFibre.lean` | (17)–(18), (19), **Lemma 3**, **Theorem 5** (`harmonic_component_const`, `isSolutionOn_reduced`, `fibre_energy_le_unforced`, `fibre_converges`, `fibre_absorbing_ball`), §5.2 linearization spectrum |
| `HodgeSystem.lean` | the instantiation on `V = ker d₀*` with `A = Δ₁|V`: `hodge_exists_global_solution`, `hodge_energy_identity`, `hodge_unforced_decay`, `hodge_absorbing_ball`, `hodge_compact_global_attractor`, `hodge_fibre_theorem` |

## Approach
The paper's Theorems 2–5 use only two structural facts: the trilinear antisymmetry (4) and
nonnegativity/coercivity of the dissipative operator.  The formalization therefore separates a
source-independent dynamical layer (`Energy`, `GlobalExistence`, `Attractor`, `HarmonicFibre`, all
stated for an arbitrary finite-dimensional real inner-product phase space) from the Hodge layer
(`Coercivity`), and glues them in `HodgeSystem`.

The one genuinely missing ingredient was global existence.  Mathlib supplies only local
Picard–Lindelöf.  The continuation is done by cutting the *whole* vector field off outside a ball
by a scalar factor `χ_R(‖x‖) ∈ [0,1]`; because the cut-off is a scalar multiple of the entire
field, the exact cancellation identity survives, so the a priori energy bound applies to the
truncated system *directly* and no first-exit-time argument is needed.  Choosing `R` above the a
priori bound on `[0,T]` makes the cut-off equal `1` along the trajectory.

Coercivity on a subspace is carried through the energy layer as a set parameter `W`, so the same
theorems serve the coercive case (`W = univ`) and the harmonic-fibre case (`W = range P₀`).

## Excluded
§6 and Appendices A–D are the deterministic numerical study.  They are computations, and the paper
states explicitly that their residuals "are not used as assumptions in any theorem".

## Log
- 2026-08-22 — created directly at stage 3; all numbered results of arXiv:2608.19360 formalized
  unconditionally; project lint clean for these modules; axiom audit `[propext, Classical.choice,
  Quot.sound]` on 61 declarations.
