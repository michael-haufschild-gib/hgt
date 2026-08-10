# CCM rational analytic Real descent — promoted to stage 3 (2026-08-10)

Card `ccm-rational-analytic-real-descent.md` moved to `3-formalized` with a companion
`-formalized.md`.  Its "Not yet represented in Lean" list was **stale**: claims 1-6 were already
proved by the 134-module `CCMRational*` layer.  Audit by reading statements (not names) found
exactly one real gap, now closed.

## The one gap, and the new module

`RHTower/CCMRationalAdelicBruhatSchwartzSpace.lean`:

- `IsCCMRationalAdelicBruhatSchwartz` — Bruhat's condition on `ℝ × 𝔸_f`: ONE compact open period
  subgroup in the finite variable, ONE compact support in the finite variable, Schwartz fibres.
  (Per-fibre local constancy is NOT enough; the single subgroup is what makes the decomposition
  finite.)
- `range_ccmRationalAdelicBruhatEval_eq` — the algebraic core `𝒮(ℝ) ⊗ C_c^∞(𝔸_f)` realizes onto
  exactly that space.  Proof: compact support meets finitely many cosets of the open period
  subgroup; classes are indexed by the image of the finite subcover in `𝔸_f ⧸ K` (no quotient
  topology needed — finiteness comes from the subcover, not from discreteness).
- `ccmRationalAdelicBruhatEval_injective` — via a basis of the finite factor:
  `Core ≃ (ι →₀ 𝒮(ℝ))` through `TensorProduct.finsuppScalarRight`; the symm formula is proved by
  `Finsupp.induction`, then `linearIndependent_iff'` kills the coefficients.
- `ccmRationalAdelicBruhatEquiv` — hence a linear isomorphism onto Bruhat's space.
- `ccmRationalAdelicBruhatEval_sigma` — the algebraic sign-reflection realizes pointwise as
  `φ ↦ conj (φ ∘ (-1))`.

## Where the rest of the theorem already lived

| card claim | Lean |
|---|---|
| 1 involution + continuity | `ccmRationalAdelicCrossedProductRealStructureₛₗ/_mul/_sq`, `ccmRationalAdelicSourceRealStructure_continuous` |
| 2 preserves `ker ε₀ ∩ ker ε₁` | `ccmRationalAdelicEpsilonZero_real`, `..._One_real`, `ccmRationalAdelicReducedSourceCyclic_real_stable`, `...ReducedSourceCyclicKReal` |
| 3 target involution | `ccmRationalMoritaTraceNormL1RealStructure_norm` (isometry), `ccmRationalMoritaTraceNormL1Trace_real`, `ccmRationalStrongDiagonalTrace_real`, `ccmRationalStrongCyclicTargetKReal` |
| 4 `ρ♮α_A♮ = α_B♮ρ♮` | `ccmRationalAdelicReducedNonunitalStrongCyclicKRealHom` (`KRealHom.real_naturality` IS the identity) |
| 5 closed quotient even `K_ℝ` | `ccmRationalAdelicClosedStrongRelativeCyclicKReal` |
| 6 idele-class action | `ccmRationalAdelicClosedStrongLefschetzKReal`, `ccmRationalNonunitalStrongCyclicRightActionDegree_real` |
| Def 4.9 landing | `ccmRationalAdelic_reduced_source_image_mem_strong` |

`CCMRationalStrongClassSpaceScalarTarget` is the comap of `DeningerMeyerStrongLogTarget`
(all-derivative, all-exponential-weight decay) — the genuine `𝐒(C_ℚ)`, not a surrogate.

## Reusable facts

- `Nat.Primes` has no `LinearOrder` in mathlib; corpus pattern is a `local instance` via
  `LinearOrder.lift'` (see `RouteEProductTruncatedReservoirMass`, and now
  `SquarefreeExteriorHorizonLift`).
- `ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer` gives the uniform additive period of
  any finite Bruhat function; intersect with `ccmRationalIntegralFiniteAdelesAddSubgroup` to make
  it compact (open subgroups are closed).
