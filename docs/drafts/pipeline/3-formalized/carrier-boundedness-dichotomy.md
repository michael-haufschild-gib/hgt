# Bounded carrier vs. differential algebraicity: falsification and the corank reformulation

- **ID:** carrier-boundedness-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Settles conjecture H1 of the RHTower status report (`docs/reports/rhtower_status_0707.md` §3).
- **Statement:** The conjecture "if the defining constraint `f(σ s) = m(s)·f(s)` is carried by a bounded operator (bounded symbol `m`) then `f` is differentially algebraic" is **false as stated**; the operative invariant is the **corank of the constraint kernel**, not the operator norm of the carrier.

## What is proved (`formal/GaloisForLFunctions/CarrierDichotomy.lean`)

Definitions: `MultiplicativeConstraint σ m f := ∀ s, f (σ s) = m s * f s` (the object is pinned in a carrier kernel, not propagated); `BoundedSymbol m := ∃ B, ∀ s, ‖m s‖ ≤ B` (bounded carrier, since the substitution part is an isometry).

1. **Falsification** — `bounded_carrier_not_sufficient_for_DA`: given any `σ`-invariant `P` that is hypertranscendental, the constraint `f(σ s) = 1·f(s)` (symbol `≡ 1`, maximally bounded) is solved by `P`, which is not differentially algebraic. The symbol's norm controls the carrier's eigenvalue, never its kernel dimension.
2. **Why it fails** — `constraint_ratio_invariant`: two solutions of one `(σ, m)` have a `σ`-invariant ratio, so the solution set is a torsor over the `σ`-invariant ring. `(σ, m)` determines `f` only up to that whole ambiguity: the corank is the operative datum.
3. **Corrected sufficient condition** — `rigid_constant_carrier_DA` + `rigid_solution_constraint`: on the rigid (corank-one) stratum, a bounded (constant) symbol *does* force DA — `f = A·exp(γ s)` solves `f(s+1) = e^γ·f(s)` and is DA.
4. **Intrinsic reading of an unbounded carrier** — `multiplier_at_of_residues` (shift `σ = ·+1`), generalized to `multiplier_at_of_residues_affine` (`σ = α·+β`, `α≠0`: `m(b) = rA/(α·rB)`) and `multiplier_at_of_residues_reflection` (`σ = β−·`): the symbol value at a substitution-pole equals a ratio of adjacent residues of `f`. Residues are intrinsic local invariants, so their growth certifies carrier unboundedness with no operator constructed. `bounded_carrier_residueRatio_le`: a bounded symbol forces bounded residue ratios (`‖rA/rB‖ ≤ B`).
5. **Γ instance** — `gamma_multiplier_pole_value` / `gamma_multiplier_pole_norm`: Γ's adjacent-residue ratio at pole `−(k+1)` is `−(k+1)`, of norm `k+1`; `gamma_residueRatio_carrier_unbounded` states the unboundedness on Γ's own residue data. Γ's difference carrier is unbounded, read off the residue tower (`gamma_residue`).
6. **Unification** — `UnboundedOn`, `no_bounded_carrier_dichotomy`: Γ's archimedean residue-ratio data `k+1` and the ζ-seam's reflected prime spectrum `p^{s−1}` (`RHTower.seam_no_bounded_reciprocity_carrier`) are both unbounded — one predicate, two instances.
7. **Completion insight** — `completedZeta_reflection_bounded` / `completedZeta_obstruction_is_seam`: the completed Λ has reflection symbol `≡ 1` (`completedRiemannZeta_one_sub`), a bounded carrier; by (1) the reflection FE is hypertranscendence-neutral, so the operator-side obstruction sits entirely in the (unbounded) prime seam. This is why the completion is required: it renders the reflection bounded and localizes the obstruction at the weld.

## The reduction it yields
The bounded-carrier conjecture is false **iff a hypertranscendental `σ`-invariant exists** — i.e. iff there is a periodic hypertranscendental function (a Hölder-type statement for a lacunary period function). That existence is the field's founding open problem, not a gap in this treatment: the falsification is register-correctly conditional on that one input (`bounded_carrier_not_sufficient_for_DA` takes it as an explicit hypothesis). No function is yet proven `Hypertranscendental` anywhere in the tree, so the input cannot presently be discharged in Lean.

## Novelty / significance
Novel bridge: boundedness of the carrier is a *flow* property (operator norm of the propagator); the invariant that controls differential algebraicity is a *constraint* property (corank of the solution kernel). This unifies the archimedean multiplier obstruction (Γ, residue-ratio blow-up) with the operator-norm reflection obstruction (ζ-seam) under one "no bounded carrier" principle, and reads carrier unboundedness intrinsically off residues without constructing any carrier — "constraint, not flow." Not a literature-search result (difference-Galois gives multiplier ⟹ HT case-by-case; the corank-vs-norm reframing and the Γ/ζ unification are new).

## Lean
`GaloisForLFunctions.{MultiplicativeConstraint, BoundedSymbol, constraint_ratio_invariant, bounded_carrier_not_sufficient_for_DA, rigid_constant_carrier_DA, rigid_solution_constraint, multiplier_at_of_residues, multiplier_at_of_residues_affine, multiplier_at_of_residues_reflection, bounded_carrier_residueRatio_le, gamma_multiplier_pole_value, gamma_multiplier_pole_norm, gamma_carrier_unbounded, gamma_residueRatio_carrier_unbounded, zeta_seam_carrier_unbounded, no_bounded_carrier_dichotomy, completedZeta_reflection_bounded, completedZeta_obstruction_is_seam}` in `formal/GaloisForLFunctions/CarrierDichotomy.lean`. `lake build` green, axiom-clean (`propext, Classical.choice, Quot.sound` only), lint pass.

## Open continuations
- Discharge the falsification unconditionally by constructing a Lean-proved hypertranscendental period function (a Mahler/lacunary HT theorem — the field's core open problem).
- Instantiate `multiplier_at_of_residues_affine` at a dilation (`|α|≠1`, Mahler) against the banked u0/Böttcher corpus, giving a third face of the unified obstruction.

## Log
- 2026-07-08 — created in 3-formalized; H1 settled (falsified-as-stated + corank reformulation), Lean axiom-clean.
