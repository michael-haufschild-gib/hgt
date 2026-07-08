# The abstract rate-lattice weld interface and its dual clock covector

- **ID:** weld-rate-lattice-interface
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Machinery: mechanical generalization of the prime-specific `WeldClassTable` results to an arbitrary ℤ-linearly-independent family, plus the dual clock-covector layer.
- **Method:** rng-blind theorem sampling of the constraint cluster → mechanical transformation classes (GENERALIZE, DUALIZE), codex-cross-checked for the transform catalogue → `lake` as the verifier. No conjecturing: each theorem is a proven generalization/dual of an existing one, and the prime results are recovered as instances.

## What is proved (`formal/GaloisForLFunctions/RHTower/WeldRateLattice.lean`, 8 declarations)

**Primal — the rate lattice.** The prime-specific weld results depend only on the rate family being ℤ-linearly independent as reals, never on the arithmetic. Extracted:
- `weldClass_indep_of_linIndep` — for any `r : ι → ℝ` with `LinearIndependent ℤ r`, the weld classes `{weldClass (r i)}` are ℤ-linearly independent in `H²`. Transported through the injective `weldClassHom`. `primes_weld_class_indep` is the instance `r = log ∘ (·)`, and this simultaneously supplies the arbitrary-`n` rank law left open by the prime table.
- `weld_isLatticeValued_iff (Λ : AddSubgroup ℝ) (θ)` — the weld cocycle is `Λ`-valued iff `θ ∈ Λ`, for an *arbitrary* ambient subgroup (the value lattice is always the rank-one `⟨θ⟩`).
- `primeLog_linearIndependent` — the bridge: the tree's unique-factorization independence of `{log p}` *is* mathlib's `LinearIndependent ℤ`, exposing it to all of mathlib's linear-algebra machinery and making the prime family a valid input to the interface. Two `example`s recover the prime statements, confirming faithfulness.

**Dual — the clock covector.** The dual of the rate lattice carries clock covectors: ℤ-linear functionals reading a time value off each accumulated rate. Dual to independence:
- `clock_covector_existsUnique` — for an independent family and *any* prescribed assignment `t : ι → ℝ`, exactly one covector on the rate lattice realizes it. The clock is **free** (any assignment achievable, by freeness of the lattice on the independent family) and **rigid** (determined on the whole lattice by its generator values).
- `clock_covector_unique` — the rigidity half standalone (needs no independence: an additive functional is fixed on the generated subgroup by its generator values).
- `foundingWeld_clock_covector_existsUnique` — the prime instance: the founding prime-rate lattice `⟨log p⟩` carries a free, unique clock covector for every assignment of a time value to each prime.

## Constraint, not flow
A clock covector is an element of the lattice's dual — a functional, not a solution propagated by a rule; no carrier is constructed. Independence (primal) and free-but-rigid clock (dual) are the two faces of the rate lattice carrying no relation among its rates.

## The selection is object-specific (the open frontier)
The lattice makes the clock covector free; it does not select one. For the primes an *external* constraint — the functional equation `s ↦ 1−s`, fixed locus the critical line (`sigmaConj_fixed_iff_critical`, `norm_cpow_eq_critical_iff`, both already in the tree) — selects the covector. A hypertranscendental object fixed by a constraint that is *not* a functional equation has its own selection, supplied by that constraint, not by the lattice. The interface is the reusable substrate; the selecting involution is the per-object input. That is where "does a coherent clock exist, and is it unique" becomes non-trivial and is not settled by known ζ theory.

## Lean
`RHTower.{weldClass_indep_of_linIndep, weld_isLatticeValued_iff, primeLog_linearIndependent, clock_covector_unique, clock_covector_existsUnique, foundingWeld_clock_covector_existsUnique}` in `formal/GaloisForLFunctions/RHTower/WeldRateLattice.lean`, imported in the `RHTower` umbrella. `lake build` green, axiom-clean (`propext, Classical.choice, Quot.sound`), lint pass.

## Log
- 2026-07-08 — created in 3-formalized. Mechanical (rng-sampled, codex-cross-checked, Lean-verified) generalization of the prime weld table to an abstract independent rate family, and the dual clock-covector existence/uniqueness. Prime family recovered as instances. Axiom-clean, 8 declarations.
