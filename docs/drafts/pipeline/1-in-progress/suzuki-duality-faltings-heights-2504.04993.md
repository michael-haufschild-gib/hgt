# Duality invariance of Faltings heights, Hodge line bundles and global periods (Suzuki, arXiv:2504.04993)

- **ID:** suzuki-dual-faltings-2504
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean)
- **Source:** arXiv:2504.04993v?, `DualHeight250902.tex` (IMRN 2025, Vol 2025 Issue 19)
- **Statement:** An abelian variety and its dual over a global field have the same Faltings
  height, isomorphic (metrized) Hodge line bundles, and equal real/global BSD periods.

## Goal
Formalise, unconditionally and closed in Lean 4, every lemma/theorem of the paper that admits a
dependency-closed formalisation on the present mathlib base, and build any missing infrastructure.

## Paper inventory (labels from the arXiv source)

| Label | Statement | Formalisation status / obstruction |
|---|---|---|
| Thm 0010 = 0014 | `h(A) = h(B)` over a global field | Needs Néron models, Tate–Shafarevich group schemes (Suzuki20a), Breen–Serre duality. **Out of reach.** |
| Prop 0007 | `det Lie A₁ ⊗ (det Lie A₂)^{-1} ≅ det RLie N ⊗ O(-c(f))` | Needs Illusie's Lie complex + determinant of perfect complexes. **Out of reach**; degree shadow formalisable. |
| Prop 0021 (0015/0016/0017/0022) | quoted from GRS24 | **Out of reach** (fppf duality of finite flat group schemes). |
| Prop 0008 | `deg Lie A₁ - deg Lie A₂ = deg RLie N - c(f)` | Degree-homomorphism shadow of 0007: **formalisable** as an abstract Picard-degree law. |
| Prop 0009 | `μ_{A₂} - μ_{A₁} = deg Lie A₁ - deg Lie A₂` | quotes GRS24 Thm 10.3. **Out of reach.** |
| Prop 0000/0032 | Néron-model extension + perfectness of the Cartier pairing | **Out of reach** (fppf derived category, Raynaud group schemes). |
| Prop 0001/0002 | lattice correspondence for `det RLie` / `det Lie` | **Out of reach.** |
| Prop 0003 | semistable + descent step | Two dependency-closed cores: (a) a rank-one lattice `L` in a 1-dim `K`-space with `L·L'^{-1} = L'·L^{-1}` forces `L = L'` (DVR self-inverse-ideal lemma); (b) `e_{L/K}`-scaled valuation descent. **Formalisable.** |
| Thm 0004 = 0011 | Hodge line bundles correspond | **Out of reach** (assembly of the above). |
| **Prop 0005** | complex period / Faltings metric preserved under `ω_A ≅ ω_B` | Crux is: `covol(Λ)·covol(Λ^∨) = 1` and the `2^g |det M|` wedge normalisation. **Formalisable (target).** |
| Thm 0012 | Faltings metrized structure preserved | Assembly of 0005 + 0011. Metric half formalisable. |
| **Prop 0020** | real period / BSD metric preserved | Crux is a Tate-cohomology (Herbrand quotient) computation for an involution on a ℤ-lattice, giving `#π₀(A(ℝ)) = #π₀(B(ℝ))`. **Formalisable (target).** |
| Thm 0031 | BSD metrized structure preserved | Assembly of 0020 + 0011. |

The paper's own final Remark states that Prop 0005 and Prop 0020 hold for arbitrary complex tori
(with conjugation). That is the level at which they are formalised here.

## Missing infrastructure to build (mathlib gaps)
1. **Tate cohomology of an involution on a module** — `Ĥ⁰(σ) = ker(σ-1)/im(σ+1)`,
   `Ĥ¹(σ) = ker(σ+1)/im(σ-1)`; the exact sequence
   `0 → Λ/(Λ⁺⊕Λ⁻) --(σ-1)--> Λ⁻/2Λ⁻ → Ĥ¹(σ) → 0`; finiteness; the index law
   `#(Λ/(Λ⁺⊕Λ⁻)) · #Ĥ¹(σ) = 2^{rank Λ⁻}`; the `σ ↦ -σ` symmetry; hence
   **the ℤ/2 Herbrand quotient formula `#Ĥ⁰(σ) · 2^{rank Λ⁻} = #Ĥ¹(σ) · 2^{rank Λ⁺}`.**
   Neither mathlib nor the corpus has Tate cohomology or Herbrand quotients.
2. **Dual-lattice covolume law** — `covol(Λ_M) = |det M|`, `covol(Λ_{(Mᵀ)⁻¹}) = |det M|⁻¹`,
   product `= 1`. mathlib has `ZLattice.covolume_eq_det` but no dual-lattice statement.
3. **Complex-torus period duality** — Faltings metric on `ω_A`, `ω_B` and its invariance.
4. **Real-period duality** — assembly of (1) into `#π₀(A(ℝ)) = #π₀(B(ℝ))` and equality of the
   two real-period integrals.

## Lean modules built (all unconditional, `#print axioms` = `propext, Classical.choice, Quot.sound`)

| Module | Content |
|---|---|
| `HTGeometry/InvolutionTateCohomology.lean` | Tate `Ĥ⁰`/`Ĥ¹` of an involution on a `ℤ`-module; the exact sequence `0 → Λ/(Λ⁺⊕Λ⁻) → Λ⁻/2Λ⁻ → Ĥ¹ → 0`; `card_defect_mul_card_H1`; the `σ ↦ -σ` symmetry; **`herbrand`** (`#Ĥ⁰·2^{rk Λ⁻} = #Ĥ¹·2^{rk Λ⁺}`); finiteness; `card_H0_eq_card_H1` in the balanced case; rank additivity `rk Λ⁺ + rk Λ⁻ = rk Λ`; a balanced model on `ℤ × ℤ`. |
| `HTGeometry/InvolutionTateDualLattice.lean` | The transposed involution on `Λ^∨`; `finrank_eigenParts_dual` (equal eigenranks, via injective restriction of functionals); `Λ⁺ ⊔ Λ⁻ = (σ-1)^{-1}(2Λ)`; `defect ≅ image of σ-1 in Λ/2Λ`; the mod-2 evaluation pairing `Λ^∨/2Λ^∨ ≅ Dual_{𝔽₂}(Λ/2Λ)`; **`card_defect_dual`**, **`card_H1_dual`**, **`card_H0_dual`** — Tate duality for `ℤ/2`. |
| `HTGeometry/RealTorusComponentGroup.lean` | **`quotEquivTateH1`**: `A^σ / image(V^σ) ≅ Ĥ¹(⟨σ⟩, Λ)` for `A = V/Λ`, i.e. `π₀(A(ℝ)) ≅ Ĥ¹` (Milne I.3.7 / Suzuki's step), by the vanishing of `H¹(⟨σ⟩, V)`. |
| `HTGeometry/RealTorusDualPeriodComponents.lean` | **`card_H1_eq_card_H1_neg_dualInvolution`**: `#π₀(A(ℝ)) = #π₀(B(ℝ))` — the final reduction of Prop 5.1 — and its geometric form `card_quot_eq_card_tateH1_neg_dual`. |
| `HTGeometry/DualZLatticeCovolume.lean` | The dual lattice `Λ*` for the standard pairing; `dual_span_eq`; `covolume_span_eq_abs_det`; **`covolume_mul_covolume_dual`** (`covol Λ · covol Λ* = 1`); the matrix form `dual_rowLattice`, `covolume_rowLattice`. |
| `HTGeometry/ComplexTorusFaltingsPeriod.lean` | `det_dzFrame`/**`norm_det_dzFrame`** (`|det| = 2^g`, the source of the `2^g` in `‖dz₁∧…∧dz_g‖²`); `faltingsNormSq` and **`faltingsNormSq_eq_sq_det_mul_dual`** — the Faltings metric is preserved by the `det M`-scaling isomorphism `ω_A ≅ ω_B`. |
| `HTGeometry/SelfInverseLatticeValuationRing.lean` | **`span_eq_span_one_of_span_eq_span_inv`**: over a valuation ring the only rank-one lattice equal to its own inverse is the unit lattice; `span_eq_of_ratio_eq_inv_ratio` — the exact step used in the proof of Prop 3.4. |
| `HTGeometry/RealTorusEigenLatticeCovolume.lean` | **`covolume_eigenSum`**: `covol(Λ⁺ ⊕ Λ⁻) = #(Λ/(Λ⁺⊕Λ⁻)) · covol(Λ)`, and `covolume_eigenSum_mul_card_H1` — Suzuki's `det Q = (2^g / #π₀(A(ℝ))) · det M` in covolume form. |
| `HTGeometry/HaarMeasureSubgroupIndex.lean` | **`measure_univ_eq_index_mul`**: for a left-invariant measure and a measurable finite-index subgroup, `μ(G) = [G:H]·μ(H)` (a mathlib gap). |
| `HTGeometry/RealTorusRealPeriod.lean` | **`measure_univ_realPoints`**: `μ(A(ℝ)) = #Ĥ¹(⟨σ⟩,Λ)·μ(A(ℝ)⁰)` — Suzuki's `(5.1)` `∫_{A(ℝ)} dz₁∧…∧dz_g = #π₀(A(ℝ))` once the identity-component period is normalised to `1`. |
| `HTGeometry/RealTorusIdentityComponent.lean` | The **topological** upgrade of §5: `span_fixedLattice` (`Λ ∩ V^σ` spans `V^σ`), `isCompact_imageFixed`, **`connectedComponent_eq`** (the image of `V^σ` *is* the identity component of `A(ℝ)`), **`card_quotient_realPoints`** (`#π₀(A(ℝ)) = #Ĥ¹(⟨σ⟩,Λ)` for the genuine topological component group) and `card_piZero_eq_card_H1_neg_dual`. |

## What is proved vs. what is out of reach

**Proved unconditionally in Lean.**  The entire arithmetic engine of §5 (Prop 5.1) up to and
including `#π₀(A(ℝ)) = #π₀(B(ℝ))` — with `π₀` the *topological* component group, since the image of
`V^σ` is proved to be the identity component of `A(ℝ)`; the component-group computation `π₀(A(ℝ)) ≅ Ĥ¹(⟨c⟩, Λ)`; Tate
duality for `ℤ/2`-lattices (a mathlib gap, and the input Suzuki quotes implicitly when passing from
`Λ` to `Λ^∨`); the covolume duality and the `2^g` frame determinant behind §4 (Prop 4.1), together
with the metric-preservation identity; the valuation-ring step of §3 (Prop 3.4).

The only ingredient of §5 left outside Lean is the normalisation
`∫_{A(ℝ)⁰} dz₁ ∧ … ∧ dz_g = 1`, i.e. integration of differential forms over a real torus, which
mathlib does not support.

**Out of reach on the present mathlib base.**  Everything requiring Néron models, Illusie's Lie
complex and determinants of perfect complexes, fppf quotients (Anantharaman), Raynaud group schemes,
Chai's base change conductor, Suzuki's Tate–Shafarevich group schemes and Breen–Serre duality:
Theorems 1.1/2.5 (`h(A) = h(B)`), Prop 2.1, Prop 2.2, Prop 2.3, Prop 2.4, Prop 3.1, Prop 3.2,
Prop 3.3, Thm 3.5, and the two assembly Theorems 4.2 and 5.2.  None of these are in mathlib, and
none can be introduced as hypotheses without breaking unconditionality; Serre duality on a complex
torus (needed to identify the transition factor `±det M` with the canonical isomorphism `(1.2)`) is
likewise absent.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper for every formalisable item
- [x] 2 → 3  formalized in Lean (all seven modules above, `scripts/formal_tools.py lint` green)
- [ ] 3 → 4  publication-ready

## Log
- 2026-08-21 — created; paper source read in full; inventory above frozen.
- 2026-08-21 — seven Lean modules landed and wired into `GaloisForLFunctions.HTGeometry`; formal
  lint green; axiom audit clean.
- 2026-08-21 — two further modules: the eigenlattice covolume identity (`det Q` step) and the
  topological identity-component theorem, upgrading `#π₀(A(ℝ)) = #Ĥ¹` from the algebraic component
  group to the genuine topological one.  Nine modules total.
- 2026-08-21 — two more: the Haar-measure index law and the real-period identity
  `μ(A(ℝ)) = #π₀ · μ(A(ℝ)⁰)`.  Eleven modules total; lint green; axiom audit clean.
