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

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per formalisable item)
- [ ] 2 → 3  formalized in Lean
- [ ] 3 → 4  publication-ready

## Log
- 2026-08-21 — created; paper source read in full; inventory above frozen.
