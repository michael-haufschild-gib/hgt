# Goncharov motivic-complex comparison

- **ID:** goncharov-motivic-complex
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** A. B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology* (Adv. Math. 114, 1995), Conjecture A / Conjecture 1.15
- **Statement:** `[CONJECTURE]` For every field `F`, weight `m ≥ 2`, and `1 ≤ j ≤ m`, the canonical comparison is a functorial isomorphism
  `H^{j,m}(Spec F, ℚ) ≅ H^j(Γ(F,m))`, where `Γ(F,m)` is Goncharov's polylogarithmic complex.

## Goal

Prove the exact all-fields, all-weights comparison without assuming Beilinson--Soulé vanishing,
mixed-Tate existence, rank-filtration degeneration, or the desired comparison; then formalize that
exact unconditional theorem in Lean 4.

## Gates

- [x] 0 → 1 in-progress: exact classical statement identified; corpus and current-literature audits opened; first unavoidable open bidegree isolated
- [ ] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [ ] 2 → 3 formalized: exact Lean theorem, targeted `lake build` green, lint and `#print axioms` pass
- [ ] 3 → 4 publication-ready: standalone paper with theorem, proof, Lean certificate, and priority audit

## Exact complex

Over `ℚ`, `Γ(F,m)` is concentrated in degrees `[1,m]`:

`B_m(F) → B_{m-1}(F) ⊗ F× → ⋯ → B_2(F) ⊗ Λ^{m-2}F× → Λ^m F×`.

For `k > 2`, the differential sends
`{x}_k ⊗ x_{k+1} ∧ ⋯ ∧ x_m` to
`{x}_{k-1} ⊗ x ∧ x_{k+1} ∧ ⋯ ∧ x_m`; at `k = 2` it sends the symbol to
`x ∧ (1-x) ∧ x_3 ∧ ⋯ ∧ x_m`.

## Frontier

- `[CORPUS]` No Goncharov complex, higher Chow complex, Quillen algebraic `K`-theory, or genuine
  Bloch--Suslin group was found by `scripts/formal_tools.py research`. Existing reusable foundations
  include Milnor `K`-theory with graded products and residues, cochain-complex cohomology and
  quasi-isomorphism APIs, exterior-power results, Tits-building homology, and a Steinberg-module
  action.
- `[LITERATURE]` Degree `j=m` is the Nesterenko--Suslin/Totaro Milnor case; `(m,j)=(2,1)` is
  Bloch--Suslin; Bolbachan, arXiv:2404.06271v2 (2025), proves `j=m-1` for characteristic-zero
  fields.
- `[LITERATURE]` Kupers--Rudenko--Sierra, arXiv:2606.23863v1 (2026), construct a Goncharov Lie
  coalgebra from `E∞`-homology of general linear groups. In weight three they prove
  `K_4^{(3)}(F)_ℚ ≅ H^2(Γ_3(F))` and an exact sequence
  `K_4^{(2)}(F)_ℚ ⊗ F×_ℚ → K_5^{(3)}(F)_ℚ → H^1(Γ_3(F)) → 0`.
- `[LITERATURE]` Kimura, arXiv:2604.17671v1 (2026), constructs the comparison inside the
  Bloch--Kriz cycle DGA under Beilinson--Soulé vanishing.  Its first nonformal choice is a
  primitive for the difference of two weight-two fillers in `N⁰(2)`, exposing rather than
  removing the present obstruction.  Bolbachan, arXiv:2311.07567v3, supplies a support-free cycle
  complex and strong Suslin reciprocity, but its proved Totaro comparison in weight two covers
  degrees `1,2`, not the obstructing degree `0`.
- `[OPEN CORE]` The first unresolved universal comparison is `(m,j)=(3,1)`. For all fields it is
  equivalent to Beilinson--Soulé vanishing `K_4^{(2)}(E)_ℚ = 0` for every field `E`. Full
  Goncharov additionally requires control of higher weights, where the Chevalley--Eilenberg model
  first contains a decomposable `Λ²G_2(F)` term absent from the displayed classical weight-four
  polylogarithmic complex.

## Active attack

Treat `Γ(F,m)` as the symbolic shadow of the rank filtration on the `E∞`-homology of `GL(F)`, not
as an isolated functional-equation presentation. Determine whether the total rank-spectral-sequence
differential canonically supplies the missing decomposable terms and yields a filtered comparison
whose associated graded is motivic cohomology. Hostile tests: hidden use of Beilinson--Soulé
vanishing, unproved degeneration, mismatch at weight four, and failure of functoriality or positive
characteristic descent.

## No-go closure

- **Exact killing theorem/mechanism:** no unconditional mechanism found; current literature still
  identifies the first required case with universal Beilinson--Soulé vanishing in weight two.
- **Strongest positive survivor:** `St₂∞(F) ≅ Λ² ker(ℚ[P¹(F)] → ℚ)`, reducing the first open
  comparison to exactness of the oriented configuration complex at five points: every rational
  syzygy among five-term relations must be an alternating six-point boundary.  Restriction to an
  algebraic closure is injective on `K₄⁽²⁾(-)ℚ`, so algebraically closed fields suffice.
- **New insight:** the equivariant configuration spectral sequence does not kill this group.  Over
  an algebraically closed field all its possible outgoing targets vanish, making the obstruction a
  permanent top-filtration quotient of `H₄(PGL₂(F); ℚ)`.  One-variable Milnor residue exactness
  also stops modulo constant classes, so a new five-point coherent moving identity is necessary.
  Equivalently, after induction on transcendence degree, the missing trace-zero term is
  `Hom_DM(k)(h¹(C),ℚ(2)[0])` for a smooth projective curve over an algebraically closed field.
- **Status:** Stage 1; no paper proof; no Lean statement may be promoted

## Log

- 2026-08-26 — created directly in Stage 1 after exact statement disambiguation. Internal search
  found substantial Milnor/Steinberg/cohomology infrastructure but no motivic-complex formalization.
  Current literature moved next-to-Milnor degree out of the frontier and identified weight-three
  degree one with universal Beilinson--Soulé vanishing.
- 2026-08-27 — isolated the open core in two exact equivalent chain models:
  `H₃(K₂ᴹ(Δ̂_F^•))ℚ` and `H₂(PGL₂(F); St₂∞(F))`. Opened supporting card
  `goncharov-weight-two-rank-contraction.md`; four tempting contraction, duality, product, and
  reversal arguments were falsified before promotion. Active route seeks a second coherent
  equivariance homotopy for the explicit rank-two decomposition resolution.
- 2026-08-27 — reduced the rank-two infinite Steinberg module to an exterior square, proved
  algebraic-closure injectivity, and falsified both Borel-stabilizer cancellation and residue-only
  coning.  Exact surviving paper target is now a degree-specific coherent moving identity for
  five-point configuration syzygies; Lean remains gated by the open proof.
- 2026-08-27 — checked Kimura's Bloch--Kriz filler and Bolbachan's non-admissible complex against
  the open degree.  Both stop exactly at weight-two degree zero.  Isolated equivalent geometric
  core `Hom_DM(k)(h¹(C),ℚ(2)[0])=0`; no weight or duality shortcut proves it.
