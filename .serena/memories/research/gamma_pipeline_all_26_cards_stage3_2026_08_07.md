# All 26 gamma cards are in stage 3 (2026-08-07)

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/gamma/` is gone; all 26 cards live in
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma/`, each with a `Stage-3 Lean
certificate` naming the exact declarations.  Audit performed: `#print axioms` on 2214 declarations
across the 623 modules the cards reference — all report only `propext`, `Classical.choice`,
`Quot.sound`; project lint shows no proof debt anywhere.

**24 cards were already formalized; the card text was stale.**  Never trust card prose ("Lean proof
open", "Verification gate (blocked)", "interfaces absent from the tree") — check the repo.

## The two cards that needed new mathematics, and how they closed

**`gamma-copoisson-sonin-full-quotient-flatness-syzygy`.**  The paper derives the boxed identity
`(2)` `T_j^+T_{j+1}^- = T_j^-T_{j+1}^+` from Burnol's completeness theorem.  Not needed.  For
`r ≥ 1` both normalized dilations *lower* the closed co-Poisson source space one aperture step
(`evenDilation_mem_coPoissonSourceSpace`), because the co-Poisson sum intertwines with the seed
dilation and the dilated seed window stays inside the shrunk aperture's window.  So a quotient
vector two apertures up is already orthogonal to `C_{j+1}` after either dilation, the source
correction in `E_{j+1} = Π_{j+1} − P_{j+1}` drops out, and **both paths act as `E_j`**.
Modules: `BurnolCoPoissonSourceDilation.lean`, `GammaCoPoissonSoninQuadrantFlatness.lean`
(plus `...QuadrantSection/Charge/Reflected/Syzygy/Zeta.lean` for the parent quadrant card).

**`irrational-elliptic-gamma-pointed-bi-anomaly-fracture`.**  The card said the gerbe half
`(11)`–`(12)` had to *import* Felder–Henriques–Rossi–Zhu.  Both halves are derivable:
* FHRZ Prop. 6.10 needs no triptic-curve theory — the fibre is contractible, so the Dixmier–Douady
  class lives in `H³(ℤ³,ℤ)` and is the explicit integral 3-cocycle `ν(λ,μ,ν) = −n₁m₂ℓ₃`.  Detector:
  the alternation over the standard basis kills every coboundary and sends `ν` to `1`.
* FHRZ Prop. 3.15 follows from theta quasi-periodicity alone: `Δ_a` is the finite theta product
  `∏_{i<M} θ(W+iu)`; iterate `θ(z+τ) = exp(2πi(κ−z))θ(z)`, telescope, and `P_a` appears exactly.
  **Mathlib's `jacobiTheta₂` satisfies both laws with `κ = −τ/2`**, and `κ` only contributes a
  bilinear term whose coboundary vanishes — so the class is normalisation-independent and the whole
  chain is unconditional.
Modules: `GammaGerbeDixmierDouadyGenerator.lean`, `GammaGerbeThetaCocycle.lean`.

## Transferable lessons

1. When a paper proves an operator identity by density of a hard-to-construct family, first ask
   whether the subspace being projected away is **monotone** under the operators in play.
2. When a card says an external theorem must be *imported*, read the actual paper: its proof often
   reduces on the relevant fibre to a finite algebraic computation plus a classical functional
   equation already in mathlib.
3. Get formulas from the arXiv **LaTeX e-print** (`arxiv.org/e-print/<id>`, gunzip), never from
   PDF text extraction — the latter loses Greek letters and subscripts and produced a wrong `P_a`.
4. `⟪·,·⟫_ℂ` on `evenSubspace` elaborates through `WithCStarModule…toInner`, so generic mathlib
   `inner_smul_left`/`inner_conj_symm` do not `rw`; use `simp`, or route through
   `Submodule.inner_left_of_mem_orthogonal` / `starProjection_inner_eq_zero`.
