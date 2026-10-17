import GaloisForLFunctions.RHTower.CHMDStationaryResolventDictionaryAndNodalPolarization

/-!
# Eigenvector Nodal Lobe Energies, Individual Lobe Cross-Jump Bounds, and Primitive Lobe $L^1$-Equality

This module establishes the individual nodal-lobe energy and edge-norm identities for arbitrary
resolvent eigenvectors, the Courant nodal lobe negativity theorem for bound-state eigenvectors, and
the two-sided primitive lobe $L^1$-to-$L^2$ bounds on `SourceGraph`:

1. **Universal Eigenvector Edge-Pairing and Nodal Lobe Energy/Edge Identities**:
   for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`:
   - `∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, ((1 - 2 * μ) / μ) • q.val.fst⟫_ℝ`,
   - `∀ p : SourceGraph, ⟪p.val.snd, q.val.snd⟫_ℝ = ((1 - μ) / μ) * ⟪p.val.fst, q.val.fst⟫_ℝ`,
   - `sourceEnergy (posGraph q) = ((1 - 2 * μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
   - `sourceEnergy (negGraph q) = ((1 - 2 * μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
   - `sourceEnergy (posGraph q) - sourceEnergy (negGraph q) = ((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2)`,
   - `‖(posGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
   - `‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`.
   Consequently, for any `0 < μ`:
   `-sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2` and
   `-sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2`,
   and for any nonzero primitive bound-state eigenvector (`1 / 2 ≤ μ`, `w ≠ 0`, `⟪w, oneL⟫_ℝ = 0`),
   both nodal lobes have strictly negative Doob energy:
   `sourceEnergy (posGraph q) < 0` and `sourceEnergy (negGraph q) < 0`.

2. **Primitive `sourcePair` Decomposition, Lobe $L^1$-Equality, and Two-Sided Lobe Bounds**:
   - for all `p, r : SourceGraph`,
     `⟪(primGraph p).val.fst, (primGraph r).val.fst⟫_ℝ = ⟪p.val.fst, r.val.fst⟫_ℝ - 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ`
     and
     `sourcePair (primGraph p) (primGraph r) = sourcePair p r + 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ`.
   - for any primitive `q : SourceGraph` (`⟪q.val.fst, oneL⟫_ℝ = 0`), the positive and negative
     lobes have identical $L^1(\mathrm{massMeasure})$ integrals:
     `⟪(posGraph q).val.fst, oneL⟫_ℝ = ⟪(negGraph q).val.fst, oneL⟫_ℝ = (1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ`,
     giving the two-sided lobe $L^1$-to-$L^2$ bound
     `⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(posGraph q).val.fst‖ ^ 2` and
     `⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(negGraph q).val.fst‖ ^ 2`,
     and the primitive lobe pairings
     `⟪(primGraph (posGraph q)).val.fst, (primGraph (negGraph q)).val.fst⟫_ℝ = -(1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`
     and
     `sourcePair (primGraph (posGraph q)) (primGraph (negGraph q)) = sourcePair (posGraph q) (negGraph q) + (1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Universal Eigenvector Nodal Lobe Energies and Individual Lobe Cross-Jump Bounds -/

/-- For every `q : SourceGraph`, `⟪(posGraph q).val.fst, q.val.fst⟫_ℝ = ‖(posGraph q).val.fst‖ ^ 2`. -/
theorem inner_posGraph_self_fst (q : SourceGraph) :
    ⟪(posGraph q).val.fst, q.val.fst⟫_ℝ = ‖(posGraph q).val.fst‖ ^ 2 := by
  have hsub : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  have h1 : ⟪(posGraph q).val.fst, q.val.fst⟫_ℝ =
      ⟪(posGraph q).val.fst, (posGraph q).val.fst - (negGraph q).val.fst⟫_ℝ := by
    rw [← hsub]
  rw [h1, inner_sub_right, inner_posGraph_negGraph_fst, sub_zero, real_inner_self_eq_norm_sq]

/-- For every `q : SourceGraph`, `⟪(negGraph q).val.fst, q.val.fst⟫_ℝ = -‖(negGraph q).val.fst‖ ^ 2`. -/
theorem inner_negGraph_self_fst (q : SourceGraph) :
    ⟪(negGraph q).val.fst, q.val.fst⟫_ℝ = -‖(negGraph q).val.fst‖ ^ 2 := by
  have hsub : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  have h1 : ⟪(negGraph q).val.fst, q.val.fst⟫_ℝ =
      ⟪(negGraph q).val.fst, (posGraph q).val.fst - (negGraph q).val.fst⟫_ℝ := by
    rw [← hsub]
  rw [h1, inner_sub_right, real_inner_comm (posGraph q).val.fst (negGraph q).val.fst,
    inner_posGraph_negGraph_fst, zero_sub, real_inner_self_eq_norm_sq]

/-- For every `q : SourceGraph`,
`⟪(absGraph q).val.fst, q.val.fst⟫_ℝ = ‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2`. -/
theorem inner_absGraph_self_fst (q : SourceGraph) :
    ⟪(absGraph q).val.fst, q.val.fst⟫_ℝ =
      ‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2 := by
  have hadd : (absGraph q).val.fst = (posGraph q).val.fst + (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_add_negGraph q).symm
  rw [hadd, inner_add_left, inner_posGraph_self_fst, inner_negGraph_self_fst]
  ring

/-- Universal `sourcePair` representation for the Riesz lift `q = rieszLift w` of any eigenvector
`resolvent w = μ • w` (`μ ≠ 0`):
`∀ p : SourceGraph, sourcePair p (rieszLift w) = ⟪p.val.fst, ((1 - 2 * μ) / μ) • (rieszLift w).val.fst⟫_ℝ`. -/
theorem sourcePair_rieszLift_eq_inner_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) (p : SourceGraph) :
    sourcePair p (rieszLift w) =
      ⟪p.val.fst, ((1 - 2 * μ) / μ) • (rieszLift w).val.fst⟫_ℝ := by
  have h1 := sourcePair_rieszLift_of_eigenvector heig p
  have hfst : (rieszLift w).val.fst = μ • w := heig
  rw [sourcePair_symm, h1, hfst, smul_smul, real_inner_smul_right, real_inner_comm w p.val.fst]
  congr 1
  field_simp [hμ]

/-- Universal edge-pairing identity for the Riesz lift `q = rieszLift w` of any eigenvector
`resolvent w = μ • w` (`μ ≠ 0`):
`∀ p : SourceGraph, ⟪p.val.snd, (rieszLift w).val.snd⟫_ℝ = ((1 - μ) / μ) * ⟪p.val.fst, (rieszLift w).val.fst⟫_ℝ`. -/
theorem inner_snd_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) (p : SourceGraph) :
    ⟪p.val.snd, (rieszLift w).val.snd⟫_ℝ =
      ((1 - μ) / μ) * ⟪p.val.fst, (rieszLift w).val.fst⟫_ℝ := by
  have h1 := inner_snd_eq_inner_fst_add_of_sourcePair_eq_inner
    (sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig) p
  have hid : (1 - 2 * μ) / μ + 1 = (1 - μ) / μ := by
    field_simp [hμ]
    ring
  calc ⟪p.val.snd, (rieszLift w).val.snd⟫_ℝ
      = ((1 - 2 * μ) / μ + 1) * ⟪p.val.fst, (rieszLift w).val.fst⟫_ℝ := by
        rw [h1, inner_add_right, real_inner_smul_right]; ring
    _ = ((1 - μ) / μ) * ⟪p.val.fst, (rieszLift w).val.fst⟫_ℝ := by
        rw [hid]

/-- **Exact Negative-Lobe Doob Energy of Any Resolvent Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`sourceEnergy (negGraph q) = ((1 - 2 * μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`. -/
theorem sourceEnergy_negGraph_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    sourceEnergy (negGraph (rieszLift w)) =
      ((1 - 2 * μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 +
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
  rw [sourceEnergy_negGraph_of_sourcePair_eq_inner
    (sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig),
    real_inner_smul_right, inner_negGraph_self_fst]
  ring

/-- **Nodal Lobe Energy Difference Identity for Resolvent Eigenvectors**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`sourceEnergy (posGraph q) - sourceEnergy (negGraph q) = ((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2)`. -/
theorem sourceEnergy_posGraph_sub_negGraph_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    sourceEnergy (posGraph (rieszLift w)) - sourceEnergy (negGraph (rieszLift w)) =
      ((1 - 2 * μ) / μ) *
        (‖(posGraph (rieszLift w)).val.fst‖ ^ 2 - ‖(negGraph (rieszLift w)).val.fst‖ ^ 2) := by
  rw [sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig,
    sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig]
  ring

/-- **Exact Positive-Lobe Edge Norm of Any Resolvent Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(posGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`. -/
theorem norm_posGraph_snd_sq_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    ‖(posGraph (rieszLift w)).val.snd‖ ^ 2 =
      ((1 - μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 +
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
  have hE : sourceEnergy (posGraph (rieszLift w)) =
      ‖(posGraph (rieszLift w)).val.snd‖ ^ 2 - ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig
  rw [hE] at h1
  have hid : (1 - 2 * μ) / μ + 1 = (1 - μ) / μ := by
    field_simp [hμ]
    ring
  linarith [congrArg (· * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2) hid]

/-- **Exact Negative-Lobe Edge Norm of Any Resolvent Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`. -/
theorem norm_negGraph_snd_sq_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    ‖(negGraph (rieszLift w)).val.snd‖ ^ 2 =
      ((1 - μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 +
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
  have hE : sourceEnergy (negGraph (rieszLift w)) =
      ‖(negGraph (rieszLift w)).val.snd‖ ^ 2 - ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig
  rw [hE] at h1
  have hid : (1 - 2 * μ) / μ + 1 = (1 - μ) / μ := by
    field_simp [hμ]
    ring
  linarith [congrArg (· * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2) hid]

/-- **Individual Nodal-Lobe Upper Bounds on the Cross-Jump Penalty**:
for every eigenvector `resolvent w = μ • w` (`0 < μ`) with `q = rieszLift w`, the cross-jump
penalty `-sourcePair (posGraph q) (negGraph q)` is bounded above by `((1 - μ) / μ)` times the
$L^2$ norm-squared of **each** nodal lobe individually:
`-sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2` and
`-sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2`. -/
theorem neg_sourcePair_posGraph_negGraph_le_pos_and_neg_lobe_of_eigenvector
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (heig : resolvent w = μ • w) :
    -sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤
        ((1 - μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 ∧
      -sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤
        ((1 - μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 := by
  have hp := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ.ne' heig
  have hn := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ.ne' heig
  have hp_nn : 0 ≤ ‖(posGraph (rieszLift w)).val.snd‖ ^ 2 := sq_nonneg _
  have hn_nn : 0 ≤ ‖(negGraph (rieszLift w)).val.snd‖ ^ 2 := sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- **Courant Nodal Lobe Negativity for Primitive Bound-State Eigenvectors**:
for every nonzero primitive eigenvector `resolvent w = μ • w` with `1 / 2 ≤ μ`, `w ≠ 0`, and
`⟪w, oneL⟫_ℝ = 0`, setting `q = rieszLift w`, both `posGraph q` and `negGraph q` have strictly
negative Doob energy:
`sourceEnergy (posGraph q) ≤ sourcePair (posGraph q) (negGraph q) < 0` and
`sourceEnergy (negGraph q) ≤ sourcePair (posGraph q) (negGraph q) < 0`. -/
theorem sourceEnergy_posGraph_and_negGraph_neg_of_boundState_eigenvector
    {μ : ℝ} (hμ : 1 / 2 ≤ μ) {w : MassSpace} (hw0 : w ≠ 0) (hprim : ⟪w, oneL⟫_ℝ = 0)
    (heig : resolvent w = μ • w) :
    sourceEnergy (posGraph (rieszLift w)) ≤
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ∧
      sourceEnergy (negGraph (rieszLift w)) ≤
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ∧
      sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) < 0 ∧
      sourceEnergy (posGraph (rieszLift w)) < 0 ∧
      sourceEnergy (negGraph (rieszLift w)) < 0 := by
  have hμ_pos : 0 < μ := by linarith
  set q := rieszLift w
  have hq_fst : q.val.fst = μ • w := heig
  have hq0 : q ≠ 0 := by
    intro h
    have hf : q.val.fst = 0 := by rw [h]; rfl
    rw [hq_fst, smul_eq_zero] at hf
    exact hw0 (hf.resolve_left hμ_pos.ne')
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    rw [hq_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hq0 hq_prim
  have hcross_neg : sourcePair (posGraph q) (negGraph q) < 0 :=
    sourcePair_posGraph_negGraph_neg_of_ne_zero hpos_ne hneg_ne
  have hcoeff_nonpos : (1 - 2 * μ) / μ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hμ_pos.le
  have hp_term : ((1 - 2 * μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos (sq_nonneg _)
  have hn_term : ((1 - 2 * μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos (sq_nonneg _)
  have hpE := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ_pos.ne' heig
  have hnE := sourceEnergy_negGraph_rieszLift_of_eigenvector hμ_pos.ne' heig
  refine ⟨by linarith, by linarith, hcross_neg, by linarith, by linarith⟩

/-! ## Section 2: Primitive `sourcePair` Decomposition, Lobe $L^1$-Equality, and Two-Sided Lobe Bounds -/

/-- Orthogonal decomposition of the `MassSpace` inner product under `primGraph`:
for all `p, r : SourceGraph`,
`⟪(primGraph p).val.fst, (primGraph r).val.fst⟫_ℝ = ⟪p.val.fst, r.val.fst⟫_ℝ - 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ`. -/
theorem inner_primGraph_fst (p r : SourceGraph) :
    ⟪(primGraph p).val.fst, (primGraph r).val.fst⟫_ℝ =
      ⟪p.val.fst, r.val.fst⟫_ℝ - 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ := by
  rw [primGraph_fst, primGraph_fst, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm oneL r.val.fst, real_inner_self_eq_norm_sq, norm_oneL_sq]
  ring

/-- **Bilinear Decomposition of `sourcePair` under `primGraph`**:
for all `p, r : SourceGraph`,
`sourcePair (primGraph p) (primGraph r) = sourcePair p r + 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ`. -/
theorem sourcePair_primGraph (p r : SourceGraph) :
    sourcePair (primGraph p) (primGraph r) =
      sourcePair p r + 2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ := by
  change ⟪(primGraph p).val.snd, (primGraph r).val.snd⟫_ℝ -
      ⟪(primGraph p).val.fst, (primGraph r).val.fst⟫_ℝ =
    (⟪p.val.snd, r.val.snd⟫_ℝ - ⟪p.val.fst, r.val.fst⟫_ℝ) +
      2 * ⟪p.val.fst, oneL⟫_ℝ * ⟪r.val.fst, oneL⟫_ℝ
  rw [primGraph_snd, primGraph_snd, inner_primGraph_fst]
  ring

/-- **Nodal Lobe $L^1$-Equality for Primitive Graph Vectors**:
for every primitive `q : SourceGraph` (`⟪q.val.fst, oneL⟫_ℝ = 0`), the positive and negative lobes
have equal pairings with `oneL`, each equal to `(1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ`. -/
theorem inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive {q : SourceGraph}
    (hq : ⟪q.val.fst, oneL⟫_ℝ = 0) :
    ⟪(posGraph q).val.fst, oneL⟫_ℝ = ⟪(negGraph q).val.fst, oneL⟫_ℝ ∧
      ⟪(posGraph q).val.fst, oneL⟫_ℝ = (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ∧
      ⟪(negGraph q).val.fst, oneL⟫_ℝ = (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ := by
  have hsub : (posGraph q).val.fst - (negGraph q).val.fst = q.val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q)
  have hadd : (posGraph q).val.fst + (negGraph q).val.fst = (absGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_add_negGraph q)
  have h1 : ⟪(posGraph q).val.fst, oneL⟫_ℝ - ⟪(negGraph q).val.fst, oneL⟫_ℝ = 0 := by
    rw [← inner_sub_left, hsub, hq]
  have h2 : ⟪(posGraph q).val.fst, oneL⟫_ℝ + ⟪(negGraph q).val.fst, oneL⟫_ℝ =
      ⟪(absGraph q).val.fst, oneL⟫_ℝ := by
    rw [← inner_add_left, hadd]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Two-Sided Nodal Lobe $L^1$-to-$L^2$ Bound for Primitive Graph Vectors**:
for every primitive `q : SourceGraph` (`⟪q.val.fst, oneL⟫_ℝ = 0`),
`⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(posGraph q).val.fst‖ ^ 2` and
`⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(negGraph q).val.fst‖ ^ 2`. -/
theorem inner_absGraph_oneL_sq_le_two_posGraph_and_negGraph_of_primitive {q : SourceGraph}
    (hq : ⟪q.val.fst, oneL⟫_ℝ = 0) :
    ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(posGraph q).val.fst‖ ^ 2 ∧
      ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ≤ 2 * ‖(negGraph q).val.fst‖ ^ 2 := by
  obtain ⟨_, hp, hn⟩ := inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive hq
  have hcs_p := two_mul_inner_oneL_sq_le_norm_sq (posGraph q).val.fst
  have hcs_n := two_mul_inner_oneL_sq_le_norm_sq (negGraph q).val.fst
  rw [hp] at hcs_p
  rw [hn] at hcs_n
  exact ⟨by linarith, by linarith⟩

/-- For any primitive `q : SourceGraph` (`⟪q.val.fst, oneL⟫_ℝ = 0`),
`⟪(primGraph (posGraph q)).val.fst, (primGraph (negGraph q)).val.fst⟫_ℝ = -(1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`
and
`sourcePair (primGraph (posGraph q)) (primGraph (negGraph q)) = sourcePair (posGraph q) (negGraph q) + (1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem primGraph_posGraph_negGraph_pairings_of_primitive {q : SourceGraph}
    (hq : ⟪q.val.fst, oneL⟫_ℝ = 0) :
    ⟪(primGraph (posGraph q)).val.fst, (primGraph (negGraph q)).val.fst⟫_ℝ =
        -(1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ∧
      sourcePair (primGraph (posGraph q)) (primGraph (negGraph q)) =
        sourcePair (posGraph q) (negGraph q) +
          (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
  obtain ⟨_, hp, hn⟩ := inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive hq
  refine ⟨?_, ?_⟩
  · rw [inner_primGraph_fst, inner_posGraph_negGraph_fst, hp, hn]
    ring
  · rw [sourcePair_primGraph, hp, hn]
    ring

/-- **Primitive Nodal Lobe Doob Energies of Any Primitive Resolvent Eigenvector**:
for every primitive eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `⟪w, oneL⟫_ℝ = 0`) with
`q = rieszLift w`,
`sourceEnergy (primGraph (posGraph q)) = ((1 - 2 * μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) + (1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`
and
`sourceEnergy (primGraph (negGraph q)) = ((1 - 2 * μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) + (1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem sourceEnergy_primGraph_posGraph_and_negGraph_rieszLift_of_primitive_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (hprim : ⟪w, oneL⟫_ℝ = 0)
    (heig : resolvent w = μ • w) :
    sourceEnergy (primGraph (posGraph (rieszLift w))) =
        ((1 - 2 * μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 +
          sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) +
          (1 / 2 : ℝ) * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ 2 ∧
      sourceEnergy (primGraph (negGraph (rieszLift w))) =
        ((1 - 2 * μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 +
          sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) +
          (1 / 2 : ℝ) * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ 2 := by
  have hq_prim : ⟪(rieszLift w).val.fst, oneL⟫_ℝ = 0 := by
    change ⟪resolvent w, oneL⟫_ℝ = 0
    rw [heig, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨_, hp1, hn1⟩ := inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive hq_prim
  refine ⟨?_, ?_⟩
  · rw [sourceEnergy_primGraph, sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig, hp1]
    ring
  · rw [sourceEnergy_primGraph, sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig, hn1]
    ring

/-! ## Section 3: Sharp Spectral-Gap Weighted Primitive Contraction and Nodal-Lobe Rayleigh Bounds -/

/-- **Exact Decomposed Doob Energy of `primGraph (absGraph (rieszLift w))` for Any Eigenvector**:
expressing `‖(rieszLift w).val.fst‖ ^ 2 = ‖(primGraph (absGraph (rieszLift w))).val.fst‖ ^ 2 + 2 * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ 2`
splits the ground-projection term with the spectral-gap factor `(1 - ν) / ν` (which vanishes as `ν → 1`):
`sourceEnergy (primGraph (absGraph q)) = ((1 - 2 * ν) / ν) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2 + 4 * sourcePair (posGraph q) (negGraph q) + ((1 - ν) / ν) * (2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem sourceEnergy_primGraph_absGraph_rieszLift_of_eigenvector {ν : ℝ} (hν : ν ≠ 0)
    {v : MassSpace} (heig : resolvent v = ν • v) :
    let q := rieszLift v
    sourceEnergy (primGraph (absGraph q)) =
      ((1 - 2 * ν) / ν) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2 +
        4 * sourcePair (posGraph q) (negGraph q) +
        ((1 - ν) / ν) * (2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
  intro q
  have hEp : sourceEnergy q = ((1 - 2 * ν) / ν) * ‖q.val.fst‖ ^ 2 := by
    have h2 : sourceEnergy q = ‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2 := rfl
    rw [h2, norm_rieszLift_snd_sq_of_eigenvector hν heig]
    field_simp [hν]
    ring
  have hnorm : ‖q.val.fst‖ ^ 2 =
      ‖(primGraph (absGraph q)).val.fst‖ ^ 2 + 2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [norm_primGraph_fst_sq, norm_absGraph_fst_sq]
    ring
  rw [sourceEnergy_primGraph, sourceEnergy_absGraph_eq, hEp, hnorm]
  field_simp [hν]
  ring

/-- **Sharp Spectral-Gap Weighted Primitive-Contraction Nodal Bound**:
for every eigenvector `resolvent v = ν • v` (`0 < ν`) with `q = rieszLift v`, and every `0 < μ_max`,
if `u_0 = (primGraph (absGraph q)).val.fst` satisfies `⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`,
then
`((ν - μ_max) / (ν * μ_max)) * ‖u_0‖ ^ 2 - 4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - ν) / ν) * (2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`.
Unlike `eigenvector_nodal_cross_le_of_primGraph_absGraph_rayleigh_le`, the right-hand side is
weighted by `(1 - ν) / ν` rather than `(1 - μ_max) / μ_max`. -/
theorem eigenvector_nodal_cross_le_spectral_gap_mul_oneL_sq
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace}
    (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2) :
    ((ν - μ_max) / (ν * μ_max)) * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2 -
        4 * sourcePair (posGraph (rieszLift v)) (negGraph (rieszLift v)) ≤
      ((1 - ν) / ν) * (2 * ⟪(absGraph (rieszLift v)).val.fst, oneL⟫_ℝ ^ 2) := by
  set q := rieszLift v
  have h1 := sourceEnergy_ge_of_inner_resolvent_le hμ hray
  have h2 := sourceEnergy_primGraph_absGraph_rieszLift_of_eigenvector hν.ne' heig
  dsimp only at h2
  have hid : -(((1 - 2 * ν) / ν) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2) -
      ((2 * μ_max - 1) / μ_max) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2 =
      ((ν - μ_max) / (ν * μ_max)) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2 := by
    field_simp [hν.ne', hμ.ne']
    ring
  linarith

/-- **Sharp Spectral-Gap Weighted Positive-Lobe Rayleigh Bound**:
for every primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `⟪v, oneL⟫_ℝ = 0`) with
`q = rieszLift v`, and every `0 < μ_max`, if `u_+ = (primGraph (posGraph q)).val.fst` satisfies
`⟪resolvent u_+, u_+⟫_ℝ ≤ μ_max * ‖u_+‖ ^ 2`, then
`((ν - μ_max) / (ν * μ_max)) * ‖u_+‖ ^ 2 - sourcePair (posGraph q) (negGraph q) ≤ ((1 - ν) / ν) * ((1 / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem eigenvector_pos_lobe_nodal_cross_le_spectral_gap_mul_oneL_sq
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace}
    (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (posGraph (rieszLift v))).val.fst,
        (primGraph (posGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (posGraph (rieszLift v))).val.fst‖ ^ 2) :
    ((ν - μ_max) / (ν * μ_max)) * ‖(primGraph (posGraph (rieszLift v))).val.fst‖ ^ 2 -
        sourcePair (posGraph (rieszLift v)) (negGraph (rieszLift v)) ≤
      ((1 - ν) / ν) * ((1 / 2 : ℝ) * ⟪(absGraph (rieszLift v)).val.fst, oneL⟫_ℝ ^ 2) := by
  set q := rieszLift v
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    change ⟪resolvent v, oneL⟫_ℝ = 0
    rw [heig, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨_, hp1, _⟩ := inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive hq_prim
  have hnorm : ‖(posGraph q).val.fst‖ ^ 2 =
      ‖(primGraph (posGraph q)).val.fst‖ ^ 2 +
        (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [norm_primGraph_fst_sq, hp1]
    ring
  have h1 := sourceEnergy_ge_of_inner_resolvent_le hμ hray
  have h2 := (sourceEnergy_primGraph_posGraph_and_negGraph_rieszLift_of_primitive_eigenvector
    hν.ne' hprim heig).1
  rw [hnorm] at h2
  have hid : ((1 - 2 * ν) / ν) *
      (‖(primGraph (posGraph q)).val.fst‖ ^ 2 +
        (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) +
      sourcePair (posGraph q) (negGraph q) +
      (1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 -
      (-((2 * μ_max - 1) / μ_max) * ‖(primGraph (posGraph q)).val.fst‖ ^ 2) =
      -((ν - μ_max) / (ν * μ_max)) * ‖(primGraph (posGraph q)).val.fst‖ ^ 2 +
        sourcePair (posGraph q) (negGraph q) +
        ((1 - ν) / ν) * ((1 / 2 : ℝ) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
    field_simp [hν.ne', hμ.ne']
    ring
  linarith

/-- Orthogonal decomposition of the $L^2$ norm-squared into positive and negative lobes:
`‖(posGraph p).val.fst‖ ^ 2 + ‖(negGraph p).val.fst‖ ^ 2 = ‖p.val.fst‖ ^ 2`. -/
theorem norm_posGraph_fst_sq_add_negGraph_fst_sq (p : SourceGraph) :
    ‖(posGraph p).val.fst‖ ^ 2 + ‖(negGraph p).val.fst‖ ^ 2 = ‖p.val.fst‖ ^ 2 := by
  have hsub : (posGraph p).val.fst - (negGraph p).val.fst = p.val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph p)
  have h1 : ⟪(posGraph p).val.fst - (negGraph p).val.fst, p.val.fst⟫_ℝ = ‖p.val.fst‖ ^ 2 := by
    rw [hsub, real_inner_self_eq_norm_sq]
  rw [inner_sub_left, inner_posGraph_self_fst, inner_negGraph_self_fst] at h1
  linarith

/-- For any odd graph vector `p` (`reflectGraph p = -p`), its positive and negative lobes have equal
`MassSpace` norm-squared, each equal to `(1 / 2) * ‖p.val.fst‖ ^ 2`. -/
theorem norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd {p : SourceGraph}
    (hp : reflectGraph p = -p) :
    ‖(posGraph p).val.fst‖ ^ 2 = (1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2 ∧
      ‖(negGraph p).val.fst‖ ^ 2 = (1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2 := by
  have heq : ‖(posGraph p).val.fst‖ = ‖(negGraph p).val.fst‖ := by
    rw [← reflectGraph_posGraph_of_odd hp, reflectGraph_fst]
    exact (reflectMass.norm_map _).symm
  have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq p
  have hsq : ‖(posGraph p).val.fst‖ ^ 2 = ‖(negGraph p).val.fst‖ ^ 2 := by rw [heq]
  exact ⟨by linarith, by linarith⟩

end RHTower.CHMDPolar
