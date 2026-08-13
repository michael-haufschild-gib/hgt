import GaloisForLFunctions.HTGeometry.NevanlinnaConstraintProjector
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Normalization independence of the Nevanlinna carrier projector

A change of the real determinant-one Nevanlinna matrix acts by right multiplication with an
element `g` of `SL(2, ℝ)`.  The twisted matrix data has denominator
`c'(x)σ + d'(x) = c(x)(g₀₀σ + g₀₁) + d(x)(g₁₀σ + g₁₁)`, so its denominator fibers are the
original fibers relabelled along the Möbius action of `g` on the projective line, and the twisted
boundary family carries the original leaves in the relabelled coordinate.  The leaf/label
covariance transport therefore applies with the relabelling `t ↦ g⁻¹ • t`, and the carrier
projector of the twisted family coincides with the original one: the canonical retraction is
independent of the chosen Nevanlinna normalization.

Continuity of the Möbius action on `OnePoint ℝ` is obtained on the finite chart by exhibiting the
action as the projective label of an auxiliary determinant-one matrix data, and at `∞` by the
cocompact limit of the Möbius quotient.
-/

open Filter Topology OnePoint Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace NevanlinnaNormalization

/-- The Möbius action of an `SL(2,ℝ)` element on the finite chart, as determinant-one matrix
data over `ℝ`. -/
def mobiusChartData (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : NevanlinnaMatrixData ℝ where
  a := fun _ => g.1 1 0
  b := fun _ => -g.1 0 0
  c := fun τ => g.1 1 0 * τ + g.1 1 1
  d := fun τ => -(g.1 0 0 * τ + g.1 0 1)
  det_one := by
    intro τ
    have hdet := g.2
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet

theorem toGL_entry (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) :
    (g.toGL : Matrix (Fin 2) (Fin 2) ℝ) i j = g.1 i j := rfl

/-- On the finite chart the Möbius action is the projective label of the chart data. -/
theorem smul_coe_eq_label (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : ℝ) :
    g.toGL • (τ : OnePoint ℝ) = (mobiusChartData g).projectiveLabel τ := by
  rw [OnePoint.smul_some_eq_ite]
  unfold NevanlinnaMatrixData.projectiveLabel mobiusChartData
  simp only [toGL_entry]
  by_cases hden : g.1 1 0 * τ + g.1 1 1 = 0
  · simp [hden]
  · simp only [hden, if_false]
    rw [OnePoint.coe_eq_coe]
    rw [neg_neg]

/-- No point of the projective line is annihilated by both rows. -/
theorem row_ne_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {σ : ℝ}
    (hden : g.1 1 0 * σ + g.1 1 1 = 0) :
    g.1 0 0 * σ + g.1 0 1 ≠ 0 := by
  intro hnum
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h1 : (g.1 0 0 * σ + g.1 0 1) * g.1 1 1 - (g.1 1 0 * σ + g.1 1 1) * g.1 0 1 =
      σ * (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) := by ring
  rw [hnum, hden] at h1
  simp only [zero_mul, sub_zero] at h1
  have hσ : σ * (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) = 0 := by linarith
  rw [hdet] at hσ
  rw [mul_one] at hσ
  subst hσ
  rw [mul_zero, zero_add] at hden hnum
  rw [hden, hnum] at hdet
  simp at hdet

/-- Cocompact convergence of the Möbius quotient when the lower-left entry does not vanish. -/
theorem tendsto_mobius_cocompact_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hg : g.1 1 0 ≠ 0) :
    Tendsto (fun τ : ℝ => g.toGL • (τ : OnePoint ℝ)) (cocompact ℝ)
      (𝓝 ((g.1 0 0 / g.1 1 0 : ℝ) : OnePoint ℝ)) := by
  have hinv : Tendsto (fun τ : ℝ => τ⁻¹) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    exact ⟨tendsto_inv_atBot_zero, tendsto_inv_atTop_zero⟩
  have hnum : Tendsto (fun τ : ℝ => g.1 0 0 + g.1 0 1 * τ⁻¹) (cocompact ℝ)
      (𝓝 (g.1 0 0)) := by
    have := (hinv.const_mul (g.1 0 1)).const_add (g.1 0 0)
    simpa using this
  have hden : Tendsto (fun τ : ℝ => g.1 1 0 + g.1 1 1 * τ⁻¹) (cocompact ℝ)
      (𝓝 (g.1 1 0)) := by
    have := (hinv.const_mul (g.1 1 1)).const_add (g.1 1 0)
    simpa using this
  have hratio : Tendsto (fun τ : ℝ =>
      (g.1 0 0 + g.1 0 1 * τ⁻¹) / (g.1 1 0 + g.1 1 1 * τ⁻¹)) (cocompact ℝ)
      (𝓝 (g.1 0 0 / g.1 1 0)) := hnum.div hden hg
  have hne0 : ∀ᶠ τ : ℝ in cocompact ℝ, τ ≠ 0 := by
    have hmem : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ cocompact ℝ := by
      rw [mem_cocompact]
      exact ⟨{0}, isCompact_singleton, le_rfl⟩
    filter_upwards [hmem] with τ hτ
    exact hτ
  have hdenne : ∀ᶠ τ : ℝ in cocompact ℝ, g.1 1 0 + g.1 1 1 * τ⁻¹ ≠ 0 :=
    hden.eventually_ne hg
  have hcoe := (OnePoint.continuous_coe.tendsto _).comp hratio
  refine hcoe.congr' ?_
  filter_upwards [hne0, hdenne] with τ hτ hdτ
  have hbig : g.1 1 0 * τ + g.1 1 1 ≠ 0 := by
    intro hzero
    apply hdτ
    field_simp
    linear_combination hzero
  rw [Function.comp_apply, OnePoint.smul_some_eq_ite]
  simp only [toGL_entry, hbig, if_false]
  rw [OnePoint.coe_eq_coe]
  field_simp

/-- Cocompact escape of the affine action when the lower-left entry vanishes. -/
theorem tendsto_mobius_cocompact_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hg : g.1 1 0 = 0) :
    Tendsto (fun τ : ℝ => g.toGL • (τ : OnePoint ℝ)) (cocompact ℝ)
      (𝓝 (∞ : OnePoint ℝ)) := by
  have hdet := g.2
  rw [Matrix.det_fin_two, hg] at hdet
  have h11 : g.1 1 1 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have h00 : g.1 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hk : g.1 0 0 / g.1 1 1 ≠ 0 := div_ne_zero h00 h11
  have haffine : Tendsto (fun τ : ℝ =>
      g.1 0 0 / g.1 1 1 * τ + g.1 0 1 / g.1 1 1) (cocompact ℝ) (cocompact ℝ) := by
    have hhomeo := ((Homeomorph.mulLeft₀ (g.1 0 0 / g.1 1 1) hk).trans
      (Homeomorph.addRight (g.1 0 1 / g.1 1 1))).isClosedEmbedding.tendsto_cocompact
    refine hhomeo.congr ?_
    intro τ
    rfl
  have hcoeInf : Tendsto ((↑) : ℝ → OnePoint ℝ) (cocompact ℝ) (𝓝 (∞ : OnePoint ℝ)) := by
    show Filter.map _ (cocompact ℝ) ≤ _
    rw [OnePoint.nhds_infty_eq, ← Filter.coclosedCompact_eq_cocompact]
    exact le_sup_left
  have hcomp := hcoeInf.comp haffine
  refine hcomp.congr' ?_
  filter_upwards with τ
  have hbig : g.1 1 0 * τ + g.1 1 1 ≠ 0 := by
    rw [hg, zero_mul, zero_add]
    exact h11
  rw [Function.comp_apply, OnePoint.smul_some_eq_ite]
  simp only [toGL_entry, hbig, if_false]
  rw [OnePoint.coe_eq_coe, hg, zero_mul, zero_add]
  field_simp

/-- **The Möbius action on the projective line is continuous.** -/
theorem continuous_smul_onePoint (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Continuous (fun t : OnePoint ℝ => g.toGL • t) := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact]
    by_cases hg : g.1 1 0 = 0
    · have hval : g.toGL • (∞ : OnePoint ℝ) = ∞ := by
        rw [OnePoint.smul_infty_eq_ite]
        simp [toGL_entry, hg]
      rw [hval]
      exact tendsto_mobius_cocompact_zero g hg
    · have hval : g.toGL • (∞ : OnePoint ℝ) =
          ((g.1 0 0 / g.1 1 0 : ℝ) : OnePoint ℝ) := by
        rw [OnePoint.smul_infty_eq_ite]
        simp [toGL_entry, hg]
      rw [hval]
      exact tendsto_mobius_cocompact_ne g hg
  · have hlabel := (mobiusChartData g).continuous_projectiveLabel
      (by fun_prop) (by fun_prop)
    refine hlabel.congr ?_
    intro τ
    exact (smul_coe_eq_label g τ).symm

end NevanlinnaNormalization

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter Topology OnePoint Matrix MeasureTheory

noncomputable section

namespace NevanlinnaNormalization

@[simp] theorem inv_entry_zero_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g⁻¹).1 0 0 = g.1 1 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp

@[simp] theorem inv_entry_zero_one (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g⁻¹).1 0 1 = -g.1 0 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp

@[simp] theorem inv_entry_one_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g⁻¹).1 1 0 = -g.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp

@[simp] theorem inv_entry_one_one (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g⁻¹).1 1 1 = g.1 0 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp

/-- The determinant identity of an `SL(2,ℝ)` element in entry form. -/
theorem det_entries (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

theorem toGL_inv (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g⁻¹).toGL = (g.toGL)⁻¹ := map_inv _ _

theorem smul_inv_smul_onePoint (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : OnePoint ℝ) :
    g.toGL • ((g⁻¹).toGL • t) = t := by
  rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

theorem inv_smul_onePoint_eq_iff (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (u t : OnePoint ℝ) : (g⁻¹).toGL • u = t ↔ u = g.toGL • t := by
  rw [toGL_inv, inv_smul_eq_iff]

end NevanlinnaNormalization

namespace NevanlinnaMatrixData

variable {X : Type*}

/-- Right translation of determinant-one matrix data by an element of `SL(2,ℝ)`: the matrix
product `W · g`, which is the change of the projective boundary coordinate. -/
def twist (W : NevanlinnaMatrixData X) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    NevanlinnaMatrixData X where
  a x := W.a x * g.1 0 0 + W.b x * g.1 1 0
  b x := W.a x * g.1 0 1 + W.b x * g.1 1 1
  c x := W.c x * g.1 0 0 + W.d x * g.1 1 0
  d x := W.c x * g.1 0 1 + W.d x * g.1 1 1
  det_one x := by
    have hW := W.det_one x
    have hg := NevanlinnaNormalization.det_entries g
    linear_combination (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) * hW + hg

@[simp] theorem twist_c (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : X) :
    (W.twist g).c x = W.c x * g.1 0 0 + W.d x * g.1 1 0 := rfl

@[simp] theorem twist_d (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : X) :
    (W.twist g).d x = W.c x * g.1 0 1 + W.d x * g.1 1 1 := rfl

/-- **Label covariance.**  Changing the Nevanlinna normalization by `g` relabels every projective
support label by the inverse Möbius transformation. -/
theorem twist_projectiveLabel (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : X) :
    (W.twist g).projectiveLabel x = (g⁻¹).toGL • W.projectiveLabel x := by
  have hg := NevanlinnaNormalization.det_entries g
  by_cases hc : W.c x = 0
  · have hd : W.d x ≠ 0 := fun h => W.C_D_ne_zero x ⟨hc, h⟩
    rw [(W.projectiveLabel_eq_infty_iff x).2 hc, OnePoint.smul_infty_eq_ite]
    simp only [NevanlinnaNormalization.toGL_entry,
      NevanlinnaNormalization.inv_entry_one_zero, NevanlinnaNormalization.inv_entry_zero_zero]
    by_cases h10 : g.1 1 0 = 0
    · rw [if_pos (by rw [h10, neg_zero])]
      refine ((W.twist g).projectiveLabel_eq_infty_iff x).2 ?_
      rw [twist_c, hc, h10]
      ring
    · have hneg : -g.1 1 0 ≠ 0 := neg_ne_zero.2 h10
      rw [if_neg hneg]
      refine ((W.twist g).projectiveLabel_eq_coe_iff x _).2 ?_
      rw [twist_c, twist_d, hc]
      field_simp
      ring
  · have hlab : W.projectiveLabel x = ((-W.d x / W.c x : ℝ) : OnePoint ℝ) := by
      unfold projectiveLabel
      rw [if_neg hc]
    rw [hlab, OnePoint.smul_some_eq_ite]
    simp only [NevanlinnaNormalization.toGL_entry,
      NevanlinnaNormalization.inv_entry_one_zero, NevanlinnaNormalization.inv_entry_one_one,
      NevanlinnaNormalization.inv_entry_zero_zero, NevanlinnaNormalization.inv_entry_zero_one]
    have hden : -g.1 1 0 * (-W.d x / W.c x) + g.1 0 0
        = (W.c x * g.1 0 0 + W.d x * g.1 1 0) / W.c x := by
      field_simp
      ring
    by_cases hc' : W.c x * g.1 0 0 + W.d x * g.1 1 0 = 0
    · rw [if_pos (by rw [hden, hc', zero_div])]
      exact ((W.twist g).projectiveLabel_eq_infty_iff x).2 hc'
    · have hdenne : -g.1 1 0 * (-W.d x / W.c x) + g.1 0 0 ≠ 0 := by
        rw [hden]
        exact div_ne_zero hc' hc
      rw [if_neg hdenne]
      refine ((W.twist g).projectiveLabel_eq_coe_iff x _).2 ?_
      rw [twist_c, twist_d, hden]
      field_simp
      ring

/-- The relabelled level sets of the projective label. -/
theorem twist_label_setOf (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : OnePoint ℝ) :
    {x | (W.twist g).projectiveLabel x = t} = {x | W.projectiveLabel x = g.toGL • t} := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, W.twist_projectiveLabel g x,
    NevanlinnaNormalization.inv_smul_onePoint_eq_iff]

/-- **Fiber covariance, finite parameter.** -/
theorem twist_finiteDenominatorFiber (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (tau : ℝ) :
    (W.twist g).finiteDenominatorFiber tau
      = {x | W.projectiveLabel x = g.toGL • (tau : OnePoint ℝ)} := by
  have h : (W.twist g).finiteDenominatorFiber tau
      = {x | (W.twist g).projectiveLabel x = (tau : OnePoint ℝ)} := by
    ext x
    exact (((W.twist g).projectiveLabel_eq_coe_iff x tau).symm)
  rw [h, twist_label_setOf]

/-- **Fiber covariance, parameter at infinity.** -/
theorem twist_infinityDenominatorFiber (W : NevanlinnaMatrixData X)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (W.twist g).infinityDenominatorFiber
      = {x | W.projectiveLabel x = g.toGL • (∞ : OnePoint ℝ)} := by
  have h : (W.twist g).infinityDenominatorFiber
      = {x | (W.twist g).projectiveLabel x = (∞ : OnePoint ℝ)} := by
    ext x
    exact (((W.twist g).projectiveLabel_eq_infty_iff x).symm)
  rw [h, twist_label_setOf]

end NevanlinnaMatrixData

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Every leaf is carried by the level set of its own projective label. -/
theorem carried_label (t : OnePoint ℝ) :
    (F.leaf t : Measure ℝ) {x : ℝ | F.matrix.projectiveLabel x = t}ᶜ = 0 := by
  induction t using OnePoint.rec with
  | infty =>
      have h : {x : ℝ | F.matrix.projectiveLabel x = (∞ : OnePoint ℝ)}
          = F.matrix.infinityDenominatorFiber := by
        ext x
        exact F.matrix.projectiveLabel_eq_infty_iff x
      rw [h]
      exact F.infinity_carried
  | coe tau =>
      have h : {x : ℝ | F.matrix.projectiveLabel x = (tau : OnePoint ℝ)}
          = F.matrix.finiteDenominatorFiber tau := by
        ext x
        exact F.matrix.projectiveLabel_eq_coe_iff x tau
      rw [h]
      exact F.finite_carried tau

/-- **The Nevanlinna boundary family in a changed normalization.**  The matrix data is translated
by `g` and the leaves are relabelled along the Möbius action of `g`. -/
def twist (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : NevanlinnaBoundaryFamily s where
  matrix := F.matrix.twist g
  continuous_c := by
    show Continuous fun x => F.matrix.c x * g.1 0 0 + F.matrix.d x * g.1 1 0
    exact (F.continuous_c.mul continuous_const).add (F.continuous_d.mul continuous_const)
  continuous_d := by
    show Continuous fun x => F.matrix.c x * g.1 0 1 + F.matrix.d x * g.1 1 1
    exact (F.continuous_c.mul continuous_const).add (F.continuous_d.mul continuous_const)
  leaf t := F.leaf (g.toGL • t)
  continuous_leaf :=
    F.continuous_leaf.comp (NevanlinnaNormalization.continuous_smul_onePoint g)
  finite_carried tau := by
    rw [NevanlinnaMatrixData.twist_finiteDenominatorFiber]
    exact F.carried_label _
  infinity_carried := by
    rw [NevanlinnaMatrixData.twist_infinityDenominatorFiber]
    exact F.carried_label _
  leaf_moments t := F.leaf_moments (g.toGL • t)

@[simp] theorem twist_matrix (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (F.twist g).matrix = F.matrix.twist g := rfl

@[simp] theorem twist_leaf (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : OnePoint ℝ) :
    (F.twist g).leaf t = F.leaf (g.toGL • t) := rfl

/-- **Normalization independence of the canonical retraction.**  A change of the real
determinant-one Nevanlinna matrix leaves the carrier projector unchanged. -/
theorem twist_carrierProjector_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (nu : ProbabilityMeasure ℝ) :
    (F.twist g).carrierProjector nu = F.carrierProjector nu := by
  refine F.carrierProjector_eq_of_leaf_label_covariance (F.twist g)
    (fun t => (g⁻¹).toGL • t) (fun t => ?_) (fun x => ?_) nu
  · show F.leaf (g.toGL • ((g⁻¹).toGL • t)) = F.leaf t
    rw [NevanlinnaNormalization.smul_inv_smul_onePoint]
  · exact F.matrix.twist_projectiveLabel g x

theorem twist_carrierProjector (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (F.twist g).carrierProjector = F.carrierProjector :=
  funext fun nu => F.twist_carrierProjector_apply g nu

/-- The Nevanlinna boundary carrier set is intrinsic: it does not depend on the choice of the
determinant-one normalization. -/
theorem twist_range_barycenter (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.range (F.twist g).barycenter = Set.range F.barycenter := by
  rw [← (F.twist g).range_carrierProjector, ← F.range_carrierProjector,
    F.twist_carrierProjector g]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
