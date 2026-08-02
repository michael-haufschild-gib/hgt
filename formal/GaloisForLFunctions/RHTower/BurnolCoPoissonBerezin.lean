import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceSpace
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Co-Poisson quotient kernels and Berezin diagonal

The closed source space constructed from literal co-Poisson sums has an orthogonal source
projection.  Subtracting that projection from Burnol's completed-Mellin Riesz vector gives the
canonical quotient kernel.  This file proves its reproducing identity, its equality with the
ambient kernel at every source-annihilator point, and positivity of the resulting Berezin reader.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Orthogonal projection onto the closed, explicitly generated co-Poisson source space. -/
def burnolCoPoissonSourceProjection (b : ℝ) :
    evenSubspace →L[ℂ] evenSubspace := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  exact (burnolCoPoissonSourceSpace b).starProjection

theorem burnolCoPoissonSourceProjection_apply_mem (b : ℝ) (f : evenSubspace) :
    burnolCoPoissonSourceProjection b f ∈ burnolCoPoissonSourceSpace b := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  exact (burnolCoPoissonSourceSpace b).starProjection_apply_mem f

theorem burnolCoPoissonSourceProjection_eq_zero_iff
    (b : ℝ) {f : evenSubspace} :
    burnolCoPoissonSourceProjection b f = 0 ↔
      f ∈ (burnolCoPoissonSourceSpace b)ᗮ := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  exact (burnolCoPoissonSourceSpace b).starProjection_apply_eq_zero_iff

theorem soninCosineUnitary_burnolCoPoissonSourceProjection
    (b : ℝ) (f : evenSubspace) :
    soninCosineUnitary (burnolCoPoissonSourceProjection b f) =
      burnolCoPoissonSourceProjection b (soninCosineUnitary f) := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  change soninCosineUnitary ((burnolCoPoissonSourceSpace b).starProjection f) =
    (burnolCoPoissonSourceSpace b).starProjection (soninCosineUnitary f)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact soninCosineUnitary_mem_coPoissonSourceSpace (Submodule.coe_mem _)
  · intro g hg
    have hFg : soninCosineUnitary g ∈ burnolCoPoissonSourceSpace b :=
      soninCosineUnitary_mem_coPoissonSourceSpace hg
    calc
      ⟪soninCosineUnitary f -
          soninCosineUnitary ((burnolCoPoissonSourceSpace b).starProjection f), g⟫_ℂ =
          ⟪soninCosineUnitary (f - (burnolCoPoissonSourceSpace b).starProjection f),
            soninCosineUnitary (soninCosineUnitary g)⟫_ℂ := by
            rw [map_sub, soninCosineUnitary_involutive]
      _ = ⟪f - (burnolCoPoissonSourceSpace b).starProjection f,
          soninCosineUnitary g⟫_ℂ := soninCosineUnitary.inner_map_map _ _
      _ = 0 := Submodule.starProjection_inner_eq_zero f _ hFg

/-- Canonical right-half-plane evaluation vector in the co-Poisson quotient realization. -/
def burnolCoPoissonQuotientEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b) :
    burnolCoPoissonQuotientSpace b := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  let k : evenSubspace := burnolExtendedSoninEvaluationVector w b hlo hhi hb
  let p : evenSubspace := (burnolCoPoissonSourceSpace b).starProjection k
  refine ⟨k - p, ?_, ?_⟩
  · exact (soninExtendedSpace b).sub_mem
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb).property
      (burnolCoPoissonSourceSpace_le_soninExtendedSpace hb
        ((burnolCoPoissonSourceSpace b).starProjection_apply_mem k))
  · exact Submodule.sub_starProjection_mem_orthogonal k

@[simp] theorem coe_burnolCoPoissonQuotientEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b) :
    (burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace) =
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) -
        burnolCoPoissonSourceProjection b
          (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) :=
  rfl

/-- Reproducing-kernel identity on the source quotient. -/
theorem inner_burnolCoPoissonQuotientEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (f : burnolCoPoissonQuotientSpace b) :
    ⟪burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb, f⟫_ℂ =
      soninMellinEvaluation w (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  change ⟪(burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace),
      (f : evenSubspace)⟫_ℂ = _
  rw [coe_burnolCoPoissonQuotientEvaluationVector, inner_sub_left]
  have hp0 : ⟪burnolCoPoissonSourceProjection b
        (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
      (f : evenSubspace)⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (burnolCoPoissonSourceProjection_apply_mem b _ ) f.property.2
  rw [hp0, sub_zero]
  exact inner_burnolExtendedSoninEvaluationVector w b hlo hhi hb
    ⟨(f : evenSubspace), f.property.1⟩

/-- A regular point annihilates the source precisely when every literal closed co-Poisson source
has zero completed-Mellin value there. -/
def BurnolCoPoissonAnnihilatorPoint
    (w : ℂ) (b : ℝ) (_hlo : 1 / 2 < w.re) (_hhi : w.re < 1) (hb : 0 < b) : Prop :=
  ∀ c : burnolCoPoissonSourceSpace b,
    soninMellinEvaluation w
      ((((⟨(c : evenSubspace), burnolCoPoissonSourceSpace_le_soninExtendedSpace hb c.property⟩ :
        soninExtendedSpace b) : evenSubspace) : SoninL2) : ℝ → ℂ) = 0

theorem burnolExtendedSoninEvaluationVector_mem_source_orthogonal
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hann : BurnolCoPoissonAnnihilatorPoint w b hlo hhi hb) :
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) ∈
      (burnolCoPoissonSourceSpace b)ᗮ := by
  intro c hc
  rw [inner_eq_zero_symm]
  change ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb,
    (⟨c, burnolCoPoissonSourceSpace_le_soninExtendedSpace hb hc⟩ :
      soninExtendedSpace b)⟫_ℂ = 0
  rw [inner_burnolExtendedSoninEvaluationVector]
  exact hann ⟨c, hc⟩

/-- On a source-annihilator fibre the quotient kernel is exactly the ambient Sonine kernel. -/
theorem coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hann : BurnolCoPoissonAnnihilatorPoint w b hlo hhi hb) :
    (burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace) =
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  rw [coe_burnolCoPoissonQuotientEvaluationVector]
  rw [(burnolCoPoissonSourceProjection_eq_zero_iff b).mpr
    (burnolExtendedSoninEvaluationVector_mem_source_orthogonal hlo hhi hb hann), sub_zero]

/-- Unnormalized co-Poisson Berezin diagonal. -/
def burnolCoPoissonBerezin
    {b : ℝ} (T : evenSubspace →L[ℂ] evenSubspace)
    (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b) : ℂ :=
  ⟪(burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace),
    T (burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace)⟫_ℂ

/-- Every positive operator has a nonnegative co-Poisson Berezin diagonal. -/
theorem burnolCoPoissonBerezin_re_nonneg
    {b : ℝ} {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : T.IsPositive) (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b) :
    0 ≤ (burnolCoPoissonBerezin T w hlo hhi hb).re :=
  hT.re_inner_nonneg_right
    (burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace)

end RHTower
