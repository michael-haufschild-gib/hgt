import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum
import Mathlib.Analysis.Real.Cardinality

/-!
# Trace-class rounding of almost-projections

A self-adjoint operator with nuclear idempotency defect differs by a nuclear operator from an
orthogonal projection. The proof derives a spectral cut from compactness; no spectral gap is
assumed. This standard operator-theory step supplies genuine projections in the continuous
cubic-charge construction. Nuclear corrections to both factors preserve an admitted commutator
trace, without admitting either separate product.
-/

open ContinuousLinearMap Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


private theorem finite_quadratic_fibre (d : ℝ) :
    {x : ℝ | x - x * x = d}.Finite := by
  by_cases h : ∃ x : ℝ, x - x * x = d
  · obtain ⟨x, hx⟩ := h
    apply ((Set.finite_singleton (1-x)).insert x).subset
    intro y hy
    have heq : (y-x) * (y+x-1) = 0 := by
      dsimp only [Set.mem_setOf_eq] at hy
      nlinarith
    rcases mul_eq_zero.mp heq with heq | heq
    · exact Or.inl (by linarith)
    · exact Or.inr (by change y = 1-x; linarith)
  · have he : {x : ℝ | x - x * x = d} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x, hx⟩
    rw [he]
    exact Set.finite_empty

/-- A compact idempotency defect makes the real spectrum countable. -/
theorem countable_spectrum_of_compact_idempotency_defect
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hD : IsCompactOperator (T - T*T)) :
    (spectrum ℝ T).Countable := by
  have hsaD : IsSelfAdjoint (T - T*T) := by
    show star (T-T*T) = T-T*T
    simp only [star_sub, star_mul, hT.star_eq]
  have hcD := countable_spectrum_of_isCompactOperator hD hsaD.isSymmetric
  have hcR : (spectrum ℝ (T-T*T)).Countable := by
    apply (hcD.preimage Complex.ofReal_injective).mono
    intro x hx
    exact (hsaD.coe_mem_spectrum_complex).mpr hx
  have himage : spectrum ℝ (T-T*T) = (fun x : ℝ => x-x*x) '' spectrum ℝ T := by
    have heq : cfc (fun x : ℝ => x-x*x) T = T-T*T := by
      rw [cfc_sub (fun x : ℝ => x) (fun x => x*x) T,
        cfc_mul (fun x : ℝ => x) (fun x => x) T, cfc_id' ℝ T]
    rw [← heq, cfc_map_spectrum (fun x : ℝ => x-x*x) T hT]
  letI := hcR.to_subtype
  have hc : (⋃ d : spectrum ℝ (T-T*T), {x : ℝ | x-x*x = d.val}).Countable :=
    Set.countable_iUnion fun d => (finite_quadratic_fibre d.val).countable
  apply hc.mono
  intro x hx
  have hd : x-x*x ∈ spectrum ℝ (T-T*T) := by
    rw [himage]
    exact ⟨x, hx, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨x-x*x, hd⟩, rfl⟩

/-- A spectral cut strictly between zero and one follows from compactness of the defect. -/
theorem exists_gap_of_compact_idempotency_defect
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hD : IsCompactOperator (T - T*T)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ b ∉ spectrum ℝ T := by
  have hc := countable_spectrum_of_compact_idempotency_defect T hT hD
  by_contra hn
  push Not at hn
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ spectrum ℝ T := by
    intro b hb
    exact hn b hb.1 hb.2
  have hbad := Cardinal.Real.Ioo_countable_iff.mp (hc.mono hsub)
  norm_num at hbad

/-- Scalar spectral-cut function used to round an almost-projection. -/
def projectionRoundingStep (b x : ℝ) : ℝ := if b < x then 1 else 0
/-- Bounded-on-spectrum multiplier factoring the rounding error through the defect. -/
def projectionRoundingFactor (b x : ℝ) : ℝ :=
  if b < x then x⁻¹ else -(1-x)⁻¹

/-- The cut and error multiplier are continuous away from the chosen cut. -/
theorem projectionRounding_continuousAt {b x : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hxb : x ≠ b) :
    ContinuousAt (projectionRoundingStep b) x ∧
      ContinuousAt (projectionRoundingFactor b) x := by
  rcases lt_or_gt_of_ne hxb with hlt | hgt
  · have he : ∀ᶠ y in 𝓝 x, y < b := eventually_lt_nhds hlt
    constructor
    · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp [projectionRoundingStep, not_lt.mpr hy.le]
    · have hne : 1-x ≠ 0 := by linarith
      have hf : ContinuousAt (fun y : ℝ => -(1-y)⁻¹) x := by fun_prop
      apply hf.congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp [projectionRoundingFactor, not_lt.mpr hy.le]
  · have he : ∀ᶠ y in 𝓝 x, b < y := eventually_gt_nhds hgt
    constructor
    · apply (continuousAt_const (y := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp [projectionRoundingStep, hy]
    · have hne : x ≠ 0 := ne_of_gt (hb0.trans hgt)
      have hf : ContinuousAt (fun y : ℝ => y⁻¹) x := by fun_prop
      apply hf.congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp [projectionRoundingFactor, hy]

/-- Exact scalar factorization of the projection-rounding error. -/
theorem projectionRounding_factorization {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (x : ℝ) :
    projectionRoundingStep b x - x = projectionRoundingFactor b x * (x-x*x) := by
  by_cases h : b < x
  · have hne : x ≠ 0 := ne_of_gt (hb0.trans h)
    simp only [projectionRoundingStep, projectionRoundingFactor, if_pos h]
    field_simp
  · have hne : 1-x ≠ 0 := by have := le_of_not_gt h; linarith
    simp only [projectionRoundingStep, projectionRoundingFactor, if_neg h]
    field_simp
    ring

/-- Every self-adjoint almost-projection with nuclear defect has an orthogonal projection lift
modulo the nuclear ideal. Positivity or an a priori spectral gap is not needed. -/
theorem exists_projection_traceClass_perturbation
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hD : MemSchattenClass 1 (T-T*T)) :
    ∃ P : H →L[ℂ] H, IsSelfAdjoint P ∧ IsIdempotentElem P ∧
      MemSchattenClass 1 (P-T) := by
  obtain ⟨b, hb0, hb1, hb⟩ :=
    exists_gap_of_compact_idempotency_defect T hT (hD.isCompactOperator one_pos)
  have hcont (x : ℝ) (hx : x ∈ spectrum ℝ T) :=
    projectionRounding_continuousAt hb0 hb1 (fun he => hb (he ▸ hx))
  have hp : ContinuousOn (projectionRoundingStep b) (spectrum ℝ T) :=
    continuousOn_of_forall_continuousAt fun x hx => (hcont x hx).1
  have hr : ContinuousOn (projectionRoundingFactor b) (spectrum ℝ T) :=
    continuousOn_of_forall_continuousAt fun x hx => (hcont x hx).2
  refine ⟨cfc (projectionRoundingStep b) T, cfc_predicate _ _, ?_, ?_⟩
  · show cfc (projectionRoundingStep b) T * cfc (projectionRoundingStep b) T = _
    rw [← cfc_mul _ _ T hp hp]
    apply cfc_congr
    intro x hx
    simp only [projectionRoundingStep]
    split_ifs <;> norm_num
  · have heq : cfc (projectionRoundingStep b) T - T =
        cfc (projectionRoundingFactor b) T * (T-T*T) := by
      calc
        _ = cfc (fun x => projectionRoundingStep b x - x) T := by
          rw [cfc_sub _ _ T hp, cfc_id' ℝ T]
        _ = cfc (fun x => projectionRoundingFactor b x * (x-x*x)) T :=
          cfc_congr fun x _ => projectionRounding_factorization hb0 hb1 x
        _ = _ := by
          rw [cfc_mul (projectionRoundingFactor b) (fun x : ℝ => x-x*x) T hr,
            cfc_sub (fun x : ℝ => x) (fun x => x*x) T,
            cfc_mul (fun x : ℝ => x) (fun x => x) T, cfc_id' ℝ T]
    rw [heq]
    exact memSchattenClass_one_comp_left hD _

private theorem nuclear_commutator_trace (E B : H →L[ℂ] H)
    (hE : MemSchattenClass 1 E) :
    MemSchattenClass 1 (E*B-B*E) ∧ opTrace (E*B-B*E) = 0 := by
  have hEB := memSchattenClass_one_comp_right hE B
  have hBE := memSchattenClass_one_comp_left hE B
  change MemSchattenClass 1 (E*B) at hEB
  change MemSchattenClass 1 (B*E) at hBE
  refine ⟨hEB.one_sub hBE, ?_⟩
  rw [opTrace_sub_of_memSchattenClass_one hEB hBE]
  have h := hE.one_opTrace_comp_comm B
  change opTrace (B*E) = opTrace (E*B) at h
  rw [h, sub_self]

/-- Nuclear corrections to both factors preserve a trace-class commutator and its ordinary trace.
No nuclearity of the separate original products is asserted or used. -/
theorem traceClass_commutator_perturbation_invariance
    (A B E F : H →L[ℂ] H)
    (hAB : MemSchattenClass 1 (A*B-B*A))
    (hE : MemSchattenClass 1 E) (hF : MemSchattenClass 1 F) :
    MemSchattenClass 1 ((A+E)*(B+F)-(B+F)*(A+E)) ∧
      opTrace ((A+E)*(B+F)-(B+F)*(A+E)) = opTrace (A*B-B*A) := by
  obtain ⟨hEB, htEB⟩ := nuclear_commutator_trace E B hE
  obtain ⟨hFA, htFA⟩ := nuclear_commutator_trace F A hF
  obtain ⟨hEF, htEF⟩ := nuclear_commutator_trace E F hE
  have heq : (A+E)*(B+F)-(B+F)*(A+E) =
      ((A*B-B*A)+(E*B-B*E)-(F*A-A*F))+(E*F-F*E) := by noncomm_ring
  rw [heq]
  refine ⟨((hAB.one_add hEB).one_sub hFA).one_add hEF, ?_⟩
  rw [opTrace_add_of_memSchattenClass_one ((hAB.one_add hEB).one_sub hFA) hEF,
    opTrace_sub_of_memSchattenClass_one (hAB.one_add hEB) hFA,
    opTrace_add_of_memSchattenClass_one hAB hEB, htEB, htFA, htEF]
  simp

end RHTower
