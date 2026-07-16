import Mathlib.Analysis.Convex.Cone.InnerDual

/-!
# Polarized fracture incidence

After linear fracture descent, positivity asks whether a target lies in the image of an admissible
positive cone.  In an infinite-dimensional or incomplete realization that image need not be
closed.  This produces three exact phases:

1. an effective positive lift exists;
2. the target is only in the closure of positive lifts, so every continuous dual positivity test
   passes although no lift exists;
3. the target is outside the closure and a strict Farkas dual certificate exists.

The second phase is the linear model of a critical all-scale or nonclosed-range obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped RealInnerProductSpace
open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A target has exact polarized incidence when it is the image of an actual point of the
admissible proper cone. -/
def ExactPolarizedIncidence
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) : Prop :=
  b ∈ C.toPointedCone.map (f : E →ₗ[ℝ] F)

/-- A target has weak polarized incidence when it lies in the closure of the cone image.  This is
exactly the image notion detected by continuous Farkas dual tests. -/
def WeakPolarizedIncidence
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) : Prop :=
  b ∈ C.map f

/-- A strict dual obstruction to polarized incidence: a dual-cone reporter is nonnegative on all
admissible source points but strictly negative on the target. -/
def HasStrictPolarizedCertificate
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) : Prop :=
  ∃ y : F,
    f.adjoint y ∈ ProperCone.innerDual (C : Set E) ∧
      ⟪b, y⟫_ℝ < 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every actual positive lift is weakly positive after passage to the closure-valued cone image. -/
theorem exactPolarizedIncidence_implies_weak
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) :
    ExactPolarizedIncidence C f b → WeakPolarizedIncidence C f b := by
  intro h
  rw [WeakPolarizedIncidence, ProperCone.mem_map]
  exact subset_closure h

/-- **Continuous dual characterization.**  Weak polarized incidence is equivalent to
nonnegativity against every dual-cone reporter. -/
theorem weakPolarizedIncidence_iff_forall_dual_nonneg
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) :
    WeakPolarizedIncidence C f b ↔
      ∀ y : F,
        f.adjoint y ∈ ProperCone.innerDual (C : Set E) →
          0 ≤ ⟪b, y⟫_ℝ := by
  simpa only [WeakPolarizedIncidence] using
    (ProperCone.relative_hyperplane_separation (C := C) (f := f) (b := b))

/-- Failure even of weak incidence is equivalent to existence of a strict dual certificate. -/
theorem not_weakPolarizedIncidence_iff_strictCertificate
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) :
    ¬ WeakPolarizedIncidence C f b ↔ HasStrictPolarizedCertificate C f b := by
  constructor
  · intro h
    change b ∉ C.map f at h
    simpa only [HasStrictPolarizedCertificate] using
      (ProperCone.hyperplane_separation_of_notMem C h)
  · rintro ⟨y, hy, hneg⟩ hweak
    have hnonneg :=
      (weakPolarizedIncidence_iff_forall_dual_nonneg C f b).mp hweak y hy
    exact (not_lt_of_ge hnonneg) hneg

/-- Closure-only incidence is the exact nonattainment phase: there is no positive lift, but every
continuous dual-cone reporter remains nonnegative. -/
theorem closureOnlyPolarizedIncidence_forall_dual_nonneg
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (h : WeakPolarizedIncidence C f b ∧ ¬ ExactPolarizedIncidence C f b) :
    (¬ ExactPolarizedIncidence C f b) ∧
      ∀ y : F,
        f.adjoint y ∈ ProperCone.innerDual (C : Set E) →
          0 ≤ ⟪b, y⟫_ℝ :=
  ⟨h.2, (weakPolarizedIncidence_iff_forall_dual_nonneg C f b).mp h.1⟩

/-- No strict continuous dual certificate can detect a closure-only nonattainment obstruction. -/
theorem closureOnlyPolarizedIncidence_no_strictCertificate
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (h : WeakPolarizedIncidence C f b ∧ ¬ ExactPolarizedIncidence C f b) :
    ¬ HasStrictPolarizedCertificate C f b := by
  intro hcert
  exact (not_weakPolarizedIncidence_iff_strictCertificate C f b).mpr hcert h.1

omit [CompleteSpace E] [CompleteSpace F] in
/-- A cofinal sequence of actual positive lifts converging to the target always produces weak
polarized incidence.  No compactness or closed-range assumption is hidden in this passage. -/
theorem weakPolarizedIncidence_of_tendsto_exact
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (x : ℕ → E) (hx : ∀ n, x n ∈ C)
    (hlim : Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds b)) :
    WeakPolarizedIncidence C f b := by
  rw [WeakPolarizedIncidence, ProperCone.mem_map]
  apply mem_closure_of_tendsto hlim
  filter_upwards [] with n
  exact ⟨x n, hx n, rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- If cofinal positive lifts converge but the target has no actual positive preimage, the target
lies in the closure-only nonattainment phase. -/
theorem closureOnlyPolarizedIncidence_of_tendsto_exact_of_not_exact
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (x : ℕ → E) (hx : ∀ n, x n ∈ C)
    (hlim : Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds b))
    (hnot : ¬ ExactPolarizedIncidence C f b) :
    WeakPolarizedIncidence C f b ∧ ¬ ExactPolarizedIncidence C f b :=
  ⟨weakPolarizedIncidence_of_tendsto_exact C f b x hx hlim, hnot⟩

/-- **Polarized-incidence trichotomy.**  A target either has an actual positive lift, lies only in
the closure of positive lifts, or admits a strict dual obstruction certificate. -/
theorem polarizedIncidence_trichotomy
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F) :
    ExactPolarizedIncidence C f b ∨
      (WeakPolarizedIncidence C f b ∧ ¬ ExactPolarizedIncidence C f b) ∨
        HasStrictPolarizedCertificate C f b := by
  by_cases hexact : ExactPolarizedIncidence C f b
  · exact Or.inl hexact
  by_cases hweak : WeakPolarizedIncidence C f b
  · exact Or.inr (Or.inl ⟨hweak, hexact⟩)
  · exact Or.inr (Or.inr
      ((not_weakPolarizedIncidence_iff_strictCertificate C f b).mp hweak))

omit [CompleteSpace E] [CompleteSpace F] in
/-- Closedness of the raw positive image removes the nonattainment phase: weak and exact polarized
incidence then coincide. -/
theorem weakPolarizedIncidence_iff_exact_of_isClosed_image
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (hclosed : IsClosed
      (C.toPointedCone.map (f : E →ₗ[ℝ] F) : Set F)) :
    WeakPolarizedIncidence C f b ↔ ExactPolarizedIncidence C f b := by
  constructor
  · intro h
    rw [WeakPolarizedIncidence, ProperCone.mem_map] at h
    change b ∈ closure
      (C.toPointedCone.map (f : E →ₗ[ℝ] F) : Set F) at h
    rw [hclosed.closure_eq] at h
    exact h
  · exact exactPolarizedIncidence_implies_weak C f b

/-- Under closed-range incidence, the trichotomy collapses to the classical exact Farkas
dichotomy: an actual positive lift or a strict dual certificate. -/
theorem exactPolarizedIncidence_or_strictCertificate_of_isClosed_image
    (C : ProperCone ℝ E) (f : E →L[ℝ] F) (b : F)
    (hclosed : IsClosed
      (C.toPointedCone.map (f : E →ₗ[ℝ] F) : Set F)) :
    ExactPolarizedIncidence C f b ∨ HasStrictPolarizedCertificate C f b := by
  by_cases hexact : ExactPolarizedIncidence C f b
  · exact Or.inl hexact
  · apply Or.inr
    apply (not_weakPolarizedIncidence_iff_strictCertificate C f b).mp
    intro hweak
    exact hexact
      ((weakPolarizedIncidence_iff_exact_of_isClosed_image C f b hclosed).mp hweak)

end

end GaloisForLFunctions.HTGeometry
