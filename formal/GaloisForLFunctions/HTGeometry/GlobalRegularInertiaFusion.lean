import GaloisForLFunctions.HTGeometry.GlobalRegularInertiaCalkin
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Split-formation fusion of the global inertia mark

A formed observer law and the Calkin class of the global regular inertia unitary are the two
components of one packet.  Projection reconstructs the observer, essential separation reconstructs
the charge, and the two-component signature — relative entropy of the observer laws and essential
distance of the charges — is reproduced exactly on formed packets and preserved by the canonical
recovery lift of a measurable observer action.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.LpDiagonal

noncomputable section

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-! ## The two-component packet -/

/-- The formed observer law together with the global inertia mark of the charge. -/
def globalInertiaPacket (μ : Measure X) (κ : Kernel X H) (q : ℤ) :
    Measure (X × H) × (LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex) :=
  (splitFormation μ κ, globalInertiaCLM q)

/-- Distances to the compact operators realized by the charge difference: the set whose infimum is
the Calkin distance of the two inertia marks. -/
def essDistSet (q q' : ℤ) : Set ℝ :=
  {x : ℝ | ∃ K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex,
    IsCompactOperator K ∧ x = ‖globalInertiaCLM q - globalInertiaCLM q' - K‖}

/-- **The exact Calkin metric** (GRC.5) in closed form: two distinct charges are at essential
distance two, and equal charges at distance zero. -/
theorem isGLB_essDistSet (q q' : ℤ) :
    IsGLB (essDistSet q q') (if q = q' then 0 else 2) := by
  by_cases h : q = q'
  · subst h
    simpa [essDistSet] using isGLB_essDist_globalInertiaCLM_self q
  · simpa [essDistSet, h] using isGLB_essDist_globalInertiaCLM h

/-! ## Joint reconstruction -/

/-- **Theorem 4.1, reconstruction.**  The packet determines both the observer law and the integer
charge: projection recovers the law, essential separation recovers the charge. -/
theorem globalInertiaPacket_reconstructs
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] (q q' : ℤ)
    (hform : (globalInertiaPacket μ κ q).1 = (globalInertiaPacket ν κ q').1)
    (hmark : IsCompactOperator ((globalInertiaPacket μ κ q).2 - (globalInertiaPacket ν κ q').2)) :
    μ = ν ∧ q = q' := by
  refine ⟨?_, globalInertiaCLM_eq_of_isCompactOperator_sub hmark⟩
  have hf := congrArg Measure.fst hform
  rw [globalInertiaPacket, globalInertiaPacket] at hf
  rwa [splitFormation_recovers_observer, splitFormation_recovers_observer] at hf

/-! ## The two-component signature -/

/-- The two-component signature of a pair of marked observer laws (GRC.10). -/
def globalInertiaSignature (μ ν : Measure X) (q q' : ℤ) : ℝ≥0∞ × ℝ :=
  (klDiv μ ν, if q = q' then 0 else 2)

/-- **Theorem 4.1, exact reproduction** (GRC.11).  Split formation reproduces both entries of the
signature: relative entropy is preserved exactly, and the essential distance of the marks is the
second entry. -/
theorem globalInertiaSignature_formed
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] (q q' : ℤ) :
    klDiv (globalInertiaPacket μ κ q).1 (globalInertiaPacket ν κ q').1
        = (globalInertiaSignature μ ν q q').1 ∧
      IsGLB (essDistSet q q') (globalInertiaSignature μ ν q q').2 :=
  ⟨klDiv_splitFormation μ ν κ, isGLB_essDistSet q q'⟩

/-- **Theorem 4.1, conservation.**  The canonical common-recovery lift of a measurable observer
embedding preserves both entries of the signature: the first by information isometry, the second
because the integer charge is transported rather than altered. -/
theorem globalInertiaSignature_lift_invariant
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] (A : X → X) (hA : MeasurableEmbedding A) (q q' : ℤ) :
    klDiv (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation μ κ)
          (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation ν κ)
        = klDiv (splitFormation μ κ) (splitFormation ν κ) ∧
      IsGLB (essDistSet q q') (globalInertiaSignature μ ν q q').2 :=
  ⟨formationLiftKernel_klDiv_isometry μ ν κ A hA, isGLB_essDistSet q q'⟩

/-! ## Reflection is neutral, not selecting -/

/-- **Functional-equation neutrality is not selection.**  A reflection that transports local
divisor multiplicity leaves the charge, hence the Calkin mark, unchanged; a nonzero charge
therefore stays maximally noncompact. -/
theorem not_isCompactOperator_globalInertiaDefect {q : ℤ} (hq : q ≠ 0) :
    ¬ IsCompactOperator (globalInertiaDefect q) :=
  fun h => hq ((isCompactOperator_globalInertiaDefect_iff q).1 h)

/-- No compact repair can identify two distinct charges (GRC.8), even after arbitrary
information-neutral formation. -/
theorem two_le_essDist_of_ne {q q' : ℤ} (h : q ≠ q') {x : ℝ} (hx : x ∈ essDistSet q q') :
    2 ≤ x := by
  obtain ⟨K, hK, rfl⟩ := hx
  exact two_le_norm_globalInertiaCLM_sub_sub h hK

end

end GaloisForLFunctions.HTGeometry
