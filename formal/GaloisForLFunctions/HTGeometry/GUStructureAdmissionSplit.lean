import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass
import GaloisForLFunctions.RHTower.SuzukiCharacteristicEntireLimitNoGo

/-!
# The G–U structure/admission split law

The law of ULF-MECH-4 has two clauses.  Clause (i) — that the two structural halves are equivalent
presentations under the classical Krein/de Branges correspondence — is cited classical mathematics
and is not restated here.  Clause (ii), the new content, is exactly a **non-transport** statement:
admission is not a function of the structural data, so no functor along a structural correspondence
can carry it.

This module certifies clause (ii) unconditionally: the abstract non-transport law, its U-side
witness (the current Hankel face leaves the crossing sign and the Christoffel port orientation
completely free), and its G-side witness (a structurally admissible gauge class whose route
admission is impossible).
-/

open Matrix Polynomial
open HTGeometry RHTower

namespace GaloisForLFunctions.HTGeometry

/-! ## The abstract non-transport law -/

/-- A property of data is *determined by* a structure map when it factors through it. -/
def DeterminedBy {D S : Type*} (str : D → S) (adm : D → Prop) : Prop :=
  ∃ φ : S → Prop, ∀ d, adm d ↔ φ (str d)

/-- Two data with identical structure and opposite admission witness underdetermination. -/
theorem not_determinedBy_of_witness {D S : Type*} (str : D → S) (adm : D → Prop)
    {d₁ d₂ : D} (hs : str d₁ = str d₂) (h₁ : adm d₁) (h₂ : ¬ adm d₂) :
    ¬ DeterminedBy str adm := by
  rintro ⟨φ, hφ⟩
  exact h₂ ((hφ d₂).mpr (hs ▸ (hφ d₁).mp h₁))

/-- **Non-transport.**  If admission is not determined by the structural data, then no property of
the *transported* structure computes it either — whatever structural correspondence is used. -/
theorem not_transports_of_not_determinedBy {D S S' : Type*} (str : D → S) (e : S → S')
    (adm : D → Prop) (h : ¬ DeterminedBy str adm) :
    ¬ ∃ ψ : S' → Prop, ∀ d, adm d ↔ ψ (e (str d)) := by
  rintro ⟨ψ, hψ⟩
  exact h ⟨fun s => ψ (e s), hψ⟩

/-- Structural admissibility does not imply route admission when one structurally admissible datum
fails it. -/
theorem not_structure_implies_admission {D : Type*} (str adm : D → Prop) {d : D}
    (h₁ : str d) (h₂ : ¬ adm d) : ¬ ∀ x, str x → adm x := fun h => h₂ (h d h₁)

/-! ## The U-side witness: the current Hankel face determines no crossing sign -/

/-- **U-side non-transport.**  Keeping the whole current Hankel face fixed, the first extension
class — the crossing sign of the route — can be made positive or negative.  Hence no property of
the face determines it. -/
theorem crossingSign_not_determinedBy_hankelFace
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    ¬ DeterminedBy (fun t : ℕ → ℝ => momentHankelMatrix t (n + 1))
        (fun t : ℕ → ℝ => 0 < finiteHankelBoundaryMonicRemainder t c) := by
  obtain ⟨t₁, hface₁, hrem₁⟩ :=
    exists_momentSequence_same_face_monicRemainder_eq s c hlast 1
  obtain ⟨t₂, hface₂, hrem₂⟩ :=
    exists_momentSequence_same_face_monicRemainder_eq s c hlast (-1)
  refine not_determinedBy_of_witness _ _ (d₁ := t₁) (d₂ := t₂) (by rw [hface₁, hface₂]) ?_ ?_
  · rw [hrem₁]; norm_num
  · rw [hrem₂]; norm_num

/-- **U-side port-orientation non-transport.**  The forward-minus-backward Christoffel port
imbalance is likewise free on a fixed face. -/
theorem portOrientation_not_determinedBy_hankelFace
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0) (hlast : c (Fin.last n) ≠ 0) :
    ¬ DeterminedBy (fun t : ℕ → ℝ => momentHankelMatrix t (n + 1))
        (fun t : ℕ → ℝ =>
          0 < momentFunctional t
                (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) -
              momentFunctional t
                (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2)) := by
  obtain ⟨t₁, hface₁, hd₁⟩ :=
    exists_momentSequence_same_face_christoffelPortDifference_eq s c hc hlast 1
  obtain ⟨t₂, hface₂, hd₂⟩ :=
    exists_momentSequence_same_face_christoffelPortDifference_eq s c hc hlast (-1)
  refine not_determinedBy_of_witness _ _ (d₁ := t₁) (d₂ := t₂) (by rw [hface₁, hface₂]) ?_ ?_
  · rw [hd₁]; norm_num
  · rw [hd₂]; norm_num

/-! ## The G-side witness: structural admissibility does not give route admission -/

/-- **G-side non-implication.**  The structural class of finite holomorphic exponential gauges
times entire real-zero characteristic functions is a genuine structural condition, but no member of
it achieves the route's admission (locally uniform convergence to the displayed target).  Route
admission is therefore not implied by the structural data. -/
theorem gaugeStructure_does_not_give_routeAdmission :
    ¬ RHTower.SuzukiHolomorphicGaugeCharacteristicLimitWall :=
  RHTower.not_suzukiHolomorphicGaugeCharacteristicLimitWall

/-! ## The split-law capstone -/

/-- **ULF-MECH-4 clause (ii).**  On the U side admission is not a function of the structural face,
so no structural correspondence transports it; on the G side structural admissibility does not even
imply route admission. -/
theorem guStructureAdmissionSplit_capstone
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    {S' : Type} (e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ → S') :
    (¬ ∃ ψ : S' → Prop, ∀ t : ℕ → ℝ,
        (0 < finiteHankelBoundaryMonicRemainder t c)
          ↔ ψ (e (momentHankelMatrix t (n + 1))))
      ∧ ¬ RHTower.SuzukiHolomorphicGaugeCharacteristicLimitWall :=
  ⟨not_transports_of_not_determinedBy _ e _
      (crossingSign_not_determinedBy_hankelFace s c hlast),
    gaugeStructure_does_not_give_routeAdmission⟩

end GaloisForLFunctions.HTGeometry
