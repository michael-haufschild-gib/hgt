import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Reference-frame covariance of differential clock observability

A derivation-preserving algebra equivalence is a change of coordinates for an algebraic clock.
It transports every jet, every finite jet-observable field, and every finite family of clock tests.
Consequently hypertranscendence and the exact clock-erosion law are invariant under the chosen
differential-algebraic presentation of the source.

This is the differential-field counterpart of covariance under a quantum reference-frame change:
the clock and the observables must move together.  See Höhn--Vanrietvelde, *How to switch between
relational quantum clocks*, arXiv:1810.04153, and Thiemann, *(Quantum) reference frames, relational
observables, gauge reduction and physical interpretation*, arXiv:2603.04072.  The transfer to
differential jet fields is an exact algebraic inference from their covariance principle.  It does
not identify different physical Hamiltonians and introduces no temporal evolution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

section DifferentialFrame

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Differential E] [Differential L] [Algebra F E] [Algebra F L]

/-- Every iterated clock reading is covariant under a derivation-preserving algebra equivalence. -/
theorem differentialJet_algEquiv
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (z : E) : ∀ n : ℕ,
    e (differentialJet n z) = differentialJet n (e z)
  | 0 => by simp
  | n + 1 => by
      rw [differentialJet_succ, hderiv,
        differentialJet_algEquiv e hderiv z n, differentialJet_succ]

/-- A differential reference-frame change carries the full finite observable field to the field
at the same resolution in the new frame. -/
theorem jetObservableField_map_algEquiv
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (x : E) (N : ℕ) :
    (jetObservableField F x N).map e.toAlgHom =
      jetObservableField F (e x) N := by
  rw [jetObservableField, jetObservableField, IntermediateField.adjoin_map]
  simp only [Set.image_image]
  have hfun : (fun n : ℕ => (e.toAlgHom : E → L) (differentialJet n x)) =
      (fun n : ℕ => differentialJet n (e x)) := by
    funext n
    exact differentialJet_algEquiv e hderiv x n
  rw [hfun]

/-- Membership in one clock-tested observable field is invariant under the frame change. -/
theorem differentialClockTest_algEquiv_iff
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (B : IntermediateField F E) (z : E) (q : ℕ) :
    differentialJet q z ∈ B ↔
      differentialJet q (e z) ∈ B.map e.toAlgHom := by
  rw [← differentialJet_algEquiv e hderiv z q]
  exact (IntermediateField.map_mem_map
    (S := B) e.toAlgHom (x := differentialJet q z)).symm

/-- The complete finite clock-observability predicate is invariant under a differential frame
change. -/
theorem finiteDifferentialClockTests_algEquiv_iff
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (B : IntermediateField F E) (z : E) (r : ℕ) :
    (∀ q : ℕ, q ≤ r → differentialJet q z ∈ B) ↔
      ∀ q : ℕ, q ≤ r → differentialJet q (e z) ∈ B.map e.toAlgHom := by
  constructor
  · intro h q hq
    exact (differentialClockTest_algEquiv_iff e hderiv B z q).mp (h q hq)
  · intro h q hq
    exact (differentialClockTest_algEquiv_iff e hderiv B z q).mpr (h q hq)

/-- Finite clock tests at a fixed jet resolution are presentation-independent. -/
theorem jetObservable_clockTests_algEquiv_iff
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (x z : E) (N r : ℕ) :
    (∀ q : ℕ, q ≤ r →
      differentialJet q z ∈ jetObservableField F x N) ↔
      ∀ q : ℕ, q ≤ r →
        differentialJet q (e z) ∈ jetObservableField F (e x) N := by
  rw [← jetObservableField_map_algEquiv e hderiv x N]
  exact finiteDifferentialClockTests_algEquiv_iff
    e hderiv (jetObservableField F x N) z r

/-- Hypertranscendence is invariant under a derivation-preserving algebra equivalence. -/
theorem hypertranscendentalOver_algEquiv_iff
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′) (x : E) :
    HypertranscendentalOver F (e x) ↔ HypertranscendentalOver F x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    hypertranscendentalOver_iff_differentialIndependent_singleton]
  unfold DifferentialIndependent
  constructor
  · intro he
    have hderivSymm : ∀ z : L, e.symm z′ = (e.symm z)′ := by
      intro z
      apply e.injective
      simp only [e.apply_symm_apply, hderiv]
    have hmap := he.map' (f := e.symm.toAlgHom) e.symm.injective
    have hfun :
        (e.symm.toAlgHom : L → E) ∘ (fun p : Unit × ℕ =>
          differentialJet p.2 (e x)) =
        (fun p : Unit × ℕ => differentialJet p.2 x) := by
      funext p
      simpa using differentialJet_algEquiv e.symm hderivSymm (e x) p.2
    rw [hfun] at hmap
    exact hmap
  · intro hx
    have hmap := hx.map' (f := e.toAlgHom) e.injective
    have hfun :
        (e.toAlgHom : E → L) ∘ (fun p : Unit × ℕ => differentialJet p.2 x) =
        (fun p : Unit × ℕ => differentialJet p.2 (e x)) := by
      funext p
      exact differentialJet_algEquiv e hderiv x p.2
    rw [hfun] at hmap
    exact hmap

end DifferentialFrame

section HypertranscendentalFrame

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Differential F] [Differential E] [Differential L]
  [Algebra F E] [Algebra F L]
  [DifferentialAlgebra F E] [DifferentialAlgebra F L]

/-- **Reference-frame covariance of the HT clock boundary.**  Surviving `r` clock tests at
resolution `N+r` in one presentation is equivalent to the transformed observable belonging to
the order-`N` field in every derivation-preserving presentation. -/
theorem hypertranscendental_clock_erosion_algEquiv_iff
    (e : E ≃ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    [CharZero E] {x : E} (hx : HypertranscendentalOver F x)
    (N r : ℕ) (z : E) :
    (∀ q : ℕ, q ≤ r →
      differentialJet q z ∈ jetObservableField F x (N + r)) ↔
      e z ∈ jetObservableField F (e x) N := by
  rw [hypertranscendental_clock_erosion_iff hx N r]
  rw [← jetObservableField_map_algEquiv e hderiv x N]
  exact (IntermediateField.map_mem_map
    (S := jetObservableField F x N) e.toAlgHom (x := z)).symm

end HypertranscendentalFrame

end

end GaloisForLFunctions.HTGeometry
