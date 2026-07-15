import GaloisForLFunctions.HTGeometry.DifferentialClockReferenceFrameCovariance

/-!
# Embedding covariance of differential clock observability

The covariance of the hypertranscendental clock does not require an invertible coordinate change.
A derivation-preserving algebra homomorphism between fields is injective, and that is enough to
transport every jet, finite observable field, finite clock test, hypertranscendence, and the exact
clock-erosion law.

This is the differential-field analogue of covariance along embeddings in locally covariant QFT
and of a one-way change of quantum reference system.  It concerns functorial observability under a
static inclusion of presentations, not temporal evolution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

section DifferentialEmbedding

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Differential E] [Differential L] [Algebra F E] [Algebra F L]

/-- Every iterated clock reading is covariant under a derivation-preserving field embedding. -/
theorem differentialJet_algHom
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (z : E) : ∀ n : ℕ,
    e (differentialJet n z) = differentialJet n (e z)
  | 0 => by simp
  | n + 1 => by
      rw [differentialJet_succ, hderiv,
        differentialJet_algHom e hderiv z n, differentialJet_succ]

/-- A differential field embedding carries the entire finite observable field onto the field at
the same resolution generated inside the target.  Surjectivity onto the ambient target field is
not required. -/
theorem jetObservableField_map_algHom
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (x : E) (N : ℕ) :
    (jetObservableField F x N).map e =
      jetObservableField F (e x) N := by
  rw [jetObservableField, jetObservableField, IntermediateField.adjoin_map]
  simp only [Set.image_image]
  have hfun : (fun n : ℕ => e (differentialJet n x)) =
      (fun n : ℕ => differentialJet n (e x)) := by
    funext n
    exact differentialJet_algHom e hderiv x n
  rw [hfun]

/-- Membership in one clock-tested observable field is reflected as well as preserved by a
differential field embedding. -/
theorem differentialClockTest_algHom_iff
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (B : IntermediateField F E) (z : E) (q : ℕ) :
    differentialJet q z ∈ B ↔
      differentialJet q (e z) ∈ B.map e := by
  rw [← differentialJet_algHom e hderiv z q]
  exact (IntermediateField.map_mem_map
    (S := B) e (x := differentialJet q z)).symm

/-- A finite family of clock tests is invariant under a differential field embedding. -/
theorem finiteDifferentialClockTests_algHom_iff
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (B : IntermediateField F E) (z : E) (r : ℕ) :
    (∀ q : ℕ, q ≤ r → differentialJet q z ∈ B) ↔
      ∀ q : ℕ, q ≤ r → differentialJet q (e z) ∈ B.map e := by
  constructor
  · intro h q hq
    exact (differentialClockTest_algHom_iff e hderiv B z q).mp (h q hq)
  · intro h q hq
    exact (differentialClockTest_algHom_iff e hderiv B z q).mpr (h q hq)

/-- Clock observability at a fixed jet resolution is invariant under a differential field
embedding. -/
theorem jetObservable_clockTests_algHom_iff
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    (x z : E) (N r : ℕ) :
    (∀ q : ℕ, q ≤ r →
      differentialJet q z ∈ jetObservableField F x N) ↔
      ∀ q : ℕ, q ≤ r →
        differentialJet q (e z) ∈ jetObservableField F (e x) N := by
  rw [← jetObservableField_map_algHom e hderiv x N]
  exact finiteDifferentialClockTests_algHom_iff
    e hderiv (jetObservableField F x N) z r

/-- Hypertranscendence is preserved and reflected by every derivation-preserving field embedding.
The inverse algebra equivalence previously used by the corpus is unnecessary. -/
theorem hypertranscendentalOver_algHom_iff
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′) (x : E) :
    HypertranscendentalOver F (e x) ↔ HypertranscendentalOver F x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    hypertranscendentalOver_iff_differentialIndependent_singleton]
  unfold DifferentialIndependent
  have hfun :
      e ∘ (fun p : Unit × ℕ => differentialJet p.2 x) =
        (fun p : Unit × ℕ => differentialJet p.2 (e x)) := by
    funext p
    exact differentialJet_algHom e hderiv x p.2
  constructor
  · intro he
    rw [← hfun] at he
    exact he.of_comp e
  · intro hx
    have hmap := hx.map' e.injective
    rw [hfun] at hmap
    exact hmap

end DifferentialEmbedding

section HypertranscendentalEmbedding

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Differential F] [Differential E] [Differential L]
  [Algebra F E] [Algebra F L]
  [DifferentialAlgebra F E]

/-- **Embedding covariance of the HT clock boundary.**  Surviving `r` clock tests at resolution
`N+r` in the source is equivalent to the embedded observable lying in the order-`N` field generated
inside any derivation-compatible target field.  No inverse map on the target is assumed. -/
theorem hypertranscendental_clock_erosion_algHom_iff
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    [CharZero E] {x : E} (hx : HypertranscendentalOver F x)
    (N r : ℕ) (z : E) :
    (∀ q : ℕ, q ≤ r →
      differentialJet q z ∈ jetObservableField F x (N + r)) ↔
      e z ∈ jetObservableField F (e x) N := by
  rw [hypertranscendental_clock_erosion_iff hx N r]
  rw [← jetObservableField_map_algHom e hderiv x N]
  exact (IntermediateField.map_mem_map
    (S := jetObservableField F x N) e (x := z)).symm

end HypertranscendentalEmbedding

end


end GaloisForLFunctions.HTGeometry
