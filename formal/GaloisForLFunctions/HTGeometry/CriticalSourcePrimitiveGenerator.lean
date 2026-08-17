import GaloisForLFunctions.HTGeometry.CriticalGeometricFieldPrimitivity

/-!
# Any escaping element of the source generates it, given full monodromy

Full geometric monodromy leaves no intermediate field strictly between the observation field and the
source field.  Consequently a single element of the source that is not already observed generates
the whole source: the field it adjoins is an intermediate field, so it is `⊥` or everything, and it
is not `⊥` because it contains the element.

This is the primitivity step of the postcritical assembly, isolated from the particular element it
will be applied to.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **An unobserved element of the source generates the source**, given full monodromy. -/
theorem criticalSourceNormalClosureFieldRange_eq_adjoin_of_full_monodromy
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfull : criticalGeometricMonodromy K m n = ⊤)
    (α : criticalNormalClosure K m n)
    (hmem : α ∈ (criticalSourceNormalClosureEmbedding K m n).fieldRange)
    (hne : α ∉ (⊥ : IntermediateField (criticalObservationField K m n)
      (criticalNormalClosure K m n))) :
    IntermediateField.adjoin (criticalObservationField K m n) {α}
      = (criticalSourceNormalClosureEmbedding K m n).fieldRange := by
  have hle : IntermediateField.adjoin (criticalObservationField K m n) {α}
      ≤ (criticalSourceNormalClosureEmbedding K m n).fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hmem
  rcases eq_bot_or_eq_criticalSourceNormalClosureFieldRange_of_full_monodromy K hm hn hfull
    (IntermediateField.adjoin (criticalObservationField K m n) {α}) hle with h | h
  · exact absurd (h ▸ IntermediateField.mem_adjoin_simple_self _ α) hne
  · exact h

end GaloisForLFunctions.HTGeometry

end
