import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.AnseloneKorevaarTranslationRank

/-!
# Kolchin production in an elastic collision phase

A factorizing elastic collision multiplies the incoming packet by the two-body scattering factor.
Because multiplication by a nonzero differentially algebraic observable preserves
hypertranscendence exactly, a hypertranscendental scattering factor transfers its whole differential
complexity to the outgoing packet, and nothing else does: the outgoing packet is hypertranscendental
precisely when the scattering factor is.  On the real axis elastic unitarity leaves the pointwise
modulus untouched, so the produced complexity is invisible to the momentum probability.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **Collision phase production.**  With `Ψ_out = Ψ_in · S`, a nonzero differentially algebraic
incoming packet makes the outgoing packet hypertranscendental exactly when the two-body scattering
factor is.  This is equation `(3)` together with the jet identification `(4)`–`(5)`: the finite jet
fields of `Ψ_out` and of `S` coincide over the incoming differential field. -/
theorem hypertranscendentalOver_outgoingPacket_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {psiIn S : E} (hpsi : DifferentialAlgebraicOver F psiIn) (hpsi0 : psiIn ≠ 0) :
    HypertranscendentalOver F (psiIn * S) ↔ HypertranscendentalOver F S := by
  rw [mul_comm]
  exact hypertranscendentalOver_mul_differentialAlgebraic_iff hpsi hpsi0

/-- **Maximal relative production `(7)`.**  A hypertranscendental scattering factor and a nonzero
differentially algebraic incoming packet produce a hypertranscendental outgoing packet. -/
theorem hypertranscendentalOver_outgoingPacket
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {psiIn S : E} (hpsi : DifferentialAlgebraicOver F psiIn) (hpsi0 : psiIn ≠ 0)
    (hS : HypertranscendentalOver F S) :
    HypertranscendentalOver F (psiIn * S) :=
  (hypertranscendentalOver_outgoingPacket_iff hpsi hpsi0).mpr hS

/-- **No production without a hypertranscendental factor.**  If the outgoing packet is
hypertranscendental then so is the scattering factor: the complexity cannot come from the incoming
differentially algebraic packet. -/
theorem hypertranscendentalOver_scattering_of_outgoingPacket
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {psiIn S : E} (hpsi : DifferentialAlgebraicOver F psiIn) (hpsi0 : psiIn ≠ 0)
    (hout : HypertranscendentalOver F (psiIn * S)) :
    HypertranscendentalOver F S :=
  (hypertranscendentalOver_outgoingPacket_iff hpsi hpsi0).mp hout

/-- **Probability invisibility.**  Elastic unitarity of the scattering factor leaves the pointwise
modulus of the packet unchanged, so the produced differential complexity carries no momentum
probability signature. -/
theorem norm_outgoingPacket_eq (psiIn S : ℂ) (hS : ‖S‖ = 1) :
    ‖psiIn * S‖ = ‖psiIn‖ := by
  rw [norm_mul, hS, mul_one]

/-! ## Infinite separation rank of the outgoing kernel -/

/-- A difference kernel of finite separation rank has finite translation rank: every translate of
the profile lies in the span of the finitely many left factors. -/
theorem finiteDimensional_translationSpan_of_separationRank {S : ℝ → ℂ} {n : ℕ}
    {f g : Fin n → ℝ → ℂ} (hsep : ∀ x y : ℝ, S (x - y) = ∑ i, f i x * g i y) :
    FiniteDimensional ℂ (translationSpan S) := by
  classical
  have hspan : translationSpan S ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.mpr ?_
    rintro h ⟨a, rfl⟩
    have hval : realTranslate a S = ∑ i, g i a • f i := by
      funext x
      rw [realTranslate_apply, hsep x a]
      simp [Finset.sum_apply, mul_comm]
    show realTranslate a S ∈ (Submodule.span ℂ (Set.range f) : Set (ℝ → ℂ))
    rw [hval]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  exact FiniteDimensional.of_injective (Submodule.inclusion hspan)
    (Submodule.inclusion_injective hspan)

/-- **Infinite separation rank.**  A continuous profile that is not an exponential polynomial has a
difference kernel of infinite separation rank: it is not a finite sum of products.  For the
outgoing packet of a hypertranscendental elastic collision this is the infinite Schmidt rank of the
labelled-packet bipartition. -/
theorem not_separationRank_of_notMem_expPolySpace {S : ℝ → ℂ} (hcont : Continuous S)
    (hnot : S ∉ expPolySpace) {n : ℕ} {f g : Fin n → ℝ → ℂ}
    (hsep : ∀ x y : ℝ, S (x - y) = ∑ i, f i x * g i y) : False := by
  exact hnot ((mem_expPolySpace_iff_finiteDimensional_translationSpan hcont).2
    (finiteDimensional_translationSpan_of_separationRank hsep))

end GaloisForLFunctions.HTGeometry
