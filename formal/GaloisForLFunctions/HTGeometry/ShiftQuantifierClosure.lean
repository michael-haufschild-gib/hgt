import GaloisForLFunctions.HTGeometry.PacketShiftTranslationCovariance

/-!
# Closing the shift quantifier

Assembling the reduction.  A single datum that is nondegenerate at one shift, together with
covariance under simultaneous translation of datum and shift, yields at every shift of a compact
patch some translate that is nondegenerate there.  The translates used depend on the parameter,
which the witness condition permits.

Since the shift space is exhausted by compact patches, the parameters witnessing every shift are
dense and residual.  Nothing about thinness, analyticity or transversality is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The shift quantifier, closed.**  With translation covariance and a single nondegenerate shift
available on a dense set of parameters, the parameters witnessing *every* shift are dense and
residual. -/
theorem dense_and_residual_forall_shift_of_translate
    {X S Z : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace S] [AddCommGroup S] [IsTopologicalAddGroup S]
    (f : Z → X × S → ℂ) (hf : ∀ z, Continuous (f z))
    (tr : Z → S → Z) (z₀ : Z)
    (hcov : ∀ (x : X) (t s : S), f (tr z₀ t) (x, s) = f z₀ (x, s - t))
    (K : ℕ → Set S) (hcover : ∀ s : S, ∃ m, s ∈ K m) (hK : ∀ m, IsCompact (K m))
    (D : Set X) (hD : Dense D)
    (hne : ∀ x ∈ D, ∃ s₀ : S, f z₀ (x, s₀) ≠ 0) :
    Dense {x : X | ∀ s, ∃ z, f z (x, s) ≠ 0} ∧
      {x : X | ∀ s, ∃ z, f z (x, s) ≠ 0} ∈ residual X := by
  classical
  -- On the patch, every parameter of `D` witnesses every shift by a translate of `z₀`.
  have hpatch : ∀ (m : ℕ), ∀ x ∈ D, ∀ s ∈ K m, ∃ z, f z (x, s) ≠ 0 := by
    intro m x hx
    have hclosed : IsClosed {s : S | f z₀ (x, s) = 0} :=
      isClosed_singleton.preimage ((hf z₀).comp (continuous_const.prodMk continuous_id))
    obtain ⟨T, hT⟩ :=
      exists_finset_no_common_zero_of_translation_covariant f x z₀ tr (hcov x)
        hclosed (hne x hx) (hK m)
    intro s hs
    obtain ⟨t, _, htne⟩ := hT s hs
    exact ⟨tr z₀ t, htne⟩
  refine dense_and_residual_of_patchwise_exists_ne_zero f K hcover ?_ hf hK
  intro m
  exact hD.mono fun x hx s hs => hpatch m x hx s hs

end

end GaloisForLFunctions.HTGeometry
