/-
# Theorem A from endpoint completeness alone

Endpoint completeness of an eigenvector family -- every ordered pair has nonzero reduced transition
-- already produces the transition channel the extension step needs: one Hermitian probe sees all
the pairs at once, and its channel in the eigenbasis is Hermitian with every off-diagonal entry
nonzero.  Feeding that into the extension step removes the channel from the hypotheses, leaving
only the two spectral conditions of the card: simple spectrum and distinct ordered gaps.

Main result:
* `exists_endpointComplete_extensionChart_quadraticOrbit_ne_zero` — **Theorem A at one extension
  step, from Lemma A1's output**.
-/
import GaloisForLFunctions.HTGeometry.ExtensionStepQuadraticOrbit
import GaloisForLFunctions.HTGeometry.HermitianCoveringProbe

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Theorem A at one extension step, from endpoint completeness.**  An endpoint-complete
eigenvector family over a simple old spectrum with distinct ordered gaps produces a Hermitian
transition channel seeing every ordered pair, and hence a one-qubit extension chart on which no
nonzero zero-sum coefficient packet satisfies the quadratic-rate relation under any labeling. -/
theorem exists_endpointComplete_extensionChart_quadraticOrbit_ne_zero
    {A cc dd : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype cc] [DecidableEq cc] [Fintype dd]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    (ψ : A → cc × dd → ℂ)
    (hne : ∀ i j : A, i ≠ j → reducedTransition (ψ i) (ψ j) ≠ 0)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ M : Matrix A A ℂ, M.IsHermitian ∧ (∀ α β : A, α ≠ β → M β α ≠ 0) ∧
      ∃ (z₀ : ℂ) (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M),
        ∃ p ∈ C.U, (∏ σ : Equiv.Perm (A × Bool),
          ((∑ i, c i * C.branch (σ i) p) ^ 2
            - κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace)) ≠ 0 := by
  obtain ⟨X, hXherm, hX⟩ := exists_hermitian_covering_endpoint_probe ψ hne
  refine ⟨endpointChannel ψ X, isHermitian_endpointChannel ψ hXherm, ?_, ?_⟩
  · intro α β hαβ
    exact endpointChannel_ne_zero ψ hX β α (Ne.symm hαβ)
  · exact exists_extensionChart_quadraticOrbit_ne_zero hcard hE hgap
      (isHermitian_endpointChannel ψ hXherm)
      (fun α β hαβ => endpointChannel_ne_zero ψ hX β α (Ne.symm hαβ)) c κ hzero hcne

end

end GaloisForLFunctions.HTGeometry
