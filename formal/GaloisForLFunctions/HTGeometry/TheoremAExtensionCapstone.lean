/-
# Theorem A on the extension architecture, from Lemma A1's output

Everything the extension step needs is constructed from three inputs only: a simple old spectrum,
distinct ordered gaps, and an endpoint-complete eigenvector family.  The covering Hermitian probe
gives the transition channel, an admissible split shift gives the base point, the eigenbranch chart
follows, the chart Hamiltonian is a polynomial family in the six chart coordinates, and the
labeling-orbit obstruction is a nonzero polynomial in them.

Consequently, inside every nonempty open set of *real* chart parameters there is a Hamiltonian at
which no relabeling of the quadratic-rate relation holds -- which is the fixed-shell nonflatness
statement, on the one-qubit extension architecture.

Main result:
* `exists_mem_real_endpointComplete_quadraticRate_ne_zero`.
-/
import GaloisForLFunctions.HTGeometry.LocalExtensionPolynomialFamily
import GaloisForLFunctions.HTGeometry.HermitianCoveringProbe

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Theorem A on the extension architecture.**  From a simple old spectrum with distinct ordered
gaps and an endpoint-complete eigenvector family: a Hermitian transition channel seeing every
ordered pair, and, inside every nonempty open set of real chart parameters, a point at which no
relabeling of the quadratic-rate relation holds for any simple root packet of the chart
Hamiltonian. -/
theorem exists_mem_real_endpointComplete_quadraticRate_ne_zero
    {A cc dd : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype cc] [DecidableEq cc] [Fintype dd]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    (ψ : A → cc × dd → ℂ)
    (hpsi : ∀ i j : A, i ≠ j → reducedTransition (ψ i) (ψ j) ≠ 0)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0)
    {V : Set (Fin (Fintype.card (Bool ⊕ Bool × Bool)) → ℝ)} (hVopen : IsOpen V)
    (hVne : V.Nonempty) :
    ∃ M : Matrix A A ℂ, M.IsHermitian ∧ (∀ α β : A, α ≠ β → M β α ≠ 0) ∧
      ∃ q ∈ V, ∀ energy : A × Bool → ℂ, Function.Injective energy →
        (∀ i, matrixCharpolyRelation
          ((genericLocalExtensionMatrix (ρ := Bool) (fun a => (E a : ℂ)) M).map
            (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))), energy i) = 0) →
        ∀ σ : Equiv.Perm (A × Bool),
          (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) ≠ 0 := by
  obtain ⟨X, hXherm, hX⟩ := exists_hermitian_covering_endpoint_probe ψ hpsi
  have hMherm : (endpointChannel ψ X).IsHermitian := isHermitian_endpointChannel ψ hXherm
  have hM : ∀ α β : A, α ≠ β → endpointChannel ψ X β α ≠ 0 := fun α β hab =>
    endpointChannel_ne_zero ψ hX β α (Ne.symm hab)
  obtain ⟨z₀, hz₀⟩ := exists_admissible_split_shift (fun a => (E a : ℂ))
  have hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)) := by
    rw [layeredEnergy_boolShift]
    exact injective_layerSplitEnergy hE hz₀
  obtain ⟨C⟩ := exists_localExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀)
    (endpointChannel ψ X) hbase
  exact ⟨endpointChannel ψ X, hMherm, hM,
    exists_mem_real_localExtension_quadraticRate_ne_zero hcard hE hgap hMherm hM hbase C c κ
      hzero hcne hVopen hVne⟩

end

end GaloisForLFunctions.HTGeometry
