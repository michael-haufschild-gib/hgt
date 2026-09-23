/-
# Theorem A at one extension step, with no chart hypothesis

An admissible split shift always exists: the split spectrum `E ± z/2` is simple as soon as `z`
avoids the finitely many old level differences, and a finite set cannot exhaust the plane.  Feeding
that into the existence of the common eigenbranch chart removes the chart from the hypotheses
entirely, so the labeling-orbit statement depends only on the old system: a simple old spectrum
with distinct ordered gaps and a Hermitian endpoint channel that sees every ordered pair.

Main results:
* `injective_layerSplitEnergy` — the split spectrum is simple off the level differences.
* `exists_admissible_split_shift` — such a shift exists.
* `exists_extensionChart_quadraticOrbit_ne_zero` — **Theorem A at one extension step**.
-/
import GaloisForLFunctions.HTGeometry.ChartQuadraticRateOrbitEscape

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
/-- **The split spectrum is simple off the old level differences.** -/
theorem injective_layerSplitEnergy {E : A → ℂ} (hE : Function.Injective E) {z : ℂ}
    (hz : ∀ α β : A, z ≠ E β - E α) : Function.Injective (layerSplitEnergy E z) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : E a + (if b then -(z / 2) else z / 2) = E a' + (if b' then -(z / 2) else z / 2) := h
  cases b <;> cases b' <;> simp only [if_true, if_false, Bool.false_eq_true] at h'
  · have : E a = E a' := by linear_combination h'
    rw [hE this]
  · exact absurd (by linear_combination h' : z = E a' - E a) (hz a a')
  · exact absurd (by linear_combination -h' : z = E a - E a') (hz a' a)
  · have : E a = E a' := by linear_combination h'
    rw [hE this]

omit [DecidableEq A] in
/-- An admissible split shift exists: the old level differences are a finite set. -/
theorem exists_admissible_split_shift (E : A → ℂ) : ∃ z : ℂ, ∀ α β : A, z ≠ E β - E α := by
  have hfin : (Set.range fun p : A × A => E p.2 - E p.1).Finite := Set.finite_range _
  obtain ⟨z, hz⟩ := hfin.infinite_compl.nonempty
  exact ⟨z, fun α β hcon => hz ⟨(α, β), hcon.symm⟩⟩

/-- **Theorem A at one extension step.**  For an old system with simple spectrum, distinct ordered
gaps and a Hermitian endpoint channel seeing every ordered pair, no nonzero zero-sum coefficient
packet satisfies the quadratic-rate relation with any labeling throughout the one-qubit extension
chart: the labeling orbit is somewhere nonzero.  No chart is assumed -- an admissible split shift
is produced, and the chart with it. -/
theorem exists_extensionChart_quadraticOrbit_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ (z₀ : ℂ) (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M),
      ∃ p ∈ C.U, (∏ σ : Equiv.Perm (A × Bool),
        ((∑ i, c i * C.branch (σ i) p) ^ (2 : ℕ)
          - κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ (2 : ℕ)).trace)) ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_admissible_split_shift (fun a => (E a : ℂ))
  have hsplit : Function.Injective (layerSplitEnergy (fun a => (E a : ℂ)) z₀) :=
    injective_layerSplitEnergy hE hz₀
  have hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)) := by
    rwa [layeredEnergy_boolShift]
  obtain ⟨C⟩ := exists_localExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M hbase
  have hM' : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0 := fun α β hab =>
    mul_ne_zero (hM β α (Ne.symm hab)) (hM α β hab)
  obtain ⟨p, hp, hne⟩ :=
    exists_chartQuadraticOrbit_ne_zero hcard hE hgap hMherm hM' hbase C c κ hzero hcne
  exact ⟨z₀, C, p, hp, hne⟩

end

end GaloisForLFunctions.HTGeometry
