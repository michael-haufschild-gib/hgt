/-
# The chart orbit is the labeling-orbit obstruction at a constant rate

The card's quadratic rate is `Q(H) = D^{-1} Tr(H²)`, and the corpus's labeling-orbit obstruction
carries its rate against the power sum `∑ λᵢ²` of the spectrum.  For a *simple root packet* those
two agree -- `∑ λᵢ² = Tr(H²)` -- so the chart obstruction with the card's rate is literally the
corpus obstruction at the constant multiple `b²/D`.

That removes the need to carry the rate as a variable at this step: the whole constant-rate pullback
machinery applies to the chart obstruction unchanged.

Main results:
* `fieldQuadraticRateOrbitValue_chart` — the two obstructions agree at every chart point.
* `exists_chart_fieldQuadraticRateOrbitValue_ne_zero` — **the chart escape, in corpus form**.
-/
import GaloisForLFunctions.HTGeometry.EndpointCompleteExtensionOrbit
import GaloisForLFunctions.HTGeometry.RootPacketPowerSum

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **At a chart point the two obstructions agree.**  The branches are a simple root packet, so
their squared power sum is the trace of the square of the chart Hamiltonian. -/
theorem fieldQuadraticRateOrbitValue_chart {E : A → ℂ} {shift₀ : Bool → ℂ} {M : Matrix A A ℂ}
    (C : LocalExtensionEigenbranchChart E shift₀ M) {p : (Bool → ℂ) × Matrix Bool Bool ℂ}
    (hp : p ∈ C.U) (c : A × Bool → ℂ) (κ : ℂ) :
    fieldQuadraticRateOrbitValue c κ (fun i => C.branch i p)
      = ∏ σ : Equiv.Perm (A × Bool),
          ((∑ i, c i * C.branch (σ i) p) ^ 2
            - κ * ((localExtensionMatrix E p.1 M p.2) ^ 2).trace) := by
  classical
  have hsum : (∑ i, C.branch i p ^ 2) = ((localExtensionMatrix E p.1 M p.2) ^ 2).trace :=
    sum_pow_rootPacket_eq_trace_pow _ (fun i => C.branch i p) (C.simple p hp) (C.root p hp) 2
  rw [fieldQuadraticRateOrbitValue_branch c κ (fun i p => C.branch i p) p]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [permutedAnalyticQuadraticRate, hsum]

/-- **The chart escape in corpus form.**  A nonzero zero-sum coefficient packet has somewhere on the
chart a nonzero labeling-orbit obstruction at the constant rate. -/
theorem exists_chart_fieldQuadraticRateOrbitValue_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ p ∈ C.U, fieldQuadraticRateOrbitValue c κ (fun i => C.branch i p) ≠ 0 := by
  have hM' : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0 := fun α β hab =>
    mul_ne_zero (hM β α (Ne.symm hab)) (hM α β hab)
  obtain ⟨p, hp, hne⟩ :=
    exists_chartQuadraticOrbit_ne_zero hcard hE hgap hMherm hM' hbase C c κ hzero hcne
  exact ⟨p, hp, by rw [fieldQuadraticRateOrbitValue_chart C hp c κ]; exact hne⟩

end

end GaloisForLFunctions.HTGeometry
