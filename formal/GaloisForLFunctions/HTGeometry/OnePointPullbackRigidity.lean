import GaloisForLFunctions.HTGeometry.NevanlinnaKernelRigidity

/-!
# Pulling rigidity back along the projective embedding

The kernel rigidity statement is proved against a measure on the real line, while the control maps
integrate against a measure on the one-point compactification.  When the latter is the pushforward
of the former along the embedding, an almost-everywhere statement upstairs pulls back to one
downstairs, and rigidity transfers.

Nothing is lost at the point at infinity, since the pushforward gives it no mass.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The projective embedding of the real line is measurable for the Borel structure. -/
theorem measurable_onePoint_some : Measurable (OnePoint.some : ℝ → OnePoint ℝ) := by
  haveI : BorelSpace (OnePoint ℝ) := ⟨rfl⟩
  exact (OnePoint.continuous_coe (X := ℝ)).measurable

/-- An almost-everywhere statement for a pushforward along the projective embedding pulls back. -/
theorem ae_onePoint_pullback {ν : Measure ℝ} {p : OnePoint ℝ → Prop}
    (h : ∀ᵐ t ∂(ν.map (OnePoint.some)), p t) : ∀ᵐ r : ℝ ∂ν, p (r : OnePoint ℝ) :=
  ae_of_ae_map measurable_onePoint_some.aemeasurable h

/-- **Rigidity of the Nevanlinna jet kernel over a projective pushforward measure.**  For a measure
on the compactified line that is the pushforward of a measure of infinite support on the real line,
an almost-everywhere vanishing real part of a packet combination of Nevanlinna jet columns forces
every coefficient to vanish. -/
theorem nevanlinnaJetColumn_coeff_eq_zero_of_ae_re_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} (hsupp : ν.support.Infinite)
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ)
    (hx : Function.Injective fun i => q (z i))
    (hupper : ∀ i, 0 < (q (z i)).im)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (c : (Σ i, Fin (n i)) → ℂ)
    (hc : ∀ᵐ t ∂(ν.map (OnePoint.some)),
      (∑ s : Σ i, Fin (n i),
        c s * projectiveNevanlinnaJetExpansionColumn a q z n t s).re = 0) :
    ∀ s, c s = 0 :=
  nevanlinnaJetColumn_coeff_eq_zero_of_ae_re hsupp a q n z hx hupper ha hq c
    (ae_onePoint_pullback hc)

end

end GaloisForLFunctions.HTGeometry
