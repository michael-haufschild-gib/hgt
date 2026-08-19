import GaloisForLFunctions.HTGeometry.GammaJetSumDatum
import GaloisForLFunctions.HTGeometry.UniformGammaFieldDatum

/-!
# The ratio of two Gamma monomials in one dominant class

Two Gamma monomials with the same total degree and the same weighted shift have the *same* boundary
shape, so their ratio tends to `1` uniformly on every vertical tube.  This is the strip bound the
ladder for a Gamma-monomial ratio needs: it says the ratio is bounded, and pins its limit.

Only the corpus's own datum for a Gamma monomial (`hasShiftTubeDatum_gammaProd`, with constant `1`)
and the tube-limit division law are used.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The ratio of two same-class Gamma monomials tends to `1` on every tube.** -/
theorem tubeLimit_gammaProd_ratio {M : ℝ} (hM : 0 < M) {rr : ℕ} (lamf : Fin rr → ℝ)
    (hlamf : ∀ i, 0 ≤ lamf i) (e f : Fin rr → ℕ)
    (hdeg : ∑ i, (e i : ℤ) = ∑ i, (f i : ℤ))
    (hmom : ∑ i, (e i : ℝ) * lamf i = ∑ i, (f i : ℝ) * lamf i) :
    TubeLimit M (fun σ t => (∏ i : Fin rr, gammaLine (σ + lamf i) t ^ e i)
      / (∏ i : Fin rr, gammaLine (σ + lamf i) t ^ f i)) 1 := by
  have he := hasShiftTubeDatum_gammaProd hM lamf hlamf e
  have hf := hasShiftTubeDatum_gammaProd hM lamf hlamf f
  rw [← hdeg, ← hmom] at hf
  have hdiv := he.2.div hf.2 one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσ
  have hne : gammaShiftShape 0 σ (∑ i : Fin rr, (e i : ℤ))
      (∑ i : Fin rr, (e i : ℝ) * lamf i) 0 t ≠ 0 :=
    gammaShiftShape_ne_zero hσ' ht _ _ _
  field_simp

end

end GaloisForLFunctions.HTGeometry
