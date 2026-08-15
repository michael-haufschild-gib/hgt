import GaloisForLFunctions.RHTower.SelbergClass.AffineGammaPoleLattice
import GaloisForLFunctions.RHTower.BVCoPoissonHellingerBetaResonanceTransmutation

/-!
# Exact residues of affine Gamma factors

Mathlib has no primitive complex-residue operator.  This file therefore uses
the defining punctured-neighborhood limit of the principal coefficient.  It
reuses the corpus proof of Gamma's residue at every negative integer and
transports it through the concrete affine map `w ↦ b * w + A`.

The result is local only: it neither chooses a contour nor applies a residue
theorem.  In particular, it is exactly the coefficient required for an
eventual Kaczorowski--Perelli contour calculation, not that calculation.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Gamma's residue at `-n`, expressed in the standard principal-part
normalization.  This is a source-normalized restatement of the existing
corpus theorem `tendsto_add_nat_mul_Gamma_nhds_neg_nat`. -/
theorem tendsto_sub_neg_nat_mul_Gamma_nhds_neg_nat (n : ℕ) :
    Tendsto (fun z : ℂ => (z - (-(n : ℂ))) * Complex.Gamma z)
      (𝓝[≠] (-(n : ℂ))) (𝓝 (((-1 : ℂ) ^ n) / n.factorial)) := by
  rw [show (fun z : ℂ => (z - (-(n : ℂ))) * Complex.Gamma z) =
    fun z : ℂ => (z + n) * Complex.Gamma z by
      funext z
      ring]
  rw [← gammaNegNatResidue_eq n]
  exact tendsto_add_nat_mul_Gamma_nhds_neg_nat n

/-- Exact local residue coefficient of the concrete affine Gamma factor
`w ↦ Gamma (b * w + A)` at its `n`th pole.  For a positive real slope `b`,
the coefficient is the requested `(-1)^n / (n! * b)`; the theorem is stated
for every nonzero real slope because the same local calculation is valid for
the reflected `Gamma (A - b*w)` factors as well. -/
theorem tendsto_affineGammaAdd_residue
    (A : ℂ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    Tendsto (fun w : ℂ =>
      (w - affineGammaAddPole A b n) * Complex.Gamma ((b : ℂ) * w + A))
      (𝓝[≠] affineGammaAddPole A b n)
      (𝓝 (((-1 : ℂ) ^ n) / ((n.factorial : ℂ) * (b : ℂ)))) := by
  let w₀ : ℂ := affineGammaAddPole A b n
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hderiv : HasDerivAt (fun w : ℂ => (b : ℂ) * w + A) (b : ℂ) w₀ := by
    simpa using (hasDerivAt_const_mul (x := w₀) (b : ℂ)).add_const A
  have hmap : Tendsto (fun w : ℂ => (b : ℂ) * w + A)
      (𝓝[≠] w₀) (𝓝[≠] (-(n : ℂ))) := by
    have hpole : (b : ℂ) * w₀ + A = -(n : ℂ) := by
      simpa [w₀] using affineGammaAddPole_argument A hb n
    rw [← hpole]
    exact hderiv.tendsto_nhdsNE hbC
  have hcore := tendsto_sub_neg_nat_mul_Gamma_nhds_neg_nat n
  have hcomp : Tendsto
      (fun w : ℂ => (((b : ℂ) * w + A) - (-(n : ℂ))) *
        Complex.Gamma ((b : ℂ) * w + A))
      (𝓝[≠] w₀) (𝓝 (((-1 : ℂ) ^ n) / n.factorial)) :=
    hcore.comp hmap
  have hscaled := hcomp.const_mul (b : ℂ)⁻¹
  have heq : ∀ᶠ w : ℂ in 𝓝[≠] w₀,
      (b : ℂ)⁻¹ * ((((b : ℂ) * w + A) - (-(n : ℂ))) *
        Complex.Gamma ((b : ℂ) * w + A)) =
        (w - w₀) * Complex.Gamma ((b : ℂ) * w + A) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hpole : (b : ℂ) * w₀ + A = -(n : ℂ) :=
      affineGammaAddPole_argument A hb n
    have harg : ((b : ℂ) * w + A) - (-(n : ℂ)) = (b : ℂ) * (w - w₀) := by
      rw [← hpole]
      ring
    rw [harg]
    field_simp [hbC]
  have hlim : (b : ℂ)⁻¹ * (((-1 : ℂ) ^ n) / n.factorial) =
      ((-1 : ℂ) ^ n) / ((n.factorial : ℂ) * (b : ℂ)) := by
    field_simp [hbC]
  rw [← hlim]
  simpa [w₀] using hscaled.congr' heq

end

end RHTower
