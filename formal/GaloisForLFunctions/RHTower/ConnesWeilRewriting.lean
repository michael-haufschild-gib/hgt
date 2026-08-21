import GaloisForLFunctions.RHTower.ConnesLocalHomogeneousDistribution

/-!
# Rewriting Weil's explicit formula in Connes' variables (Appendix II (12)-(21))

Formalization of the change of variables (12) and the term-by-term evaluation (19)(20) of
Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Weil's explicit formula is stated for a distribution `Δ = log|d^{-1}| δ_1 + D - ∑_v D_v` on `C_k`
paired with `F(|w|) Χ(w)`.  Connes substitutes

  `|g|^{-1/2} h(g^{-1}) = F(|g|) Χ_0(g)`                                       (12)

and rewrites every term in `h`.  The first two terms give

  `⟨D , F(|g|) Χ_0(g)⟩ = ∫ h(u)(1 + |u|) d^*u = ĥ(0) + ĥ(1)`,                   (19)

and the local terms give `- ∑_v Pfw ∫ h(u^{-1})|1-u|^{-1} d^*u`                 (20).

The two substitutions behind (19) and (20) are the inversion invariance of the Haar measure of the
idele class group together with `|g^{-1}| = |g|^{-1}`; both are proved here for an arbitrary
commutative group with an inversion-invariant measure and a multiplicative modulus, so they apply
verbatim to `C_k`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableInv G]
  {μ : Measure G} [μ.IsInvInvariant]

set_option linter.unusedSectionVars false

/-- Connes' Fourier transform `ĥ(Χ, z) = ∫ h(u) Χ(u) |u|^z d^*u` of Corollary III.2. -/
def connesHatMoment (mod : G → ℝ) (μ : Measure G) (χ : G → ℂ) (z : ℂ) (h : G → ℂ) : ℂ :=
  ∫ u, h u * χ u * connesModulusPower mod z u ∂μ

/-- **Appendix II (18)/(19), the two polar terms.**  With the trivial character,
`ĥ(0) + ĥ(1) = ∫ h(u)(1 + |u|) d^*u`. -/
theorem connesHatMoment_zero_add_one {mod : G → ℝ} (hmodpos : ∀ g : G, 0 < mod g)
    (h : G → ℂ) (hint0 : Integrable (fun u => h u) μ)
    (hint1 : Integrable (fun u => h u * ((mod u : ℝ) : ℂ)) μ) :
    connesHatMoment mod μ (fun _ => 1) 0 h + connesHatMoment mod μ (fun _ => 1) 1 h
      = ∫ u, h u * ((1 + mod u : ℝ) : ℂ) ∂μ := by
  have hz0 : ∀ u : G, connesModulusPower mod 0 u = 1 := by
    intro u
    simp [connesModulusPower]
  have hz1 : ∀ u : G, connesModulusPower mod 1 u = ((mod u : ℝ) : ℂ) := by
    intro u
    rw [connesModulusPower, one_mul, ← Complex.ofReal_exp, Real.exp_log (hmodpos u)]
  simp only [connesHatMoment, hz0, hz1, mul_one]
  rw [← MeasureTheory.integral_add hint0 hint1]
  refine integral_congr_ae ?_
  filter_upwards with u
  push_cast
  ring

/-- **Appendix II (12)/(19), the inversion substitution.**  Connes' change of variables
`|g|^{-1/2} h(g^{-1}) = F(|g|) Χ_0(g)` turns the archimedean term `D` of Weil's distribution into
`∫ h(u)(1 + |u|) d^*u`. -/
theorem connes_weilD_inversion {mod : G → ℝ} (hmodpos : ∀ g : G, 0 < mod g)
    (hmodinv : ∀ g : G, mod g⁻¹ = (mod g)⁻¹) (h : G → ℂ) :
    (∫ g, connesModulusPower mod (-(1/2)) g * h g⁻¹ *
        (connesModulusPower mod (1/2) g + connesModulusPower mod (-(1/2)) g) ∂μ)
      = ∫ u, h u * ((1 + mod u : ℝ) : ℂ) ∂μ := by
  set Ψ : G → ℂ := fun u => h u * ((1 + mod u : ℝ) : ℂ) with hΨ
  have hinv : (∫ g, Ψ g⁻¹ ∂μ) = ∫ u, Ψ u ∂μ := integral_inv_eq_self Ψ μ
  rw [← hinv]
  refine integral_congr_ae ?_
  filter_upwards with g
  have hpos := hmodpos g
  have hne : Complex.exp (-(1/2 : ℂ) * (Real.log (mod g) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hprod : connesModulusPower mod (-(1/2)) g * connesModulusPower mod (1/2) g = 1 := by
    simp only [connesModulusPower, ← Complex.exp_add]
    rw [show (-(1/2 : ℂ)) * (Real.log (mod g) : ℂ) + (1/2 : ℂ) * (Real.log (mod g) : ℂ) = 0 by ring]
    exact Complex.exp_zero
  have hsq : connesModulusPower mod (-(1/2)) g * connesModulusPower mod (-(1/2)) g
      = ((mod g⁻¹ : ℝ) : ℂ) := by
    simp only [connesModulusPower, ← Complex.exp_add]
    rw [show (-(1/2 : ℂ)) * (Real.log (mod g) : ℂ) + (-(1/2 : ℂ)) * (Real.log (mod g) : ℂ)
      = -((Real.log (mod g) : ℂ)) by ring]
    rw [hmodinv g]
    rw [show (-((Real.log (mod g) : ℝ) : ℂ)) = (((-Real.log (mod g)) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos]
  simp only [hΨ]
  push_cast
  calc connesModulusPower mod (-(1/2)) g * h g⁻¹ *
        (connesModulusPower mod (1/2) g + connesModulusPower mod (-(1/2)) g)
      = h g⁻¹ * (connesModulusPower mod (-(1/2)) g * connesModulusPower mod (1/2) g
          + connesModulusPower mod (-(1/2)) g * connesModulusPower mod (-(1/2)) g) := by ring
    _ = h g⁻¹ * (1 + ((mod g⁻¹ : ℝ) : ℂ)) := by rw [hprod, hsq]

end

end GaloisForLFunctions.RHTower
