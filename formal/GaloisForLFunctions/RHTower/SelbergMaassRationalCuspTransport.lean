import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspFactor

/-!
# Rational transport of Maass cusp decay

A rational matrix composed with an integral cusp scaling has an integral-cusp
factorization followed by an upper-triangular map. Since the latter preserves the
upper-half-plane infinity filter, rational pullback preserves the source's exact
integral-cusp decay condition. Positive rational pullback consequently preserves
both the Maass eigen-equation and cusp decay.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups LinearAlgebra.Projectivization

noncomputable section

/-- Casting a rational matrix after composing with an integral special-linear
matrix equals the corresponding real product. -/
set_option backward.isDefEq.respectTransparency false in
theorem rationalGL_mul_integral_real (g : GL (Fin 2) ℚ) (B : SL2Z) :
    (g * mapGL ℚ B).map (algebraMap ℚ ℝ) =
      g.map (algebraMap ℚ ℝ) * mapGL ℝ B := by
  rw [Matrix.GeneralLinearGroup.map_mul]
  rw [← (Rat.castHom ℝ).algebraMap_toAlgebra]
  exact congrArg (fun h : GL (Fin 2) ℝ →* GL (Fin 2) ℝ => h g) (by
    rw [Matrix.SpecialLinearGroup.map_mapGL])

/-- Rational pullback preserves decay at each integral cusp. -/
set_option backward.isDefEq.respectTransparency false in
theorem rationalGL_cuspidal_pullback (g : GL (Fin 2) ℚ) (f : ℍ → ℂ)
    (hf : IsCuspidalAtIntegralCusps f) :
    IsCuspidalAtIntegralCusps (fun w => f (g.map (algebraMap ℚ ℝ) • w)) := by
  intro B
  let gB : GL (Fin 2) ℚ := g * mapGL ℚ B
  obtain ⟨A, hA⟩ := rationalGL_exists_integral_upperTriangular gB
  let U : GL (Fin 2) ℝ := (mapGL ℝ A)⁻¹ * gB.map (algebraMap ℚ ℝ)
  have hU : U 1 0 = 0 := by
    simpa only [U] using hA
  have hfactor : gB.map (algebraMap ℚ ℝ) = mapGL ℝ A * U := by
    dsimp only [U]
    group
  have hdecay : Tendsto (fun z => f (mapGL ℝ A • z)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa only [IsZeroAtImInfty, ZeroAtFilter] using hf A
  have htransport := hdecay.comp (UpperHalfPlane.tendsto_smul_atImInfty hU)
  change Tendsto (fun z => f (g.map (algebraMap ℚ ℝ) • (B • z))) atImInfty (𝓝 (0 : ℂ))
  have hmul : g.map (algebraMap ℚ ℝ) * mapGL ℝ B = gB.map (algebraMap ℚ ℝ) := by
    rw [rationalGL_mul_integral_real]
  apply htransport.congr'
  filter_upwards [] with z
  change f (g.map (algebraMap ℚ ℝ) • ((mapGL ℝ B : GL (Fin 2) ℝ) • z)) =
    f (mapGL ℝ A • (U • z))
  rw [← mul_smul, hmul, hfactor, mul_smul]

/-- A positive rational pullback preserves the analytic Maass equation and the
integral-cusp condition simultaneously. -/
theorem rationalGL_maass_eigenfunction_cuspidal_pullback (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) (f : ℍ → ℂ)
    (heigen : IsMaassEigenfunction lam f) (hcusp : IsCuspidalAtIntegralCusps f) :
    IsMaassEigenfunction lam (fun w => f (g.map (algebraMap ℚ ℝ) • w)) ∧
      IsCuspidalAtIntegralCusps (fun w => f (g.map (algebraMap ℚ ℝ) • w)) :=
  ⟨SelbergMaassCuspTransport.eigenfunction_pullback_gl (g.map (algebraMap ℚ ℝ)) hg lam f heigen,
    rationalGL_cuspidal_pullback g f hcusp⟩

end

end GaloisForLFunctions.RHTower
