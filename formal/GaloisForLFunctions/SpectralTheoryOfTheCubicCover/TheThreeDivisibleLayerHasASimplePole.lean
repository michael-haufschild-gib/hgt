import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedCorrelationHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTwistedSquarefreeCombinationHasASimplePole

/-!
# The three-divisible layer has a simple pole

For `Re s > 4` the rotated correlation reads only frequencies divisible by `3`
(`rotatedCorrelation_eq_three_layer`):

`C_ω(s) = \overline{C}² Z₀(3s/2 − 1) Q₃(s)`,
`Q₃(s) = Σ_u Σ_{m ≥ 2} (T(ωuλ^m) T(uλ^m)/T(1)²) (4π|ξ_{uλ^m}|)^{−s} S_{ω²uλ^m}(s/2)`.

Dividing the double pole `(s − 4/3)² M(s) C_ω(s) → 54 π³ r³` (`rotatedCorrelation_double_pole`) by the simple
pole of `Z₀(3s/2 − 1)` gives (`threeLayerCombination_simple_pole`)

`(s − 4/3) M(s) Q₃(s) → 243 π³ r³ / (2 \overline{C}² L(1, χ₋₃)) ≠ 0`,

half the residue of the full combination `Q` (`twistedSquarefreeCombination_simple_pole`). So the theta
coefficients at frequencies divisible by `3` are not negligible: some `T(uλ^m)`, `m ≥ 2`, is nonzero, and at
least one of the twisted squarefree series `S_{ω²uλ^m}` has a pole at `w = 2/3`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

theorem omega_ne_one : omega ≠ 1 := omega_primitive.ne_one (by norm_num)

theorem omega_ne_neg_one : omega ≠ -1 := by
  intro h
  have h3 := omega_cube
  rw [h] at h3
  have h2 : (2 : O) = 0 := by linear_combination -h3
  exact two_ne_zero h2

/-- The three-divisible twisted combination `Q₃(s)`. -/
def threeLayerCombination (s : ℂ) : ℂ :=
  ∑' u : Oˣ, ∑' m : ℕ, rotatedLayerCoeff cuspOmegaUnit u (m + 2) s *
    twistedSquarefreeSeries (((cuspOmegaUnit ^ 2 * u : Oˣ) : O) * lambda ^ (m + 2)) (s / 2)

theorem rotatedCorrelation_eq_threeLayer (s : ℂ) (hs : 4 < s.re) :
    rotatedCorrelation cuspOmegaUnit s =
      star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) * threeLayerCombination s :=
  rotatedCorrelation_eq_three_layer cuspOmegaUnit (by rw [cuspOmegaUnit_val]; exact omega_ne_one)
    (by rw [cuspOmegaUnit_val]; exact omega_ne_neg_one) s hs

/-- The continuation `(s − 4/3) Λ_R(s) / (\overline{C}² (2/3) Z̃(s))` of `M(s) Q₃(s)`. -/
def completedThreeLayer (s : ℂ) : ℂ :=
  (s - 4 / 3) * completedRotated s / (star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s)

theorem completedThreeLayer_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    completedThreeLayer s = besselSqMellin s * threeLayerCombination s := by
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hden : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      (clearedCubeZeta_ne_zero (by linarith))
  unfold completedThreeLayer
  rw [completedRotated_eq s hs4 hs hi, rotatedCorrelation_eq_threeLayer s hs4, div_eq_iff hden]
  linear_combination (besselSqMellin s * star rationalSourceThetaScalar ^ 2 * threeLayerCombination s) * hZ

theorem completedThreeLayer_differentiableAt (s : ℂ) (hs1 : 4 / 3 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) : DifferentiableAt ℂ completedThreeLayer s := by
  have hden : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      (clearedCubeZeta_ne_zero hs1)
  unfold completedThreeLayer
  exact ((differentiableAt_id.sub_const _).mul
    (completedRotated_differentiableAt s (by linarith) hs hi)).div
      ((differentiableAt_const _).mul (clearedCubeZeta_differentiable s)) hden

theorem completedThreeLayer_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedThreeLayer s := by
  filter_upwards [completedRotated_differentiableAt_near,
    nhdsWithin_le_nhds clearedCubeZeta_eventually_ne] with s hΛ hZ
  unfold completedThreeLayer
  exact ((differentiableAt_id.sub_const _).mul hΛ).div
    ((differentiableAt_const _).mul (clearedCubeZeta_differentiable s))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num)) hZ)

/-- The residue `243 π³ r³ / (2 \overline{C}² L(1, χ₋₃))` of `M·Q₃` at `4/3`. -/
abbrev threeLayerResidue : ℂ :=
  243 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 /
    (2 * star rationalSourceThetaScalar ^ 2 * DirichletCharacter.LFunction chi3D 1)

theorem threeLayerResidue_ne_zero : threeLayerResidue ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
    Real.pi_ne_zero))) (pow_ne_zero 3 constantArithmeticResidue_ne_zero))
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 scalar_star_ne_zero)) LFunction_chi3D_one_ne_zero)

theorem completedThreeLayer_simple_pole :
    Tendsto (fun s => (s - 4 / 3) * completedThreeLayer s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 threeLayerResidue) := by
  have hZ : Tendsto clearedCubeZeta (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (clearedCubeZeta (4 / 3))) :=
    ((clearedCubeZeta_differentiable _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hden0 : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      clearedCubeZeta_four_thirds_ne_zero
  have h := completedRotated_double_pole.div (tendsto_const_nhds.mul hZ) hden0
  have hlim : 6 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue /
      (star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3)) = threeLayerResidue := by
    have hL := LFunction_chi3D_one_ne_zero
    have hC := scalar_star_ne_zero
    rw [clearedCubeZeta_four_thirds, thetaCoeff]
    field_simp
    ring
  rw [← hlim]
  refine h.congr fun s => ?_
  simp only [Pi.div_apply]
  unfold completedThreeLayer
  ring

/-- **The three-divisible layer has a simple pole at `4/3`.** `M(s) Q₃(s)` continues holomorphically to
`4/3 < Re s < 13/3`, `Im s > 0` and to a punctured neighbourhood of `4/3`, with
`(s − 4/3) M(s) Q₃(s) → 243 π³ r³ / (2 \overline{C}² L(1, χ₋₃)) ≠ 0`; since `M(4/3) ≠ 0`,
`(s − 4/3) Q₃(s)` tends to that residue divided by `M(4/3)`. -/
theorem threeLayerCombination_simple_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * threeLayerCombination s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 threeLayerResidue) ∧
      Tendsto (fun s => (s - 4 / 3) * (Λ s / besselSqMellin s)) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (threeLayerResidue / besselSqMellin (4 / 3))) ∧
      threeLayerResidue ≠ 0 := by
  have hM : Tendsto besselSqMellin (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (besselSqMellin (4 / 3))) :=
    ((besselSqMellin_differentiableAt _ (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨completedThreeLayer, completedThreeLayer_eq, completedThreeLayer_differentiableAt,
    completedThreeLayer_differentiableAt_near, completedThreeLayer_simple_pole, ?_, threeLayerResidue_ne_zero⟩
  refine (completedThreeLayer_simple_pole.div hM besselSqMellin_four_thirds_ne_zero).congr fun s => ?_
  simp only [Pi.div_apply]
  ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
