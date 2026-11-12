import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesHasADoublePole

/-!
# The twisted squarefree combination has a simple pole at `4/3`

For `Re s > 4`, `D(s) = \overline{C}² Z₀(3s/2 − 1) Q(s)` (`thetaSqDirichlet_eq_zeta_mul`) with the
twisted squarefree combination

`Q(s) = Σ_{u, m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)`.

The unramified zeta `Z₀(z) = (1 − 3^{−z}) ζ(z) L(z, χ₋₃)` has a simple pole at `z = 1`, i.e. `s = 4/3`:
`(s − 4/3) Z₀(3s/2 − 1) = (2/3) Z̃(s)` with `Z̃` entire and `Z̃(4/3) = (2/3) L(1, χ₋₃) ≠ 0`
(`sub_mul_cubeZeta`, `clearedCubeZeta_four_thirds`). Dividing the continuation `Λ` of `M·D`
(`completedThetaSq`) by `\overline{C}² Z₀` gives the continuation

`Λ_Q(s) = (s − 4/3) Λ(s) / (\overline{C}² (2/3) Z̃(s))`

of `M(s) Q(s)` to `{4/3 < Re s < 13/3, Im s > 0}` and to a punctured neighbourhood of `4/3`, with
(`twistedSquarefreeCombination_simple_pole`)

`(s − 4/3) Λ_Q(s) → 243 π³ r³ / (\overline{C}² L(1, χ₋₃)) ≠ 0`.

So `Q` has a simple pole at `4/3` with residue `243 π³ r³ / (M(4/3) \overline{C}² L(1, χ₋₃))`: one linear
relation among the residues at `w = 2/3` of the nine twisted squarefree series `S_{aλ^r}`, and at least
one of them has a pole there.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The twisted squarefree combination `Q(s) = Σ_{u,m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)`. -/
def twistedSquarefreeCombination (s : ℂ) : ℂ :=
  ∑' u : Oˣ, ∑' m : ℕ,
    (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
        rationalSourceResidualFourierCoefficient 1) ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
        twistedSquarefreeSeries ((u : O) * lambda ^ m) (s / 2)

theorem thetaSqDirichlet_eq_combination (s : ℂ) (hs : 4 < s.re) :
    thetaSqDirichlet s = star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
      twistedSquarefreeCombination s :=
  thetaSqDirichlet_eq_zeta_mul s hs

/-- The pole-cleared `Z₀(3s/2 − 1)`: `(1 − 3^{−z}) (z − 1)ζ(z) L(z, χ₋₃)` at `z = 3s/2 − 1`. -/
def clearedCubeZeta (s : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (-(3 * (s / 2) - 1))) *
    (_root_.RHTower.zetaPoleFilled (3 * (s / 2) - 1) * DirichletCharacter.LFunction chi3D (3 * (s / 2) - 1))

theorem cubeZeta_re (s : ℂ) : (3 * (s / 2) - 1).re = 3 * (s.re / 2) - 1 := by simp

/-- `(s − 4/3) Z₀(3s/2 − 1) = (2/3) Z̃(s)` for `Re s > 4/3`. -/
theorem sub_mul_cubeZeta {s : ℂ} (hs : 4 / 3 < s.re) :
    (s - 4 / 3) * unramifiedIdealZeta (3 * (s / 2) - 1) = (2 / 3) * clearedCubeZeta s := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have h1 : 3 * (s / 2) - 1 ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [cubeZeta_re, Complex.one_re] at this
    linarith
  rw [unramifiedIdealZeta_eq_dedekindZeta _ hz, dedekindZeta_thirdCyclotomic (CyclotomicField 3 ℚ) hz]
  unfold clearedCubeZeta
  rw [_root_.RHTower.zetaPoleFilled_of_ne h1]
  ring

theorem clearedCubeZeta_differentiable : Differentiable ℂ clearedCubeZeta := by
  have hlin : Differentiable ℂ (fun s : ℂ => 3 * (s / 2) - 1) :=
    ((differentiable_id.div_const 2).const_mul 3).sub_const 1
  intro s
  unfold clearedCubeZeta
  exact ((differentiableAt_const 1).sub ((hlin s).neg.const_cpow (Or.inl (by norm_num)))).mul
    (((_root_.RHTower.differentiable_zetaPoleFilled _).comp s (hlin s)).mul
      ((DirichletCharacter.differentiable_LFunction chi3D_ne_one _).comp s (hlin s)))

/-- `Z̃(4/3) = (2/3) L(1, χ₋₃)`. -/
theorem clearedCubeZeta_four_thirds :
    clearedCubeZeta (4 / 3) = (2 / 3) * DirichletCharacter.LFunction chi3D 1 := by
  unfold clearedCubeZeta
  rw [show (3 : ℂ) * (4 / 3 / 2) - 1 = 1 by norm_num,
    show _root_.RHTower.zetaPoleFilled 1 = 1 from Function.update_self _ _ _, Complex.cpow_neg_one]
  norm_num

theorem LFunction_chi3D_one_ne_zero : DirichletCharacter.LFunction chi3D 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero chi3D_ne_one

theorem clearedCubeZeta_four_thirds_ne_zero : clearedCubeZeta (4 / 3) ≠ 0 := by
  rw [clearedCubeZeta_four_thirds]
  exact mul_ne_zero (by norm_num) LFunction_chi3D_one_ne_zero

theorem clearedCubeZeta_ne_zero {s : ℂ} (hs : 4 / 3 < s.re) : clearedCubeZeta s ≠ 0 := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hs0 : s - 4 / 3 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at this
    norm_num at this
    linarith
  intro h
  have he := sub_mul_cubeZeta hs
  rw [h, mul_zero] at he
  exact mul_ne_zero hs0 (unramifiedIdealZeta_ne_zero _ hz) he

theorem scalar_star_ne_zero : star rationalSourceThetaScalar ≠ 0 :=
  star_ne_zero.mpr rationalSourceThetaScalar_ne_zero

/-- The continuation `Λ_Q(s) = (s − 4/3) Λ(s) / (\overline{C}² (2/3) Z̃(s))` of `M(s) Q(s)`. -/
def completedCombination (s : ℂ) : ℂ :=
  (s - 4 / 3) * completedThetaSq s / (star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s)

theorem completedCombination_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    completedCombination s = besselSqMellin s * twistedSquarefreeCombination s := by
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hden : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      (clearedCubeZeta_ne_zero (by linarith))
  unfold completedCombination
  rw [completedThetaSq_eq s hs4 hs hi, thetaSqDirichlet_eq_combination s hs4, div_eq_iff hden]
  linear_combination (besselSqMellin s * star rationalSourceThetaScalar ^ 2 *
    twistedSquarefreeCombination s) * hZ

theorem completedCombination_differentiableAt (s : ℂ) (hs1 : 4 / 3 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) : DifferentiableAt ℂ completedCombination s := by
  have hden : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      (clearedCubeZeta_ne_zero hs1)
  unfold completedCombination
  exact ((differentiableAt_id.sub_const _).mul
    (completedThetaSq_differentiableAt s (by linarith) hs hi)).div
      ((differentiableAt_const _).mul (clearedCubeZeta_differentiable s)) hden

theorem clearedCubeZeta_eventually_ne : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), clearedCubeZeta s ≠ 0 :=
  (clearedCubeZeta_differentiable _).continuousAt.eventually_ne clearedCubeZeta_four_thirds_ne_zero

theorem completedCombination_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedCombination s := by
  filter_upwards [completedThetaSq_differentiableAt_near,
    nhdsWithin_le_nhds clearedCubeZeta_eventually_ne] with s hΛ hZ
  unfold completedCombination
  exact ((differentiableAt_id.sub_const _).mul hΛ).div
    ((differentiableAt_const _).mul (clearedCubeZeta_differentiable s))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num)) hZ)

/-- The residue `243 π³ r³ / (\overline{C}² L(1, χ₋₃))` of `M·Q` at `4/3`. -/
abbrev combinationResidue : ℂ :=
  243 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 /
    (star rationalSourceThetaScalar ^ 2 * DirichletCharacter.LFunction chi3D 1)

theorem combinationResidue_ne_zero : combinationResidue ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
    Real.pi_ne_zero))) (pow_ne_zero 3 constantArithmeticResidue_ne_zero))
    (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) LFunction_chi3D_one_ne_zero)

theorem completedCombination_simple_pole :
    Tendsto (fun s => (s - 4 / 3) * completedCombination s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 combinationResidue) := by
  have hZ : Tendsto clearedCubeZeta (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (clearedCubeZeta (4 / 3))) :=
    ((clearedCubeZeta_differentiable _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hden0 : star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
      clearedCubeZeta_four_thirds_ne_zero
  have h := completedThetaSq_double_pole.div (tendsto_const_nhds.mul hZ) hden0
  have hlim : 12 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue /
      (star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3)) = combinationResidue := by
    have hL := LFunction_chi3D_one_ne_zero
    have hC := scalar_star_ne_zero
    rw [clearedCubeZeta_four_thirds, thetaCoeff]
    field_simp
    ring
  rw [← hlim]
  refine h.congr fun s => ?_
  simp only [Pi.div_apply]
  unfold completedCombination
  ring

/-- **The twisted squarefree combination has a simple pole at `4/3`.** The function
`M(s) Q(s)` (`4 < Re s < 13/3`, `Im s > 0`) continues holomorphically to `4/3 < Re s < 13/3`, `Im s > 0`
and to a punctured neighbourhood of `4/3`, where `(s − 4/3) M(s) Q(s) → 243 π³ r³ / (\overline{C}² L(1, χ₋₃)) ≠ 0`;
since `M(4/3) ≠ 0`, `(s − 4/3) Q(s)` tends to that residue divided by `M(4/3)`. -/
theorem twistedSquarefreeCombination_simple_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * twistedSquarefreeCombination s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 combinationResidue) ∧
      Tendsto (fun s => (s - 4 / 3) * (Λ s / besselSqMellin s)) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (combinationResidue / besselSqMellin (4 / 3))) ∧
      combinationResidue ≠ 0 := by
  have hM : Tendsto besselSqMellin (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (besselSqMellin (4 / 3))) :=
    ((besselSqMellin_differentiableAt _ (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨completedCombination, completedCombination_eq, completedCombination_differentiableAt,
    completedCombination_differentiableAt_near, completedCombination_simple_pole, ?_,
    combinationResidue_ne_zero⟩
  refine (completedCombination_simple_pole.div hM besselSqMellin_four_thirds_ne_zero).congr fun s => ?_
  simp only [Pi.div_apply]
  ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
