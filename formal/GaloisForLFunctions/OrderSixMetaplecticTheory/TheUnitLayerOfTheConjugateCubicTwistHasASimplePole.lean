import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnramifiedConjugateTwistCarriesHalfTheDoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.EveryLayerIsTheUnitLayerOfAnEvenTwist
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicTwistsOfTheSquarefreeCombinationHaveSimplePoles
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeThetaSeriesHasASimplePole

/-!
# The unit layer of the conjugate cubic twist has a simple pole

On the support of `T` the frequencies prime to `3` are those prime to `λ` (`T(uλ) = 0`), so the unramified conjugate
twist is the unramified twisted theta square `D₀^ψ` of `ψ = χ_q⁻¹` (`besselDirichlet_unramConj`). That square is the
unit layer (`unramifiedTwist_eq`), and for the cubic character `χ_q⁻¹` its cube factor is `Z₀` without its Euler factor at
`q` (`cubeZetaW_cubic`):

`(s − 4/3) D₀^{χ̄_q}(s) = C̄²(2/3)Z̃(s)E_q(s) · 2(4π|ξ₁|)^{−s} S^{χ̄_q}_1(s/2)`   (`sub_mul_unramConj`),

`S^{χ̄_q}_1(w) = Σ_A χ_q(gen A)⁻¹ σ(A) N(A)^{−w}` over squarefree ideals prime to `3`. The double pole of `D₀^{χ̄_q}`
(`unramifiedConjugateCubicTwist_double_pole`) is therefore a simple pole of the unit layer (`conjugateUnitLayer_simple_pole`):

**for every odd primary prime `q` the squarefree theta series twisted by the conjugate cubic character,
`S^{χ̄_q}_1(w)`, has a simple pole at `w = 2/3` with an explicit nonzero residue.** This is the single-layer statement
for a twisted family: the unit layer is isolated without the 3-adic theta coefficients `T(uλ^m)`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- On the support of `T`, `3 ∣ h` iff `λ ∣ h`. -/
theorem three_dvd_iff_lambda_dvd_of_coeff (h : O) (hT : rationalSourceResidualFourierCoefficient h ≠ 0) :
    (3 : O) ∣ h ↔ lambda ∣ h := by
  constructor
  · exact fun h3 => lambda_dvd_three.trans h3
  · intro hl
    by_contra h3
    have hh : h ≠ 0 := fun hz => h3 (hz ▸ dvd_zero 3)
    rcases primary_or_negative_primary_of_source_mask h h3 (sourceFourier_phase_of_ne_zero h hh hT) with hp | hp
    · exact lambda_not_dvd_of_primary hp hl
    · exact lambda_not_dvd_of_primary hp (dvd_neg.mpr hl)

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem unramConjCoeff_eq_twist (h : O) :
    P.unramConjCoeff h = (P.resTwist P.chi⁻¹ * unramifiedChar) h * rationalSourceResidualFourierCoefficient h ^ 2 := by
  have hu : unramifiedChar h = if lambda ∣ h then 0 else 1 := rfl
  have hr : P.resTwist P.chi⁻¹ h = (P.chi (P.res h))⁻¹ := by
    show P.chi⁻¹ (P.res h) = _
    rw [MulChar.inv_apply_eq_inv']
  rw [MonoidHom.mul_apply, hu, hr]
  by_cases hT : rationalSourceResidualFourierCoefficient h = 0
  · simp [unramConjCoeff, conjTwistCoeff, hT]
  · have hiff := three_dvd_iff_lambda_dvd_of_coeff h hT
    unfold unramConjCoeff conjTwistCoeff
    by_cases h3 : (3 : O) ∣ h
    · rw [if_pos h3, if_pos (hiff.mp h3)]
      ring
    · rw [if_neg h3, if_neg (fun hl => h3 (hiff.mpr hl))]
      ring

theorem besselDirichlet_unramConj (s : ℂ) :
    besselDirichlet P.unramConjCoeff s = twistDirichletG (P.resTwist P.chi⁻¹ * unramifiedChar) s := by
  unfold twistDirichletG
  congr 1
  funext h
  exact P.unramConjCoeff_eq_twist h

theorem resTwist_chi_inv_sign : P.resTwist P.chi⁻¹ 1 + P.resTwist P.chi⁻¹ (-1) = 2 := by
  have e : ∀ x : O, P.resTwist P.chi⁻¹ x = (P.chi (P.res x))⁻¹ := fun x => by
    show P.chi⁻¹ (P.res x) = _
    rw [MulChar.inv_apply_eq_inv']
  rw [e, e, map_one, MulChar.map_one, map_neg, map_one, P.chi_neg_one]
  norm_num

/-- **The unit layer of the conjugate twist.** `(s − 4/3)D₀^{χ̄}(s) = C̄²(2/3)Z̃(s)E_q(s)·2(4π|ξ₁|)^{−s}S^{χ̄}_1(s/2)`. -/
theorem sub_mul_unramConj (s : ℂ) (hs : 4 < s.re) :
    (s - 4 / 3) * besselDirichlet P.unramConjCoeff s =
      P.combinationDenom s * (2 * unitFrequencyWeight s * P.twistedSquarefreeSeriesW P.chi⁻¹ 1 (s / 2)) := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hU := unramifiedTwist_eq (P.resTwist P.chi⁻¹) (P.norm_resTwist_le _) s hs
  have hcz : cubeZetaG (P.resTwist P.chi⁻¹) (3 * (s / 2) - 1) = P.cubeZetaW P.chi⁻¹ (3 * (s / 2) - 1) := rfl
  have hsq : twistedSquarefreeSeriesG (P.resTwist P.chi⁻¹) 1 (s / 2) =
      P.twistedSquarefreeSeriesW P.chi⁻¹ 1 (s / 2) := rfl
  rw [P.besselDirichlet_unramConj, hU, hcz, hsq, P.resTwist_chi_inv_sign,
    P.cubeZetaW_cubic _ P.chi_inv_pow_three _ hz]
  unfold combinationDenom eulerFactorQ unitFrequencyWeight
  linear_combination (star rationalSourceThetaScalar ^ 2 *
    (1 - unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})) *
      (2 * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
        P.twistedSquarefreeSeriesW P.chi⁻¹ 1 (s / 2))) * hZ

/-- The residue of `M(s)S^{χ̄_q}_1(s/2)` at `4/3`. -/
def conjUnitResidue : ℂ :=
  (P.gaussAt 1)⁻¹ * P.conjLimit / 2 / (2 * unitFrequencyWeight (4 / 3) * P.combinationDenom (4 / 3))

theorem conjUnitResidue_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.conjUnitResidue ≠ 0 :=
  div_ne_zero (div_ne_zero (mul_ne_zero (inv_ne_zero P.gaussAt_one_ne_zero) (P.conjLimit_ne_zero h2)) (by norm_num))
    (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero)

/-- **The unit layer of the conjugate cubic twist has a simple pole.** For every odd primary prime `q`,
`M(s)S^{χ̄_q}_1(s/2)`, `S^{χ̄_q}_1(w) = Σ_A χ_q(gen A)⁻¹σ(A)N(A)^{−w}`, continues to `{4/3 < Re s < 13/3, Im s > 0}` and
to a punctured neighbourhood of `4/3`, and `(s − 4/3)M(s)S^{χ̄_q}_1(s/2)` tends to `conjUnitResidue ≠ 0`. -/
theorem conjugateUnitLayer_simple_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * P.twistedSquarefreeSeriesW P.chi⁻¹ 1 (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.conjUnitResidue) ∧
      P.conjUnitResidue ≠ 0 := by
  obtain ⟨Λu, hu_eq, hu_d, hu_n, hu_l, -⟩ := P.unramifiedConjugateCubicTwist_double_pole h2
  set D : ℂ → ℂ := fun s => 2 * unitFrequencyWeight s * P.combinationDenom s with hD
  have hDd : Differentiable ℂ D := fun s =>
    ((unitFrequencyWeight_differentiable s).const_mul 2).mul (P.combinationDenom_differentiable s)
  have hD0 : D (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero
  have hDne : ∀ s : ℂ, 4 / 3 < s.re → D s ≠ 0 := fun s hs =>
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) (P.combinationDenom_ne_zero hs)
  have hD_ev : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), D s ≠ 0 := (hDd _).continuousAt.eventually_ne hD0
  refine ⟨fun s => (s - 4 / 3) * Λu s / D s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    P.conjUnitResidue_ne_zero h2⟩
  · have hd := hDne s (by linarith)
    have hL := P.sub_mul_unramConj s hs4
    show (s - 4 / 3) * Λu s / D s = _
    rw [hu_eq s hs4 hs hi, div_eq_iff hd]
    simp only [hD]
    linear_combination besselSqMellin s * hL
  · exact ((differentiableAt_id.sub_const _).mul (hu_d s (by linarith) hs hi)).div (hDd s) (hDne s hs1)
  · filter_upwards [hu_n, nhdsWithin_le_nhds hD_ev] with s h1 h2'
    exact ((differentiableAt_id.sub_const _).mul h1).div (hDd s) h2'
  · have hDt : Tendsto D (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (D (4 / 3))) :=
      ((hDd _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hval : P.conjUnitResidue = (P.gaussAt 1)⁻¹ * P.conjLimit / 2 / D (4 / 3) := by
      simp only [conjUnitResidue, hD]
    rw [hval]
    refine (hu_l.div hDt hD0).congr fun s => ?_
    simp only [Pi.div_apply]
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
