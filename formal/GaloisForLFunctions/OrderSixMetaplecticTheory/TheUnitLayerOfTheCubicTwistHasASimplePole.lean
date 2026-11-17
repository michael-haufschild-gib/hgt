import GaloisForLFunctions.OrderSixMetaplecticTheory.ThePhasedCubicTwistCarriesAQuarterOfTheDoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayerOfTheConjugateCubicTwistHasASimplePole

/-!
# The unit layer of the cubic twist has a simple pole

STCC's selector `φ(k) + φ(−k) ∈ {2, −1}` (as `3 ∣ k` or not, on the support of `T`) applies to the cubic twist at
every primary prime `p`, since `χ_p` is even (`twist_sub_phased`):

`L_{χ_p}(s) − L^φ_{χ_p}(s) = (3/2) Σ_{3∤k} (k/p)₃T(k)²(4π|ξ_k|)^{−s}`.

`L_{χ_p}` has the double pole with leading coefficient `L` (Hecke trace), its phased version `L/4` (shifted Hecke trace),
so the unramified cubic twist has `L/2` (`unramifiedCubicTwist_double_pole`). That twist is the unramified twisted
theta square of `ψ = χ_p`, which is the unit layer, and its cube factor is `Z₀` without the Euler factor at `p`:

`(s − 4/3)D₀^{χ_p}(s) = C̄²(2/3)Z̃(s)E_p(s)·2(4π|ξ₁|)^{−s}S^{χ_p}_1(s/2)`   (`sub_mul_unramTwist`).

**For every primary prime `p` the squarefree theta series twisted by the cubic character, `S^{χ_p}_1(w) =
Σ_A χ_p(gen A)σ(A)N(A)^{−w}`, has a simple pole at `w = 2/3` with an explicit nonzero residue**
(`cubicUnitLayer_simple_pole`). With the conjugate twist (`conjugateUnitLayer_simple_pole`) every character of the
cubic grade modulo an odd primary prime reaches the unit layer.
-/

noncomputable section

open MeasureTheory Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The selector -/

theorem twistCoeff_eq_chi (h : O) :
    P.twistCoeff h = P.chi (P.res h) * rationalSourceResidualFourierCoefficient h ^ 2 := by
  rw [twistCoeff, P.chi_res]

/-- `(k/p)₃T(k)²` on `k` prime to `3`. -/
def unramTwistCoeff (h : O) : ℂ := if (3 : O) ∣ h then 0 else P.twistCoeff h

theorem twistCoeff_neg (h : O) : P.twistCoeff (-h) = P.twistCoeff h := by
  rw [P.twistCoeff_eq_chi, P.twistCoeff_eq_chi, P.chi_res_neg, rationalSourceResidualFourierCoefficient_neg]

theorem norm_twistCoeff_le (h : O) :
    ‖P.twistCoeff h‖ ≤ ‖rationalSourceResidualFourierCoefficient h ^ 2‖ := by
  rw [P.twistCoeff_eq_chi, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)

/-- The selector at one frequency. -/
theorem twist_selector (h : O) :
    P.twistCoeff h * (1 - (tracePhase (2 * (cuspFrequency h * ringComplex omega)) +
        tracePhase (-(2 * (cuspFrequency h * ringComplex omega)))) / 2) = (3 / 2 : ℂ) * P.unramTwistCoeff h := by
  have hs := thetaSquare_translation_selector h
  rw [P.twistCoeff_eq_chi, mul_assoc, hs]
  unfold unramTwistCoeff
  rw [P.twistCoeff_eq_chi]
  split_ifs <;> ring

/-- **The selector on the cubic twist.** `L_{χ_p} − L^φ_{χ_p} = (3/2) L^{(3∤)}_{χ_p}`. -/
theorem twist_sub_phased (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.twistCoeff s - besselDirichlet P.phTwistCoeff s =
      (3 / 2 : ℂ) * besselDirichlet P.unramTwistCoeff s := by
  let F : O → ℂ := fun h => if h = 0 then 0 else P.twistCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let C : O → ℂ := fun h => if h = 0 then 0 else P.phTwistCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  have hT := summable_thetaSqDirichlet_term s hs
  have hF : Summable F := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [F]
    split_ifs with hh
    · simp
    · rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (P.norm_twistCoeff_le h) (norm_nonneg _)
  have hC : Summable C := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [C]
    split_ifs with hh
    · simp
    · rw [phTwistCoeff, norm_mul, norm_mul, norm_mul, norm_shiftPhase, one_mul]
      exact mul_le_mul_of_nonneg_right (P.norm_twistCoeff_le h) (norm_nonneg _)
  have hneg : Summable (fun h => C (-h)) := hC.comp_injective neg_injective
  have he : (∑' h, C (-h)) = ∑' h, C h := (Equiv.neg O).tsum_eq C
  change (∑' h, F h) - (∑' h, C h) = _
  calc
    _ = (∑' h, F h) - ((∑' h, C h) + ∑' h, C (-h)) / 2 := by rw [he]; ring
    _ = ∑' h, (F h - (C h + C (-h)) / 2) := by
      rw [← hC.tsum_add hneg, ← tsum_div_const, hF.tsum_sub ((hC.add hneg).div_const 2)]
    _ = ∑' h : O, (3 / 2 : ℂ) * (if h = 0 then 0 else P.unramTwistCoeff h *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun h => ?_
      by_cases hh : h = 0
      · simp [F, C, hh]
      · simp only [F, C, hh, neg_ne_zero.mpr hh, if_false, cuspFrequency_neg, norm_neg, phTwistCoeff,
          P.twistCoeff_neg]
        rw [shiftPhase_omega_neg, shiftPhase_omega_eq]
        have hp := P.twist_selector h
        linear_combination (((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) * hp
    _ = _ := by rw [tsum_mul_left]; rfl

/-- **The unramified cubic twist has the double pole with half the leading coefficient.** For every primary prime
`p`, `(s − 4/3)²M(s)Σ_{3∤k}(k/p)₃T(k)²(4π|ξ_k|)^{−s} → L/2 ≠ 0`, `L` the leading coefficient of `L_{χ_p}`. -/
theorem unramifiedCubicTwist_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.unramTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.twistLimit / 2)) ∧
      P.twistLimit / 2 ≠ 0 := by
  obtain ⟨Λc, hc_eq, hc_d, hc_n, hc_l, -⟩ := P.cubicTwistAtPrime_double_pole
  obtain ⟨Λφ, hφ_eq, hφ_d, hφ_n, hφ_l⟩ := P.phasedCubicTwist_double_pole
  refine ⟨fun s => (2 / 3 : ℂ) * (Λc s - Λφ s), fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    div_ne_zero P.twistLimit_ne_zero (by norm_num)⟩
  · show (2 / 3 : ℂ) * (Λc s - Λφ s) = _
    rw [hc_eq s hs4 hs hi, hφ_eq s hs4 hs hi, ← mul_sub, P.twist_sub_phased s hs4]
    ring
  · exact ((hc_d s hs1 hs hi).sub (hφ_d s hs1 hs hi)).const_mul _
  · filter_upwards [hc_n, hφ_n] with s h1 h2'
    exact (h1.sub h2').const_mul _
  · have h := (hc_l.sub hφ_l).const_mul (2 / 3 : ℂ)
    have he : (2 / 3 : ℂ) * (P.twistLimit - P.twistLimit / 4) = P.twistLimit / 2 := by ring
    rw [show (2 * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
        (P.dilateFactor (4 / 3) * (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)))) =
          P.twistLimit from rfl, he] at h
    exact h.congr fun s => by ring

/-! ### The unit layer -/

theorem unramTwistCoeff_eq_twist (h : O) :
    P.unramTwistCoeff h = (P.resTwist P.chi * unramifiedChar) h * rationalSourceResidualFourierCoefficient h ^ 2 := by
  have hu : unramifiedChar h = if lambda ∣ h then 0 else 1 := rfl
  have hr : P.resTwist P.chi h = P.chi (P.res h) := rfl
  rw [MonoidHom.mul_apply, hu, hr]
  by_cases hT : rationalSourceResidualFourierCoefficient h = 0
  · simp [unramTwistCoeff, twistCoeff, hT]
  · have hiff := three_dvd_iff_lambda_dvd_of_coeff h hT
    unfold unramTwistCoeff
    rw [P.twistCoeff_eq_chi]
    by_cases h3 : (3 : O) ∣ h
    · rw [if_pos h3, if_pos (hiff.mp h3)]
      ring
    · rw [if_neg h3, if_neg (fun hl => h3 (hiff.mpr hl))]
      ring

theorem besselDirichlet_unramTwist (s : ℂ) :
    besselDirichlet P.unramTwistCoeff s = twistDirichletG (P.resTwist P.chi * unramifiedChar) s := by
  unfold twistDirichletG
  congr 1
  funext h
  exact P.unramTwistCoeff_eq_twist h

theorem resTwist_chi_sign : P.resTwist P.chi 1 + P.resTwist P.chi (-1) = 2 := by
  have e : ∀ x : O, P.resTwist P.chi x = P.chi (P.res x) := fun x => rfl
  rw [e, e, map_one, MulChar.map_one, map_neg, map_one, P.chi_neg_one]
  norm_num

/-- **The unit layer of the cubic twist.** `(s − 4/3)D₀^{χ}(s) = C̄²(2/3)Z̃(s)E_p(s)·2(4π|ξ₁|)^{−s}S^{χ}_1(s/2)`. -/
theorem sub_mul_unramTwist (s : ℂ) (hs : 4 < s.re) :
    (s - 4 / 3) * besselDirichlet P.unramTwistCoeff s =
      P.combinationDenom s * (2 * unitFrequencyWeight s * P.twistedSquarefreeSeriesW P.chi 1 (s / 2)) := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hU := unramifiedTwist_eq (P.resTwist P.chi) (P.norm_resTwist_le _) s hs
  have hcz : cubeZetaG (P.resTwist P.chi) (3 * (s / 2) - 1) = P.cubeZetaW P.chi (3 * (s / 2) - 1) := rfl
  have hsq : twistedSquarefreeSeriesG (P.resTwist P.chi) 1 (s / 2) = P.twistedSquarefreeSeriesW P.chi 1 (s / 2) := rfl
  rw [P.besselDirichlet_unramTwist, hU, hcz, hsq, P.resTwist_chi_sign, P.cubeZetaW_cubic _ P.chi_pow_three _ hz]
  unfold combinationDenom eulerFactorQ unitFrequencyWeight
  linear_combination (star rationalSourceThetaScalar ^ 2 *
    (1 - unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})) *
      (2 * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) * P.twistedSquarefreeSeriesW P.chi 1 (s / 2))) * hZ

/-- The residue of `M(s)S^{χ_p}_1(s/2)` at `4/3`. -/
def twistUnitResidue : ℂ :=
  P.twistLimit / 2 / (2 * unitFrequencyWeight (4 / 3) * P.combinationDenom (4 / 3))

theorem twistUnitResidue_ne_zero : P.twistUnitResidue ≠ 0 :=
  div_ne_zero (div_ne_zero P.twistLimit_ne_zero (by norm_num))
    (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero)

/-- **The unit layer of the cubic twist has a simple pole.** For every primary prime `p`, `M(s)S^{χ_p}_1(s/2)`,
`S^{χ_p}_1(w) = Σ_Aχ_p(gen A)σ(A)N(A)^{−w}`, continues to `{4/3 < Re s < 13/3, Im s > 0}` and to a punctured
neighbourhood of `4/3`, and `(s − 4/3)M(s)S^{χ_p}_1(s/2)` tends to `twistUnitResidue ≠ 0`. -/
theorem cubicUnitLayer_simple_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * P.twistedSquarefreeSeriesW P.chi 1 (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.twistUnitResidue) ∧
      P.twistUnitResidue ≠ 0 := by
  obtain ⟨Λu, hu_eq, hu_d, hu_n, hu_l, -⟩ := P.unramifiedCubicTwist_double_pole
  set D : ℂ → ℂ := fun s => 2 * unitFrequencyWeight s * P.combinationDenom s with hD
  have hDd : Differentiable ℂ D := fun s =>
    ((unitFrequencyWeight_differentiable s).const_mul 2).mul (P.combinationDenom_differentiable s)
  have hD0 : D (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero
  have hDne : ∀ s : ℂ, 4 / 3 < s.re → D s ≠ 0 := fun s hs =>
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) (P.combinationDenom_ne_zero hs)
  have hD_ev : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), D s ≠ 0 := (hDd _).continuousAt.eventually_ne hD0
  refine ⟨fun s => (s - 4 / 3) * Λu s / D s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    P.twistUnitResidue_ne_zero⟩
  · have hd := hDne s (by linarith)
    have hL := P.sub_mul_unramTwist s hs4
    show (s - 4 / 3) * Λu s / D s = _
    rw [hu_eq s hs4 hs hi, div_eq_iff hd]
    simp only [hD]
    linear_combination besselSqMellin s * hL
  · exact ((differentiableAt_id.sub_const _).mul (hu_d s (by linarith) hs hi)).div (hDd s) (hDne s hs1)
  · filter_upwards [hu_n, nhdsWithin_le_nhds hD_ev] with s h1 h2'
    exact ((differentiableAt_id.sub_const _).mul h1).div (hDd s) h2'
  · have hDt : Tendsto D (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (D (4 / 3))) :=
      ((hDd _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hval : P.twistUnitResidue = P.twistLimit / 2 / D (4 / 3) := by
      simp only [twistUnitResidue, hD]
    rw [hval]
    refine (hu_l.div hDt hD0).congr fun s => ?_
    simp only [Pi.div_apply]
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
