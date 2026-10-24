import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGoldenCurveIsABeurlingSystem
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve

/-!
# The selectivity battery of orientation

Every identity of §3.1–3.2 of the programme holds on every scaling datum: Lefschetz, adjunction,
pullback, the Lefschetz–adjunction identity, the Rosati adjoint and `π π′ = q`. The battery shows
that none of them, and none of the arithmetic data that the golden curve shares with a curve,
orients a cycle; and it shows what orientation does not depend on.

* **Curve configurations are symmetric under the functional equation**
  (`fesSymmetric_curveConfig`): `q^{½ − ρ} = β_i⁻¹ = β_{fe(i)}`.
* **Unitary curves orient every cycle** (`unitaryCurve_orbitHodgeIndex`): their zeros lie on the line.
* **The golden curve orients no generic cycle** (`golden_orbitCorr_rate_iff`,
  `golden_not_oriented`). The golden datum `1 − 5X + 5X²` has an integral zeta series, integral
  point counts from a Beurling system with nonnegative prime counts, and the functional equation
  (`goldenDatum_beurling_not_pure`); all its zeros have depth exactly `log φ/log 5`, and the orbit
  correlation of a generic real test grows like `e^{σ t}` iff `σ ≥ log φ/log 5`
  (`golden_soft_structure_and_disorientation`).
* **Orientation is blind to multiplicity** (`blindAbove_congr_carrier`,
  `orientation_congr_carrier`). Which cycles are oriented, and at which rate, depends only on the set
  of zeros, never on their multiplicities: two symmetric configurations with the same zeros orient
  the same cycles. An anti-collapse principle bounding off-line multiplicity therefore plays no
  role in orientation; it enters only mass floors, where multiplicity is mass.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

/-! ### Curves -/

section Curves

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

theorem CurveDatum.cpow_one_sub_sub_half {ρ : ℂ} :
    (D.q : ℂ) ^ ((1 - ρ) - 1 / 2) = ((D.q : ℂ) ^ (ρ - 1 / 2))⁻¹ := by
  rw [show (1 - ρ) - 1 / 2 = -(ρ - 1 / 2) by ring, Complex.cpow_neg]

/-- **Curve configurations are symmetric under the functional equation.** -/
theorem fesSymmetric_curveConfig : FESymmetric (D.curveConfig hD) := by
  intro ρ hρ
  obtain ⟨i, hi⟩ := (D.mem_curveConfig_iff hD).mp hρ
  have hfe : D.β (D.fePerm i) = (D.β i)⁻¹ := eq_inv_of_mul_eq_one_left (D.β_fePerm i)
  refine ⟨(D.mem_curveConfig_iff hD).mpr ⟨D.fePerm i, ?_⟩, ?_⟩
  · rw [D.cpow_one_sub_sub_half, hi, hfe]
  · show (univ.filter fun j => (D.q : ℂ) ^ ((1 - ρ) - 1 / 2) = D.β j).card =
      (univ.filter fun j => (D.q : ℂ) ^ (ρ - 1 / 2) = D.β j).card
    rw [D.cpow_one_sub_sub_half]
    refine Finset.card_bij (fun j _ => D.fePerm j) (fun j hj => ?_)
      (fun _ _ _ _ h => D.fePerm.injective h) (fun j hj => ⟨D.fePerm.symm j, ?_, by simp⟩)
    · have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left (D.β_fePerm j), ← hj', inv_inv]
    · have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 := D.β_fePerm (D.fePerm.symm j)
      rw [Equiv.apply_symm_apply] at h1
      rw [← hj'] at h1
      rw [inv_eq_of_mul_eq_one_left h1]

/-- The zeros of a unitary curve lie on the critical line. -/
theorem curveConfig_onLine_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) :
    ∀ ρ ∈ (D.curveConfig hD).carrier, ρ.re = 1 / 2 := by
  rintro _ ⟨⟨i, k⟩, rfl⟩
  rw [CurveDatum.re_zetaZero, hU i, Real.log_one, zero_div, add_zero]

/-- **Unitary curves orient every cycle.** -/
theorem unitaryCurve_orbitHodgeIndex (hU : ∀ i, ‖D.β i‖ = 1) (x : ScalingCycle) :
    (configScalingDatum _ (D.temperedConfig_curveConfig hD)).OrbitHodgeIndex x :=
  (configScalingDatum _ (D.temperedConfig_curveConfig hD)).orbitHodgeIndex_of_hodgeIndex
    (configSurface_hodgeIndex_of_onLine _ _ (curveConfig_onLine_of_unitary D hD hU)) x

end Curves

/-! ### The golden curve -/

/-- The zeros of the golden curve. -/
abbrev goldenConfig : ZeroConfig := goldenDatum.curveConfig goldenDatum_strip

theorem temperedConfig_goldenConfig : TemperedConfig goldenConfig :=
  goldenDatum.temperedConfig_curveConfig goldenDatum_strip

theorem fesSymmetric_goldenConfig : FESymmetric goldenConfig :=
  fesSymmetric_curveConfig goldenDatum goldenDatum_strip

/-- The depth `log φ / log 5` of the golden zeros. -/
def goldenDepth : ℝ := Real.log goldenRatio / Real.log 5

theorem goldenDepth_pos : 0 < goldenDepth :=
  div_pos (Real.log_pos Real.one_lt_goldenRatio) (Real.log_pos (by norm_num))

/-- **Every golden zero has depth exactly `log φ / log 5`.** -/
theorem abs_re_sub_half_goldenConfig {ρ : ℂ} (hρ : ρ ∈ goldenConfig.carrier) :
    |ρ.re - 1 / 2| = goldenDepth := by
  obtain ⟨⟨i, k⟩, rfl⟩ := hρ
  rw [CurveDatum.re_zetaZero, add_sub_cancel_left]
  have hq : goldenDatum.q = 5 := rfl
  have hl : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [hq, goldenDepth]
  fin_cases i
  · show |Real.log ‖((goldenRatio : ℝ) : ℂ)‖ / Real.log 5| = _
    rw [Complex.norm_real, Real.norm_of_nonneg Real.goldenRatio_pos.le,
      abs_of_pos (div_pos (Real.log_pos Real.one_lt_goldenRatio) hl)]
  · show |Real.log ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ / Real.log 5| = _
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr Real.goldenRatio_pos).le,
      Real.log_inv, neg_div, abs_neg,
      abs_of_pos (div_pos (Real.log_pos Real.one_lt_goldenRatio) hl)]

/-- **The orientation rate of a generic cycle of the golden curve is `log φ / log 5`.** -/
theorem golden_orbitCorr_rate_iff (x : ScalingCycle) (hgen : RealSpectrallyGeneric goldenConfig x.2.2)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |(configScalingDatum goldenConfig temperedConfig_goldenConfig).orbitCorr x t| ≤
        K * Real.exp (σ * t)) ↔ goldenDepth ≤ σ := by
  rw [orbitCorr_rate_iff_blindAbove _ _ fesSymmetric_goldenConfig hσ x,
    blindAbove_iff_of_generic _ hgen]
  constructor
  · intro h
    have hmem : goldenDatum.zetaZero 0 0 ∈ goldenConfig.carrier := ⟨⟨0, 0⟩, rfl⟩
    rw [← abs_re_sub_half_goldenConfig hmem]
    exact h _ hmem
  · intro h ρ hρ
    rw [abs_re_sub_half_goldenConfig hρ]
    exact h

/-- **The golden curve orients no generic cycle.** -/
theorem golden_not_oriented (x : ScalingCycle) (hgen : RealSpectrallyGeneric goldenConfig x.2.2) :
    ¬ ∀ t : ℝ, (configScalingDatum goldenConfig temperedConfig_goldenConfig).HasseWeilAt x t := by
  intro h
  have hb := (orientation_tfae goldenConfig temperedConfig_goldenConfig fesSymmetric_goldenConfig
    x).out 0 2 |>.mp h
  have hon := (onLine_iff_blindOffLine_of_generic _ hgen).mp hb
  have hmem : goldenDatum.zetaZero 0 0 ∈ goldenConfig.carrier := ⟨⟨0, 0⟩, rfl⟩
  have hd := abs_re_sub_half_goldenConfig hmem
  rw [hon _ hmem, sub_self, abs_zero] at hd
  exact goldenDepth_pos.ne hd

/-- **Soft structure does not orient.** The golden curve has a Beurling system with nonnegative
prime counts, an integral zeta series and the functional equation, and is impure; its configuration
is a scaling datum (so it has Lefschetz numbers, adjunction, pullback and `ππ′ = q`); and the orbit of
a generic real test is not oriented, with orientation rate `log φ / log 5`. -/
theorem golden_soft_structure_and_disorientation :
    ((∃ π : ℕ → ℕ, ∀ k, 1 ≤ k → goldenDatum.pointCount k = ∑ d ∈ k.divisors, (d : ℝ) * π d) ∧
      (∃ Zℤ : PowerSeries ℤ, PowerSeries.constantCoeff Zℤ = 1 ∧
        PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
      (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
      ¬ ∀ i, ‖goldenDatum.β i‖ = 1) ∧
    ∃ x : ScalingCycle,
      (¬ ∀ t : ℝ, (configScalingDatum goldenConfig temperedConfig_goldenConfig).HasseWeilAt x t) ∧
      ∀ σ : ℝ, 0 ≤ σ → ((∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
        |(configScalingDatum goldenConfig temperedConfig_goldenConfig).orbitCorr x t| ≤
          K * Real.exp (σ * t)) ↔ goldenDepth ≤ σ) := by
  refine ⟨goldenDatum_beurling_not_pure, ?_⟩
  obtain ⟨f, hf, hgen⟩ := exists_realSpectrallyGeneric goldenConfig
  exact ⟨(0, 0, ⟨f, hf⟩), golden_not_oriented _ hgen,
    fun σ hσ => golden_orbitCorr_rate_iff _ hgen hσ⟩

/-! ### Orientation does not see multiplicity -/

/-- Blindness depends only on the set of zeros. -/
theorem blindAbove_congr_carrier {Z Z' : ZeroConfig} (h : Z.carrier = Z'.carrier) (σ : ℝ)
    (f : ℝ → ℝ) : BlindAbove Z σ f ↔ BlindAbove Z' σ f := by
  unfold BlindAbove
  rw [h]

/-- **Orientation is blind to multiplicity.** Two symmetric tempered configurations with the same
zeros, whatever their multiplicities, orient exactly the same cycles. -/
theorem orientation_congr_carrier {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hFE : FESymmetric Z) (hFE' : FESymmetric Z')
    (h : Z.carrier = Z'.carrier) (x : ScalingCycle) :
    (∀ t : ℝ, (configScalingDatum Z hZ).HasseWeilAt x t) ↔
      ∀ t : ℝ, (configScalingDatum Z' hZ').HasseWeilAt x t := by
  rw [(orientation_tfae Z hZ hFE x).out 0 2, (orientation_tfae Z' hZ' hFE' x).out 0 2,
    ← blindAbove_zero_iff, ← blindAbove_zero_iff, blindAbove_congr_carrier h]

/-- The orientation rate is blind to multiplicity as well. -/
theorem orientationRate_congr_carrier {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hFE : FESymmetric Z) (hFE' : FESymmetric Z')
    (h : Z.carrier = Z'.carrier) {σ : ℝ} (hσ : 0 ≤ σ) (x : ScalingCycle) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t)) ↔
      ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
        |(configScalingDatum Z' hZ').orbitCorr x t| ≤ K * Real.exp (σ * t) := by
  rw [orbitCorr_rate_iff_blindAbove Z hZ hFE hσ, orbitCorr_rate_iff_blindAbove Z' hZ' hFE' hσ,
    blindAbove_congr_carrier h]

end GaloisForLFunctions.ArithmeticOrientationGeometry
