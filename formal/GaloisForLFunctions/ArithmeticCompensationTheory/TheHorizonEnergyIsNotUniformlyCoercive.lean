import GaloisForLFunctions.ArithmeticCompensationTheory.TheTranslationLawHasAnInverseSquareDeficit

/-!
# The horizon energy is not uniformly coercive

Every nonzero test has positive horizon energy (`horizonEnergy_pos`), and on Lipschitz tests of a
fixed aperture `J(F) ≥ A_F(0) − Λ²(8R + 48)` (`horizonEnergy_ge_of_lipschitz`). Over the whole test
class there is no coercive constant:

* `horizonEnergy_concentratedTest_le`: the concentrated tests `F_λ(x) = √λ φ(λx)` keep their mass
  (`integral_concentratedTest_sq`) and have `J(F_λ) ≤ (2λ)^{−1} ∫_{v>0} |A_φ(v)| dv`, since
  `A_{F_λ}(u) = A_φ(λu)` (`autoCorr_concentratedTest`) and the horizon density is at most `½`;
* `not_exists_horizonEnergy_ge`: **no `c > 0` has `J(F) ≥ c ∫F²` for every test**;
* `exists_combEnergy_le_mul`: hence for every `c > 0` some test of unit mass has raw comb energy
  `E_r(F) ≤ c S_r² ∫F²` at every large aperture.

The integer comb shifts by the dense set `{log p}`, and its horizon law is the resolvent of the
unbounded operator `1 + 2∂`, which a narrow bump defeats. A curve comb shifts by the lattice
`ℕ log q`, and its comb is uniformly coercive, `‖C_D F‖² ≥ (q^D/12) ∫F²`
(`exists_curveCombEnergy_ge`). Uniform coercivity is therefore not a property the horizon law can
supply over the integers: a coercive estimate must come from a restricted test class (aperture,
smoothness) or from the arithmetic of the pairing, not from the comb alone.
-/

open Filter Topology Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The concentrated test `F_λ(x) = √λ φ(λx)`: the profile `φ` squeezed to width `1/λ`, mass kept. -/
def concentratedTest (φ : ℝ → ℝ) (lam : ℝ) (x : ℝ) : ℝ := Real.sqrt lam * φ (lam * x)

theorem continuous_concentratedTest {φ : ℝ → ℝ} (hφ : Continuous φ) (lam : ℝ) :
    Continuous (concentratedTest φ lam) :=
  continuous_const.mul (hφ.comp (continuous_const.mul continuous_id))

theorem hasCompactSupport_concentratedTest {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) {lam : ℝ}
    (hlam : 0 < lam) : HasCompactSupport (concentratedTest φ lam) :=
  (hφc.comp_homeomorph (Homeomorph.mulLeft₀ lam hlam.ne')).mul_left

/-- The concentrated test keeps the mass: `∫F_λ² = ∫φ²`. -/
theorem integral_concentratedTest_sq (φ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ∫ x, concentratedTest φ lam x ^ 2 = ∫ x, φ x ^ 2 := by
  have hpt : ∀ x, concentratedTest φ lam x ^ 2 = lam * (fun y => φ y ^ 2) (lam * x) := fun x => by
    simp only [concentratedTest, mul_pow, Real.sq_sqrt hlam.le]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hlam), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hlam.ne', one_mul]

/-- The concentrated test rescales the autocorrelation: `A_{F_λ}(u) = A_φ(λu)`. -/
theorem autoCorr_concentratedTest (φ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    autoCorr (concentratedTest φ lam) u = autoCorr φ (lam * u) := by
  have hpt : ∀ x, concentratedTest φ lam x * concentratedTest φ lam (x + u) =
      lam * (fun y => φ y * φ (y + lam * u)) (lam * x) := fun x => by
    simp only [concentratedTest]
    rw [show lam * (x + u) = lam * x + lam * u by ring]
    have := Real.mul_self_sqrt hlam.le
    linear_combination (φ (lam * x) * φ (lam * x + lam * u)) * this
  rw [autoCorr, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hlam), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hlam.ne', one_mul, autoCorr]

/-- **Concentration kills the horizon energy.** `J(F_λ) ≤ (2λ)^{−1} ∫_{v>0} |A_φ(v)| dv`. -/
theorem horizonEnergy_concentratedTest_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {lam : ℝ} (hlam : 0 < lam) :
    horizonEnergy (concentratedTest φ lam) ≤ (∫ v in Ioi (0 : ℝ), |autoCorr φ v|) / (2 * lam) := by
  have hF := continuous_concentratedTest hφ lam
  have hFc := hasCompactSupport_concentratedTest hφc hlam
  have hA := continuous_autoCorr hφ hφc
  have hAc := hasCompactSupport_autoCorr hφc
  have hAbF : ∀ t, |autoCorr (concentratedTest φ lam) t| ≤ autoCorr (concentratedTest φ lam) 0 :=
    abs_autoCorr_le_autoCorr_zero hF hFc
  rw [horizonEnergy_eq_horizonIntegral_autoCorr hF hFc, horizonIntegral]
  -- the majorant `|A_φ(λu)|/2`
  have hgi : Integrable fun u => |autoCorr φ (lam * u)| / 2 := by
    have hcs : HasCompactSupport fun u => autoCorr φ (lam * u) :=
      hAc.comp_homeomorph (Homeomorph.mulLeft₀ lam hlam.ne')
    exact ((hA.comp (continuous_const.mul continuous_id)).abs.div_const 2).integrable_of_hasCompactSupport
      ((hcs.comp_left (g := fun y : ℝ => |y|) abs_zero).comp_left (g := fun y : ℝ => y / 2)
        (zero_div 2))
  have hle : (∫ u in Ioi (0 : ℝ), autoCorr (concentratedTest φ lam) u * horizonDensity u) ≤
      ∫ u in Ioi (0 : ℝ), |autoCorr φ (lam * u)| / 2 := by
    refine setIntegral_mono_on (integrableOn_mul_horizonDensity (continuous_autoCorr hF hFc)
      hAbF 0) hgi.integrableOn measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [autoCorr_concentratedTest φ hlam u]
    have hρ0 := horizonDensity_nonneg u
    have hρ : horizonDensity u ≤ 1 / 2 := by
      simp only [horizonDensity]
      have : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    calc autoCorr φ (lam * u) * horizonDensity u ≤ |autoCorr φ (lam * u)| * horizonDensity u :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hρ0
      _ ≤ |autoCorr φ (lam * u)| * (1 / 2) := mul_le_mul_of_nonneg_left hρ (abs_nonneg _)
      _ = |autoCorr φ (lam * u)| / 2 := by ring
  have hsub := integral_comp_mul_left_Ioi (fun v => |autoCorr φ v| / 2) 0 hlam
  simp only [mul_zero, smul_eq_mul] at hsub
  refine hle.trans (le_of_eq ?_)
  rw [hsub, integral_div]
  field_simp

/-- **The horizon energy is not uniformly coercive.** No `c > 0` satisfies `c ∫F² ≤ J(F)` for every
continuous compactly supported test. -/
theorem not_exists_horizonEnergy_ge :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ F : ℝ → ℝ, Continuous F → HasCompactSupport F →
      c * ∫ x, F x ^ 2 ≤ horizonEnergy F := by
  rintro ⟨c, hc, h⟩
  -- the profile `oddBump`, of positive mass
  have hφ := continuous_oddBump
  have hφc := hasCompactSupport_oddBump
  have hmass : 0 < ∫ x, oddBump x ^ 2 := by
    have := autoCorr_oddBump_zero_pos
    simpa [autoCorr, sq] using this
  set K := ∫ v in Ioi (0 : ℝ), |autoCorr oddBump v|
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  -- choose `λ` with `K/(2λ) < c ∫φ²`
  set lam := K / (c * ∫ x, oddBump x ^ 2) + 1
  have hlam : 0 < lam := by positivity
  have hJ := horizonEnergy_concentratedTest_le hφ hφc hlam
  have hlow := h _ (continuous_concentratedTest hφ lam) (hasCompactSupport_concentratedTest hφc hlam)
  rw [integral_concentratedTest_sq oddBump hlam] at hlow
  have hcm : 0 < c * ∫ x, oddBump x ^ 2 := mul_pos hc hmass
  have hkey : K / (2 * lam) < c * ∫ x, oddBump x ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have : K < c * (∫ x, oddBump x ^ 2) * lam := by
      simp only [lam]
      rw [mul_add, mul_div_cancel₀ _ hcm.ne', mul_one]
      linarith
    nlinarith
  linarith

/-- **The raw integer comb is not uniformly coercive.** For every `c > 0` there is a continuous
compactly supported test of positive mass with `E_r(F) ≤ c S_r² ∫F²` for all large apertures. -/
theorem exists_combEnergy_le_mul {c : ℝ} (hc : 0 < c) :
    ∃ F : ℝ → ℝ, Continuous F ∧ HasCompactSupport F ∧ 0 < ∫ x, F x ^ 2 ∧
      ∀ᶠ r in atTop, combEnergy F (combPrimes r) combWeight ≤ c * combMass r ^ 2 * ∫ x, F x ^ 2 := by
  have hφ := continuous_oddBump
  have hφc := hasCompactSupport_oddBump
  have hmass : 0 < ∫ x, oddBump x ^ 2 := by
    have := autoCorr_oddBump_zero_pos
    simpa [autoCorr, sq] using this
  set K := ∫ v in Ioi (0 : ℝ), |autoCorr oddBump v|
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  set lam := K / (c * ∫ x, oddBump x ^ 2) + 1
  have hlam : 0 < lam := by positivity
  set F := concentratedTest oddBump lam
  have hF := continuous_concentratedTest hφ lam
  have hFc := hasCompactSupport_concentratedTest hφc hlam
  have hFm : ∫ x, F x ^ 2 = ∫ x, oddBump x ^ 2 := integral_concentratedTest_sq oddBump hlam
  have hcm : 0 < c * ∫ x, oddBump x ^ 2 := mul_pos hc hmass
  have hJ : horizonEnergy F < c * ∫ x, F x ^ 2 := by
    refine (horizonEnergy_concentratedTest_le hφ hφc hlam).trans_lt ?_
    rw [hFm, div_lt_iff₀ (by positivity)]
    have : K < c * (∫ x, oddBump x ^ 2) * lam := by
      simp only [lam]
      rw [mul_add, mul_div_cancel₀ _ hcm.ne', mul_one]
      linarith
    nlinarith
  refine ⟨F, hF, hFc, hFm ▸ hmass, ?_⟩
  filter_upwards [(tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc).eventually
    (eventually_le_nhds hJ), eventually_combMass_pos] with r hr hS
  rw [div_le_iff₀ (by positivity)] at hr
  linarith

end GaloisForLFunctions.ArithmeticCompensationTheory
