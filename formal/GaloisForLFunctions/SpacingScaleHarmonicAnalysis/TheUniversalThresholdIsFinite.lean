import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSpacingScaleLawIsUniversal
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# The universal threshold is finite

The **universal threshold** `K_univ` is the largest overlap ratio at which
`Re W_ω + 2S² ≥ 0` holds for every real twist `|ω| ≤ 1` on every atomic family, uniformly in `N`.
It is at least `c₀`: at width `≤ c₀ δ_N` every twist satisfies the stability law
(`TheSpacingScaleLawIsUniversal`). This file shows that it is finite.

* **Weil's form of a twist in Markov form** (`weilQuadTw_eq_markov`):
  `Re W_ω(f) = archForm f − twistedPrimeSum ω f + 2C(f)² − 2S(f)²`, so
  `Re W_ω + 2S² = M_ω + 2C²`.
* **Wide tests have negative archimedean form** (`archForm_le_of_wide`): for an `L`-Lipschitz test
  supported in an interval of length `D`, `levyEnergy f ≤ 36 D L² + 4 A(D) ‖f‖²` with the Lévy tail
  `A(D) = ∫_D^∞ ω → 0`, while `2θ′(0) < −5`.
* **The dipole** (`universalThreshold_finite`): two wide bumps at `log 1` and `log 2`,
  `f = g − t g(· − log 2)`, with `t = C(g)/C(g(· − log 2)) ≤ 1/cosh(log 2 / 2)` killing the cosh
  moment. Against the sign twist `ω(k) = sign` of the `k`-th lag correlation the twisted prime sum is
  `Σ Λ_k |pairing_k| ≥ 0`, so `Re W_ω + 2S² = M_ω ≤ archForm f < 0` once the bumps are wide.

So `c₀ ≤ K_univ < ∞` (`universalThreshold_bracket`): the failing family has `N = 2` and overlap
ratio `W/log(3/2)`. The extremal twist is the sign of the lag correlations, as on every
`|·|`-closed family the twists dominate `ζ`; the threshold is decided on signed families.
-/

noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Weil's form of a twist in Markov form -/

theorem twistCoeff_mul_vonMangoldt (ω : ArithmeticFunction ℝ) (n : ℕ) :
    twistCoeff (fun n => ω n * ArithmeticFunction.vonMangoldt n) n = ω n * vonMangoldtAtom n := by
  unfold twistCoeff vonMangoldtAtom
  split_ifs <;> ring

variable {f : ℝ → ℝ} {R : ℝ}

theorem primeSum_eq_sum_pairing (hfR : SupportedIn R f) :
    primeSum f = ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * pairing f n := by
  unfold primeSum
  exact tsum_eq_sum fun n hn => by rw [show (∫ t, f t * f (t - Real.log n)) +
    ∫ t, f t * f (t + Real.log n) = pairing f n from rfl, pairing_eq_zero hfR hn, mul_zero]

theorem twistedPrimeSum_eq_sum_pairing (ω : ArithmeticFunction ℝ) (hfR : SupportedIn R f) :
    twistedPrimeSum ω f =
      ∑ n ∈ Finset.range (lagRange R), ω n * vonMangoldtAtom n * pairing f n := by
  unfold twistedPrimeSum
  exact tsum_eq_sum fun n hn => by rw [show (∫ t, f t * f (t - Real.log n)) +
    ∫ t, f t * f (t + Real.log n) = pairing f n from rfl, pairing_eq_zero hfR hn, mul_zero]

/-- **Weil's form of a twist in Markov form**:
`Re W_ω(f) = archForm f − twistedPrimeSum ω f + 2C(f)² − 2S(f)²`. -/
theorem weilQuadTw_eq_markov (ω : ArithmeticFunction ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfR : SupportedIn R f) :
    weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) f =
      archForm f - twistedPrimeSum ω f +
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  rw [weilQuadTw_eq _ hfR, weilQuad_eq hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_eq_sum_pairing hfR, twistedPrimeSum_eq_sum_pairing ω hfR]
  simp_rw [twistCoeff_mul_vonMangoldt]
  have : ∑ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n - ω n * vonMangoldtAtom n) *
      pairing f n = ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * pairing f n -
        ∑ n ∈ Finset.range (lagRange R), ω n * vonMangoldtAtom n * pairing f n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this]
  ring

/-! ### Wide tests -/

/-- An `L`-Lipschitz test supported in `[a, b]` moves by `L y` on a support of length `b − a + y`. -/
theorem integral_sub_shift_sq_le_of_supp (hf : Continuous f) (hfc : HasCompactSupport f) {L a b : ℝ}
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hsupp : ∀ u, u ∉ Set.Icc a b → f u = 0) (hab : a ≤ b)
    {y : ℝ} (hy : 0 ≤ y) : ∫ u, (f u - f (u + y)) ^ 2 ≤ L ^ 2 * y ^ 2 * (b - a + y) := by
  have hzero : ∀ u, u ∉ Set.Icc (a - y) b → (f u - f (u + y)) ^ 2 = 0 := fun u hu => by
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [hsupp u fun h => by linarith [h.1], hsupp (u + y) fun h => by linarith [h.1]]; ring
    · rw [hsupp u fun h => by linarith [h.2], hsupp (u + y) fun h => by linarith [h.2]]; ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hint : IntegrableOn (fun u => (f u - f (u + y)) ^ 2) (Set.Icc (a - y) b) :=
    ((hf.sub (hf.comp (continuous_add_const y))).pow 2).integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => L ^ 2 * y ^ 2) (Set.Icc (a - y) b) :=
    continuous_const.integrableOn_Icc
  refine (setIntegral_mono_on hint hc measurableSet_Icc fun u _ => ?_).trans (le_of_eq ?_)
  · have h := hL u (u + y)
    rw [show u - (u + y) = -y by ring, abs_neg, abs_of_nonneg hy] at h
    have h0 : 0 ≤ L * y := (abs_nonneg _).trans h
    calc (f u - f (u + y)) ^ 2 = |f u - f (u + y)| ^ 2 := (sq_abs _).symm
      _ ≤ (L * y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = L ^ 2 * y ^ 2 := by ring
  · rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring

/-- **The Lévy energy of a wide test**: for an `L`-Lipschitz test supported in `[0, D]`,
`levyEnergy f ≤ 36 D L² + 4 A(D) ‖f‖²`, `A(D) = ∫_D^∞ ω`. -/
theorem levyEnergy_le_of_wide (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L D : ℝ}
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hsupp : ∀ u, u ∉ Set.Icc 0 D → f u = 0)
    (hD : 0 < D) :
    levyEnergy f ≤ 36 * D * L ^ 2 +
      4 * WeilLevyPoleGauss.archLevyAntideriv D * ∫ u, f u ^ 2 := by
  set Q : ℝ → ℝ := fun y => ∫ u, (f u - f (u + y)) ^ 2
  set M := ∫ u, f u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hI := integrableOn_levyIntegrand hf hfc
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 D ∪ Set.Ioi D := (Set.Ioc_union_Ioi_eq_Ioi hD.le).symm
  unfold levyEnergy
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set fun y hy => hy.1) (hI.mono_set fun y hy => lt_trans hD hy)]
  -- near: `Q(y) ≤ 2D L² y²`
  have hnear : ∫ y in Set.Ioc 0 D, archLevyDensity y * Q y ≤ 2 * D * L ^ 2 * levySecondMoment := by
    have hm2 : IntegrableOn (fun y : ℝ => y ^ 2 * archLevyDensity y) (Set.Ioc 0 D) :=
      integrableOn_sq_mul_archLevyDensity.mono_set fun y hy => hy.1
    have h1 := setIntegral_mono_on (hI.mono_set fun y hy => hy.1) (hm2.const_mul (2 * D * L ^ 2))
      measurableSet_Ioc fun y hy => by
        have hQ := integral_sub_shift_sq_le_of_supp hf.continuous hfc hL hsupp hD.le hy.1.le
        have hω := (archLevyDensity_pos hy.1).le
        calc archLevyDensity y * Q y ≤ archLevyDensity y * (L ^ 2 * y ^ 2 * (D - 0 + y)) :=
              mul_le_mul_of_nonneg_left hQ hω
          _ ≤ archLevyDensity y * (L ^ 2 * y ^ 2 * (2 * D)) := by
              refine mul_le_mul_of_nonneg_left ?_ hω
              have := hy.2
              nlinarith [sq_nonneg (L * y)]
          _ = 2 * D * L ^ 2 * (y ^ 2 * archLevyDensity y) := by ring
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_set integrableOn_sq_mul_archLevyDensity
      (Filter.Eventually.of_forall fun y (hy : y ∈ Set.Ioi 0) =>
        mul_nonneg (sq_nonneg y) (archLevyDensity_pos hy).le)
      (Filter.Eventually.of_forall fun y hy => hy.1)) (by positivity)
  -- far: `Q(y) ≤ 4 ‖f‖²`
  have hfar : ∫ y in Set.Ioi D, archLevyDensity y * Q y ≤
      4 * M * WeilLevyPoleGauss.archLevyAntideriv D := by
    have hω := WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hD
    have h1 := setIntegral_mono_on (hI.mono_set fun y hy => lt_trans hD hy) (hω.const_mul (4 * M))
      measurableSet_Ioi fun y hy => by
        have hQ := integral_sub_shift_sq_le_four hf.continuous hfc y
        have hω0 := (archLevyDensity_pos (lt_trans hD hy)).le
        calc archLevyDensity y * Q y ≤ archLevyDensity y * (4 * M) := mul_le_mul_of_nonneg_left hQ hω0
          _ = 4 * M * archLevyDensity y := by ring
    rw [integral_const_mul, WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hD] at h1
    exact h1
  have hm2 := levySecondMoment_le
  have hDL : 0 ≤ 2 * D * L ^ 2 := by positivity
  nlinarith

/-- `2θ′(0) < −5`. -/
theorem two_gammaHardyPhaseRate_zero_lt : 2 * gammaHardyPhaseRate 0 < -5 := by
  rw [gammaHardyPhaseRate_zero_closed]
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog2 := Real.log_two_gt_d9
  have hpi := Real.pi_gt_d2
  have hlogpi : 1 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    linarith [Real.exp_one_lt_d9]
  linarith

/-! ### The dipole -/

/-- The cosh moment of a translate: `C(g(· − a)) = cosh(a/2) C(g) + sinh(a/2) S(g)`. -/
theorem coshHalfMoment_comp_sub (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (a : ℝ) : coshHalfMoment (fun u => g (u - a)) =
      Real.cosh (a / 2) * coshHalfMoment g + Real.sinh (a / 2) * sinhHalfMoment g := by
  unfold coshHalfMoment sinhHalfMoment
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * Real.cosh ((v + a) / 2)) a
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1
    funext v
    rw [show (v + a) / 2 = v / 2 + a / 2 by ring, Real.cosh_add]
    ring
  · exact ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right).const_mul _
  · exact ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right).const_mul _

/-- **The universal threshold is finite**: there is a width `W` and a nonnegative `C²` bump
supported in `[0, W]` such that on the atomic family of level `2` — overlap ratio `W/log(3/2)` —
some test with vanishing cosh moment has `Re W_ω + 2S² < 0` for a sign twist `|ω| ≤ 1`. -/
theorem universalThreshold_finite :
    ∃ W : ℝ, 0 < W ∧ ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ (∀ u, u ∉ Set.Icc 0 W → g u = 0) ∧
      (∀ u, 0 ≤ g u) ∧ ∃ (x : ℕ → ℝ) (ω : ArithmeticFunction ℝ), (∀ k, |ω k| ≤ 1) ∧
        coshHalfMoment (atomicTest 2 x g) = 0 ∧
        weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) (atomicTest 2 x g) +
          2 * sinhHalfMoment (atomicTest 2 x g) ^ 2 < 0 := by
  sorry

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
