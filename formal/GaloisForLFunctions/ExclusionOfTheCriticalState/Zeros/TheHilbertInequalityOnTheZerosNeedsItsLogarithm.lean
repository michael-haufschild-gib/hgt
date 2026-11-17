import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSumOfAProfileConvergesAfterOneSubtraction
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower
import GaloisForLFunctions.RHTower.XiHeatMomentSmallTimePositivity

/-!
# The Hilbert inequality on the zeros needs its logarithm

By (★) the transform of the critical state is the Cauchy transform `Σ_z c_z/(w + 8 − z)` of its
square-summable zero values; a space in which (★) is a reproducing formula would need the synthesis
map `c ↦ Σ_z c_z/(σ + it − z)` to be bounded from `ℓ²` to `L²(dt)` on lines right of the zeros. ECS
proves the bound with the weight `1/log(|t| + 4)`
(`integrable_and_integral_norm_sq_tsum_zeroCauchy_le`), and the weight cannot be removed.

* **Clusters** (`exists_zeroCluster_lintegral_gt`). By the Riemann–von Mangoldt count some window
  `(T − h, T + h]` of fixed width contains at least `log T` zero copies
  (`exists_xiZeroCount_window_ge_log`, `exists_finset_xiZeroCopy_window`). On `Re s = σ ≥ 1` every
  Cauchy kernel of such a zero has real part at least `c₁ = ½/((σ + ½)² + 4h²)` for `t` in the window
  (`re_inv_cauchyKernel_ge`), so with `c = 1` on the cluster of `n` zeros
  `∫ |Σ_z c_z/(σ + it − z)|² dt ≥ 2h c₁² n² = 2h c₁² n · Σ |c_z|²`.
* **No unweighted inequality** (`not_exists_zeroHilbert_without_log`): for `σ ≥ 1` no constant `K`
  gives `∫ |Σ_z c_z/(σ + it − z)|² dt ≤ K Σ |c_z|²` for all finitely supported `c`.

The first alternative of the tool E-T4 (a Hilbert inequality on the zeros without the logarithmic
weight) is therefore false; removing the logarithm from the decay side needs regularity of the zero
values of the state, not of the zeros.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- On `Re s = σ ≥ 1`, within `2h` of the ordinate of a zero, its Cauchy kernel has real part at
least `½/((σ + ½)² + 4h²)`. -/
theorem re_inv_cauchyKernel_ge {σ h t : ℝ} (hσ : 1 ≤ σ) {q : XiZeroCopy}
    (ht : |t - (centredZero q).im| ≤ 2 * h) :
    1 / 2 / ((σ + 1 / 2) ^ 2 + (2 * h) ^ 2) ≤ (((σ : ℂ) + t * I - centredZero q)⁻¹).re := by
  have hx := abs_lt.mp (abs_re_centredZero_lt q)
  set x := (centredZero q).re
  set y := (centredZero q).im
  have hre : ((σ : ℂ) + t * I - centredZero q).re = σ - x := by simp [x]
  have him : ((σ : ℂ) + t * I - centredZero q).im = t - y := by simp [y]
  rw [Complex.inv_re, Complex.normSq_apply, hre, him]
  have h1 : 1 / 2 ≤ σ - x := by linarith
  have h2 : σ - x ≤ σ + 1 / 2 := by linarith
  have hh : 0 ≤ 2 * h := (abs_nonneg _).trans ht
  have h3 : (t - y) ^ 2 ≤ (2 * h) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have k1 : (σ - x) ^ 2 ≤ (σ + 1 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  have k2 : 1 / 2 * (σ + 1 / 2) ^ 2 ≤ (σ - x) * (σ + 1 / 2) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have k3 : 1 / 2 * (2 * h) ^ 2 ≤ (σ - x) * (2 * h) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hpos : 0 < (σ - x) * (σ - x) + (t - y) * (t - y) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith [k1, k2, k3, h3]

/-- **Clusters of zeros defeat every unweighted Hilbert constant.** For `σ ≥ 1` and every `K` some
finite set `P` of zero copies has `∫ |Σ_{z ∈ P} 1/(σ + it − z)|² dt > K · #P`. -/
theorem exists_zeroCluster_lintegral_gt {σ : ℝ} (hσ : 1 ≤ σ) (K : ℝ) :
    ∃ P : Finset XiZeroCopy, ENNReal.ofReal (K * P.card) <
      ∫⁻ t : ℝ, ENNReal.ofReal (‖∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹‖ ^ 2) := by
  obtain ⟨h, hh, T₁, hT₁, hwin⟩ := exists_xiZeroCount_window_ge_log
  set c₁ : ℝ := 1 / 2 / ((σ + 1 / 2) ^ 2 + (2 * h) ^ 2)
  have hc₁ : 0 < c₁ := by positivity
  obtain ⟨T, hTK, hTge⟩ := ((Real.tendsto_log_atTop.eventually_gt_atTop
    (K / (2 * h * c₁ ^ 2))).and (eventually_ge_atTop (max T₁ (h + 1)))).exists
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hTge
  have hTh : 0 ≤ T - h := by linarith [le_max_right T₁ (h + 1)]
  obtain ⟨P, hP, hcard⟩ := exists_finset_xiZeroCopy_window hTh hh.le
  have hcardT : Real.log T ≤ P.card := (hwin T hTT₁).trans hcard
  have hlog1 : 1 < Real.log T := by
    have h4 : (4 : ℝ) ≤ T := hT₁.trans hTT₁
    have : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) h4
    have h4e : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have : 1 < Real.log 4 := by rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact h4e
    linarith
  have hn : (0 : ℝ) < P.card := by linarith
  refine ⟨P, ?_⟩
  have hpt : ∀ t ∈ Icc (T - h) (T + h), ((P.card : ℝ) * c₁) ^ 2 ≤
      ‖∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹‖ ^ 2 := by
    intro t ht
    have hw : ∀ q ∈ P, |t - (centredZero q).im| ≤ 2 * h := by
      intro q hq
      have h1 := hP q hq
      have hy : (centredZero q).im = xiCopyOrdinate q := by simp [centredZero, xiCopyOrdinate]
      rw [hy, abs_le]
      constructor <;> linarith [ht.1, ht.2, h1.1, h1.2]
    have hre : (P.card : ℝ) * c₁ ≤ (∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹).re := by
      rw [Complex.re_sum]
      have := Finset.card_nsmul_le_sum P (fun q => (((σ : ℂ) + t * I - centredZero q)⁻¹).re) c₁
        (fun q hq => re_inv_cauchyKernel_ge hσ (hw q hq))
      simpa [nsmul_eq_mul] using this
    exact pow_le_pow_left₀ (by positivity) (hre.trans (Complex.re_le_norm _)) 2
  have hlow : ENNReal.ofReal (((P.card : ℝ) * c₁) ^ 2 * (2 * h)) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (‖∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹‖ ^ 2) := by
    calc ENNReal.ofReal (((P.card : ℝ) * c₁) ^ 2 * (2 * h))
        = ∫⁻ _ in Icc (T - h) (T + h), ENNReal.ofReal (((P.card : ℝ) * c₁) ^ 2) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ∫⁻ t in Icc (T - h) (T + h),
            ENNReal.ofReal (‖∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹‖ ^ 2) :=
          setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal (hpt t ht)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  refine lt_of_lt_of_le ?_ hlow
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hK : K < 2 * h * c₁ ^ 2 * P.card := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * h * c₁ ^ 2)).1 (hTK.trans_le hcardT)
    linarith
  nlinarith

/-- **E-M17: the logarithm in the Hilbert inequality on the zeros is necessary.** For `σ ≥ 1` no
constant `K` satisfies `∫ |Σ_{z ∈ P} 1/(σ + it − z)|² dt ≤ K · #P` for all finite sets `P` of zero
copies. -/
theorem not_exists_zeroHilbert_without_log {σ : ℝ} (hσ : 1 ≤ σ) :
    ¬ ∃ K : ℝ, ∀ P : Finset XiZeroCopy,
      ∫⁻ t : ℝ, ENNReal.ofReal (‖∑ q ∈ P, ((σ : ℂ) + t * I - centredZero q)⁻¹‖ ^ 2) ≤
        ENNReal.ofReal (K * P.card) := by
  rintro ⟨K, hK⟩
  obtain ⟨P, hP⟩ := exists_zeroCluster_lintegral_gt hσ K
  exact lt_irrefl _ (hP.trans_le (hK P))

end GaloisForLFunctions.ExclusionOfTheCriticalState
