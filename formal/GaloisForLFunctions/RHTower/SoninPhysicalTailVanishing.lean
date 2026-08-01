import GaloisForLFunctions.RHTower.SoninPacketSupportCutoffs
import GaloisForLFunctions.RHTower.GaussianEvenCarrier

/-!
# Vectors whose support escapes to infinity are weakly null

The `L²` mass of a fixed vector outside a growing central interval tends to zero.  A family of
uniformly bounded vectors that is annihilated by physical cutoffs of growing aperture therefore
pairs to zero with every fixed vector, so every compact operator kills it.

This is the escape mechanism for the *dilated* wavepacket: unlike the packet itself, whose weak
escape comes from oscillation, the dilate escapes because its support leaves every bounded set.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

/-- **`L²` tails vanish.**  The mass of a fixed vector outside a growing central interval tends to
zero. -/
theorem tendsto_norm_sub_indicatorCutoff_atTop (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖g - indicatorCutoff (centralInterval (R n)) (measurableSet_centralInterval (R n)) g‖)
      atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun n x =>
    ‖(g : ℝ → ℂ) x - (centralInterval (R n)).indicator (fun y : ℝ => (g : ℝ → ℂ) y) x‖ ^ 2
    with hF
  have hgint : Integrable (fun x : ℝ => ‖(g : ℝ → ℂ) x‖ ^ 2) volume := by
    have := (Lp.memLp g).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    exact (((Lp.aestronglyMeasurable g).sub
      ((Lp.aestronglyMeasurable g).indicator
        (measurableSet_centralInterval (R n)))).norm).pow 2
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ, ‖F n x‖ ≤ ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    intro n
    filter_upwards with x
    simp only [hF]
    have hnn : (0 : ℝ) ≤ ‖(g : ℝ → ℂ) x - (centralInterval (R n)).indicator
        (fun y : ℝ => (g : ℝ → ℂ) y) x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    by_cases hmem : x ∈ centralInterval (R n)
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    have hev : ∀ᶠ n : ℕ in atTop, F n x = 0 := by
      have habs : ∀ᶠ n : ℕ in atTop, |x| ≤ R n := hR.eventually_ge_atTop |x|
      filter_upwards [habs] with n hn
      have hmem : x ∈ centralInterval (R n) := abs_le.mp hn
      simp [hF, Set.indicator_of_mem hmem]
    exact Tendsto.congr' (by filter_upwards [hev] with n hn; rw [hn]) tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖(g : ℝ → ℂ) x‖ ^ 2) hmeas hgint hbound hlim
  rw [integral_zero] at hdct
  have hsq : Tendsto (fun n : ℕ =>
      ‖g - indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) g‖ ^ 2) atTop (𝓝 0) := by
    refine hdct.congr fun n => ?_
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub g (indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) g),
      indicatorCutoff_ae (centralInterval (R n)) (measurableSet_centralInterval (R n)) g]
      with x hsub hind
    rw [hF]
    simp only
    rw [hsub]
    simp only [Pi.sub_apply, hind]
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **Weak escape by support.**  A uniformly bounded family annihilated by physical cutoffs of
growing aperture pairs to zero with every fixed vector. -/
theorem tendsto_inner_of_evenIndicatorCutoff_apply_eq_zero
    (g : evenSubspace) (v : ℕ → evenSubspace) (M : ℝ) (hM : ∀ n, ‖v n‖ ≤ M)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hzero : ∀ n, evenIndicatorCutoff (R n) (v n) = 0) :
    Tendsto (fun n : ℕ => ⟪g, v n⟫_ℂ) atTop (𝓝 0) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (v 0)) (hM 0)
  have htail := tendsto_norm_sub_indicatorCutoff_atTop (g : SoninL2) R hR
  have hsplit : ∀ n : ℕ, ⟪g, v n⟫_ℂ =
      ⟪(g : SoninL2) - indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) (g : SoninL2), (v n : SoninL2)⟫_ℂ := by
    intro n
    have hadj : ⟪indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) (g : SoninL2), (v n : SoninL2)⟫_ℂ = 0 := by
      have hsym := indicatorCutoff_symmetric (centralInterval (R n))
        (measurableSet_centralInterval (R n)) (g : SoninL2) (v n : SoninL2)
      rw [show ⟪indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) (g : SoninL2), (v n : SoninL2)⟫_ℂ =
          ⟪(g : SoninL2), indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) (v n : SoninL2)⟫_ℂ from hsym]
      have hv : indicatorCutoff (centralInterval (R n))
          (measurableSet_centralInterval (R n)) (v n : SoninL2) = 0 := by
        have h := congrArg (fun z : evenSubspace => (z : SoninL2)) (hzero n)
        simpa using h
      rw [hv, inner_zero_right]
    rw [inner_sub_left, hadj, sub_zero]
    rfl
  have hbound : ∀ n : ℕ, ‖⟪g, v n⟫_ℂ‖ ≤
      ‖(g : SoninL2) - indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) (g : SoninL2)‖ * M := by
    intro n
    rw [hsplit n]
    calc ‖⟪(g : SoninL2) - indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) (g : SoninL2), (v n : SoninL2)⟫_ℂ‖
        ≤ ‖(g : SoninL2) - indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) (g : SoninL2)‖ * ‖(v n : SoninL2)‖ :=
          norm_inner_le_norm _ _
      _ ≤ _ := by
          gcongr
          exact hM n
  have hzeroLim : Tendsto (fun n : ℕ =>
      ‖(g : SoninL2) - indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) (g : SoninL2)‖ * M) atTop (𝓝 0) := by
    simpa using htail.mul_const M
  refine squeeze_zero_norm hbound hzeroLim

end RHTower
