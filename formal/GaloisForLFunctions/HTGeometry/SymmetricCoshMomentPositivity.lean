import GaloisForLFunctions.HTGeometry.SymmetricCoshKernelPositiveDefinite

/-!
# Positive definiteness of arc superpositions from moment positivity

For `|c| < 1` the symmetric kernel `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}` expands as

  `𝒦_c(v) = ∑_j 2 C(−½, 2j) c^{2j} (cosh v)^{−1/2−2j}`,   `C(−½, 2j) > 0`.

Hence for a real (possibly signed) density `k` on `[−c₀, c₀]`, `c₀ < 1`,

  `∫ k(c) 𝒦_c(v) dc = ∑_j 2 C(−½, 2j) m_j (cosh v)^{−1/2−2j}`,   `m_j = ∫ k(c) c^{2j} dc`,

and every `(cosh v)^{−s}`, `s > 0`, has a strictly positive cosine transform.  So the superposition is
strictly positive definite as soon as all even moments `m_j` are nonnegative and `m_0 > 0`.  This is
weaker than `k ≥ 0`: only the moments of the even part of `k`, pushed forward to `c²`, enter.

## Main results

* `integral_cos_mul_coshPowerSeries_pos`: `∑_j b_j (cosh v)^{−1/2−2j}` with `b_j ≥ 0`, `∑ b_j < ∞`,
  `b_0 > 0` is strictly positive definite.
* `integral_density_mul_symCoshKernel_eq_tsum`: the moment expansion of a superposition.
* `integral_cos_mul_momentPositive_symCoshKernel_pos`: strict positive definiteness from nonnegative
  even moments.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-! ### Power series in `sech` with nonnegative coefficients -/

/-- `∑_j b_j (cosh v)^{−1/2−2j}`. -/
def coshPowerSeries (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑' j, b j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))

theorem cosh_rpow_neg_half_two_mul_le (j : ℕ) (v : ℝ) :
    Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) ≤ Real.cosh v ^ (-(1 / 2) : ℝ) :=
  cosh_rpow_neg_le_of_le (by have := j.cast_nonneg (α := ℝ); linarith) v

/-- **A `sech`-power series with nonnegative coefficients is strictly positive definite.** -/
theorem integral_cos_mul_coshPowerSeries_pos {b : ℕ → ℝ} (hb0 : ∀ j, 0 ≤ b j)
    (hbsum : Summable b) (hbpos : 0 < b 0) (τ : ℝ) :
    0 < ∫ v : ℝ, Real.cos (τ * v) * coshPowerSeries b v := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  set F : ℕ → ℝ → ℝ := fun j v =>
    Real.cos (τ * v) * (b j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))) with hF
  have hbound : ∀ j v, ‖F j v‖ ≤ b j * Real.cosh v ^ (-(1 / 2) : ℝ) := by
    intro j v
    simp only [hF]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 j),
      abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos v).le _)]
    calc |Real.cos (τ * v)| * (b j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)))
        ≤ 1 * (b j * Real.cosh v ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul (Real.abs_cos_le_one _)
            (mul_le_mul_of_nonneg_left (cosh_rpow_neg_half_two_mul_le j v) (hb0 j))
            (mul_nonneg (hb0 j) (Real.rpow_nonneg (Real.cosh_pos v).le _)) zero_le_one
      _ = _ := one_mul _
  have hFint : ∀ j, Integrable (F j) := fun j =>
    (hI.const_mul (b j)).mono' (by simp only [hF]; fun_prop) (Eventually.of_forall (hbound j))
  have hnormsum : Summable fun j => ∫ v, ‖F j v‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun v => norm_nonneg _)
      (fun j => ?_) (hbsum.mul_right (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)))
    rw [← integral_const_mul]
    exact integral_mono (hFint j).norm (hI.const_mul (b j)) (hbound j)
  have hswap := integral_tsum_of_summable_integral_norm hFint hnormsum
  have hpt : ∀ v, Real.cos (τ * v) * coshPowerSeries b v = ∑' j, F j v := by
    intro v
    rw [coshPowerSeries, ← tsum_mul_left]
  simp_rw [hpt]
  rw [← hswap]
  have hterm : ∀ j, ∫ v, F j v =
      b j * ∫ v, Real.cos (τ * v) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := by
    intro j
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF]; ring
  have hnn : ∀ j, 0 ≤ ∫ v, F j v := fun j => by
    rw [hterm]
    exact mul_nonneg (hb0 j) (integral_cos_mul_cosh_rpow_neg_pos (by positivity) τ).le
  have hsumm : Summable fun j => ∫ v, F j v :=
    Summable.of_norm_bounded hnormsum fun j => norm_integral_le_integral_norm _
  refine hsumm.tsum_pos hnn 0 ?_
  rw [hterm]
  exact mul_pos hbpos (integral_cos_mul_cosh_rpow_neg_pos (by norm_num) τ)

/-! ### The moment expansion of a superposition -/

theorem abs_symCoshTerm_le {c₀ c : ℝ} (hc : |c| ≤ c₀) (j : ℕ) (v : ℝ) :
    |symCoshTerm c j v| ≤ 2 * (c₀ ^ 2) ^ j := by
  unfold symCoshTerm
  have hch : Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh v) (by
      have := j.cast_nonneg (α := ℝ); linarith)
  have hch0 : 0 ≤ Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) :=
    Real.rpow_nonneg (Real.cosh_pos v).le _
  have hbin := abs_choose_neg_half_le_one (2 * j)
  have hcpow : |c ^ (2 * j)| ≤ (c₀ ^ 2) ^ j := by
    rw [abs_pow, pow_mul]
    exact pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (abs_nonneg c) hc 2) j
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hch0, abs_two]
  calc 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |c ^ (2 * j)| * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))
      ≤ 2 * 1 * (c₀ ^ 2) ^ j * 1 := by
        gcongr
    _ = 2 * (c₀ ^ 2) ^ j := by ring

/-- **Moment expansion.** For an integrable density `k` on `[−c₀, c₀]`, `c₀ < 1`,
`∫ k(c) 𝒦_c(v) dc = ∑_j 2 C(−½, 2j) (∫ k(c) c^{2j} dc) (cosh v)^{−1/2−2j}`. -/
theorem integral_density_mul_symCoshKernel_eq_tsum {c₀ : ℝ} (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ < 1)
    {k : ℝ → ℝ} (hk : IntegrableOn k (Icc (-c₀) c₀)) (v : ℝ) :
    ∫ c in Icc (-c₀) c₀, k c * symCoshKernel c v =
      coshPowerSeries (fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) *
        ∫ c in Icc (-c₀) c₀, k c * c ^ (2 * j)) v := by
  set μ := volume.restrict (Icc (-c₀) c₀) with hμ
  have hc : ∀ c ∈ Icc (-c₀) c₀, |c| ≤ c₀ := fun c hc => abs_le.mpr ⟨hc.1, hc.2⟩
  have hc1 : ∀ c ∈ Icc (-c₀) c₀, |c| < 1 := fun c hcm => lt_of_le_of_lt (hc c hcm) hc₀
  have hc₀0' : 0 ≤ c₀ ^ 2 := sq_nonneg _
  set G : ℕ → ℝ → ℝ := fun j c => k c * symCoshTerm c j v with hG
  have hGmeas : ∀ j, AEStronglyMeasurable (G j) μ := fun j =>
    hk.aestronglyMeasurable.mul (by unfold symCoshTerm; fun_prop : Continuous fun c =>
      symCoshTerm c j v).aestronglyMeasurable
  have hGbound : ∀ j, ∀ᵐ c ∂μ, ‖G j c‖ ≤ |k c| * (2 * (c₀ ^ 2) ^ j) := by
    intro j
    rw [hμ, ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun c hcm => ?_
    simp only [hG, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_symCoshTerm_le (hc c hcm) j v) (abs_nonneg _)
  have hGint : ∀ j, Integrable (G j) μ := fun j =>
    (hk.abs.mul_const (2 * (c₀ ^ 2) ^ j)).mono' (hGmeas j) (hGbound j)
  have hgeom : Summable fun j : ℕ => (c₀ ^ 2) ^ j :=
    summable_geometric_of_lt_one hc₀0' (by nlinarith)
  have hnormsum : Summable fun j => ∫ c, ‖G j c‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun c => norm_nonneg _)
      (fun j => integral_mono_ae (hGint j).norm (hk.abs.mul_const _) (hGbound j))
      ?_
    simp_rw [integral_mul_const]
    exact (hgeom.mul_left 2).mul_left _
  have hswap := integral_tsum_of_summable_integral_norm hGint hnormsum
  have hpt : ∀ᵐ c ∂μ, k c * symCoshKernel c v = ∑' j, G j c := by
    rw [hμ, ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun c hcm => ?_
    rw [(hasSum_symCoshKernel (hc1 c hcm) v).tsum_eq.symm, ← tsum_mul_left]
  rw [integral_congr_ae hpt, ← hswap, coshPowerSeries]
  congr 1
  funext j
  simp only [hG, symCoshTerm]
  have hre : ∀ a : ℝ, k a * (2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * a ^ (2 * j) *
      Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))) = (2 * Ring.choose (-1 / 2 : ℝ) (2 * j) *
      Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))) * (k a * a ^ (2 * j)) := fun a => by ring
  simp_rw [hre]
  rw [integral_const_mul]
  ring

/-- **Strict positive definiteness from nonnegative even moments.**  If `k` is integrable on
`[−c₀, c₀]` with `c₀ < 1`, all even moments `∫ k(c) c^{2j} dc` are nonnegative, and the total mass is
positive, then the superposition `v ↦ ∫ k(c) 𝒦_c(v) dc` is strictly positive definite. -/
theorem integral_cos_mul_momentPositive_symCoshKernel_pos {c₀ : ℝ} (hc₀ : c₀ < 1) {k : ℝ → ℝ}
    (hk : IntegrableOn k (Icc (-c₀) c₀))
    (hmom : ∀ j : ℕ, 0 ≤ ∫ c in Icc (-c₀) c₀, k c * c ^ (2 * j))
    (hmass : 0 < ∫ c in Icc (-c₀) c₀, k c) (τ : ℝ) :
    0 < ∫ v : ℝ, Real.cos (τ * v) * ∫ c in Icc (-c₀) c₀, k c * symCoshKernel c v := by
  have hc : ∀ c ∈ Icc (-c₀) c₀, |c| ≤ c₀ := fun c hc => abs_le.mpr ⟨hc.1, hc.2⟩
  have hne : (Icc (-c₀) c₀).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Measure.restrict_empty, integral_zero_measure] at hmass
    exact lt_irrefl 0 hmass
  obtain ⟨c', hc'⟩ := hne
  have hc₀0 : 0 ≤ c₀ := le_trans (abs_nonneg c') (hc c' hc')
  simp_rw [integral_density_mul_symCoshKernel_eq_tsum hc₀0 hc₀ hk]
  set m : ℕ → ℝ := fun j => ∫ c in Icc (-c₀) c₀, k c * c ^ (2 * j) with hm
  have hb0 : ∀ j, 0 ≤ 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * m j := fun j =>
    mul_nonneg (mul_nonneg two_pos.le (choose_neg_half_even_pos j).le) (hmom j)
  -- summability of the coefficients: `|m_j| ≤ (c₀²)^j ∫|k|`
  have hmbound : ∀ j, |m j| ≤ (c₀ ^ 2) ^ j * ∫ c in Icc (-c₀) c₀, |k c| := by
    intro j
    rw [hm]
    calc |∫ c in Icc (-c₀) c₀, k c * c ^ (2 * j)|
        ≤ ∫ c in Icc (-c₀) c₀, |k c * c ^ (2 * j)| := abs_integral_le_integral_abs
      _ ≤ ∫ c in Icc (-c₀) c₀, |k c| * (c₀ ^ 2) ^ j := by
          refine setIntegral_mono_on (hk.mul_continuousOn (by fun_prop)
            isCompact_Icc).abs (hk.norm.mul_const _) measurableSet_Icc fun c hcm => ?_
          rw [abs_mul, abs_pow, pow_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact pow_le_pow_left₀ (by positivity)
            (pow_le_pow_left₀ (abs_nonneg c) (hc c hcm) 2) j
      _ = (c₀ ^ 2) ^ j * ∫ c in Icc (-c₀) c₀, |k c| := by
          rw [integral_mul_const, mul_comm]
  have hgeom : Summable fun j : ℕ => (c₀ ^ 2) ^ j :=
    summable_geometric_of_lt_one (sq_nonneg _) (by nlinarith)
  have hbsum : Summable fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * m j := by
    refine Summable.of_norm_bounded ((hgeom.mul_right (∫ c in Icc (-c₀) c₀, |k c|)).mul_left 2)
      fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    calc 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |m j|
        ≤ 2 * 1 * ((c₀ ^ 2) ^ j * ∫ c in Icc (-c₀) c₀, |k c|) := by
          gcongr
          · exact abs_choose_neg_half_le_one _
          · exact hmbound j
      _ = 2 * ((c₀ ^ 2) ^ j * ∫ c in Icc (-c₀) c₀, |k c|) := by ring
  have hbpos : 0 < 2 * Ring.choose (-1 / 2 : ℝ) (2 * 0) * m 0 := by
    have h0 : m 0 = ∫ c in Icc (-c₀) c₀, k c := by simp [hm]
    rw [h0]
    have : Ring.choose (-1 / 2 : ℝ) (2 * 0) = 1 := by simp
    rw [this]
    linarith
  exact integral_cos_mul_coshPowerSeries_pos hb0 hbsum hbpos τ

end

end HTGeometry
end GaloisForLFunctions
