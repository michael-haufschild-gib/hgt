import GaloisForLFunctions.HTGeometry.JensenScaledWeight

/-!
# Jensen's theorem, converse direction

If every Jensen polynomial of a real coefficient sequence splits over `ℝ`, then the entire function
it defines belongs to the Laguerre–Pólya class.  The rescaled Jensen polynomials
`J^d(z/d) = ∑_{i ≤ d} d^{(i)}d^{-i} c_i z^i` split, and because the weights `d^{(i)}d^{-i}` lie in
`[0,1]` and tend to `1`, dominated convergence of the coefficient series makes them converge
locally uniformly to `∑ c_i z^i`.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {c : ℕ → ℝ} {F : ℂ → ℂ}

theorem summable_abs_mul_pow (hF : ∀ z : ℂ, HasSum (fun i => ((c i : ℝ) : ℂ) * z ^ i) (F z))
    {R : ℝ} (hR : 0 ≤ R) : Summable (fun i => |c i| * R ^ i) := by
  have hw : Summable (fun i => ((c i : ℝ) : ℂ) * (((R + 1 : ℝ) : ℂ)) ^ i) := (hF _).summable
  have hnorm : Summable (fun i => ‖((c i : ℝ) : ℂ) * (((R + 1 : ℝ) : ℂ)) ^ i‖) :=
    summable_norm_iff.2 hw
  have hval : ∀ i, ‖((c i : ℝ) : ℂ) * (((R + 1 : ℝ) : ℂ)) ^ i‖ = |c i| * (R + 1) ^ i := by
    intro i
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ R + 1)]
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hnorm.congr hval)
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR (by linarith) i) (abs_nonneg _)

theorem tendstoUniformlyOn_polyEvalC_jensenScaled
    (hF : ∀ z : ℂ, HasSum (fun i => ((c i : ℝ) : ℂ) * z ^ i) (F z))
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun d => polyEvalC (jensenScaled c d)) F atTop
      (Metric.closedBall (0 : ℂ) R) := by
  have hbound : Summable (fun i => |c i| * R ^ i) := summable_abs_mul_pow hF hR
  have hnn : ∀ d i, 0 ≤ |c i| * (1 - jensenWeight d i) * R ^ i := fun d i =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith [jensenWeight_le_one d i]))
      (pow_nonneg hR i)
  have hle : ∀ d i, |c i| * (1 - jensenWeight d i) * R ^ i ≤ |c i| * R ^ i := by
    intro d i
    have h1 : 1 - jensenWeight d i ≤ 1 := by linarith [jensenWeight_nonneg d i]
    calc |c i| * (1 - jensenWeight d i) * R ^ i
        ≤ (|c i| * 1) * R ^ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg (c i)))
            (pow_nonneg hR i)
      _ = |c i| * R ^ i := by ring
  have hEsummable : ∀ d, Summable (fun i => |c i| * (1 - jensenWeight d i) * R ^ i) :=
    fun d => Summable.of_nonneg_of_le (hnn d) (hle d) hbound
  have hEtend : Tendsto (fun d => ∑' i : ℕ, |c i| * (1 - jensenWeight d i) * R ^ i)
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑' i : ℕ, |c i| * (1 - (1 : ℝ)) * R ^ i := by simp
    rw [h0]
    refine tendsto_tsum_of_dominated_convergence hbound (fun i => ?_) ?_
    · exact ((tendsto_const_nhds.sub (tendsto_jensenWeight i)).const_mul _).mul_const _
    · refine Filter.Eventually.of_forall fun d i => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn d i)]
      exact hle d i
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hEtend.eventually (gt_mem_nhds hε)] with d hd z hz
  have hz' : ‖z‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hz
  have hpoly : polyEvalC (jensenScaled c d) z
      = ∑' i : ℕ, ((c i * jensenWeight d i : ℝ) : ℂ) * z ^ i := by
    rw [polyEvalC_jensenScaled]
    refine (tsum_eq_sum ?_).symm
    intro i hi
    have hdi : d < i := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [jensenWeight_eq_zero_of_lt hdi]
    simp
  have hsum1 : Summable (fun i => ((c i * jensenWeight d i : ℝ) : ℂ) * z ^ i) := by
    refine summable_of_ne_finset_zero (s := Finset.range (d + 1)) fun i hi => ?_
    have hdi : d < i := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [jensenWeight_eq_zero_of_lt hdi]
    simp
  have hdiff : F z - polyEvalC (jensenScaled c d) z
      = ∑' i : ℕ, (((c i : ℝ) : ℂ) * z ^ i - ((c i * jensenWeight d i : ℝ) : ℂ) * z ^ i) := by
    rw [hpoly, ← (hF z).tsum_eq, ← Summable.tsum_sub (hF z).summable hsum1]
  rw [dist_eq_norm, hdiff]
  refine lt_of_le_of_lt (tsum_of_norm_bounded (hEsummable d).hasSum fun i => ?_) hd
  have hterm : ((c i : ℝ) : ℂ) * z ^ i - ((c i * jensenWeight d i : ℝ) : ℂ) * z ^ i
      = ((c i * (1 - jensenWeight d i) : ℝ) : ℂ) * z ^ i := by
    push_cast
    ring
  rw [hterm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by linarith [jensenWeight_le_one d i] : (0:ℝ) ≤ 1 - jensenWeight d i)]
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz' i)
    (by linarith [jensenWeight_le_one d i])

/-- **Jensen's theorem, converse direction.** -/
theorem laguerrePolya_of_splits_jensenPoly
    (hF : ∀ z : ℂ, HasSum (fun i => ((c i : ℝ) : ℂ) * z ^ i) (F z))
    (hsplits : ∀ d, (jensenPoly c d).Splits) :
    LaguerrePolya F := by
  refine ⟨fun m => jensenScaled c (m + 1),
    fun m => splits_jensenScaled (Nat.succ_ne_zero m) (hsplits _), ?_⟩
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K hKsub hK
  obtain ⟨R, hRK⟩ := hK.isBounded.subset_closedBall 0
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hsub : K ⊆ Metric.closedBall (0 : ℂ) (max R 0) :=
    hRK.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hmain := (tendstoUniformlyOn_polyEvalC_jensenScaled hF hR0).mono hsub
  intro u hu
  exact (tendsto_add_atTop_nat 1).eventually (hmain u hu)

end

end GaloisForLFunctions.HTGeometry
