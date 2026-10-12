import GaloisForLFunctions.RHTower.LiSignDensity
import GaloisForLFunctions.RHTower.LiSubexponentialCriterion

/-! # Bounded profiles retaining the full negative Li magnitudes

The profile is defined from the actual paired Li coefficients, without a zero-location
test. Under failure of RH its values approach one along escaping coefficient indices,
for every fixed positive normalization budget.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

abbrev PaperLiBudget := {b : ℝ // 0 < b}

def paperLiNegativeMass (n : ℕ) : ℝ := max 0 (-(xiLiPaired n).re)

theorem paperLiNegativeMass_nonneg (n : ℕ) : 0 ≤ paperLiNegativeMass n := le_max_left _ _

theorem paperLiNegativeMass_eq_zero_iff (n : ℕ) :
    paperLiNegativeMass n = 0 ↔ 0 ≤ (xiLiPaired n).re := by
  simp [paperLiNegativeMass]

theorem paperLiNegativeMass_of_RH (h : RiemannHypothesis) (n : ℕ) :
    paperLiNegativeMass n = 0 :=
  (paperLiNegativeMass_eq_zero_iff n).mpr (re_xiLiPaired_nonneg_of_rh h n)

def paperLiNegativeWeight (b : PaperLiBudget) (n : ℕ) : ℝ :=
  paperLiNegativeMass n / (paperLiNegativeMass n + b.val)

theorem paperLiNegativeWeight_nonneg (b : PaperLiBudget) (n : ℕ) :
    0 ≤ paperLiNegativeWeight b n :=
  div_nonneg (paperLiNegativeMass_nonneg n)
    (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property).le

theorem paperLiNegativeWeight_lt_one (b : PaperLiBudget) (n : ℕ) :
    paperLiNegativeWeight b n < 1 := by
  rw [paperLiNegativeWeight, div_lt_one
    (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property)]
  linarith [b.property]

theorem paperLiNegativeWeight_norm_le (b : PaperLiBudget) (n : ℕ) :
    ‖(paperLiNegativeWeight b n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (paperLiNegativeWeight_nonneg b n)]
  exact (paperLiNegativeWeight_lt_one b n).le

theorem paperLiNegativeWeight_eq_zero_iff (b : PaperLiBudget) (n : ℕ) :
    paperLiNegativeWeight b n = 0 ↔ 0 ≤ (xiLiPaired n).re := by
  have hd := (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property).ne'
  simp only [paperLiNegativeWeight, div_eq_zero_iff, hd, or_false,
    paperLiNegativeMass_eq_zero_iff]

theorem paperLiNegativeWeight_of_RH (h : RiemannHypothesis) (b : PaperLiBudget) (n : ℕ) :
    paperLiNegativeWeight b n = 0 :=
  (paperLiNegativeWeight_eq_zero_iff b n).mpr (re_xiLiPaired_nonneg_of_rh h n)

/-- The native negative Li magnitude is cofinally unbounded if RH fails. -/
theorem paperLiNegativeMass_escape (h : ¬ RiemannHypothesis) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => paperLiNegativeMass (j k)) atTop atTop := by
  classical
  obtain ⟨M, hm, hv, hM, hs, _, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ, hρ⟩ := hbad h
  have hunbounded (B : ℝ) : ∃ n : ℕ, (xiLiPaired n).re < -B := by
    obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_lt_neg_pow hm hv hM hs hρ
      (ρ := (1 : ℝ)) (B := B) zero_le_one hρ
    refine ⟨n, ?_⟩
    simpa only [re_xiLiPaired_eq_tsum_mult, one_pow, mul_one] using hn
  choose j hj using fun k : ℕ => hunbounded
    ((∑ i ∈ Finset.range k, |(xiLiPaired i).re|) + (k : ℝ) + 1)
  have hmass (k : ℕ) : (k : ℝ) ≤ paperLiNegativeMass (j k) := by
    have ht : 0 ≤ ∑ i ∈ Finset.range k, |(xiLiPaired i).re| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hq : -(xiLiPaired (j k)).re ≤ paperLiNegativeMass (j k) := le_max_right _ _
    linarith [hj k]
  have hindex (k : ℕ) : k ≤ j k := by
    by_contra hn
    have hmem : j k ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have hb := Finset.single_le_sum (fun i (_ : i ∈ Finset.range k) => abs_nonneg (xiLiPaired i).re) hmem
    have hn0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith [hj k, neg_abs_le (xiLiPaired (j k)).re]
  exact ⟨j, tendsto_atTop_mono hindex tendsto_id,
    tendsto_atTop_mono hmass (tendsto_natCast_atTop_atTop (R := ℝ))⟩

/-- Every fixed finite budget leaves an escaping unit character in the actual coefficient history. -/
theorem paperLiNegativeWeight_escape (h : ¬ RiemannHypothesis) (b : PaperLiBudget) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => (paperLiNegativeWeight b (j k) : ℂ)) atTop (𝓝 1) := by
  obtain ⟨j, hj, hq⟩ := paperLiNegativeMass_escape h
  have hi := tendsto_inv_atTop_zero.comp (hq.atTop_add (tendsto_const_nhds (x := b.val)))
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul b.val)
  have he (k : ℕ) : 1 - b.val * (paperLiNegativeMass (j k) + b.val)⁻¹ =
      paperLiNegativeWeight b (j k) := by
    have hd := (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg (j k)) b.property).ne'
    unfold paperLiNegativeWeight
    field_simp
    ring
  have hw : Tendsto (fun k => paperLiNegativeWeight b (j k)) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using hr.congr he
  exact ⟨j, hj, by simpa only [Function.comp_def, Complex.ofReal_one] using
    (Complex.continuous_ofReal.tendsto 1).comp hw⟩

end
end RHTower
