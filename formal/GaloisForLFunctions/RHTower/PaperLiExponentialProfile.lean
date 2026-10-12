import GaloisForLFunctions.RHTower.PaperLiNegativeProfile

/-! # Exponential budgets for the literal negative Li magnitudes

Rates above a Cayley bound suppress the full coefficient tail. A root beyond the
chosen rate produces an escaping unit character. The boundary rate is left open.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

abbrev PaperLiRate := {r : ℝ // 1 ≤ r}

theorem paperLiRate_pos (r : PaperLiRate) : 0 < r.val := lt_of_lt_of_le zero_lt_one r.property

def paperLiExponentialBudget (b : PaperLiBudget) (r : PaperLiRate) (n : ℕ) : PaperLiBudget :=
  ⟨b.val * r.val ^ n, mul_pos b.property (pow_pos (paperLiRate_pos r) n)⟩

def paperLiScaledMass (r : PaperLiRate) (n : ℕ) : ℝ := paperLiNegativeMass n / r.val ^ n

theorem paperLiScaledMass_nonneg (r : PaperLiRate) (n : ℕ) : 0 ≤ paperLiScaledMass r n :=
  div_nonneg (paperLiNegativeMass_nonneg n) (pow_pos (paperLiRate_pos r) n).le

def paperLiExponentialWeight (b : PaperLiBudget) (r : PaperLiRate) (n : ℕ) : ℝ :=
  paperLiNegativeWeight (paperLiExponentialBudget b r n) n

theorem paperLiExponentialWeight_eq_scaled (b : PaperLiBudget) (r : PaperLiRate) (n : ℕ) :
    paperLiExponentialWeight b r n = paperLiScaledMass r n / (paperLiScaledMass r n + b.val) := by
  have hr := (pow_pos (paperLiRate_pos r) n).ne'
  have hd := (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n)
    (paperLiExponentialBudget b r n).property).ne'
  have hs := (add_pos_of_nonneg_of_pos (paperLiScaledMass_nonneg r n) b.property).ne'
  simp only [paperLiExponentialWeight, paperLiNegativeWeight, paperLiExponentialBudget,
    paperLiScaledMass] at *
  field_simp

theorem paperLiExponentialWeight_nonneg (b : PaperLiBudget) (r : PaperLiRate) (n : ℕ) :
    0 ≤ paperLiExponentialWeight b r n := paperLiNegativeWeight_nonneg _ _

theorem paperLiExponentialWeight_norm_le (b : PaperLiBudget) (r : PaperLiRate) (n : ℕ) :
    ‖(paperLiExponentialWeight b r n : ℂ)‖ ≤ 1 := paperLiNegativeWeight_norm_le _ _

/-- A strict gap in rates absorbs the native polynomial factor in the Li growth bound. -/
theorem paperLiScaledMass_tendsto {R : ℝ} (hR : 1 ≤ R) (r : PaperLiRate) (hRr : R < r.val)
    (hroots : ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R) :
    Tendsto (paperLiScaledMass r) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_norm_xiLiPaired_le_of_cayley hroots
  have hratio : 0 ≤ R / r.val := div_nonneg (by linarith) (paperLiRate_pos r).le
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ 2 * (R / r.val) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by
      rw [Real.norm_eq_abs, abs_of_nonneg hratio]
      exact (div_lt_one (paperLiRate_pos r)).mpr hRr)
  have hlim := hsum.tendsto_atTop_zero.const_mul (max C 0)
  simp only [mul_zero] at hlim
  apply squeeze_zero (paperLiScaledMass_nonneg r) (fun n => ?_) hlim
  have hq : paperLiNegativeMass n ≤ ‖xiLiPaired n‖ := by
    apply max_le (norm_nonneg _)
    linarith [Complex.abs_re_le_norm (xiLiPaired n), neg_abs_le (xiLiPaired n).re]
  have hbound : paperLiNegativeMass n ≤ max C 0 * ((n : ℝ) ^ 2 * R ^ n) :=
    hq.trans ((hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  rw [paperLiScaledMass, div_le_iff₀ (pow_pos (paperLiRate_pos r) n)]
  have he : max C 0 * ((n : ℝ) ^ 2 * (R / r.val) ^ n) * r.val ^ n =
      max C 0 * ((n : ℝ) ^ 2 * R ^ n) := by
    rw [div_pow]
    field_simp [(pow_pos (paperLiRate_pos r) n).ne']
  rw [he]
  exact hbound

theorem paperLiExponentialWeight_tendsto {R : ℝ} (hR : 1 ≤ R)
    (b : PaperLiBudget) (r : PaperLiRate) (hRr : R < r.val)
    (hroots : ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R) :
    Tendsto (paperLiExponentialWeight b r) atTop (𝓝 0) := by
  have hq := paperLiScaledMass_tendsto hR r hRr hroots
  have h : Tendsto (fun n => paperLiScaledMass r n / (paperLiScaledMass r n + b.val))
      atTop (𝓝 (0 / (0 + b.val))) :=
    hq.div (hq.add_const b.val) (by simpa using b.property.ne')
  simpa only [← paperLiExponentialWeight_eq_scaled, zero_div] using h

/-- A root outside the budget rate forces unbounded scaled negative magnitudes at escaping indices. -/
theorem paperLiScaledMass_escape (r : PaperLiRate) (ρ : XiDivisorSupport)
    (hρ : r.val < ‖xiRootV (ρ : ℂ)‖) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => paperLiScaledMass r (j k)) atTop atTop := by
  classical
  obtain ⟨M, hm, hv, hM, hs, _, _⟩ := xiLi_family_facts
  have hunbounded (B : ℝ) : ∃ n : ℕ, B < paperLiScaledMass r n := by
    obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_lt_neg_pow hm hv hM hs
      ((r.property).trans_lt hρ) (ρ := r.val) (B := B) (paperLiRate_pos r).le hρ
    rw [← re_xiLiPaired_eq_tsum_mult] at hn
    refine ⟨n, (lt_div_iff₀ (pow_pos (paperLiRate_pos r) n)).mpr ?_⟩
    have hq : -(xiLiPaired n).re ≤ paperLiNegativeMass n := le_max_right _ _
    linarith
  choose j hj using fun k : ℕ => hunbounded
    ((∑ i ∈ Finset.range k, paperLiScaledMass r i) + (k : ℝ) + 1)
  have hmass (k : ℕ) : (k : ℝ) ≤ paperLiScaledMass r (j k) := by
    have hs : 0 ≤ ∑ i ∈ Finset.range k, paperLiScaledMass r i :=
      Finset.sum_nonneg (fun i _ => paperLiScaledMass_nonneg r i)
    linarith [hj k]
  have hindex (k : ℕ) : k ≤ j k := by
    by_contra hn
    have hmem : j k ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have hb := Finset.single_le_sum
      (fun i (_ : i ∈ Finset.range k) => paperLiScaledMass_nonneg r i) hmem
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith [hj k]
  exact ⟨j, tendsto_atTop_mono hindex tendsto_id,
    tendsto_atTop_mono hmass (tendsto_natCast_atTop_atTop (R := ℝ))⟩

theorem paperLiExponentialWeight_escape (b : PaperLiBudget) (r : PaperLiRate)
    (ρ : XiDivisorSupport) (hρ : r.val < ‖xiRootV (ρ : ℂ)‖) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => (paperLiExponentialWeight b r (j k) : ℂ)) atTop (𝓝 1) := by
  obtain ⟨j, hj, hq⟩ := paperLiScaledMass_escape r ρ hρ
  have hi := tendsto_inv_atTop_zero.comp (hq.atTop_add (tendsto_const_nhds (x := b.val)))
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul b.val)
  have he (k : ℕ) : 1 - b.val * (paperLiScaledMass r (j k) + b.val)⁻¹ =
      paperLiExponentialWeight b r (j k) := by
    rw [paperLiExponentialWeight_eq_scaled]
    have hd := (add_pos_of_nonneg_of_pos (paperLiScaledMass_nonneg r (j k)) b.property).ne'
    field_simp
    ring
  have hw : Tendsto (fun k => paperLiExponentialWeight b r (j k)) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using hr.congr he
  exact ⟨j, hj, by simpa only [Function.comp_def, Complex.ofReal_one] using
    (Complex.continuous_ofReal.tendsto 1).comp hw⟩

end
end RHTower
