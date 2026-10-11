import GaloisForLFunctions.RHTower.LiSignDensity
import GaloisForLFunctions.RHTower.LiSubexponentialCriterion

/-!
# Li's criterion from above: the quadratic ceiling

The paired Li coefficients satisfy the sharp ceiling `Re 2λ_n ≤ n²·Re 2λ_1` for every `n` iff the
Riemann hypothesis holds (`riemannHypothesis_iff_re_xiLiPaired_le_sq_mul_one`). Equivalently, RH
holds iff the coefficients grow at most subexponentially *from above*
(`riemannHypothesis_iff_re_xiLiPaired_upper_subexp`). Together with Li's criterion `λ_n ≥ 0` this
shows that RH pins the coefficients between `0` and `n²λ_1`, and a violation of either side forces
violations of both.

**Mechanism.**
* *On the line.* For `‖v‖ = 1`, `Re(2 − vⁿ − v⁻ⁿ) = ‖1 − vⁿ‖²`, and `1 − vⁿ = (1 − v)Σ_{k<n}vᵏ` gives
  the chord bound `‖1 − vⁿ‖ ≤ n‖1 − v‖`. Summing over the zeros gives the ceiling
  (`re_liTerm_le_sq_mul_of_norm_eq_one`). Equivalently, `n ↦ 2λ_n` is the squared displacement
  `‖Uⁿξ − ξ‖²` of a unitary orbit, a conditionally negative definite function on `ℤ`, so `√λ_n`
  is subadditive.
* *Off the line.* The dominant part `−Rⁿ Σ_{i∈D} m_i Re(u_iⁿ)` is below `−ε` on a positive proportion
  of `n` (`exists_card_filter_gt_and_lt`), so `Re 2λ_n ≥ (ε/2)Rⁿ` infinitely often
  (`exists_re_xiLiPaired_ge_exp_of_not_riemannHypothesis`). The upper failure sits at the half-turn
  phases `nθ ≈ π` of the top Cayley roots; the lower failure (`λ_n < 0`) sits at `nθ ≈ 0`.
-/

open Complex Filter Finset Topology

noncomputable section

namespace RHTower

/-! ## The chord bound on the unit circle -/

theorem norm_one_sub_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith [this]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith [h1]

theorem norm_one_sub_pow_le {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) : ‖1 - v ^ n‖ ≤ n * ‖1 - v‖ := by
  have e : 1 - v ^ n = (1 - v) * ∑ k ∈ range n, v ^ k := by
    have := geom_sum_mul v n
    linear_combination this
  rw [e, norm_mul, mul_comm]
  gcongr
  calc ‖∑ k ∈ range n, v ^ k‖ ≤ ∑ k ∈ range n, ‖v ^ k‖ := norm_sum_le _ _
    _ = n := by simp [norm_pow, hv]

/-- On the unit circle, `Re(2 − vⁿ − v⁻ⁿ) = ‖1 − vⁿ‖²`. -/
theorem re_liTerm_eq_norm_sq_of_norm_eq_one {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) :
    (liTerm v n).re = ‖1 - v ^ n‖ ^ 2 := by
  have hvn : ‖v ^ n‖ = 1 := by rw [norm_pow, hv, one_pow]
  have hinv : v⁻¹ ^ n = (starRingEnd ℂ) (v ^ n) := by
    rw [inv_pow, Complex.inv_def, Complex.normSq_eq_norm_sq, hvn]
    simp
  unfold liTerm
  rw [hinv, norm_one_sub_sq_of_norm_eq_one hvn]
  simp only [Complex.sub_re, Complex.re_ofNat, Complex.conj_re]
  ring

/-- **The chord bound.** For `‖v‖ = 1`, `Re liTerm(v, n) ≤ n² Re liTerm(v, 1)`. -/
theorem re_liTerm_le_sq_mul_of_norm_eq_one {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) :
    (liTerm v n).re ≤ (n : ℝ) ^ 2 * (liTerm v 1).re := by
  rw [re_liTerm_eq_norm_sq_of_norm_eq_one hv, re_liTerm_eq_norm_sq_of_norm_eq_one hv, pow_one]
  have h := norm_one_sub_pow_le hv n
  have h0 : 0 ≤ ‖1 - v ^ n‖ := norm_nonneg _
  calc ‖1 - v ^ n‖ ^ 2 ≤ (n * ‖1 - v‖) ^ 2 := by gcongr
    _ = (n : ℝ) ^ 2 * ‖1 - v‖ ^ 2 := by ring

/-! ## The ceiling under the Riemann hypothesis -/

theorem summable_re_xiLiPairedTerm_mult (n : ℕ) : Summable fun ρ : XiDivisorSupport =>
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re := by
  refine (Complex.reCLM.summable (summable_xiLiPairedTerm n)).congr fun ρ => ?_
  simp only [Complex.reCLM_apply]
  rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]

theorem norm_xiRootV_eq_one_of_rh (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ‖xiRootV (ρ : ℂ)‖ = 1 := by
  have hne0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hne1 : (ρ : ℂ) ≠ 1 := by
    intro h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  exact le_antisymm ((riemannHypothesis_iff_cayley_le_one.mp hRH) _
    (xi_eq_zero_of_mem_divisor_support ρ)) (one_le_norm_xiRootV hne0 hne1)

/-- **The quadratic ceiling.** Under RH, `Re 2λ_n ≤ n²·Re 2λ_1` for every `n`. -/
theorem re_xiLiPaired_le_sq_mul_one_of_rh (hRH : RiemannHypothesis) (n : ℕ) :
    (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := by
  rw [re_xiLiPaired_eq_tsum_mult, re_xiLiPaired_eq_tsum_mult, ← tsum_mul_left]
  refine (summable_re_xiLiPairedTerm_mult n).tsum_le_tsum (fun ρ => ?_)
    ((summable_re_xiLiPairedTerm_mult 1).mul_left _)
  have hm : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    have := xi_divisor_pos_on_support ρ
    exact_mod_cast this.le
  have h := re_liTerm_le_sq_mul_of_norm_eq_one (norm_xiRootV_eq_one_of_rh hRH ρ) n
  calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re
      ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          ((n : ℝ) ^ 2 * (liTerm (xiRootV (ρ : ℂ)) 1).re) := mul_le_mul_of_nonneg_left h hm
    _ = (n : ℝ) ^ 2 * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (liTerm (xiRootV (ρ : ℂ)) 1).re) := by ring

/-! ## Exponentially large positive values off the line -/

/-- **Abstract form.** If one member of a non-real family lies strictly outside the unit circle,
the paired Li sums exceed `εRⁿ` for infinitely many `n`, with `R > 1`. -/
theorem exists_re_tsum_liTerm_ge_exp {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) (hnr : ∀ i, (v i).im ≠ 0)
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ R ε : ℝ, 1 < R ∧ 0 < ε ∧ ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      ε * R ^ n ≤ ∑' i, m i * (liTerm (v i) n).re := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  have hu2 : ∀ i, u i ^ 2 ≠ 1 := by
    intro i h
    have him : (u i).im ≠ 0 := by
      rw [hudef]; simp only
      rw [Complex.div_ofReal_im]
      exact div_ne_zero (hnr i) hR0.ne'
    have : u i = 1 ∨ u i = -1 := by
      have h' : (u i - 1) * (u i + 1) = 0 := by ring_nf; rw [h]; ring
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases this with h1 | h1 <;> rw [h1] at him <;> simp at him
  obtain ⟨ε, c, K, hε, hc, hcount⟩ :=
    exists_card_filter_gt_and_lt u (fun i => m i) hunit hu2 (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  refine ⟨R, ε / 2, hR1, by linarith, fun N₀ => ?_⟩
  set A : ℕ := max N₀ N₁ with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (((A : ℝ) + K) / c)
  have hbig : A < ((range N).filter
      (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε)).card := by
    have h1 := (hcount N).2
    have h2 : (A : ℝ) + K < c * N := by
      rw [div_lt_iff₀ hc] at hN; linarith
    have : (A : ℝ) < (((range N).filter
        (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε)).card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨n, hn, hnA⟩ : ∃ n ∈ (range N).filter
      (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε), A ≤ n := by
    by_contra hno
    push Not at hno
    have hsub : (range N).filter (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε)
        ⊆ range A := fun n hn => mem_range.mpr (hno n hn)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  have hP := (mem_filter.mp hn).2
  rw [hf] at hP
  have hd := hN₁ n (le_trans (le_max_right _ _) hnA)
  have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
  refine ⟨n, le_trans (le_max_left _ _) hnA, ?_⟩
  have h2 := (abs_le.mp hd).1
  have h3 := mul_pos hRn (by linarith : (0 : ℝ) < -(∑ i ∈ D, m i * ((v i / R) ^ n).re) - ε)
  nlinarith

/-- **Off the line the paired Li coefficients are exponentially large and positive infinitely
often.** -/
theorem exists_re_xiLiPaired_ge_exp_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ R ε : ℝ, 1 < R ∧ 0 < ε ∧ ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ε * R ^ n ≤ (xiLiPaired n).re := by
  obtain ⟨M, hmult, hvnorm, hvM, hsum, hnr, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨R, ε, hR, hε, h⟩ := exists_re_tsum_liTerm_ge_exp hmult hvnorm hvM hsum hnr hρ₀
  refine ⟨R, ε, hR, hε, fun N₀ => ?_⟩
  obtain ⟨n, hn, hle⟩ := h N₀
  exact ⟨n, hn, by rw [re_xiLiPaired_eq_tsum_mult]; exact hle⟩

/-! ## The criteria -/

theorem exists_sq_le_mul_pow {r : ℝ} (hr : 1 < r) : ∃ C : ℝ, ∀ n : ℕ, (n : ℝ) ^ 2 ≤ C * r ^ n := by
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (tendsto_pow_const_div_const_pow_of_one_lt 2 hr))
    1 one_pos
  refine ⟨max 1 ((N₀ : ℝ) ^ 2), fun n => ?_⟩
  have hrn : 1 ≤ r ^ n := one_le_pow₀ hr.le
  have hrpos : 0 < r ^ n := by positivity
  rcases lt_or_ge n N₀ with h | h
  · have h1 : (n : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 := by
      have : (n : ℝ) ≤ N₀ := by exact_mod_cast h.le
      gcongr
    calc (n : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 := h1
      _ ≤ max 1 ((N₀ : ℝ) ^ 2) := le_max_right _ _
      _ ≤ max 1 ((N₀ : ℝ) ^ 2) * r ^ n := le_mul_of_one_le_right (by positivity) hrn
  · have hd := hN₀ n h
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hrpos] at hd
    calc (n : ℝ) ^ 2 ≤ 1 * r ^ n := by linarith
      _ ≤ max 1 ((N₀ : ℝ) ^ 2) * r ^ n := by gcongr; exact le_max_left _ _

theorem riemannHypothesis_of_re_xiLiPaired_upper_subexp
    (h : ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ n : ℕ, (xiLiPaired n).re ≤ C * r ^ n) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨R, ε, hR, hε, hbig⟩ := exists_re_xiLiPaired_ge_exp_of_not_riemannHypothesis hRH
  set r : ℝ := (1 + R) / 2 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hrR : r < R := by rw [hr]; linarith
  clear_value r
  have hR0 : 0 < R := by linarith
  obtain ⟨C, hC⟩ := h r hr1
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := by rw [div_lt_one hR0]; exact hrR
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hlim) (ε / (|C| + 1)) (by positivity)
  obtain ⟨n, hn, hle⟩ := hbig N₀
  have hd := hN₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
  have hRn : 0 < R ^ n := pow_pos hR0 n
  have hrn : r ^ n = R ^ n * (r / R) ^ n := by rw [div_pow]; field_simp
  have h1 := hC n
  have h2 : C * r ^ n ≤ |C| * r ^ n := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h3 : |C| * (r / R) ^ n < ε := by
    have hC1 : 0 < |C| + 1 := by positivity
    calc |C| * (r / R) ^ n ≤ (|C| + 1) * (r / R) ^ n := by
          gcongr; linarith
      _ < (|C| + 1) * (ε / (|C| + 1)) := by gcongr
      _ = ε := by field_simp
  have h4 : |C| * r ^ n < ε * R ^ n := by
    rw [hrn]
    calc |C| * (R ^ n * (r / R) ^ n) = R ^ n * (|C| * (r / R) ^ n) := by ring
      _ < R ^ n * ε := by gcongr
      _ = ε * R ^ n := by ring
  linarith

/-- **Li's criterion from above, with exponential slack.** RH holds iff for every `r > 1` some `C`
gives `Re 2λ_n ≤ C rⁿ` for all `n`. -/
theorem riemannHypothesis_iff_re_xiLiPaired_upper_subexp :
    RiemannHypothesis ↔
      ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ n : ℕ, (xiLiPaired n).re ≤ C * r ^ n := by
  refine ⟨fun hRH r hr => ?_, riemannHypothesis_of_re_xiLiPaired_upper_subexp⟩
  obtain ⟨C₂, hC₂⟩ := exists_sq_le_mul_pow hr
  have hl1 := re_xiLiPaired_nonneg_of_rh hRH 1
  refine ⟨(xiLiPaired 1).re * C₂, fun n => ?_⟩
  calc (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := re_xiLiPaired_le_sq_mul_one_of_rh hRH n
    _ ≤ (C₂ * r ^ n) * (xiLiPaired 1).re := mul_le_mul_of_nonneg_right (hC₂ n) hl1
    _ = (xiLiPaired 1).re * C₂ * r ^ n := by ring

/-- **Li's criterion from above, sharp form.** RH holds iff `Re 2λ_n ≤ n²·Re 2λ_1` for every
`n`. -/
theorem riemannHypothesis_iff_re_xiLiPaired_le_sq_mul_one :
    RiemannHypothesis ↔ ∀ n : ℕ, (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := by
  refine ⟨re_xiLiPaired_le_sq_mul_one_of_rh, fun h => ?_⟩
  refine riemannHypothesis_of_re_xiLiPaired_upper_subexp fun r hr => ?_
  obtain ⟨C₂, hC₂⟩ := exists_sq_le_mul_pow hr
  refine ⟨max (xiLiPaired 1).re 0 * C₂, fun n => ?_⟩
  have hm : 0 ≤ max (xiLiPaired 1).re 0 := le_max_right _ _
  calc (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := h n
    _ ≤ (n : ℝ) ^ 2 * max (xiLiPaired 1).re 0 := by
        gcongr; exact le_max_left _ _
    _ ≤ (C₂ * r ^ n) * max (xiLiPaired 1).re 0 := mul_le_mul_of_nonneg_right (hC₂ n) hm
    _ = max (xiLiPaired 1).re 0 * C₂ * r ^ n := by ring

end RHTower

end
