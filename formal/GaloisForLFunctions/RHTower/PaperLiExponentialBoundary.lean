import GaloisForLFunctions.RHTower.PaperLiExponentialFrontier

/-!
# The boundary rate of the Li exponential frontier

Let `W > 1` be the modulus of a normalized Cayley root `v_{ρ₀}`.  Then
`Re(2λ_n) ≤ −W^n/4` for arbitrarily large `n`
(`exists_ge_re_xiLiPaired_le_neg_quarter_pow`).  This is the hard half of Li's criterion with no
loss in the rate.  Pigeonhole on the finitely many roots of modulus near the top makes all of
them point near the positive axis at once.  At such times every one of them pushes the Li sum
down, while the roots of modulus `≤ (1+W)/2` contribute only `O(n²((1+W)/2)ⁿ)`.

So the negative-Li weights at the rate `W` itself stay above `1/(1+4b)` infinitely often, and the
diagonal operator is not compact (`paperLiExponentialOperator_not_compact_at_root`).  This closes
the boundary case of the frontier: for every rate `r ≥ 1`, the operator is compact iff every root
has modulus `< r`, or RH holds (`paperLiExponentialOperator_compact_iff`).
-/

namespace RHTower

noncomputable section

open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators

variable {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}

/-- **Lossless hard half of Li's criterion, abstract form.**  If one member of the family has
modulus `W > 1`, then the paired Li sum drops below `−(m_{i₀}/4) Wⁿ` at arbitrarily large `n`. -/
theorem exists_ge_re_tsum_liTerm_le_neg_quarter_pow
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ))
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑' i, m i * (liTerm (v i) n).re) ≤ -(m i₀ / 4 * ‖v i₀‖ ^ n) := by
  classical
  set W : ℝ := ‖v i₀‖ with hWdef
  set q : ℝ := (1 + W) / 2 with hqdef
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqW : q < W := by rw [hqdef]; linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hFfin : {i | q ≤ ‖v i‖}.Finite := finite_far_set hm hs hq1
  set S : Finset ι := hFfin.toFinset with hSdef
  have hmemS : ∀ i, i ∈ S ↔ q ≤ ‖v i‖ := by
    intro i
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl
  have hi₀S : i₀ ∈ S := (hmemS i₀).mpr (le_of_lt hqW)
  set C : ℝ := ∑' i, m i * ‖v i - 1‖ ^ (2 : ℕ) with hCdef
  have hm0 : ∀ i, (0 : ℝ) ≤ m i := fun i => by linarith [hm i]
  have hC0 : 0 ≤ C := tsum_nonneg fun i => mul_nonneg (hm0 i) (sq_nonneg _)
  set T : ℝ := ∑ i ∈ S, m i with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => hm0 i
  -- the polynomial-times-`q^n` part is eventually below `m₀ Wⁿ / 4`
  set r : ℝ := q / W with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hW0]; exact hqW
  have hlim : Tendsto (fun n : ℕ => (3 * T + C * (n : ℝ) ^ (2 : ℕ)) * r ^ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 2 (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    have h2 := hsum.tendsto_atTop_zero
    have := (h1.const_mul (3 * T)).add (h2.const_mul C)
    simpa [add_mul, mul_assoc] using this
  have hm4 : (0 : ℝ) < m i₀ / 4 := by linarith [hm i₀]
  obtain ⟨N₀, hN₀⟩ := (hlim.eventually (gt_mem_nhds hm4)).exists_forall_of_atTop
  -- pigeonhole at a time `n ≥ max N N₀`
  have hunit : ∀ i : {x // x ∈ S}, ‖v (i : ι) / (‖v (i : ι)‖ : ℂ)‖ = 1 := by
    rintro ⟨i, hi⟩
    have hvi : (0 : ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvi, div_self (ne_of_gt hvi)]
  obtain ⟨n, hnN, -, hnre⟩ :=
    exists_ge_pow_re_gt_half (fun i : {x // x ∈ S} => v (i : ι) / (‖v (i : ι)‖ : ℂ)) hunit
      (max N N₀)
  refine ⟨n, le_trans (le_max_left _ _) hnN, ?_⟩
  have hsummable := summable_re_liTerm_of_one_le hm0 hv hM hs n
  have hsplit := hsummable.sum_add_tsum_compl (s := S)
  -- the tail
  have hBsum : Summable fun i : {x // x ∈ (↑S : Set ι)ᶜ} =>
      (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) :=
    (hs.subtype _).mul_left _
  have hBle : ∀ i : {x // x ∈ (↑S : Set ι)ᶜ},
      m (i : ι) * (liTerm (v (i : ι)) n).re
        ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) := by
    rintro ⟨i, hi⟩
    have hiS : ¬ (q ≤ ‖v i‖) := by
      intro h
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hi
      exact hi ((hmemS i).mpr h)
    have hlt' : ‖v i‖ < q := lt_of_not_ge hiS
    have hvne : v i ≠ 0 := by
      intro h; have h1 := hv i; rw [h] at h1; simp at h1; linarith
    have hmax : max ‖v i‖ ‖v i‖⁻¹ = ‖v i‖ := by
      refine max_eq_left ?_
      have h1 : (0 : ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith [hv i]
    have hbase := norm_liTerm_le hvne n
    rw [hmax] at hbase
    have hpow : ‖v i‖ ^ n ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg _) hlt'.le n
    have hchain : ‖liTerm (v i) n‖ ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v i - 1‖ ^ (2 : ℕ) := by
      refine le_trans hbase ?_
      rw [mul_assoc, mul_assoc]
      gcongr
    calc m i * (liTerm (v i) n).re
        ≤ m i * ((n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v i - 1‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans hchain) (hm0 i)
      _ = (n : ℝ) ^ (2 : ℕ) * q ^ n * (m i * ‖v i - 1‖ ^ (2 : ℕ)) := by ring
  have htailC : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) ≤ C := by
    have hsp := hs.sum_add_tsum_compl (s := S)
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ S, m i * ‖v i - 1‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hm0 i) (sq_nonneg _)
    rw [hCdef, ← hsp]
    linarith
  have htail : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re)
      ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * C := by
    refine le_trans (Summable.tsum_le_tsum hBle (hsummable.subtype ((↑S : Set ι)ᶜ)) hBsum) ?_
    rw [Summable.tsum_mul_left]
    · exact mul_le_mul_of_nonneg_left htailC (by positivity)
    · exact hs.subtype _
  -- the head
  have hbig : ∀ i ∈ S, ‖v i‖ ^ n / 2 ≤ (v i ^ n).re := by
    intro i hi
    have hvi : (0 : ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
    have hfac : v i = (‖v i‖ : ℂ) * (v i / (‖v i‖ : ℂ)) := by
      have hcne : ((‖v i‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hvi)
      field_simp
    have hpow : v i ^ n = ((‖v i‖ : ℂ)) ^ n * (v i / (‖v i‖ : ℂ)) ^ n := by
      rw [← mul_pow, ← hfac]
    have hre : (v i ^ n).re = ‖v i‖ ^ n * ((v i / (‖v i‖ : ℂ)) ^ n).re := by
      rw [hpow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have hhalf := hnre ⟨i, hi⟩
    rw [hre]
    have hpos : (0 : ℝ) < ‖v i‖ ^ n := by positivity
    nlinarith
  have hSup : ∑ i ∈ S, m i * (liTerm (v i) n).re ≤ 3 * T - ∑ i ∈ S, m i * (v i ^ n).re := by
    rw [hTdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hinv : (-1 : ℝ) ≤ ((v i)⁻¹ ^ n).re := by
      have h2 : ‖(v i)⁻¹ ^ n‖ ≤ 1 := by
        rw [norm_pow, norm_inv]
        exact pow_le_one₀ (by positivity)
          ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hv i))).mpr (hv i))
      have h3 : -‖(v i)⁻¹ ^ n‖ ≤ ((v i)⁻¹ ^ n).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)
      linarith
    have hlire : (liTerm (v i) n).re = 2 - (v i ^ n).re - ((v i)⁻¹ ^ n).re := by
      rw [liTerm]; simp
    rw [hlire]
    nlinarith [hm0 i]
  have hall : ∀ i ∈ S, (0 : ℝ) ≤ m i * (v i ^ n).re := by
    intro i hi
    have h1 := hbig i hi
    have h2 : (0 : ℝ) ≤ ‖v i‖ ^ n := by positivity
    nlinarith [hm0 i]
  have hone : m i₀ * (v i₀ ^ n).re ≤ ∑ i ∈ S, m i * (v i ^ n).re :=
    Finset.single_le_sum hall hi₀S
  have hi₀big : m i₀ * (W ^ n / 2) ≤ m i₀ * (v i₀ ^ n).re :=
    mul_le_mul_of_nonneg_left (hbig i₀ hi₀S) (hm0 i₀)
  -- assemble: `3T + n² qⁿ C ≤ (m₀/4) Wⁿ`
  have hsmall := hN₀ n (le_trans (le_max_right _ _) hnN)
  have hWn : (0 : ℝ) < W ^ n := pow_pos hW0 n
  have hqn : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq1.le
  have hrn : r ^ n * W ^ n = q ^ n := by rw [hrdef, div_pow]; field_simp
  have hpoly : 3 * T + (n : ℝ) ^ (2 : ℕ) * q ^ n * C ≤ m i₀ / 4 * W ^ n := by
    have h1 : 3 * T ≤ 3 * T * q ^ n := le_mul_of_one_le_right (by linarith) hqn
    have h2 : (3 * T + C * (n : ℝ) ^ (2 : ℕ)) * r ^ n * W ^ n ≤ m i₀ / 4 * W ^ n :=
      mul_le_mul_of_nonneg_right hsmall.le hWn.le
    have h3 : (3 * T + C * (n : ℝ) ^ (2 : ℕ)) * r ^ n * W ^ n =
        (3 * T + C * (n : ℝ) ^ (2 : ℕ)) * q ^ n := by rw [mul_assoc, hrn]
    nlinarith
  rw [← hsplit]
  linarith

/-! ### The actual Li coefficients -/

/-- **Lossless hard half for the actual paired Li coefficients.**  A normalized Cayley root of
modulus `W > 1` forces `Re(2λ_n) ≤ −Wⁿ/4` at arbitrarily large `n`. -/
theorem exists_ge_re_xiLiPaired_le_neg_quarter_pow {ρ₁ : ℂ} (hρ₁ : xi ρ₁ = 0)
    (hW : 1 < ‖xiRootV ρ₁‖) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (xiLiPaired n).re ≤ -(‖xiRootV ρ₁‖ ^ n / 4) := by
  set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁⟩
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := fun ρ => by
    rw [norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)]; exact hMb ρ
  obtain ⟨n, hnN, hn⟩ := exists_ge_re_tsum_liTerm_le_neg_quarter_pow one_le_liSupport_mult
    (fun ρ => one_le_norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)) hvM
    summable_liSupport_mult_norm_xiRootV_sub_one_sq (i₀ := ρ₀) (by simpa [ρ₀] using hW) N
  refine ⟨n, hnN, ?_⟩
  rw [re_xiLiPaired_eq_tsum]
  have hm1 := one_le_liSupport_mult ρ₀
  have hWn : (0 : ℝ) ≤ ‖xiRootV ρ₁‖ ^ n := by positivity
  have hcmp : ‖xiRootV ρ₁‖ ^ n / 4 ≤
      ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ) : ℝ) / 4 * ‖xiRootV (ρ₀ : ℂ)‖ ^ n := by
    simp only [ρ₀]
    nlinarith
  linarith

/-- At the rate `W` of a root, the negative-Li weights exceed `1/(1+4b)` infinitely often. -/
theorem exists_ge_paperLiExponentialWeight_at_root (b : PaperLiBudget) {ρ₁ : ℂ}
    (hρ₁ : xi ρ₁ = 0) (hW : 1 < ‖xiRootV ρ₁‖) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 / (1 + 4 * b.val) ≤
      paperLiExponentialWeight b ⟨‖xiRootV ρ₁‖, hW.le⟩ n := by
  obtain ⟨n, hnN, hn⟩ := exists_ge_re_xiLiPaired_le_neg_quarter_pow hρ₁ hW N
  refine ⟨n, hnN, ?_⟩
  set W : ℝ := ‖xiRootV ρ₁‖ with hWdef
  have hWn : 0 < W ^ n := pow_pos (by linarith) n
  have hmass : W ^ n / 4 ≤ paperLiNegativeMass n := by
    rw [paperLiNegativeMass]; exact le_max_of_le_right (by linarith)
  have hscaled : 1 / 4 ≤ paperLiScaledMass ⟨W, hW.le⟩ n := by
    rw [paperLiScaledMass, le_div_iff₀ hWn]
    linarith
  rw [paperLiExponentialWeight_eq_scaled]
  set s : ℝ := paperLiScaledMass ⟨W, hW.le⟩ n with hs
  have hb := b.property
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- **The boundary rate is not compact.**  At the rate equal to the modulus of a root outside
the unit circle, the negative-Li operator is not compact. -/
theorem paperLiExponentialOperator_not_compact_at_root (b : PaperLiBudget) {ρ₁ : ℂ}
    (hρ₁ : xi ρ₁ = 0) (hW : 1 < ‖xiRootV ρ₁‖) :
    ¬ IsCompactOperator (paperLiExponentialOperator b ⟨‖xiRootV ρ₁‖, hW.le⟩) := by
  intro hK
  have hlim := tendsto_norm_of_isCompactOperator_lpDiagonalCLM _ zero_le_one
    (paperLiExponentialWeight_norm_le b ⟨‖xiRootV ρ₁‖, hW.le⟩) hK
  have hc : (0 : ℝ) < 1 / (1 + 4 * b.val) := by have := b.property; positivity
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hc)).exists_forall_of_atTop
  obtain ⟨n, hnN, hn⟩ := exists_ge_paperLiExponentialWeight_at_root b hρ₁ hW N
  have h := hN n hnN
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperLiExponentialWeight_nonneg _ _ _)] at h
  linarith

/-- **The frontier with its boundary.**  For every rate `r ≥ 1` and every budget, the negative-Li
operator is compact iff every normalized Cayley root has modulus strictly below `r`, or RH holds. -/
theorem paperLiExponentialOperator_compact_iff (b : PaperLiBudget) (r : PaperLiRate) :
    IsCompactOperator (paperLiExponentialOperator b r) ↔
      (∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ < r.val) ∨ RiemannHypothesis := by
  constructor
  · intro hK
    by_cases hRH : RiemannHypothesis
    · exact Or.inr hRH
    left
    intro ρ hρ
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with heq | hgt
    · -- the root sits exactly at the rate
      rcases eq_or_lt_of_le r.property with hr1 | hr1
      · -- rate one: use a root strictly outside the unit circle
        have hcay := (riemannHypothesis_iff_cayley_le_one).not.mp hRH
        push Not at hcay
        obtain ⟨ρ₂, hρ₂, hgt₂⟩ := hcay
        have hd := compactIdealDistance_eq_zero_of_isCompactOperator _ hK
        rw [paperLiExponentialOperator_unit_distance b r
          ⟨ρ₂, mem_xi_divisor_support_of_eq_zero hρ₂⟩ (by simpa [← hr1] using hgt₂)] at hd
        exact one_ne_zero hd
      · have hW : 1 < ‖xiRootV ρ‖ := by rw [← heq]; exact hr1
        have hr : r = ⟨‖xiRootV ρ‖, hW.le⟩ := Subtype.ext heq
        rw [hr] at hK
        exact paperLiExponentialOperator_not_compact_at_root b hρ hW hK
    · have hd := compactIdealDistance_eq_zero_of_isCompactOperator _ hK
      rw [paperLiExponentialOperator_unit_distance b r
        ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩ hgt] at hd
      exact one_ne_zero hd
  · rintro (hlt | hRH)
    · by_cases hRH : RiemannHypothesis
      · -- under RH every weight vanishes
        have hw : ∀ n, paperLiExponentialWeight b r n = 0 := by
          intro n
          rw [paperLiExponentialWeight_eq_scaled, paperLiScaledMass,
            paperLiNegativeMass_of_RH hRH]
          simp
        apply isCompactOperator_lpDiagonalCLM
        simp [hw]
      -- off RH some root lies outside the unit circle, so `r > 1`
      have hcay := (riemannHypothesis_iff_cayley_le_one).not.mp hRH
      push Not at hcay
      obtain ⟨ρ₂, hρ₂, hgt₂⟩ := hcay
      have hr1 : 1 < r.val := lt_trans hgt₂ (hlt ρ₂ hρ₂)
      set q : ℝ := (1 + r.val) / 2 with hq
      have hq1 : 1 < q := by rw [hq]; linarith
      have hqr : q < r.val := by rw [hq]; linarith
      obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
      have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := fun ρ => by
        rw [norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)]; exact hMb ρ
      have hfin : {ρ : XiDivisorSupport | q ≤ ‖xiRootV (ρ : ℂ)‖}.Finite :=
        finite_far_set (v := fun ρ : XiDivisorSupport => xiRootV (ρ : ℂ)) one_le_liSupport_mult
          summable_liSupport_mult_norm_xiRootV_sub_one_sq hq1
      -- a uniform bound `R < r` for all roots
      obtain ⟨R, hR1, hRr, hroots⟩ : ∃ R : ℝ, 1 ≤ R ∧ R < r.val ∧
          ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R := by
        by_cases hne : hfin.toFinset.Nonempty
        · obtain ⟨ρs, hρs, hmax⟩ :=
            hfin.toFinset.exists_max_image (fun ρ : XiDivisorSupport => ‖xiRootV (ρ : ℂ)‖) hne
          refine ⟨max q ‖xiRootV (ρs : ℂ)‖, le_trans hq1.le (le_max_left _ _), ?_, ?_⟩
          · exact max_lt hqr (hlt _ (xi_eq_zero_of_mem_divisor_support ρs))
          · intro ρ hρ
            set ρ' : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
            by_cases hbig : q ≤ ‖xiRootV ρ‖
            · have hmem : ρ' ∈ hfin.toFinset := by
                rw [Set.Finite.mem_toFinset]; exact hbig
              exact le_trans (hmax ρ' hmem) (le_max_right _ _)
            · exact le_trans (le_of_lt (lt_of_not_ge hbig)) (le_max_left _ _)
        · refine ⟨q, hq1.le, hqr, fun ρ hρ => ?_⟩
          by_contra hbig
          push Not at hbig
          apply hne
          refine ⟨⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩, ?_⟩
          rw [Set.Finite.mem_toFinset]
          exact hbig.le
      exact paperLiExponentialOperator_compact hR1 b r hRr hroots
    · -- under RH every weight vanishes
      have hw : ∀ n, paperLiExponentialWeight b r n = 0 := by
        intro n
        rw [paperLiExponentialWeight_eq_scaled, paperLiScaledMass,
          paperLiNegativeMass_of_RH hRH]
        simp
      apply isCompactOperator_lpDiagonalCLM
      simp [hw]

end

end RHTower
