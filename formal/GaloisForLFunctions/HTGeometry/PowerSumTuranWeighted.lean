import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound

/-!
# A separation-free lower bound for weighted power sums

Let `z_1, …, z_N ∈ ℂ` with some `|z_i| ≥ 1`, and let the weights `β_i ∈ ℂ` lie in the sector
`|β_i| ≤ 2 Re β_i`.  For every `M ≥ 0` some exponent `M + 1 ≤ ν ≤ M + N` satisfies

`|Σ_i β_i z_i^ν| ≥ (Σ_{|z_i| ≥ 1} |β_i|) / (4e N (6(N+1)(M+2N+2))^N)`

(`exists_norm_weightedPowerSum_ge`).  No separation of the points is assumed.

This is the weighted form of Turán's second main theorem with sector weights.  The separating
polynomial of the unit-weight case vanishes at every inner point and is `≈ 1` at every outer point.
Sector weights cannot cancel each other there: the real part of `Σ_outer β_o Q(z_o)` is at least
`Σ |β_o| / 2 − Σ |β_o| / 4`.

Use: a cluster of near-coincident terms with nearly positive weights (for instance, zeros of nearly
equal real part seen through a positive explicit-formula weight) cannot make a power sum small on a
whole window of `N` consecutive exponents.
-/

open Polynomial Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Combination lemma with an arbitrary lower constant. -/
theorem exists_norm_ge_of_combination' {N M : ℕ} (hN : 1 ≤ N) (q S : ℕ → ℂ) {B c : ℝ}
    (hB : 0 < B) (hq : ∑ k ∈ range N, ‖q k‖ ≤ B)
    (hlow : c ≤ ‖∑ k ∈ range N, q k * S (M + N - k)‖) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧ c / B ≤ ‖S ν‖ := by
  obtain ⟨k₀, hk₀, hk₀max⟩ := Finset.exists_max_image (range N)
    (fun k => ‖S (M + N - k)‖) ⟨0, Finset.mem_range.2 (by omega)⟩
  refine ⟨M + N - k₀, by have := Finset.mem_range.1 hk₀; omega, by omega, ?_⟩
  have hup : c ≤ B * ‖S (M + N - k₀)‖ := by
    refine hlow.trans ((norm_sum_le _ _).trans ?_)
    calc ∑ k ∈ range N, ‖q k * S (M + N - k)‖ ≤ ∑ k ∈ range N, ‖q k‖ * ‖S (M + N - k₀)‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hk₀max k hk) (norm_nonneg _)
      _ = (∑ k ∈ range N, ‖q k‖) * ‖S (M + N - k₀)‖ := by rw [Finset.sum_mul]
      _ ≤ B * ‖S (M + N - k₀)‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  rw [div_le_iff₀ hB]
  linarith

/-- The weighted values of the separating polynomial: with sector weights the outer sum keeps a
quarter of its total weight. -/
theorem norm_sum_sepPoly_values_weighted_ge {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (β : ι → ℂ)
    (O I : Finset ι) (hOI : Disjoint O I) (u : ℕ → ℂ) {n J M N : ℕ} (hn1 : 1 ≤ n)
    (hnode : ∀ o ∈ O, ∃ l < n, u l = (z o)⁻¹) (hO0 : ∀ o ∈ O, z o ≠ 0)
    (hdeg : (sepPoly z I u n J (M + N)).natDegree < N) (hIN : I.card ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ) (hJ : (1 + ρ ^ (J + 1)) ^ N - 1 ≤ 1 / 4)
    (hβ : ∀ o ∈ O, ‖β o‖ / 2 ≤ (β o).re) :
    (∑ o ∈ O, ‖β o‖) / 4 ≤ ‖∑ i ∈ O ∪ I, β i * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k)‖ := by
  have hNm : N ≤ M + N := by omega
  have hval_inner : ∀ i ∈ I,
      ∑ k ∈ range N, (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k) = 0 := by
    intro i hi
    by_cases h0 : z i = 0
    · rw [h0]; exact sum_coeff_mul_zero_pow_sub_eq hNm
    · rw [sum_coeff_mul_pow_sub_eq hdeg hNm h0, eval_sepPoly_inner z I u _ _ _ hi h0, mul_zero]
  have hval_outer : ∀ o ∈ O,
      ∑ k ∈ range N, (sepPoly z I u n J (M + N)).coeff k * z o ^ (M + N - k) =
        ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) := by
    intro o ho
    obtain ⟨l, hl, hul⟩ := hnode o ho
    rw [sum_coeff_mul_pow_sub_eq hdeg hNm (hO0 o ho), ← hul, eval_sepPoly_node z I u hn1 hl, hul,
      ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hO0 o ho), one_pow, one_mul]
  have hI0 : ∑ x ∈ I, β x * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z x ^ (M + N - k) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hval_inner i hi, mul_zero]
  have hOv : ∑ x ∈ O, β x * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z x ^ (M + N - k) =
        ∑ o ∈ O, β o * ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) :=
    Finset.sum_congr rfl fun o ho => by rw [hval_outer o ho]
  rw [Finset.sum_union hOI, hI0, add_zero, hOv]
  have herr : ∀ o ∈ O, ‖∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1‖ ≤ 1 / 4 := by
    intro o ho
    have h1 := norm_prod_one_add_sub_one_le I (fun j => -(z j * (z o)⁻¹) ^ (J + 1))
    simp only [← sub_eq_add_neg] at h1
    refine h1.trans ?_
    have hρJ : 0 ≤ ρ ^ (J + 1) := pow_nonneg hρ0 _
    have h2 : ∏ j ∈ I, (1 + ‖-(z j * (z o)⁻¹) ^ (J + 1)‖) ≤ (1 + ρ ^ (J + 1)) ^ N := by
      calc ∏ j ∈ I, (1 + ‖-(z j * (z o)⁻¹) ^ (J + 1)‖) ≤ ∏ _j ∈ I, (1 + ρ ^ (J + 1)) := by
            refine Finset.prod_le_prod (fun _ _ => by positivity) fun j hj => ?_
            rw [norm_neg, norm_pow]
            have := pow_le_pow_left₀ (norm_nonneg _) (hρ o ho j hj) (J + 1)
            linarith
        _ = (1 + ρ ^ (J + 1)) ^ I.card := by rw [Finset.prod_const]
        _ ≤ (1 + ρ ^ (J + 1)) ^ N := pow_le_pow_right₀ (by linarith) hIN
    linarith
  -- real part of the outer sum
  have hre : (∑ o ∈ O, ‖β o‖) / 4 ≤
      (∑ o ∈ O, β o * ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1))).re := by
    rw [Complex.re_sum]
    have hterm : ∀ o ∈ O, ‖β o‖ / 4 ≤
        (β o * ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1))).re := by
      intro o ho
      set P := ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1))
      have hsplit : β o * P = β o + β o * (P - 1) := by ring
      rw [hsplit, Complex.add_re]
      have h1 : -(‖β o‖ / 4) ≤ (β o * (P - 1)).re := by
        have := Complex.abs_re_le_norm (β o * (P - 1))
        rw [norm_mul] at this
        have h2 : ‖β o‖ * ‖P - 1‖ ≤ ‖β o‖ * (1 / 4) :=
          mul_le_mul_of_nonneg_left (herr o ho) (norm_nonneg _)
        have h3 := neg_abs_le (β o * (P - 1)).re
        linarith
      linarith [hβ o ho]
    calc (∑ o ∈ O, ‖β o‖) / 4 = ∑ o ∈ O, ‖β o‖ / 4 := by rw [Finset.sum_div]
      _ ≤ _ := Finset.sum_le_sum hterm
  exact hre.trans (Complex.re_le_norm _)

/-- **Weighted separation-free power-sum lower bound.**  If `|z_i| ≥ 1` for some `i ∈ s` and every
weight lies in the sector `|β_i| ≤ 2 Re β_i`, then for every `M` some exponent
`M + 1 ≤ ν ≤ M + N`, `N = #s`, has
`|Σ_i β_i z_i^ν| ≥ (Σ_{|z_i| ≥ 1} |β_i|) / (4e N (6(N+1)(M+2N+2))^N)`. -/
theorem exists_norm_weightedPowerSum_ge {ι : Type*} (s : Finset ι) (z β : ι → ℂ)
    (htop : ∃ i ∈ s, 1 ≤ ‖z i‖) (hβ : ∀ i ∈ s, ‖β i‖ / 2 ≤ (β i).re) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      (∑ i ∈ s.filter (fun i => 1 ≤ ‖z i‖), ‖β i‖) /
          (4 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) ≤
        ‖∑ i ∈ s, β i * z i ^ ν‖ := by
  classical
  obtain ⟨i₀, hi₀s, hi₀⟩ := htop
  have hN1 : 1 ≤ s.card := Finset.card_pos.2 ⟨i₀, hi₀s⟩
  have hθ0 : 0 < 1 / ((M : ℝ) + 2 * s.card + 2) := by positivity
  obtain ⟨r, hr1, hr2, hsplit⟩ := exists_gap_radius s (fun i => ‖z i‖) hθ0
  set g : ℝ := 1 / ((M : ℝ) + 2 * s.card + 2) / (2 * (s.card + 1)) with hg
  obtain ⟨hg0, hrg, hr0, -, -, -, -, -⟩ := gap_params hN1 hg hr1 hr2
  have hrgpos : 0 < r + g := by linarith
  set O := s.filter (fun i => r + g ≤ ‖z i‖) with hO
  set I := s.filter (fun i => ¬ (r + g ≤ ‖z i‖)) with hI
  have hIle : ∀ i ∈ I, ‖z i‖ ≤ r - g := by
    intro i hi
    obtain ⟨his, hn⟩ := Finset.mem_filter.1 hi
    rcases hsplit i his with h | h
    · exact h
    · exact absurd h hn
  have hOge : ∀ i ∈ O, r + g ≤ ‖z i‖ := fun i hi => (Finset.mem_filter.1 hi).2
  have hcardOI : O.card + I.card = s.card := Finset.card_filter_add_card_filter_not _
  have hO1 : 1 ≤ O.card := Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨hi₀s, hrg.trans hi₀⟩⟩
  have hO0 : ∀ o ∈ O, z o ≠ 0 := by
    intro o ho h; have := hOge o ho; rw [h, norm_zero] at this; linarith
  set u : ℕ → ℂ := fun l => if h : l < O.card then (z (O.equivFin.symm ⟨l, h⟩).1)⁻¹ else 0
    with hu
  have huR : ∀ l, ‖u l‖ ≤ 1 / (r + g) := by
    intro l
    by_cases h : l < O.card
    · simp only [hu]
      rw [dif_pos h, norm_inv, one_div]
      exact inv_anti₀ hrgpos (hOge _ (O.equivFin.symm ⟨l, h⟩).2)
    · simp only [hu]
      rw [dif_neg h, norm_zero]; positivity
  have hnode : ∀ o ∈ O, ∃ l < O.card, u l = (z o)⁻¹ := by
    intro o ho
    refine ⟨O.equivFin ⟨o, ho⟩, (O.equivFin ⟨o, ho⟩).2, ?_⟩
    simp only [hu]
    rw [dif_pos (O.equivFin ⟨o, ho⟩).2]
    simp only [Fin.eta, Equiv.symm_apply_apply]
  set ρ : ℝ := (r - g) / (r + g) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hrgpos]; linarith
  have hρz : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ := by
    intro o ho j hj
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact div_le_div₀ hr0.le (hIle j hj) hrgpos (hOge o ho)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (1 + ρ ^ (J + 1)) ^ s.card - 1 ≤ 1 / 4 := by
    have h1 : Tendsto (fun J : ℕ => ρ ^ (J + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
    have ht : Tendsto (fun J : ℕ => (1 + ρ ^ (J + 1)) ^ s.card - 1) atTop
        (𝓝 ((1 + 0) ^ s.card - 1)) :=
      ((tendsto_const_nhds.add h1).pow _).sub tendsto_const_nhds
    rw [add_zero, one_pow, sub_self] at ht
    exact (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  have hdeg : (sepPoly z I u O.card J (M + s.card)).natDegree < s.card := by
    have h := natDegree_sepPoly_le z I u O.card J (M + s.card)
    omega
  have hOI : Disjoint O I := Finset.disjoint_filter_filter_not _ _ _
  have hs : O ∪ I = s := Finset.filter_union_filter_not_eq _ _
  have hlow := norm_sum_sepPoly_values_weighted_ge z β O I hOI u hO1 hnode hO0 hdeg (by omega)
    hρ0 hρz hJ (fun o ho => hβ o (Finset.mem_filter.1 ho).1)
  rw [hs] at hlow
  have hcoef : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ ≤
      Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card := by
    have hw1 : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ =
        wNorm 1 (sepPoly z I u O.card J (M + s.card)) := by
      rw [wNorm_eq_sum_of_lt 1 hdeg]; simp
    rw [hw1]
    exact wNorm_sepPoly_le_of_gap z I u hN1 hcardOI hg hr1 hr2 hIle huR
  have hident : ∑ i ∈ s, β i * ∑ k ∈ range s.card,
      (sepPoly z I u O.card J (M + s.card)).coeff k * z i ^ (M + s.card - k) =
        ∑ k ∈ range s.card, (sepPoly z I u O.card J (M + s.card)).coeff k *
          ∑ i ∈ s, β i * z i ^ (M + s.card - k) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hident] at hlow
  -- the outer weight dominates the weight on `|z| ≥ 1`
  have hOsub : s.filter (fun i => 1 ≤ ‖z i‖) ⊆ O := by
    intro i hi
    obtain ⟨his, h1⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨his, hrg.trans h1⟩
  have hmass : (∑ i ∈ s.filter (fun i => 1 ≤ ‖z i‖), ‖β i‖) ≤ ∑ o ∈ O, ‖β o‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hOsub fun _ _ _ => norm_nonneg _
  set B : ℝ := Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card
    with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  obtain ⟨ν, h1, h2, h3⟩ := exists_norm_ge_of_combination' hN1 _ (fun ν => ∑ i ∈ s, β i * z i ^ ν)
    hBpos hcoef hlow
  refine ⟨ν, h1, h2, le_trans ?_ h3⟩
  have e := div_div (∑ o ∈ O, ‖β o‖) 4 B
  rw [e]
  exact div_le_div_of_nonneg_right hmass (mul_pos (by norm_num) hBpos).le

end

end GaloisForLFunctions.HTGeometry
