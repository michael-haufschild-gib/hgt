import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound

/-!
# Weighted separation-free power-sum lower bound

For complex points `z_1, …, z_N`, at least one of modulus `≥ 1`, and complex weights `b_i`, suppose
that every *top group* `{i : |z_i| ≥ t}` with `1 − 1/(M + 2N + 2) ≤ t ≤ 1` has weight sum of modulus at
least `β > 0`.  Then some exponent `M + 1 ≤ ν ≤ M + N` satisfies

`|Σ_i b_i z_i^ν| ≥ β / (2e N (6(N+1)(M+2N+2))^N)`

(`exists_norm_weightedPowerSum_ge`; scaled form `exists_norm_weightedPowerSum_ge_scaled`).

This is Turán's second main theorem with coefficients.  The separating polynomial of the unit-weight
case (`PowerSumTuranLowerBound`) vanishes on the inner group and is `≈ 1` on the outer group, so the
weighted value sum is the outer weight sum up to a relative error `(1 + ρ^{J+1})^N − 1`, which the
truncation length `J` makes as small as needed.  The coefficient mass of the separating polynomial does
not depend on `J`.  No separation of the points is assumed.
-/

open Polynomial Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weighted values of the separating polynomial: inner points contribute `0`, outer points
contribute `b_o (1 + small)`. -/
theorem norm_weighted_sum_sepPoly_values_ge {ι : Type*} [DecidableEq ι] (z b : ι → ℂ)
    (O I : Finset ι) (hOI : Disjoint O I) (u : ℕ → ℂ) {n J M N : ℕ} (hn1 : 1 ≤ n)
    (hIN : I.card ≤ N) (hnode : ∀ o ∈ O, ∃ l < n, u l = (z o)⁻¹) (hO0 : ∀ o ∈ O, z o ≠ 0)
    (hdeg : (sepPoly z I u n J (M + N)).natDegree < N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ) {β : ℝ} (hβ : β ≤ ‖∑ o ∈ O, b o‖)
    (hJ : ((1 + ρ ^ (J + 1)) ^ N - 1) * ∑ o ∈ O, ‖b o‖ ≤ β / 4) :
    3 * β / 4 ≤ ‖∑ i ∈ O ∪ I, b i * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k)‖ := by
  have hNm : N ≤ M + N := by omega
  have hval_inner : ∀ i ∈ I, b i * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k) = 0 := by
    intro i hi
    by_cases h0 : z i = 0
    · rw [h0, sum_coeff_mul_zero_pow_sub_eq hNm, mul_zero]
    · rw [sum_coeff_mul_pow_sub_eq hdeg hNm h0, eval_sepPoly_inner z I u _ _ _ hi h0, mul_zero,
        mul_zero]
  have hval_outer : ∀ o ∈ O, b o * ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z o ^ (M + N - k) =
        b o * ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) := by
    intro o ho
    obtain ⟨l, hl, hul⟩ := hnode o ho
    rw [sum_coeff_mul_pow_sub_eq hdeg hNm (hO0 o ho), ← hul, eval_sepPoly_node z I u hn1 hl, hul,
      ← mul_assoc (z o ^ (M + N)), ← mul_pow, mul_inv_cancel₀ (hO0 o ho), one_pow, one_mul]
  rw [Finset.sum_union hOI, Finset.sum_eq_zero hval_inner, add_zero,
    Finset.sum_congr rfl hval_outer]
  set ε : ℝ := (1 + ρ ^ (J + 1)) ^ N - 1 with hε
  have herr : ∀ o ∈ O, ‖∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1‖ ≤ ε := by
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
    rw [hε]
    linarith
  set E : ℂ := ∑ o ∈ O, b o * (∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1) with hE
  have hsplit : ∑ o ∈ O, b o * ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) =
      ∑ o ∈ O, b o + E := by
    rw [hE, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  have hEb : ‖E‖ ≤ ε * ∑ o ∈ O, ‖b o‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun o ho => ?_
    rw [norm_mul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (herr o ho) (norm_nonneg _)
  have h3 := norm_sub_norm_le (∑ o ∈ O, b o) (-E)
  rw [norm_neg, sub_neg_eq_add] at h3
  rw [hsplit]
  linarith

/-- **Weighted separation-free power-sum lower bound** (Turán's second main theorem with
coefficients).  If some `|z_i| ≥ 1` and every top group `{i : t ≤ |z_i|}`,
`1 − 1/(M + 2N + 2) ≤ t ≤ 1`, has weight sum of modulus `≥ β > 0`, then some exponent
`M + 1 ≤ ν ≤ M + N` has `|Σ_i b_i z_i^ν| ≥ β/(2e N (6(N+1)(M+2N+2))^N)`. -/
theorem exists_norm_weightedPowerSum_ge {ι : Type*} (s : Finset ι) (z b : ι → ℂ)
    (htop : ∃ i ∈ s, 1 ≤ ‖z i‖) (M : ℕ) {β : ℝ} (hβ0 : 0 < β)
    (hβ : ∀ t : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ t → t ≤ 1 →
      β ≤ ‖∑ i ∈ s.filter (fun i => t ≤ ‖z i‖), b i‖) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      β / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) ≤
        ‖∑ i ∈ s, b i * z i ^ ν‖ := by
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
  -- the outer weight sum
  have hβO : β ≤ ‖∑ o ∈ O, b o‖ := hβ (r + g) (by linarith) hrg
  -- outer reciprocals as Newton nodes
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
  -- the truncation length
  set ρ : ℝ := (r - g) / (r + g) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hrgpos]; linarith
  have hρz : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ := by
    intro o ho j hj
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact div_le_div₀ hr0.le (hIle j hj) hrgpos (hOge o ho)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ((1 + ρ ^ (J + 1)) ^ s.card - 1) * ∑ o ∈ O, ‖b o‖ ≤ β / 4 := by
    have h1 : Tendsto (fun J : ℕ => ρ ^ (J + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
    have ht : Tendsto (fun J : ℕ => ((1 + ρ ^ (J + 1)) ^ s.card - 1) * ∑ o ∈ O, ‖b o‖) atTop
        (𝓝 (((1 + 0) ^ s.card - 1) * ∑ o ∈ O, ‖b o‖)) :=
      (((tendsto_const_nhds.add h1).pow _).sub tendsto_const_nhds).mul_const _
    rw [add_zero, one_pow, sub_self, zero_mul] at ht
    exact (ht.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < β / 4))).exists
  -- the separating polynomial
  have hdeg : (sepPoly z I u O.card J (M + s.card)).natDegree < s.card := by
    have h := natDegree_sepPoly_le z I u O.card J (M + s.card)
    omega
  have hOI : Disjoint O I := Finset.disjoint_filter_filter_not _ _ _
  have hs : O ∪ I = s := Finset.filter_union_filter_not_eq _ _
  have hlow := norm_weighted_sum_sepPoly_values_ge z b O I hOI u hO1 (by omega) hnode hO0 hdeg
    hρ0 hρz hβO hJ
  rw [hs] at hlow
  have hcoef : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ ≤
      Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card := by
    have hw1 : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ =
        wNorm 1 (sepPoly z I u O.card J (M + s.card)) := by
      rw [wNorm_eq_sum_of_lt 1 hdeg]; simp
    rw [hw1]
    exact wNorm_sepPoly_le_of_gap z I u hN1 hcardOI hg hr1 hr2 hIle huR
  -- normalize by `β` and apply the combination lemma
  set S : ℕ → ℂ := fun ν => (∑ i ∈ s, b i * z i ^ ν) / (β : ℂ) with hS
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hident : ∑ k ∈ range s.card, (sepPoly z I u O.card J (M + s.card)).coeff k *
      S (M + s.card - k) = (∑ i ∈ s, b i * ∑ k ∈ range s.card,
        (sepPoly z I u O.card J (M + s.card)).coeff k * z i ^ (M + s.card - k)) / (β : ℂ) := by
    simp only [hS, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hlow' : 3 / 4 ≤ ‖∑ k ∈ range s.card, (sepPoly z I u O.card J (M + s.card)).coeff k *
      S (M + s.card - k)‖ := by
    rw [hident, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0, le_div_iff₀ hβ0]
    linarith
  obtain ⟨ν, h1, h2, h3⟩ := exists_norm_ge_of_combination hN1 _ S (by positivity) hcoef hlow'
  refine ⟨ν, h1, h2, ?_⟩
  set B' : ℝ := Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card
    with hB'
  have h3' : 1 / (2 * B') ≤ ‖∑ i ∈ s, b i * z i ^ ν‖ / β := by
    have e : ‖S ν‖ = ‖∑ i ∈ s, b i * z i ^ ν‖ / β := by
      rw [hS]; simp only; rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
    rw [← e]; exact h3
  rw [le_div_iff₀ hβ0] at h3'
  calc β / (2 * B') = 1 / (2 * B') * β := by ring
    _ ≤ _ := h3'

/-- **Scaled weighted form.**  If some `|z_i| ≥ Z > 0` and every top group `{i : tZ ≤ |z_i|}`,
`1 − 1/(M + 2N + 2) ≤ t ≤ 1`, has weight sum of modulus `≥ β > 0`, then some `M + 1 ≤ ν ≤ M + N` has
`|Σ_i b_i z_i^ν| ≥ β Z^ν/(2e N (6(N+1)(M+2N+2))^N)`. -/
theorem exists_norm_weightedPowerSum_ge_scaled {ι : Type*} (s : Finset ι) (z b : ι → ℂ) {Z : ℝ}
    (hZ : 0 < Z) (htop : ∃ i ∈ s, Z ≤ ‖z i‖) (M : ℕ) {β : ℝ} (hβ0 : 0 < β)
    (hβ : ∀ t : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ t → t ≤ 1 →
      β ≤ ‖∑ i ∈ s.filter (fun i => t * Z ≤ ‖z i‖), b i‖) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      β * Z ^ ν / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^
        s.card)) ≤ ‖∑ i ∈ s, b i * z i ^ ν‖ := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := htop
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hnz : ∀ i, ‖z i / (Z : ℂ)‖ = ‖z i‖ / Z := fun i => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  have hfilter : ∀ t : ℝ, s.filter (fun i => t ≤ ‖z i / (Z : ℂ)‖) =
      s.filter (fun i => t * Z ≤ ‖z i‖) := by
    intro t
    refine Finset.filter_congr fun i _ => ?_
    rw [hnz, le_div_iff₀ hZ]
  obtain ⟨ν, h1, h2, h3⟩ := exists_norm_weightedPowerSum_ge s (fun i => z i / Z) b
    ⟨i₀, hi₀s, by rw [hnz, le_div_iff₀ hZ, one_mul]; exact hi₀⟩ M hβ0
    (fun t ht1 ht2 => by rw [hfilter t]; exact hβ t ht1 ht2)
  refine ⟨ν, h1, h2, ?_⟩
  have hsum : ∑ i ∈ s, b i * (z i / Z) ^ ν = (∑ i ∈ s, b i * z i ^ ν) / (Z : ℂ) ^ ν := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [div_pow, mul_div_assoc]
  rw [hsum, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ,
    le_div_iff₀ (pow_pos hZ ν)] at h3
  set L : ℝ := 2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^
    s.card) with hL
  have hLpos : 0 < L := by
    have hs : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 ⟨i₀, hi₀s⟩
    rw [hL]; positivity
  rw [div_le_iff₀ hLpos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hLpos] at h3
  nlinarith [pow_pos hZ ν]

end

end GaloisForLFunctions.HTGeometry
