import Mathlib

/-!
# Superexponential ratio growth beats every linear scale

If the successive ratios of a positive sequence tend to infinity, the sequence eventually
dominates any geometric sequence, so it beats the linear scale:
`b (n+1) / b n → ∞` forces `b n / n → ∞`
(`tendsto_div_natCast_atTop_of_ratio_tendsto_atTop`).  This is the growth input turning a
log-superlacunary Taylor magnitude `|a_n| = exp(−b_n)` into an entire function: the
coefficient decay beats every power scale.
-/

open Filter

namespace GaloisForLFunctions

/-- Geometric growth beats the linear scale: `2^n/n → ∞`. -/
theorem tendsto_two_pow_div_natCast_atTop :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n / n) atTop atTop := by
  have hhalf : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
    simpa using tendsto_self_mul_const_pow_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hmem : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (1 / 2 : ℝ) ^ n ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    exact mul_pos hn' hp
  have hwithin : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hhalf, hmem⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  show ((n : ℝ) * (1 / 2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ n / n
  rw [one_div, inv_pow, mul_inv, inv_inv]
  ring

/-- **Superexponential ratio growth beats the linear scale**: if the successive ratios of an
eventually positive sequence tend to infinity, so does the sequence divided by `n`. -/
theorem tendsto_div_natCast_atTop_of_ratio_tendsto_atTop {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    Tendsto (fun n => b n / n) atTop atTop := by
  have h2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ b (n + 1) / b n := hratio.eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hpos.and h2)
  have hgeo : ∀ k : ℕ, 2 ^ k * b N ≤ b (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hnk := hN (N + k) (by omega)
      have hstep : 2 * b (N + k) ≤ b (N + k + 1) := by
        have hb := hnk.1
        have hr := hnk.2
        rw [le_div_iff₀ hb] at hr
        linarith
      have hdouble : 2 * (2 ^ k * b N) ≤ 2 * b (N + k) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      calc 2 ^ (k + 1) * b N = 2 * (2 ^ k * b N) := by ring
        _ ≤ 2 * b (N + k) := hdouble
        _ ≤ b (N + k + 1) := hstep
  have hbN : 0 < b N := (hN N le_rfl).1
  have hc : 0 < b N / 2 ^ N := by positivity
  have hmin : Tendsto (fun n : ℕ => (b N / 2 ^ N) * ((2 : ℝ) ^ n / n)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_two_pow_div_natCast_atTop
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0] with n hnN hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgn := hgeo (n - N)
  rw [show N + (n - N) = n by omega] at hgn
  have hpow : (2 : ℝ) ^ (n - N) = 2 ^ n / 2 ^ N :=
    pow_sub₀ (2 : ℝ) (by norm_num) (by omega)
  rw [hpow] at hgn
  have hquot : (2 ^ n / 2 ^ N) * b N / n ≤ b n / n := by
    gcongr
  calc (b N / 2 ^ N) * ((2 : ℝ) ^ n / n) = (2 ^ n / 2 ^ N) * b N / n := by ring
    _ ≤ b n / n := hquot

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Superexponential coefficient decay beats every geometric scale**: if `b n / n → ∞`,
then `exp(−b n)·Rⁿ` is summable for every radius `R > 0` — the coefficients
`|aₙ| = exp(−bₙ)` define an entire series. -/
theorem summable_exp_neg_mul_pow {b : ℕ → ℝ}
    (h : Tendsto (fun n => b n / n) atTop atTop) {R : ℝ} (hR : 0 < R) :
    Summable (fun n => Real.exp (-b n) * R ^ n) := by
  have hev : ∀ᶠ n in atTop, Real.exp (-b n) * R ^ n ≤ Real.exp (-1 * n) := by
    have hlog := h.eventually_ge_atTop (Real.log R + 1)
    filter_upwards [hlog, Filter.eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hRn : R ^ n = Real.exp (n * Real.log R) := by
      rw [← Real.exp_log hR, ← Real.exp_nat_mul, Real.log_exp]
    rw [hRn, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hbn : (Real.log R + 1) * n ≤ b n := (le_div_iff₀ hn').mp hn
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  rw [← summable_nat_add_iff N]
  have hgeom : Summable (fun n : ℕ => Real.exp (-1 * (n + N : ℕ))) := by
    have hbase : Summable (fun n : ℕ => (Real.exp (-1)) ^ (n + N)) := by
      have h1 : Summable (fun n : ℕ => (Real.exp (-1)) ^ n) :=
        summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _))
          (by rw [Real.exp_lt_one_iff]; norm_num)
      exact (summable_nat_add_iff N).mpr h1
    refine hbase.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
  · positivity
  · exact hN (n + N) (by omega)

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Increment explosion**: for an eventually positive sequence with ratio tending to
infinity, the successive increments are eventually positive and their ratios also tend to
infinity.  Moving one unit of index mass toward a higher position costs an exploding
increment — the mechanism isolating the balanced atom in superlacunary magnitude
comparisons. -/
theorem increments_ratio_tendsto_atTop {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    (∀ᶠ n in atTop, 0 < b (n + 1) - b n) ∧
      Tendsto (fun n => (b (n + 2) - b (n + 1)) / (b (n + 1) - b n)) atTop atTop := by
  have h2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ b (n + 1) / b n := hratio.eventually_ge_atTop 2
  have hstep : ∀ᶠ n in atTop, 0 < b n ∧ 2 * b n ≤ b (n + 1) := by
    filter_upwards [hpos, h2] with n hb hr
    exact ⟨hb, by rw [le_div_iff₀ hb] at hr; linarith⟩
  constructor
  · filter_upwards [hstep] with n hn
    linarith [hn.1, hn.2]
  · -- Δ_{n+1}/Δ_n ≥ b(n+2)/b(n+1) − 1 → ∞
    have hshift : Tendsto (fun n => b (n + 2) / b (n + 1)) atTop atTop := by
      have := hratio.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp] using this
    have hminor : Tendsto (fun n => b (n + 2) / b (n + 1) - 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1) hshift
    refine tendsto_atTop_mono' atTop ?_ hminor
    filter_upwards [hstep, (tendsto_add_atTop_nat 1).eventually hstep] with n hn hn1
    have hb1 : 0 < b (n + 1) := hn1.1
    have hd0 : 0 < b (n + 1) - b n := by linarith [hn.1, hn.2]
    have hd1 : 0 ≤ b (n + 2) - b (n + 1) := by linarith [hn1.2, hn1.1]
    have hle : b (n + 1) - b n ≤ b (n + 1) := by linarith [hn.1]
    have hmono : (b (n + 2) - b (n + 1)) / b (n + 1)
        ≤ (b (n + 2) - b (n + 1)) / (b (n + 1) - b n) :=
      div_le_div_of_nonneg_left hd1 hd0 hle
    calc b (n + 2) / b (n + 1) - 1
        = (b (n + 2) - b (n + 1)) / b (n + 1) := by
          field_simp
      _ ≤ (b (n + 2) - b (n + 1)) / (b (n + 1) - b n) := hmono

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **The swap inequality**: past a threshold, moving one unit of index mass inward strictly
decreases the exponent sum — `b (j+1) + b (k−1) < b j + b k` whenever `j` is past the
threshold and `k ≥ j + 2`.  Unbalanced index pairs carry strictly larger exponent sums than
their balanced contractions: the rearrangement mechanism isolating the balanced atom. -/
theorem eventually_swap_inequality {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ N : ℕ, ∀ j k, N ≤ j → j + 2 ≤ k → b (j + 1) + b (k - 1) < b j + b k := by
  obtain ⟨hinc, hincratio⟩ := increments_ratio_tendsto_atTop hpos hratio
  have h2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ (b (n + 2) - b (n + 1)) / (b (n + 1) - b n) :=
    hincratio.eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hinc.and h2)
  refine ⟨N, fun j k hj hk => ?_⟩
  have hstep : ∀ m, N ≤ m → b (m + 1) - b m < b (m + 2) - b (m + 1) := by
    intro m hm
    have h := hN m hm
    have hd := h.1
    have hr := h.2
    rw [le_div_iff₀ hd] at hr
    linarith
  have hmono : ∀ d m, N ≤ m → b (m + 1) - b m ≤ b (m + d + 1) - b (m + d) := by
    intro d
    induction d with
    | zero => intro m _; simp
    | succ d ih =>
      intro m hm
      have h1 := ih m hm
      have h2' : b (m + d + 1) - b (m + d) < b (m + d + 2) - b (m + d + 1) :=
        hstep (m + d) (by omega)
      have he : m + (d + 1) + 1 = m + d + 2 := by omega
      have he2 : m + (d + 1) = m + d + 1 := by omega
      rw [he, he2]
      linarith
  have h1 : b (j + 1) - b j < b (j + 2) - b (j + 1) := hstep j hj
  have h2' := hmono ((k - 1) - (j + 1)) (j + 1) (by omega)
  rw [show j + 1 + ((k - 1) - (j + 1)) = k - 1 by omega,
    show k - 1 + 1 = k by omega] at h2'
  have hj2 : j + 1 + 1 = j + 2 := rfl
  rw [hj2] at h2'
  linarith

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Strict pair contraction**: past a threshold, any strict contraction of an index pair
at fixed index sum strictly decreases the exponent sum — `b j' + b k' < b j + b k` whenever
`j < j' ≤ k' < k` and `j + k = j' + k'`.  Iterated form of the swap inequality: strict
Schur convexity of the exponent sum on index pairs. -/
theorem eventually_pair_contraction_lt {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ N : ℕ, ∀ j j' k' k, N ≤ j → j < j' → j' ≤ k' → k' < k → j + k = j' + k' →
      b j' + b k' < b j + b k := by
  obtain ⟨N, hswap⟩ := eventually_swap_inequality hpos hratio
  have key : ∀ d j j' k' k, N ≤ j → j' = j + d + 1 → j' ≤ k' → k' < k →
      j + k = j' + k' → b j' + b k' < b j + b k := by
    intro d
    induction d with
    | zero =>
      intro j j' k' k hj hj' hjk hkk hsum
      have h := hswap j k hj (by omega)
      rw [show k - 1 = k' by omega, show j + 1 = j' by omega] at h
      exact h
    | succ d ih =>
      intro j j' k' k hj hj' hjk hkk hsum
      have h1 := hswap j k hj (by omega)
      have h2 := ih (j + 1) j' k' (k - 1) (by omega) (by omega) hjk (by omega) (by omega)
      linarith
  exact ⟨N, fun j j' k' k hj hjj hjk hkk hsum =>
    key (j' - j - 1) j j' k' k hj (by omega) hjk hkk hsum⟩

/-- **Balanced-pair minimality**: past a threshold, the balanced pair carries the strictly
smallest exponent sum among all index pairs with its index sum — `2·b m < b j + b k` for
`j < m < k` with `j + k = 2m`.  The degree-two balanced atom is exponent-separated from
every unbalanced pair: no other pair at the same index sum can reach its exponent. -/
theorem eventually_balanced_pair_min {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ N : ℕ, ∀ j m k, N ≤ j → j < m → m < k → j + k = m + m →
      2 * b m < b j + b k := by
  obtain ⟨N, h⟩ := eventually_pair_contraction_lt hpos hratio
  refine ⟨N, fun j m k hj hjm hmk hsum => ?_⟩
  have hc := h j m m k hj hjm le_rfl hmk hsum
  linarith

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- Splitting a composite sum over `Fin D` at two distinct indices. -/
theorem sum_comp_pair_split {M : Type*} [AddCommMonoid M] {D : ℕ} (t : Fin D → ℕ)
    (g : ℕ → M) {i₀ i₁ : Fin D} (h : i₀ ≠ i₁) :
    ∑ i, g (t i) = g (t i₀) + g (t i₁) + ∑ i ∈ (Finset.univ.erase i₀).erase i₁, g (t i) := by
  have h1 : g (t i₀) + ∑ i ∈ Finset.univ.erase i₀, g (t i) = ∑ i, g (t i) :=
    Finset.add_sum_erase _ (fun i => g (t i)) (Finset.mem_univ i₀)
  have h2 : g (t i₁) + ∑ i ∈ (Finset.univ.erase i₀).erase i₁, g (t i)
      = ∑ i ∈ Finset.univ.erase i₀, g (t i) :=
    Finset.add_sum_erase _ (fun i => g (t i))
      (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ i₁⟩)
  rw [← h1, ← h2, add_assoc]

/-- **Balanced-tuple minimality**: past a threshold, the balanced tuple carries the strictly
smallest exponent sum among all index tuples with its index sum — for any `D`-tuple `t` of
indices past the threshold with `∑ t i = D·m` and some entry different from `m`,
`D·b m < ∑ b (t i)`.  Contraction descent: any unbalanced tuple has an entry below and an
entry above the mean, and pulling that pair one step together strictly decreases both the
exponent sum (the swap inequality) and the sum of squares, so finitely many contractions
reach the balanced tuple with a strict drop at every step. -/
theorem eventually_balanced_tuple_min {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ N : ℕ, ∀ (D m : ℕ) (t : Fin D → ℕ), (∀ i, N ≤ t i) → (∑ i, t i) = D * m →
      (∃ i, t i ≠ m) → (D : ℝ) * b m < ∑ i, b (t i) := by
  obtain ⟨N, hswap⟩ := eventually_swap_inequality hpos hratio
  have main : ∀ (V D m : ℕ) (t : Fin D → ℕ), (∑ i, t i * t i) ≤ V → (∀ i, N ≤ t i) →
      (∑ i, t i) = D * m → (∃ i, t i ≠ m) → (D : ℝ) * b m < ∑ i, b (t i) := by
    intro V
    induction V with
    | zero =>
      intro D m t hV hN hsum hex
      obtain ⟨i, hi⟩ := hex
      have htz : ∀ j, t j = 0 := fun j =>
        mul_self_eq_zero.mp
          (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hV) j (Finset.mem_univ j))
      have h0 : D * m = 0 := by
        rw [← hsum]
        exact Finset.sum_eq_zero fun j _ => htz j
      rcases Nat.mul_eq_zero.mp h0 with hD0 | hm0
      · exact absurd hD0 i.pos.ne'
      · rw [hm0] at hi
        exact absurd (htz i) hi
    | succ V ih =>
      intro D m t hV hN hsum hex
      by_cases hle : (∑ i, t i * t i) ≤ V
      · exact ih D m t hle hN hsum hex
      · obtain ⟨i, hi⟩ := hex
        have hex_hi : ∀ i₀ : Fin D, t i₀ < m → ∃ i₁, m < t i₁ := by
          intro i₀ h₀
          by_contra hno
          push Not at hno
          have hlt : (∑ j, t j) < ∑ _j : Fin D, m :=
            Finset.sum_lt_sum (fun j _ => hno j) ⟨i₀, Finset.mem_univ i₀, h₀⟩
          rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul] at hlt
          exact lt_irrefl _ hlt
        have hex_lo : ∀ i₁ : Fin D, m < t i₁ → ∃ i₀, t i₀ < m := by
          intro i₁ h₁
          by_contra hno
          push Not at hno
          have hlt : (∑ _j : Fin D, m) < ∑ j, t j :=
            Finset.sum_lt_sum (fun j _ => hno j) ⟨i₁, Finset.mem_univ i₁, h₁⟩
          rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul] at hlt
          exact lt_irrefl _ hlt
        obtain ⟨i₀, i₁, h₀, h₁⟩ : ∃ i₀ i₁ : Fin D, t i₀ < m ∧ m < t i₁ := by
          rcases Nat.lt_or_ge (t i) m with hlt | hge
          · obtain ⟨i₁, h₁⟩ := hex_hi i hlt
            exact ⟨i, i₁, hlt, h₁⟩
          · have hgt : m < t i := lt_of_le_of_ne hge (Ne.symm hi)
            obtain ⟨i₀, h₀⟩ := hex_lo i hgt
            exact ⟨i₀, i, h₀, hgt⟩
        have hne : i₀ ≠ i₁ := fun h => by rw [h] at h₀; omega
        set t' : Fin D → ℕ := Function.update (Function.update t i₀ (t i₀ + 1)) i₁ (t i₁ - 1)
          with ht'def
        have ht'0 : t' i₀ = t i₀ + 1 := by
          rw [ht'def, Function.update_of_ne hne, Function.update_self]
        have ht'1 : t' i₁ = t i₁ - 1 := by
          rw [ht'def, Function.update_self]
        have ht'o : ∀ j, j ≠ i₀ → j ≠ i₁ → t' j = t j := fun j hj0 hj1 => by
          rw [ht'def, Function.update_of_ne hj1, Function.update_of_ne hj0]
        have hNm : N ≤ m := le_trans (hN i₀) (Nat.le_of_lt h₀)
        have hN' : ∀ j, N ≤ t' j := by
          intro j
          by_cases hj1 : j = i₁
          · rw [hj1, ht'1]; omega
          · by_cases hj0 : j = i₀
            · rw [hj0, ht'0]; exact le_trans (hN i₀) (Nat.le_succ _)
            · rw [ht'o j hj0 hj1]; exact hN j
        have hs1 : (∑ j, t' j) = t' i₀ + t' i₁
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t' j :=
          sum_comp_pair_split t' id hne
        have hs2 : (∑ j, t j) = t i₀ + t i₁
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t j :=
          sum_comp_pair_split t id hne
        have hb1 : (∑ j, b (t' j)) = b (t' i₀) + b (t' i₁)
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, b (t' j) :=
          sum_comp_pair_split t' b hne
        have hb2 : (∑ j, b (t j)) = b (t i₀) + b (t i₁)
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, b (t j) :=
          sum_comp_pair_split t b hne
        have hq1 : (∑ j, t' j * t' j) = t' i₀ * t' i₀ + t' i₁ * t' i₁
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t' j * t' j :=
          sum_comp_pair_split t' (fun a => a * a) hne
        have hq2 : (∑ j, t j * t j) = t i₀ * t i₀ + t i₁ * t i₁
            + ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t j * t j :=
          sum_comp_pair_split t (fun a => a * a) hne
        have htail_id : ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t' j
            = ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t j :=
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_erase, Finset.mem_erase] at hj
            rw [ht'o j hj.2.1 hj.1]
        have htail_b : ∑ j ∈ (Finset.univ.erase i₀).erase i₁, b (t' j)
            = ∑ j ∈ (Finset.univ.erase i₀).erase i₁, b (t j) :=
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_erase, Finset.mem_erase] at hj
            rw [ht'o j hj.2.1 hj.1]
        have htail_q : ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t' j * t' j
            = ∑ j ∈ (Finset.univ.erase i₀).erase i₁, t j * t j :=
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_erase, Finset.mem_erase] at hj
            rw [ht'o j hj.2.1 hj.1]
        have hsum'eq : (∑ j, t' j) = ∑ j, t j := by
          rw [hs1, hs2, ht'0, ht'1, htail_id]
          omega
        have hblt : (∑ j, b (t' j)) < ∑ j, b (t j) := by
          have hsw := hswap (t i₀) (t i₁) (hN i₀) (by omega)
          rw [hb1, hb2, ht'0, ht'1, htail_b]
          linarith
        have hqlt : (∑ j, t' j * t' j) < ∑ j, t j * t j := by
          rw [hq1, hq2, ht'0, ht'1, htail_q]
          obtain ⟨e, he⟩ : ∃ e, t i₁ = e + 1 := ⟨t i₁ - 1, by omega⟩
          rw [he]
          simp only [Nat.add_sub_cancel]
          have hae : t i₀ < e := by omega
          nlinarith [hae]
        have hqV : (∑ j, t' j * t' j) ≤ V := Nat.lt_succ_iff.mp (lt_of_lt_of_le hqlt hV)
        by_cases hbal : ∀ j, t' j = m
        · have hconst : (∑ j, b (t' j)) = (D : ℝ) * b m := by
            have h1 : (∑ j, b (t' j)) = ∑ _j : Fin D, b m :=
              Finset.sum_congr rfl fun j _ => by rw [hbal j]
            rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← hconst]
          exact hblt
        · push Not at hbal
          have hrec := ih D m t' hqV hN' (hsum'eq.trans hsum) hbal
          linarith
  exact ⟨N, fun D m t hN' hsum hex => main (∑ i, t i * t i) D m t le_rfl hN' hsum hex⟩

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Unique balanced representation**: for each degree `D`, past a threshold the balanced
value `D·b m` admits no representation `∑ b (t i)` by a `D`-tuple of tail indices other than
the constant tuple at `m`.  A tuple with an entry above `m` already overshoots — one jump of
the sequence exceeds `D·b m` and the remaining terms are positive — while a tuple staying
at or below `m` with one entry strictly below undershoots by strict monotonicity. -/
theorem eventually_balanced_unique_rep {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (D : ℕ) :
    ∃ N : ℕ, ∀ (m : ℕ) (t : Fin D → ℕ), N ≤ m → (∀ i, N ≤ t i) →
      (∑ i, b (t i)) = D * b m → ∀ i, t i = m := by
  obtain ⟨hinc, _⟩ := increments_ratio_tendsto_atTop hpos hratio
  have hDge : ∀ᶠ n in atTop, ((D : ℝ) + 1) ≤ b (n + 1) / b n :=
    hratio.eventually_ge_atTop _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hpos.and (hinc.and hDge))
  have hmono : ∀ p, N ≤ p → ∀ q, p < q → b p < b q := by
    intro p hp q
    induction q with
    | zero => intro h; omega
    | succ q ihq =>
      intro h
      rcases Nat.lt_or_ge p q with hlt | hge
      · have h1 := ihq hlt
        have h2 := (hN q (by omega)).2.1
        linarith
      · have hpq : p = q := by omega
        subst hpq
        have h2 := (hN p hp).2.1
        linarith
  have hjump : ∀ n, N ≤ n → (D : ℝ) * b n < b (n + 1) := by
    intro n hn
    obtain ⟨hb, _, hr⟩ := hN n hn
    rw [le_div_iff₀ hb] at hr
    have hexp : ((D : ℝ) + 1) * b n = (D : ℝ) * b n + b n := by ring
    linarith [hexp ▸ hr]
  refine ⟨N, fun m t hm hNt hsum => ?_⟩
  have hA : ∀ j, t j ≤ m := by
    intro j
    by_contra hgt
    push Not at hgt
    have hb1 : b (m + 1) ≤ b (t j) := by
      rcases Nat.lt_or_ge (m + 1) (t j) with hlt | hge
      · exact le_of_lt (hmono (m + 1) (by omega) (t j) hlt)
      · have he : t j = m + 1 := by omega
        rw [he]
    have hrest : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.erase j, b (t i) :=
      Finset.sum_nonneg fun i _ => le_of_lt (hN (t i) (hNt i)).1
    have hsplit : b (t j) + ∑ i ∈ Finset.univ.erase j, b (t i) = ∑ i, b (t i) :=
      Finset.add_sum_erase _ (fun i => b (t i)) (Finset.mem_univ j)
    have hj := hjump m hm
    rw [hsum] at hsplit
    linarith
  intro i
  by_contra hne
  have hilt : t i < m := lt_of_le_of_ne (hA i) hne
  have hlt : (∑ j, b (t j)) < ∑ _j : Fin D, b m := by
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases Nat.lt_or_ge (t j) m with hltj | hgej
      · exact le_of_lt (hmono (t j) (hNt j) m hltj)
      · have he : t j = m := le_antisymm (hA j) hgej
        rw [he]
    · exact hmono (t i) (hNt i) m hilt
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  exact lt_irrefl _ hlt

end GaloisForLFunctions
