import GaloisForLFunctions.RHTower.LiSignDensity
import GaloisForLFunctions.RHTower.Sieve.WeylDifferencing

/-!
# Li's criterion along the perfect squares

If the Riemann hypothesis fails, there are `Q ≥ 1` and `c > 0` such that for all large `N` at least
`cN` of the `k < N` have `Re 2λ_{(Qk)²} < 0`
(`exists_density_re_xiLiPaired_sq_neg_of_not_riemannHypothesis`). Hence the Riemann hypothesis
holds iff the paired Li coefficients are eventually nonnegative along the squares
(`riemannHypothesis_iff_eventually_re_xiLiPaired_sq_nonneg`): the density-zero subsequence
`(λ_{m²})` already decides Li's criterion.

**Mechanism.**
* *Dominant part.* `Re 2λ_n = −Rⁿ f(n) + o(Rⁿ)` with `f(n) = Σ_{i∈D} m_i Re(u_iⁿ)`, `‖u_i‖ = 1`
  (`abs_re_tsum_liTerm_add_dominant_le`).
* *Quadratic Weyl sums.* For unimodular `w` with no positive power equal to `1`,
  `‖Σ_{k<N} w^{k²}‖ = o(N)`: the van der Corput inequality reduces it to the geometric sums
  `Σ_n (w^{2h})ⁿ` (`eventually_norm_sum_pow_sq_le`).
* *Roots of unity.* Choosing `Q` as a common period of the finitely many roots of unity among
  `u_i`, `u_iu_j`, `u_i ū_j` makes each of them equal to `1` along `Q²k²`, while the others keep
  `o(N)` quadratic sums. Then `Σ_{k<N} f(Q²k²) ≥ −o(N)` and `Σ_{k<N} f(Q²k²)² ≥ (N/2)Σm_i² − o(N)`,
  which forces `f(Q²k²) > ε` on at least `cN` of the `k < N` (`exists_card_filter_pow_sq_gt`).
-/

open Complex Filter Finset

noncomputable section

namespace RHTower

/-! ## Quadratic Weyl sums -/

/-- The van der Corput correlation of `k ↦ w^{k²}` is `w^{h²} Σ_{n<N−h} (w^{2h})ⁿ`. -/
theorem weylCorr_pow_sq {w : ℂ} (hw : ‖w‖ = 1) (N h : ℕ) :
    Sieve.weylCorr (fun k => w ^ (k ^ 2)) N h =
      w ^ (h ^ 2) * ∑ n ∈ range (N - h), (w ^ (2 * h)) ^ n := by
  unfold Sieve.weylCorr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only
  have hn : ‖w ^ (n ^ 2)‖ = 1 := by rw [norm_pow, hw, one_pow]
  have hmc : w ^ (n ^ 2) * (starRingEnd ℂ) (w ^ (n ^ 2)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have e : (n + h) ^ 2 = n ^ 2 + (h ^ 2 + 2 * h * n) := by ring
  rw [e, pow_add, pow_add, pow_mul]
  calc w ^ (n ^ 2) * (w ^ (h ^ 2) * (w ^ (2 * h)) ^ n) * (starRingEnd ℂ) (w ^ (n ^ 2))
      = (w ^ (n ^ 2) * (starRingEnd ℂ) (w ^ (n ^ 2))) * (w ^ (h ^ 2) * (w ^ (2 * h)) ^ n) := by
        ring
    _ = w ^ (h ^ 2) * (w ^ (2 * h)) ^ n := by rw [hmc, one_mul]

theorem norm_weylCorr_pow_sq_le {w : ℂ} (hw : ‖w‖ = 1) {h : ℕ} (hh : w ^ (2 * h) ≠ 1) (N : ℕ) :
    ‖Sieve.weylCorr (fun k => w ^ (k ^ 2)) N h‖ ≤ unimodularGeomBound (w ^ (2 * h)) := by
  rw [weylCorr_pow_sq hw, norm_mul, norm_pow, hw, one_pow, one_mul]
  unfold unimodularGeomBound
  rw [if_neg hh]
  exact norm_geom_sum_le_of_norm_eq_one (by rw [norm_pow, hw, one_pow]) hh (N - h)

/-- **Quadratic Weyl sums are `o(N)`.** For unimodular `w` with `wⁿ ≠ 1` for every `n ≥ 1`,
`‖Σ_{k<N} w^{k²}‖ ≤ δN` for all large `N`. -/
theorem eventually_norm_sum_pow_sq_le {w : ℂ} (hw : ‖w‖ = 1)
    (hroot : ∀ n : ℕ, 0 < n → w ^ n ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (k ^ 2)‖ ≤ δ * N := by
  obtain ⟨H, hH⟩ := exists_nat_gt (8 / δ ^ 2)
  have hHpos : (0 : ℝ) < H := lt_trans (by positivity) hH
  have hH1 : 1 ≤ H := by exact_mod_cast hHpos
  set C : ℝ := ∑ h ∈ Icc 1 (H - 1), unimodularGeomBound (w ^ (2 * h)) with hC
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => unimodularGeomBound_nonneg _
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 * C / (H * δ ^ 2))
  refine ⟨max H (max N₁ 1), fun N hN => ?_⟩
  have hHN : H ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1' : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1'
  have hvdc := Sieve.weyl_vdc (fun k => w ^ (k ^ 2)) (fun k => by rw [norm_pow, hw, one_pow])
    N H hH1 hHN
  have hcorr : ∑ h ∈ Icc 1 (H - 1), ‖Sieve.weylCorr (fun k => w ^ (k ^ 2)) N h‖ ≤ C :=
    sum_le_sum fun h hh => norm_weylCorr_pow_sq_le hw
      (hroot _ (by simp only [mem_Icc] at hh; omega)) N
  set S : ℝ := ‖∑ k ∈ range N, w ^ (k ^ 2)‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have h1 : (H : ℝ) * S ^ 2 ≤ 4 * N * (N + C) := by
    refine le_trans hvdc ?_
    gcongr
  have hHδ : 8 < (H : ℝ) * δ ^ 2 := by
    rw [div_lt_iff₀ (by positivity)] at hH; linarith
  have hNδ : 8 * C < (H : ℝ) * δ ^ 2 * N := by
    have h' : 8 * C / (H * δ ^ 2) < N := lt_of_lt_of_le hN₁ (by exact_mod_cast hN1)
    rw [div_lt_iff₀ (by positivity)] at h'; linarith
  have h2 : (H : ℝ) * S ^ 2 ≤ (H : ℝ) * (δ * N) ^ 2 := by
    have a1 : 8 * (N : ℝ) ^ 2 ≤ H * δ ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_right hHδ.le (sq_nonneg _)
    have a2 : 8 * C * N ≤ H * δ ^ 2 * N * N := mul_le_mul_of_nonneg_right hNδ.le hNpos.le
    have : 4 * N * (N + C) ≤ (H : ℝ) * (δ * N) ^ 2 := by nlinarith
    linarith
  have h3 : S ^ 2 ≤ (δ * N) ^ 2 := le_of_mul_le_mul_left h2 hHpos
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) two_ne_zero).mp h3

/-! ## Roots of unity along a common period -/

/-- For a finite family of complex numbers there is a common period `Q ≥ 1` of all its roots of
unity. -/
theorem exists_pow_eq_one_or_not_root {κ : Type*} [Fintype κ] (w : κ → ℂ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ j, w j ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w j ^ n ≠ 1 := by
  classical
  set d : κ → ℕ := fun j => if h : ∃ n, 0 < n ∧ w j ^ n = 1 then Nat.find h else 1 with hd
  have hdpos : ∀ j, 0 < d j := by
    intro j
    simp only [hd]
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact one_pos
  refine ⟨∏ j, d j, Finset.prod_pos fun j _ => hdpos j, fun j => ?_⟩
  by_cases h : ∃ n, 0 < n ∧ w j ^ n = 1
  · left
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    have hw : w j ^ d j = 1 := by
      simp only [hd, dif_pos h]; exact (Nat.find_spec h).2
    rw [hr, pow_mul, hw, one_pow]
  · right
    intro n hn hw
    exact h ⟨n, hn, hw⟩

theorem pow_eq_one_or_not_root_of_dvd {w : ℂ} {Q Q' : ℕ}
    (h : w ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1) (hQ : Q ∣ Q') :
    w ^ Q' = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1 := by
  rcases h with h | h
  · left; obtain ⟨r, hr⟩ := hQ; rw [hr, pow_mul, h, one_pow]
  · right; exact h

/-- Along `Q²k²` the quadratic sums of `w` are `N` (if `w^Q = 1`) or `o(N)`; in either case their
real parts are at least `−δN` for all large `N`. -/
theorem eventually_neg_le_re_sum_pow_sq {w : ℂ} (hw : ‖w‖ = 1) {Q : ℕ} (hQ : 0 < Q)
    (hd : w ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ (∑ k ∈ range N, w ^ (Q ^ 2 * k ^ 2)).re := by
  rcases hd with h1 | hnr
  · refine ⟨0, fun N _ => ?_⟩
    have hk : ∀ k : ℕ, w ^ (Q ^ 2 * k ^ 2) = 1 := fun k => by
      rw [show Q ^ 2 * k ^ 2 = Q * (Q * k ^ 2) by ring, pow_mul, h1, one_pow]
    simp only [hk, sum_const, card_range, nsmul_eq_mul, mul_one, natCast_re]
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  · have hw' : ‖w ^ (Q ^ 2)‖ = 1 := by rw [norm_pow, hw, one_pow]
    have hnr' : ∀ n : ℕ, 0 < n → (w ^ (Q ^ 2)) ^ n ≠ 1 := fun n hn => by
      rw [← pow_mul]; exact hnr _ (Nat.mul_pos (pow_pos hQ 2) hn)
    obtain ⟨N₀, hN₀⟩ := eventually_norm_sum_pow_sq_le hw' hnr' hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have e : ∑ k ∈ range N, w ^ (Q ^ 2 * k ^ 2) = ∑ k ∈ range N, (w ^ (Q ^ 2)) ^ (k ^ 2) :=
      sum_congr rfl fun k _ => pow_mul _ _ _
    rw [e]
    have h1 := hN₀ N hN
    have h2 := Complex.abs_re_le_norm (∑ k ∈ range N, (w ^ (Q ^ 2)) ^ (k ^ 2))
    have h3 := neg_abs_le (∑ k ∈ range N, (w ^ (Q ^ 2)) ^ (k ^ 2)).re
    linarith

/-! ## Counting from the first two moments -/

/-- **Mean and mean square force a positive density.** If `|f| ≤ B`, `Σ_{k<N} f(k) ≥ −o(N)` and
`Σ_{k<N} f(k)² ≥ sN − o(N)` with `s > 0`, then `f > ε` on at least `cN` of the `k < N` for all
large `N`. -/
theorem exists_card_filter_gt_of_mean_sq {f : ℕ → ℝ} {B s : ℝ} (hB0 : 0 < B)
    (hB : ∀ k, |f k| ≤ B) (hs : 0 < s)
    (hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k)
    (hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter (fun k => ε < f k)).card : ℝ) := by
  classical
  set δ : ℝ := s / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := min 1 δ with hε
  have hε0 : 0 < ε := lt_min one_pos hδ0
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hδB : δ * (B + 1) = s / 4 := by rw [hδ]; field_simp
  obtain ⟨N₁, hN₁⟩ := hmean δ hδ0
  obtain ⟨N₂, hN₂⟩ := hsq δ hδ0
  refine ⟨ε, s / (8 * B ^ 2), hε0, by positivity, max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  have hpt : ∀ k, f k ^ 2 ≤ 2 * B ^ 2 * (if ε < f k then (1 : ℝ) else 0)
      + (ε ^ 2 + B * ε) - B * f k := by
    intro k
    have hb := abs_le.mp (hB k)
    split_ifs with hk
    · nlinarith
    · rcases le_or_gt 0 (f k) with h0 | h0
      · have hk' : f k ≤ ε := not_lt.mp hk
        nlinarith
      · nlinarith
  have hsum := sum_le_sum fun k (_ : k ∈ range N) => hpt k
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul] at hsum
  have hcard : ∑ k ∈ range N, (if ε < f k then (1 : ℝ) else 0)
      = (((range N).filter (fun k => ε < f k)).card : ℝ) := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  rw [hcard] at hsum
  set A : ℝ := (((range N).filter (fun k => ε < f k)).card : ℝ) with hA
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hεsq : ε ^ 2 + B * ε ≤ s / 4 := by nlinarith
  have hkey : s / 4 * N ≤ 2 * B ^ 2 * A := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ## Cosine sums along `Q²k²` -/

/-- `f(k)² = Σ_{i,j} (m_im_j/2)(Re((u_iu_j)^e) + Re((u_iū_j)^e))` for `f = Σ_i m_i Re(u_i^e)`. -/
theorem sq_sum_mul_re_pow_eq {ι : Type*} [Fintype ι] (u : ι → ℂ) (m : ι → ℝ) (e : ℕ) :
    (∑ i, m i * (u i ^ e).re) ^ 2 = ∑ i, ∑ j, m i * m j / 2 *
      (((u i * u j) ^ e).re + ((u i * (starRingEnd ℂ) (u j)) ^ e).re) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, mul_pow, ← map_pow]
  have := re_mul_re_eq_half_sum (u i ^ e) (u j ^ e)
  rw [show m i * (u i ^ e).re * (m j * (u j ^ e).re) = m i * m j * ((u i ^ e).re * (u j ^ e).re)
    by ring, this]
  ring

/-- **Positive density along the squares.** For unimodular `u_i` and weights `m_i > 0` there are a
period `Q ≥ 1` and `ε, c > 0` such that `Σ_i m_i Re(u_i^{Q²k²}) > ε` for at least `cN` of the
`k < N`, for all large `N`. -/
theorem exists_card_filter_pow_sq_gt {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℂ)
    (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ε < ∑ i, m i * (u i ^ (Q ^ 2 * k ^ 2)).re)).card : ℝ) := by
  classical
  obtain ⟨Q₁, hQ₁, hd₁⟩ := exists_pow_eq_one_or_not_root u
  obtain ⟨Q₂, hQ₂, hd₂⟩ := exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * u p.2)
  obtain ⟨Q₃, hQ₃, hd₃⟩ :=
    exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * (starRingEnd ℂ) (u p.2))
  set Q : ℕ := Q₁ * Q₂ * Q₃ with hQ
  have hQpos : 0 < Q := Nat.mul_pos (Nat.mul_pos hQ₁ hQ₂) hQ₃
  have e₁ : ∀ i, u i ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → u i ^ n ≠ 1 := fun i =>
    pow_eq_one_or_not_root_of_dvd (hd₁ i) ⟨Q₂ * Q₃, by rw [hQ]; ring⟩
  have e₂ : ∀ p : ι × ι, (u p.1 * u p.2) ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → (u p.1 * u p.2) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₂ p) ⟨Q₁ * Q₃, by rw [hQ]; ring⟩
  have e₃ : ∀ p : ι × ι, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ Q = 1 ∨
      ∀ n : ℕ, 0 < n → (u p.1 * (starRingEnd ℂ) (u p.2)) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₃ p) ⟨Q₁ * Q₂, by rw [hQ]; ring⟩
  have hu₂ : ∀ p : ι × ι, ‖u p.1 * u p.2‖ = 1 := fun p => by
    rw [norm_mul, hu, hu, one_mul]
  have hu₃ : ∀ p : ι × ι, ‖u p.1 * (starRingEnd ℂ) (u p.2)‖ = 1 := fun p => by
    rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]
  set f : ℕ → ℝ := fun k => ∑ i, m i * (u i ^ (Q ^ 2 * k ^ 2)).re with hf
  set B : ℝ := ∑ i, m i with hBdef
  have hB0 : 0 < B := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hfB : ∀ k, |f k| ≤ B := by
    intro k
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hm i)]
    have h1 := Complex.abs_re_le_norm (u i ^ (Q ^ 2 * k ^ 2))
    rw [norm_pow, hu, one_pow] at h1
    nlinarith [hm i]
  set s : ℝ := (∑ i, m i ^ 2) / 2 with hsdef
  have hs0 : 0 < s := by
    have : 0 < ∑ i, m i ^ 2 := Finset.sum_pos (fun i _ => by have := hm i; positivity)
      Finset.univ_nonempty
    positivity
  have hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k := by
    intro δ hδ
    have hex : ∀ i, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ / B * N) ≤ (∑ k ∈ range N, u i ^ (Q ^ 2 * k ^ 2)).re := fun i =>
      eventually_neg_le_re_sum_pow_sq (hu i) hQpos (e₁ i) (by positivity)
    choose N₀ hN₀ using hex
    refine ⟨Finset.univ.sup N₀, fun N hN => ?_⟩
    have hswap : ∑ k ∈ range N, f k = ∑ i, m i * (∑ k ∈ range N, u i ^ (Q ^ 2 * k ^ 2)).re := by
      simp only [hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
    rw [hswap]
    have hle : ∀ i ∈ (Finset.univ : Finset ι),
        m i * (-(δ / B * N)) ≤ m i * (∑ k ∈ range N, u i ^ (Q ^ 2 * k ^ 2)).re := fun i _ =>
      mul_le_mul_of_nonneg_left
        (hN₀ i N (le_trans (Finset.le_sup (Finset.mem_univ i)) hN)) (hm i).le
    have hsum := Finset.sum_le_sum hle
    have heq : ∑ i, m i * (-(δ / B * N)) = -(δ * N) := by
      rw [← Finset.sum_mul, ← hBdef]; field_simp
    linarith
  have hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2 := by
    intro δ hδ
    set δ' : ℝ := δ / (B ^ 2 + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    have hex₂ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * u p.2) ^ (Q ^ 2 * k ^ 2)).re := fun p =>
      eventually_neg_le_re_sum_pow_sq (hu₂ p) hQpos (e₂ p) hδ'0
    have hex₃ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ (Q ^ 2 * k ^ 2)).re :=
      fun p => eventually_neg_le_re_sum_pow_sq (hu₃ p) hQpos (e₃ p) hδ'0
    choose N₂ hN₂ using hex₂
    choose N₃ hN₃ using hex₃
    refine ⟨max (Finset.univ.sup N₂) (Finset.univ.sup N₃), fun N hN => ?_⟩
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    -- the double-sum form of the second moment
    have hswap : ∑ k ∈ range N, f k ^ 2 = ∑ i, ∑ j, m i * m j / 2 *
        ((∑ k ∈ range N, (u i * u j) ^ (Q ^ 2 * k ^ 2)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (Q ^ 2 * k ^ 2)).re) := by
      simp only [hf, sq_sum_mul_re_pow_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hswap]
    -- each pair is at least `[i = j]N − 2δ'N`
    have hpair : ∀ i j, (if i = j then (N : ℝ) else 0) - 2 * δ' * N ≤
        (∑ k ∈ range N, (u i * u j) ^ (Q ^ 2 * k ^ 2)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (Q ^ 2 * k ^ 2)).re := by
      intro i j
      have h2 := hN₂ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_left _ _) hN))
      have h3 := hN₃ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_right _ _) hN))
      simp only at h2 h3
      have hδN : 0 ≤ δ' * N := mul_nonneg hδ'0.le hN0
      split_ifs with hij
      · subst hij
        have hone : u i * (starRingEnd ℂ) (u i) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
        rw [hone]
        simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, natCast_re]
        linarith
      · linarith
    have hlow : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) ≤
        ∑ i, ∑ j, m i * m j / 2 *
          ((∑ k ∈ range N, (u i * u j) ^ (Q ^ 2 * k ^ 2)).re +
            (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (Q ^ 2 * k ^ 2)).re) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hpair i j) (by have := hm i; have := hm j; positivity)
    have heval : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
        s * N - δ' * B ^ 2 * N := by
      have h1 : ∀ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
          m i ^ 2 / 2 * N - m i * B * δ' * N := by
        intro i
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, ← hBdef]
        ring
      have e1 : ∑ i, m i ^ 2 / 2 * (N : ℝ) = s * N := by
        rw [hsdef, Finset.sum_div, Finset.sum_mul]
      have e2 : ∑ i, m i * B * δ' * (N : ℝ) = δ' * B ^ 2 * N := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hBdef]; ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, e1, e2]
    have hδB : δ' * B ^ 2 ≤ δ := by
      rw [hδ', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [heval] at hlow
    nlinarith
  obtain ⟨ε, c, hε, hc, N₀, hcount⟩ := exists_card_filter_gt_of_mean_sq hB0 hfB hs0 hmean hsq
  exact ⟨Q, hQpos, ε, c, hε, hc, N₀, hcount⟩

/-! ## Li coefficients along the squares -/

theorem le_mul_sq_of_pos {T k : ℕ} (hT : 0 < T) : k ≤ (T * k) ^ 2 := by
  have h1 : k ≤ T * k := Nat.le_mul_of_pos_left k hT
  nlinarith

/-- **Negative along the squares with positive density, abstract form.** If one member of the family
lies strictly outside the unit circle, there are `T ≥ 1` and `c > 0` such that the paired Li sum at
index `(Tk)²` is negative for at least `cN` of the `k < N`, for all large `N`. -/
theorem exists_density_sq_re_tsum_liTerm_neg {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ T : ℕ, 0 < T ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0)).card : ℝ) := by
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
  obtain ⟨T, hT, ε, c, hε, hc, N₀, hcount⟩ :=
    exists_card_filter_pow_sq_gt u (fun i => m i) hunit (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * N₁ / c)
  refine ⟨T, hT, c / 2, by positivity, max N₀ N₂, fun N hN => ?_⟩
  have hle := card_filter_le_card_filter_add
    (P := fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (T ^ 2 * k ^ 2)).re)
    (Q := fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0) (N₁ := N₁)
    (fun k hk hP => by
      have hn : N₁ ≤ (T * k) ^ 2 := le_trans hk (le_mul_sq_of_pos hT)
      have hd := hN₁ _ hn
      rw [show (T * k) ^ 2 = T ^ 2 * k ^ 2 by ring] at hd ⊢
      rw [hf] at hP
      have hRn : (0 : ℝ) < R ^ (T ^ 2 * k ^ 2) := pow_pos hR0 _
      have h2 := (abs_le.mp hd).2
      have h3 := mul_pos hRn (sub_pos.mpr hP)
      nlinarith) N
  have h1 := hcount N (le_trans (le_max_left _ _) hN)
  have hle' : (((range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (T ^ 2 * k ^ 2)).re)).card : ℝ)
      ≤ (((range N).filter
        (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0)).card : ℝ) + N₁ := by
    exact_mod_cast hle
  have hNN : 2 * N₁ / c < N := lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_lt_iff₀ hc] at hNN
  linarith

/-- **Off the critical line the Li coefficients are negative along the squares with positive
density.** If the Riemann hypothesis fails, there are `T ≥ 1` and `c > 0` such that
`Re 2λ_{(Tk)²} < 0` for at least `cN` of the `k < N`, for all large `N`. -/
theorem exists_density_re_xiLiPaired_sq_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ T : ℕ, 0 < T ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter (fun k => (xiLiPaired ((T * k) ^ 2)).re < 0)).card : ℝ) := by
  classical
  obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨T, hT, c, hc, N₀, hcount⟩ :=
    exists_density_sq_re_tsum_liTerm_neg hmult hvnorm hvM hsum hρ₀
  refine ⟨T, hT, c, hc, N₀, fun N hN => ?_⟩
  simp_rw [re_xiLiPaired_eq_tsum_mult]
  exact hcount N hN

/-- **Li's criterion along the squares.** The Riemann hypothesis holds iff the paired Li
coefficients are eventually nonnegative along the perfect squares. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_sq_nonneg :
    RiemannHypothesis ↔ ∀ᶠ m in atTop, 0 ≤ (xiLiPaired (m ^ 2)).re := by
  classical
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun m => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨T, hT, c, hc, N₀, hcount⟩ :=
      exists_density_re_xiLiPaired_sq_neg_of_not_riemannHypothesis hRH
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp h
    obtain ⟨N, hN⟩ := exists_nat_gt ((M₀ : ℝ) / c + N₀)
    have hM0 : (0 : ℝ) ≤ (M₀ : ℝ) / c := by positivity
    have hNN₀ : N₀ ≤ N := by
      have : (N₀ : ℝ) < N := by linarith
      exact_mod_cast this.le
    have h1 := hcount N hNN₀
    have hcN : (M₀ : ℝ) < c * N := by
      have : (M₀ : ℝ) / c < N := by linarith
      rwa [div_lt_iff₀ hc, mul_comm] at this
    have hbig : M₀ < ((range N).filter (fun k => (xiLiPaired ((T * k) ^ 2)).re < 0)).card := by
      have : (M₀ : ℝ) < (((range N).filter
          (fun k => (xiLiPaired ((T * k) ^ 2)).re < 0)).card : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨k, hk, hkM⟩ : ∃ k ∈ (range N).filter (fun k => (xiLiPaired ((T * k) ^ 2)).re < 0),
        M₀ ≤ k := by
      by_contra hno
      push Not at hno
      have hsub : (range N).filter (fun k => (xiLiPaired ((T * k) ^ 2)).re < 0) ⊆ range M₀ :=
        fun k hk => mem_range.mpr (hno k hk)
      have := card_le_card hsub
      rw [card_range] at this
      omega
    have hneg := (mem_filter.mp hk).2
    have hnn := hM₀ (T * k) (le_trans hkM (Nat.le_mul_of_pos_left k hT))
    linarith

end RHTower

end
