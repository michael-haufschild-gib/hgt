import GaloisForLFunctions.PrimeTorusTheory.TheSavingAtEveryLength

/-!
# The sup bound for the sum of integer powers

The word has mass zero, so it cannot see a common rotation of the phases. So the sum of `n^{it}` over `n < N` is shorter than `N`, at
every length past the Kronecker scale:

* `‖Σ_{1≤n<N} n^{it}‖ ≤ N (1 − 1/(10⁹ L⁸ ℓ⁴))` for `N ≥ 48 L² ℓ` (`norm_sum_le_of_large`);
* `‖Σ_{1≤n<N} n^{it}‖ ≤ N (1 − exp(−L^β))` for `N ≥ 7 L^A`, `1 < A ≤ 2`, `β > 2 − A` (`norm_sum_le_of_length`).

The bound holds on every progression `r + qm`, `1 ≤ r ≤ q`, of length `K ≥ 48 L² ℓ`, uniformly in `q` (`norm_sum_ap_le_of_large`).

These are absolute savings, against the proportional saving of Vinogradov–Korobov above `exp(L^{2/3})`.
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- A lower bound for the distances against every rotation bounds the sum of the phases. -/
theorem norm_sum_le_of_rotDist {ι : Type*} (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) {t C : ℝ}
    {K : ℕ} (hC : 0 ≤ C) (hcard : s.card ≤ K) (hK : 0 < K)
    (hmean : ∀ φ : ℝ, (K : ℝ) * C ≤ ∑ i ∈ s, rotDist t φ (n i)) :
    ‖∑ i ∈ s, Complex.exp (Complex.I * (t * Real.log (n i)))‖ ≤ (K : ℝ) * (1 - 8 * C ^ 2) := by
  classical
  set T : ℂ := ∑ i ∈ s, Complex.exp (Complex.I * (t * Real.log (n i))) with hT
  set α : ℝ := Complex.arg T with hα
  set φ : ℝ := α / (2 * π) with hφ
  have hπ := Real.pi_pos
  have hNr : (0 : ℝ) < K := by exact_mod_cast hK
  have hnorm : ‖T‖ = ∑ i ∈ s, Real.cos (2 * π * (t * Real.log (n i) / (2 * π) - φ)) := by
    have h1 : ((‖T‖ : ℝ) : ℂ) = T * Complex.exp (-(Complex.I * (α : ℂ))) := by
      have h2 := Complex.norm_mul_exp_arg_mul_I T
      calc ((‖T‖ : ℝ) : ℂ) = (‖T‖ : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) *
            Complex.exp (-(Complex.I * (α : ℂ)))) := by
            rw [← Complex.exp_add]
            have : (α : ℂ) * Complex.I + -(Complex.I * (α : ℂ)) = 0 := by ring
            rw [this, Complex.exp_zero, mul_one]
        _ = _ := by
            rw [← mul_assoc, h2]
    have h3 := congrArg Complex.re h1
    rw [Complex.ofReal_re, hT, Finset.sum_mul, Complex.re_sum] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.exp_add]
    have e : Complex.I * ((t : ℂ) * (Real.log (n i) : ℂ)) + -(Complex.I * (α : ℂ)) =
        (((t * Real.log (n i) - α : ℝ) : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.exp_ofReal_mul_I_re]
    congr 1
    rw [hφ]
    field_simp
  have hd : ∀ i ∈ s, Real.cos (2 * π * (t * Real.log (n i) / (2 * π) - φ)) ≤
      1 - 8 * rotDist t φ (n i) ^ 2 := by
    intro i hi
    have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log (n i) / (2 * π) - φ)
    unfold rotDist
    rw [if_neg (hn i hi)]
    linarith
  have hmean2 := hmean φ
  have hcard' : (s.card : ℝ) ≤ K := by exact_mod_cast hcard
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => rotDist t φ (n i))
  have hsq0 : 0 ≤ ∑ i ∈ s, rotDist t φ (n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqlow : (K : ℝ) * C ^ 2 ≤ ∑ i ∈ s, rotDist t φ (n i) ^ 2 := by
    have h1 : ((K : ℝ) * C) ^ 2 ≤ (∑ i ∈ s, rotDist t φ (n i)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmean2 2
    have h2 : (∑ i ∈ s, rotDist t φ (n i)) ^ 2 ≤ (K : ℝ) * ∑ i ∈ s, rotDist t φ (n i) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right hcard' hsq0)
    have h3 : (K : ℝ) * ((K : ℝ) * C ^ 2) ≤ (K : ℝ) * ∑ i ∈ s, rotDist t φ (n i) ^ 2 := by
      calc (K : ℝ) * ((K : ℝ) * C ^ 2) = ((K : ℝ) * C) ^ 2 := by ring
        _ ≤ _ := h1.trans h2
    exact le_of_mul_le_mul_left h3 hNr
  rw [hnorm]
  calc ∑ i ∈ s, Real.cos (2 * π * (t * Real.log (n i) / (2 * π) - φ))
      ≤ ∑ i ∈ s, (1 - 8 * rotDist t φ (n i) ^ 2) := Finset.sum_le_sum hd
    _ = (s.card : ℝ) - 8 * ∑ i ∈ s, rotDist t φ (n i) ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    _ ≤ (K : ℝ) - 8 * ((K : ℝ) * C ^ 2) := by linarith
    _ = _ := by ring

/-- **The sup bound on progressions**, for a word of height `H`, uniformly in `q ≥ r ≥ 1`. -/
theorem WordSetup.norm_sum_ap_le {H R : ℝ} {M k N₁ K q r : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : WordSetup H R M k N₁ c t) (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hr : r ≤ q) (hK : 6 * M + 6 ≤ K) :
    ‖∑ m ∈ range K, Complex.exp (Complex.I * (t * Real.log ((r + q * m : ℕ) : ℝ)))‖ ≤
      (K : ℝ) * (1 - 8 * (1 / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2)) ^ 2) := by
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  refine norm_sum_le_of_rotDist (range K) (fun m => r + q * m) (fun m _ => by omega) (by positivity)
    (by simp) (by omega) fun φ => ?_
  have h := S.le_sum_rotDist_ap φ hq hr hK
  rw [mul_one_div]
  exact h

/-- **The sup bound**, for a word of height `H`. -/
theorem WordSetup.norm_sum_le {H R : ℝ} {M k N₁ N : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : WordSetup H R M k N₁ c t) (hN : 6 * M + 6 ≤ N) :
    ‖∑ n ∈ Finset.Ico 1 N, Complex.exp (Complex.I * (t * Real.log n))‖ ≤
      (N : ℝ) * (1 - 8 * (1 / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2)) ^ 2) := by
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hN0 : 0 < N := by omega
  refine norm_sum_le_of_rotDist (Finset.Ico 1 N) (fun n => n)
    (fun n hn => by have := (Finset.mem_Ico.mp hn).1; omega) (by positivity)
    (by rw [Nat.card_Ico]; omega) hN0 fun φ => ?_
  have h := S.le_sum_rotDist φ hN
  have hsumrot : ∑ n ∈ range N, rotDist t φ n = ∑ n ∈ Finset.Ico 1 N, rotDist t φ n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0]
    simp [rotDist]
  rw [mul_one_div, ← hsumrot]
  exact h

/-- The constant of the sup bound at height `1`. -/
theorem one_div_le_eight_sq {L ℓ : ℝ} {M : ℕ} (hL : 0 < L) (hℓ : 0 < ℓ)
    (hsq : ((M : ℝ) + 1) ^ 2 ≤ 64 * (L ^ 4 * ℓ ^ 2)) :
    1 - 8 * (1 / (48 * 16 * 1 ^ 2 * ((M : ℝ) + 1) ^ 2)) ^ 2 ≤ 1 - 1 / (10 ^ 9 * L ^ 8 * ℓ ^ 4) := by
  have hpos : 0 < L ^ 4 * ℓ ^ 2 := by positivity
  have h1 : 1 / (49152 * (L ^ 4 * ℓ ^ 2)) ≤ 1 / (48 * 16 * 1 ^ 2 * ((M : ℝ) + 1) ^ 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    norm_num
    nlinarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  have e : (1 / (49152 * (L ^ 4 * ℓ ^ 2))) ^ 2 = 1 / 49152 ^ 2 * (1 / (L ^ 8 * ℓ ^ 4)) := by
    field_simp
  have e2 : 1 / (10 ^ 9 * L ^ 8 * ℓ ^ 4) = 1 / 10 ^ 9 * (1 / (L ^ 8 * ℓ ^ 4)) := by
    field_simp
  rw [e] at h2
  rw [e2]
  have hq : 0 < 1 / (L ^ 8 * ℓ ^ 4) := by positivity
  have h3 : (1 : ℝ) / 10 ^ 9 ≤ 8 * (1 / 49152 ^ 2) := by norm_num
  nlinarith

/-- **The sup bound at length `(log |t|)² log log |t|`.** -/
theorem norm_sum_le_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      ‖∑ n ∈ Finset.Ico 1 N, Complex.exp (Complex.I * (t * Real.log n))‖ ≤
        (N : ℝ) * (1 - 1 / (10 ^ 9 * Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4)) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize Real.log L = ℓ at h hN ⊢
  obtain ⟨M, k, N₁, c, hS, hNnat, hsq⟩ := h.exists_data hexp hN
  refine (hS.norm_sum_le hNnat).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
  exact one_div_le_eight_sq (by linarith [h.hundred_le]) (by linarith [h.one_le]) hsq

/-- **The sup bound on progressions, uniformly in the modulus.** -/
theorem norm_sum_ap_le_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ K q r : ℕ, 1 ≤ r → r ≤ q →
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ K →
      ‖∑ m ∈ range K, Complex.exp (Complex.I * (t * Real.log ((r + q * m : ℕ) : ℝ)))‖ ≤
        (K : ℝ) * (1 - 1 / (10 ^ 9 * Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4)) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht K q r hr1 hr hK => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hK ⊢
  generalize Real.log L = ℓ at h hK ⊢
  obtain ⟨M, k, N₁, c, hS, hNnat, hsq⟩ := h.exists_data hexp hK
  refine (hS.norm_sum_ap_le (by omega) hr1 hr hNnat).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K))
  exact one_div_le_eight_sq (by linarith [h.hundred_le]) (by linarith [h.one_le]) hsq

/-- **The sup bound at every length past the Kronecker scale.** -/
theorem norm_sum_le_of_length {A β : ℝ} (hA1 : 1 < A) (hA2 : A ≤ 2) (hβ : 2 - A < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ, 7 * Real.log |t| ^ A ≤ N →
      ‖∑ n ∈ Finset.Ico 1 N, Complex.exp (Complex.I * (t * Real.log n))‖ ≤
        (N : ℝ) * (1 - Real.exp (-Real.log |t| ^ β)) := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_lengthSize hA1 hA2 hβ)
  refine ⟨Real.exp L₀, Real.exp_pos _, fun t ht N hN => ?_⟩
  have htpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hLge : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht
  have h := hL₀ _ hLge
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize 6 * L ^ (2 - A) * Real.log L = lam at h
  generalize Real.log L = ℓ at h
  obtain ⟨H, R, M, k, N₁, c, hS, hNnat, hden⟩ := h.exists_word_data hexp hN
  refine (hS.norm_sum_le hNnat).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  have hH0 : 0 < H := by linarith [hS.one_le_H]
  have hR0 : 0 < R := by linarith [hS.one_le_R]
  have hlow : Real.exp (-(15 + 6 * lam + 4 * ℓ)) ≤ 1 / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) := by
    rw [Real.exp_neg, ← one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hpos : 0 ≤ 48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2 := by positivity
    linarith
  have hsq := pow_le_pow_left₀ (Real.exp_pos _).le hlow 2
  have e : Real.exp (-(15 + 6 * lam + 4 * ℓ)) ^ 2 = Real.exp (-(30 + 12 * lam + 8 * ℓ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e] at hsq
  have hfin : Real.exp (-L ^ β) ≤ Real.exp (-(30 + 12 * lam + 8 * ℓ)) :=
    Real.exp_le_exp.mpr (by linarith [h.final])
  have hpos := Real.exp_pos (-(30 + 12 * lam + 8 * ℓ))
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
