import GaloisForLFunctions.MatomakiRadziwill.LadderBlocks

/-!
# The moment computation for normalised prime blocks

For a block `B = {p ∈ Pr' : ⌊H' log p⌋ = u}` of primes in `[S, Se^{1/H'})`, `S = e^{u/H'} ≥ H' ≥ 3`, a
cofactor range `(lo, 4lo]`, `lo ≥ 1`, and `W ≤ S^ℓ lo` (`integral_normSq_blockQ_pow_mul_blockR_le`):

`∫_{|w| ≤ W} |Q_u(w)^ℓ R_v(w)|² ≤ 144 (18ℓ/H')^ℓ`.

Rescale `Q_u = S^{-1} Σ_{p ∈ B} a'_p p^{2πiw}` and `R_v = lo^{-1} Σ_{m} c'_m m^{2πiw}` with
`|a'|, |c'| ≤ 1`, and apply the coincidence count (`integral_normSq_logPoly_pow_mul_logPoly_le`):
`#B ≤ 3S/H'`, `B_max ≤ 2S`, so `#B^ℓ (#B + ℓB_max)^ℓ / S^ℓ ≤ (9ℓS/H')^ℓ`; the length
`S^ℓ lo ≥ W` makes the height term harmless.
-/

open Finset MeasureTheory RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem logPoly_const_mul (a : ℕ → ℂ) (s : Finset ℕ) (c : ℂ) (w : ℝ) :
    logPoly (fun n => c * a n) s w = c * logPoly a s w := by
  simp only [logPoly, mul_sum, mul_assoc]

theorem logPoly_congr {a b : ℕ → ℂ} {s : Finset ℕ} (h : ∀ n ∈ s, a n = b n) (w : ℝ) :
    logPoly a s w = logPoly b s w := by
  simp only [logPoly]
  exact sum_congr rfl fun n hn => by rw [h n hn]

/-- The primes of a block lie in `[e^{u/H}, e^{(u+1)/H})`. -/
theorem mem_block_bounds {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {H : ℝ} (hH : 0 < H) {u p : ℕ}
    (hp : p ∈ Pr.filter fun p => blk H p = u) :
    Real.exp ((u : ℝ) / H) ≤ p ∧ (p : ℝ) < Real.exp ((u : ℝ) / H) * Real.exp (1 / H) := by
  rw [mem_filter] at hp
  obtain ⟨h1, h2⟩ := exp_blk_le hH (hPr p hp.1).one_lt.le
  rw [hp.2] at h1 h2
  refine ⟨h1, ?_⟩
  rw [← Real.exp_add, show (u : ℝ) / H + 1 / H = ((u : ℝ) + 1) / H by ring]
  exact h2

/-- `#B ≤ S(e^{1/H} − 1) + 1`. -/
theorem card_block_le {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {H : ℝ} (hH : 0 < H) (u : ℕ) :
    ((Pr.filter fun p => blk H p = u).card : ℝ)
      ≤ Real.exp ((u : ℝ) / H) * (Real.exp (1 / H) - 1) + 1 := by
  classical
  set S := Real.exp ((u : ℝ) / H) with hS
  set E := Real.exp (1 / H) with hE
  have hS0 : 0 < S := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hsub : Pr.filter (fun p => blk H p = u) ⊆ Ico ⌈S⌉₊ ⌈S * E⌉₊ := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_block_bounds hPr hH hp
    rw [mem_Ico]
    exact ⟨Nat.ceil_le.mpr h1, Nat.lt_ceil.mpr h2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Ico] at h1
  have hc1 : (⌈S * E⌉₊ : ℝ) < S * E + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc2 : S ≤ (⌈S⌉₊ : ℝ) := Nat.le_ceil S
  have hab : ⌈S⌉₊ ≤ ⌈S * E⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  have h1' : ((Pr.filter fun p => blk H p = u).card : ℝ) ≤ (⌈S * E⌉₊ : ℝ) - ⌈S⌉₊ := by
    rw [← Nat.cast_sub hab]; exact_mod_cast h1
  nlinarith

/-- **The normalised moment computation.** -/
theorem integral_normSq_blockQ_pow_mul_blockR_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {Pr' : Finset ℕ} (hPr' : ∀ q ∈ Pr', q.Prime) {H' : ℝ} (hH' : 3 ≤ H') (u ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hS : H' ≤ Real.exp ((u : ℝ) / H')) (Pr : Finset ℕ) (rest : ℕ → Prop) [DecidablePred rest]
    (X : ℕ) (H : ℝ) (v : ℕ) (hlo : 1 ≤ cofLo X H v) {W : ℝ} (hW : 1 ≤ W)
    (hlen : W ≤ Real.exp ((u : ℝ) / H') ^ ℓ * cofLo X H v) :
    (∫ w in Set.Icc (-W) W, ‖blockQ f Pr' H' u w ^ ℓ * blockR f Pr rest X H v w‖ ^ (2 : ℕ))
      ≤ 144 * (18 * ℓ / H') ^ ℓ := by
  classical
  have hH0 : 0 < H' := by linarith
  set S := Real.exp ((u : ℝ) / H') with hSdef
  set E := Real.exp (1 / H') with hEdef
  set lo := cofLo X H v with hlodef
  set B := Pr'.filter fun p => blk H' p = u with hBdef
  set D := cof rest X H v with hDdef
  have hS0 : 0 < S := Real.exp_pos _
  have hE2 : E ≤ 2 := exp_inv_le_two (by linarith)
  have hE1 : E - 1 ≤ 2 / H' := exp_inv_sub_one_le (by linarith)
  have hlo0 : 0 < lo := by linarith
  -- rescaled coefficients
  set a' : ℕ → ℂ := fun p => if p ∈ B then (S : ℂ) * coefA f p else 0 with ha'
  set c' : ℕ → ℂ := fun m => if m ∈ D then (lo : ℂ) * coefC f Pr m else 0 with hc'
  have ha'1 : ∀ p, ‖a' p‖ ≤ 1 := by
    intro p
    simp only [ha']
    split_ifs with hp
    · obtain ⟨h1, -⟩ := mem_block_bounds hPr' hH0 hp
      have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hS0 h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0]
      calc S * ‖coefA f p‖ ≤ S * (1 / p) := mul_le_mul_of_nonneg_left (norm_coefA_le hf p) hS0.le
        _ ≤ 1 := by rw [mul_one_div, div_le_one hp0]; exact h1
    · rw [norm_zero]; exact zero_le_one
  have hc'1 : ∀ m, ‖c' m‖ ≤ 1 := by
    intro m
    simp only [hc']
    split_ifs with hm
    · have hm' := (mem_cof.mp hm).1
      have hm0 : (0 : ℝ) < m := lt_trans hlo0 hm'
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlo0]
      calc lo * ‖coefC f Pr m‖ ≤ lo * (1 / m) :=
            mul_le_mul_of_nonneg_left (norm_coefC_le hf Pr m) hlo0.le
        _ ≤ 1 := by rw [mul_one_div, div_le_one hm0]; exact hm'.le
    · rw [norm_zero]; exact zero_le_one
  have hQ : ∀ w, blockQ f Pr' H' u w = (S : ℂ)⁻¹ * logPoly a' B w := by
    intro w
    rw [blockQ, ← hBdef, logPoly_congr (b := fun p => (S : ℂ)⁻¹ * a' p) (fun p hp => by
      simp only [ha', if_pos hp]
      have : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
      field_simp) w, logPoly_const_mul]
  have hR : ∀ w, blockR f Pr rest X H v w = (lo : ℂ)⁻¹ * logPoly c' D w := by
    intro w
    rw [blockR, ← hDdef, logPoly_congr (b := fun m => (lo : ℂ)⁻¹ * c' m) (fun m hm => by
      simp only [hc', if_pos hm]
      have : (lo : ℂ) ≠ 0 := by exact_mod_cast hlo0.ne'
      field_simp) w, logPoly_const_mul]
  have hnorm : ∀ w, ‖blockQ f Pr' H' u w ^ ℓ * blockR f Pr rest X H v w‖ ^ (2 : ℕ)
      = (S ^ ℓ * lo)⁻¹ ^ 2 * ‖logPoly a' B w ^ ℓ * logPoly c' D w‖ ^ (2 : ℕ) := by
    intro w
    rw [hQ, hR, mul_pow, show (S : ℂ)⁻¹ ^ ℓ * logPoly a' B w ^ ℓ * ((lo : ℂ)⁻¹ * logPoly c' D w)
        = (((S ^ ℓ * lo)⁻¹ : ℝ) : ℂ) * (logPoly a' B w ^ ℓ * logPoly c' D w) by
      push_cast; ring, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  simp_rw [hnorm]
  rw [integral_const_mul]
  -- the coincidence count
  set Bmax : ℕ := ⌊S * E⌋₊ with hBmax
  set N : ℕ := ⌊4 * lo⌋₊ with hN
  have hBbounds : ∀ p ∈ B, S ≤ p ∧ p ≤ Bmax := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_block_bounds hPr' hH0 hp
    exact ⟨h1, Nat.le_floor h2.le⟩
  have hDbounds : ∀ m ∈ D, 1 ≤ m ∧ m ≤ N := fun m hm => by
    have hm := mem_cof.mp hm
    have h1 : (1 : ℝ) ≤ m := le_trans hlo hm.1.le
    exact ⟨by exact_mod_cast h1, Nat.le_floor hm.2.1⟩
  have hcore := integral_normSq_logPoly_pow_mul_logPoly_le (B := B) (D := D)
    (fun p hp => hPr' p (mem_filter.mp hp).1) ha'1 hc'1 hDbounds hS0
    (fun p hp => (hBbounds p hp).1) (fun p hp => (hBbounds p hp).2) ℓ hW
  -- numerical bounds
  have hBmaxle : (Bmax : ℝ) ≤ 2 * S := le_trans (Nat.floor_le (by positivity)) (by nlinarith)
  have hNle : (N : ℝ) ≤ 4 * lo := Nat.floor_le (by linarith)
  have hcardB : (B.card : ℝ) ≤ 3 * S / H' := by
    have h := card_block_le hPr' hH0 u
    rw [← hSdef, ← hEdef, ← hBdef] at h
    have h1 : S * (E - 1) ≤ 2 * S / H' := by
      calc S * (E - 1) ≤ S * (2 / H') := mul_le_mul_of_nonneg_left hE1 hS0.le
        _ = 2 * S / H' := by ring
    have h2 : (1 : ℝ) ≤ S / H' := by rw [le_div_iff₀ hH0]; linarith
    linarith
  have hcardB2 : (B.card : ℝ) + ℓ * Bmax ≤ 3 * ℓ * S := by
    have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have h1 : 3 * S / H' ≤ S := by rw [div_le_iff₀ hH0]; nlinarith
    have h2 : (ℓ : ℝ) * Bmax ≤ ℓ * (2 * S) := mul_le_mul_of_nonneg_left hBmaxle (by linarith)
    nlinarith
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hprod : (B.card : ℝ) ^ ℓ * N * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / S ^ ℓ
      ≤ 4 * lo * (9 * ℓ * S / H') ^ ℓ := by
    have h1 : (B.card : ℝ) ^ ℓ ≤ (3 * S / H') ^ ℓ := pow_le_pow_left₀ hB0 hcardB ℓ
    have h2 : ((B.card : ℝ) + ℓ * Bmax) ^ ℓ ≤ (3 * ℓ * S) ^ ℓ :=
      pow_le_pow_left₀ (by positivity) hcardB2 ℓ
    have hSℓ : 0 < S ^ ℓ := pow_pos hS0 ℓ
    rw [div_le_iff₀ hSℓ]
    calc (B.card : ℝ) ^ ℓ * N * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ
        ≤ (3 * S / H') ^ ℓ * (4 * lo) * (3 * ℓ * S) ^ ℓ := by
          gcongr
      _ = 4 * lo * (9 * ℓ * S / H') ^ ℓ * S ^ ℓ := by
          rw [show (9 * ℓ * S / H') ^ ℓ * S ^ ℓ = (3 * S / H') ^ ℓ * (3 * ℓ * S) ^ ℓ by
            rw [← mul_pow, ← mul_pow]; congr 1; ring]
          ring
  have hfirst : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * N : ℕ) : ℝ)
      ≤ 36 * 2 ^ ℓ * (S ^ ℓ * lo) := by
    have hpi : Real.pi ≤ 16 / 5 := by linarith [Real.pi_lt_d2]
    have he : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have hBN : ((Bmax ^ ℓ * N : ℕ) : ℝ) ≤ (2 * S) ^ ℓ * (4 * lo) := by
      push_cast
      exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hBmaxle ℓ) hNle (Nat.cast_nonneg _)
        (by positivity)
    have h2ℓ : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    have hL : 0 < S ^ ℓ * lo := by positivity
    have h1 : 5 * Real.pi / 2 * W ≤ 8 * (S ^ ℓ * lo) := by nlinarith
    have h3 : 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * N : ℕ) : ℝ) ≤ 7 * ((2 * S) ^ ℓ * (4 * lo)) := by
      have : 0 ≤ ((Bmax ^ ℓ * N : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h4 : (2 * S) ^ ℓ * (4 * lo) = 4 * 2 ^ ℓ * (S ^ ℓ * lo) := by rw [mul_pow]; ring
    nlinarith
  have hfirst0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * N : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le; have : (0 : ℝ) ≤ W := by linarith
    positivity
  have hscale : 0 ≤ (S ^ ℓ * lo)⁻¹ ^ 2 := by positivity
  calc (S ^ ℓ * lo)⁻¹ ^ 2 * ∫ w in Set.Icc (-W) W, ‖logPoly a' B w ^ ℓ * logPoly c' D w‖ ^ (2 : ℕ)
      ≤ (S ^ ℓ * lo)⁻¹ ^ 2 * ((36 * 2 ^ ℓ * (S ^ ℓ * lo)) * (4 * lo * (9 * ℓ * S / H') ^ ℓ)) := by
        refine mul_le_mul_of_nonneg_left (hcore.trans ?_) hscale
        exact mul_le_mul hfirst hprod (by positivity) (by positivity)
    _ = 144 * (2 ^ ℓ * (9 * ℓ * S / H') ^ ℓ / S ^ ℓ) := by
        field_simp
        ring
    _ = 144 * (18 * ℓ / H') ^ ℓ := by
        congr 1
        rw [← mul_pow, ← div_pow]
        congr 1
        field_simp
        ring

end

end GaloisForLFunctions.MatomakiRadziwill
