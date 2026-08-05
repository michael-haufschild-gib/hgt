import GaloisForLFunctions.RHTower.Sieve.SecondDerivativeTest
import GaloisForLFunctions.RHTower.Sieve.PhaseCorrelation

/-!
# The k-th derivative test

For a phase whose `k`-th derivative is pinned between `λ` and `h·λ` on the span of `N`
unit-spaced sample points, with `0 < λ ≤ 1 ≤ h` and `k ≥ 2`,

  `‖∑_{n<N} e(g(x₀+n))‖ ≤ 256·( N·(h²λ)^{1/(2^k−2)} + N^{1−4/2^k}·λ^{−2/2^k} )`.

Induction on `k`: the base is the second-derivative test; the step differences the phase
through the windowed Weyl–van der Corput inequality.  The `h'`-differenced phase has
`(k−1)`-th derivative `h'·g^{(k)}(ξ)` by the mean value theorem — the same ratio `h` one
order down — so the induction hypothesis applies when `h'λ ≤ 1`, and the trivial bound is
already strong enough when `h'λ > 1`.  The window `H ≈ (h²λ)^{−e'/(1+e')}` balances the two
main terms, and the exponent identity `(1/2)·e'/(1+e') = e_k` squares the bound back into
the claimed form.  The constant `256` absorbs every step: the recursion demands only
`√2052 ≤ 256` and `√1024 ≤ 256`.
-/

namespace RHTower.Sieve

open Real

set_option maxHeartbeats 1600000 in
/-- **The k-th derivative test.**  `G` is the derivative chain of the phase `G 0`. -/
theorem kth_derivative_test (k : ℕ) (hk : 2 ≤ k)
    (G : ℕ → ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hgrow1 : 1 ≤ hgrow)
    (hchain : ∀ i < k, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (G i) (G (i + 1) x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ G k x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), G k x ≤ hgrow * lam) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 256 * ((N : ℝ) * (hgrow ^ 2 * lam) ^ (1 / ((2:ℝ) ^ k - 2))
          + (N : ℝ) ^ (1 - 4 / (2:ℝ) ^ k) * lam ^ (-(2 / (2:ℝ) ^ k))) := by
  induction k, hk using Nat.le_induction generalizing G x₀ N lam hgrow with
  | base =>
    have hD2 := second_derivative_test' (G 0) (G 1) (G 2) x₀ N hN hlam0 hlam1
      (fun x hx => hchain 0 (by omega) x hx)
      (fun x hx => hchain 1 (by omega) x hx) hlo hhi
    have hg0 : (0:ℝ) < hgrow := lt_of_lt_of_le one_pos hgrow1
    have he1 : 1 / ((2:ℝ) ^ 2 - 2) = 1/2 := by norm_num
    have he2 : 1 - 4 / (2:ℝ) ^ 2 = 0 := by norm_num
    have he3 : 2 / (2:ℝ) ^ 2 = 1/2 := by norm_num
    rw [he1, he2, he3, Real.rpow_zero, one_mul]
    have hsq : (hgrow ^ 2 * lam) ^ ((1:ℝ)/2) = hgrow * Real.sqrt lam := by
      rw [Real.mul_rpow (sq_nonneg hgrow) hlam0.le, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, Real.sqrt_sq hg0.le]
    have hneg : lam ^ (-(1/2 : ℝ)) = (Real.sqrt lam)⁻¹ := by
      rw [Real.rpow_neg hlam0.le, ← Real.sqrt_eq_rpow]
    rw [hsq, hneg]
    have hf1 : (0:ℝ) ≤ (N : ℝ) * (hgrow * Real.sqrt lam) :=
      mul_nonneg (Nat.cast_nonneg N) (mul_nonneg hg0.le (Real.sqrt_nonneg lam))
    have hf2 : (0:ℝ) ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg lam)
    rw [div_eq_mul_inv] at hD2
    linarith only [hD2, hf1, hf2]
  | succ k hk ih =>
    rw [show ((2:ℝ) ^ (k + 1)) = (2:ℝ) ^ k * 2 from pow_succ 2 k]
    -- numeric groundwork
    have hp4 : (4:ℝ) ≤ (2:ℝ) ^ k := by
      calc (4:ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
    have hDpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
    have hD2pos : (0:ℝ) < (2:ℝ) ^ k - 2 := by linarith
    have hDD2pos : (0:ℝ) < (2:ℝ) ^ k * 2 - 2 := by linarith
    have hne1 : ((2:ℝ) ^ k - 2) ≠ 0 := ne_of_gt hD2pos
    have hne3 : ((2:ℝ) ^ k * 2 - 2) ≠ 0 := ne_of_gt hDD2pos
    have hne4 : ((2:ℝ) ^ k - 1) ≠ 0 := by
      have : (0:ℝ) < (2:ℝ) ^ k - 1 := by linarith
      exact ne_of_gt this
    have hDne : ((2:ℝ) ^ k) ≠ 0 := ne_of_gt hDpos
    -- the exponents at level k (in the induction hypothesis) and at level k+1 (goal)
    set e' : ℝ := 1 / ((2:ℝ) ^ k - 2) with he'def
    set β : ℝ := 1 - 4 / (2:ℝ) ^ k with hβdef
    set γ : ℝ := 2 / (2:ℝ) ^ k with hγdef
    set E : ℝ := 1 / ((2:ℝ) ^ k * 2 - 2) with hEdef
    set β' : ℝ := 1 - 4 / ((2:ℝ) ^ k * 2) with hβ'def
    set γ' : ℝ := 2 / ((2:ℝ) ^ k * 2) with hγ'def
    have he'0 : 0 < e' := by rw [he'def]; exact div_pos one_pos hD2pos
    have he'half : e' ≤ 1/2 := by
      rw [he'def]
      rw [div_le_div_iff₀ hD2pos (by norm_num : (0:ℝ) < 2)]
      linarith
    have h1e'pos : (0:ℝ) < 1 + e' := by linarith
    have hne2 : (1 + e') ≠ 0 := ne_of_gt h1e'pos
    have hβ0 : 0 ≤ β := by
      rw [hβdef]
      have h1 : 4 / (2:ℝ) ^ k ≤ 1 := by
        rw [div_le_one hDpos]; linarith
      linarith
    have hγ0 : 0 < γ := by rw [hγdef]; positivity
    have hγ'0 : 0 < γ' := by rw [hγ'def]; positivity
    have hE0 : 0 < E := by rw [hEdef]; exact div_pos one_pos hDD2pos
    have h2β' : 2 * β' = 1 + β := by
      rw [hβ'def, hβdef]
      field_simp
      ring
    have h2γ' : 2 * γ' = γ := by
      rw [hγ'def, hγdef]
      field_simp
    -- the base and its trivial branch
    have hg0 : (0:ℝ) < hgrow := lt_of_lt_of_le one_pos hgrow1
    set B : ℝ := hgrow ^ 2 * lam with hBdef
    have hB0 : 0 < B := by rw [hBdef]; exact mul_pos (pow_pos hg0 2) hlam0
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN1cast : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlamexp1 : (1:ℝ) ≤ lam ^ (-γ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam0 hlam1 (by linarith)
    rcases le_or_gt 1 B with htriv | hBlt1
    · -- `h²λ ≥ 1`: the first main term alone beats the trivial bound
      have hSN := norm_phase_sum_le_card (G 0) x₀ N
      have h1B : (1:ℝ) ≤ B ^ E := by
        calc (1:ℝ) = B ^ (0:ℝ) := (Real.rpow_zero B).symm
          _ ≤ B ^ E := Real.rpow_le_rpow_of_exponent_le htriv hE0.le
      have hV0 : (0:ℝ) ≤ (N:ℝ) ^ β' * lam ^ (-γ') :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.rpow_nonneg hlam0.le _)
      have hU0 : (0:ℝ) ≤ (N:ℝ) * B ^ E :=
        mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hB0.le _)
      calc ‖∑ n ∈ Finset.range N,
            Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
          ≤ (N:ℝ) := hSN
        _ ≤ (N:ℝ) * B ^ E := le_mul_of_one_le_right (Nat.cast_nonneg N) h1B
        _ ≤ 256 * ((N:ℝ) * B ^ E + (N:ℝ) ^ β' * lam ^ (-γ')) := by linarith only [hU0, hV0]
    -- main branch: `B = h²λ < 1`; window and differencing
    · set s : ℝ := e' / (1 + e') with hsdef
      have hs0 : 0 < s := div_pos he'0 h1e'pos
      have hs_eq : s * (1 + e') = e' := by rw [hsdef]; field_simp
      have h1pe' : 1 + e' = ((2:ℝ) ^ k - 1) / ((2:ℝ) ^ k - 2) := by
        rw [he'def]; field_simp; ring
      have hs2E : s = 2 * E := by
        rw [hsdef, h1pe', he'def, hEdef]
        rw [div_div_div_cancel_right₀]
        · field_simp
        · exact hne1
      have hexp_id : e' + -(s * e') = 2 * E := by
        have h1 : s + s * e' = e' := by linarith only [hs_eq]
        linarith only [hs2E, h1]
      set H₀ : ℝ := B ^ (-s) with hH₀def
      have hH₀1 : 1 < H₀ := by
        rw [hH₀def]
        exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hB0 hBlt1 (neg_lt_zero.mpr hs0)
      have hH₀pos : (0:ℝ) < H₀ := lt_trans one_pos hH₀1
      set H : ℕ := min ⌈H₀⌉₊ N with hHdef
      have hHceil1 : 1 ≤ ⌈H₀⌉₊ := Nat.one_le_ceil_iff.mpr hH₀pos
      have hH1 : 1 ≤ H := le_min hHceil1 hN
      have hHN : H ≤ N := min_le_right _ _
      have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
      -- the phase sequence and the Weyl step
      set a : ℕ → ℂ := fun n =>
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) with hadef
      have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
      have hSa : (∑ n ∈ Finset.range N,
          Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I))
          = ∑ n ∈ Finset.range N, a n := by simp only [hadef]
      rw [hSa]
      have hW := weyl_vdc a hanorm N H hH1 hHN
      -- the target terms
      set U : ℝ := (N:ℝ) * B ^ E with hUdef
      set V : ℝ := (N:ℝ) ^ β' * lam ^ (-γ') with hVdef
      have hU0 : (0:ℝ) ≤ U := by
        rw [hUdef]
        exact mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hB0.le _)
      have hV0 : (0:ℝ) ≤ V := by
        rw [hVdef]
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          (Real.rpow_nonneg hlam0.le _)
      have hU2 : U ^ 2 = (N:ℝ) ^ 2 * B ^ (2 * E) := by
        rw [hUdef, mul_pow]
        congr 1
        rw [← Real.rpow_natCast (B ^ E) 2, ← Real.rpow_mul hB0.le]
        congr 1
        push_cast
        ring
      have hV2 : V ^ 2 = (N:ℝ) ^ (2 * β') * lam ^ (-(2 * γ')) := by
        rw [hVdef, mul_pow]
        congr 1
        · rw [← Real.rpow_natCast ((N:ℝ) ^ β') 2, ← Real.rpow_mul (Nat.cast_nonneg N)]
          congr 1
          push_cast
          ring
        · rw [← Real.rpow_natCast (lam ^ (-γ')) 2, ← Real.rpow_mul hlam0.le]
          congr 1
          push_cast
          ring
      clear_value U V a H H₀ s B E β' γ' β γ e'
      -- the uniform correlation bound
      have hcorr : ∀ h' ∈ Finset.Icc 1 (H - 1),
          ‖weylCorr a N h'‖
            ≤ 256 * ((N:ℝ) * B ^ e' * (H:ℝ) ^ e' + (N:ℝ) ^ β * lam ^ (-γ)) := by
        intro h' hh'
        rw [Finset.mem_Icc] at hh'
        have hh'1 : 1 ≤ h' := hh'.1
        have hh'N : h' < N := by omega
        have hch'0 : (0:ℝ) < (h' : ℝ) := by exact_mod_cast hh'1
        have hch'1 : (1:ℝ) ≤ (h' : ℝ) := by exact_mod_cast hh'1
        have hh'H : h' ≤ H := by omega
        have hh'e_le_He : ((h':ℝ)) ^ e' ≤ ((H:ℝ)) ^ e' :=
          Real.rpow_le_rpow hch'0.le (by exact_mod_cast hh'H) he'0.le
        rcases le_or_gt ((h':ℝ) * lam) 1 with hsmall | hbig
        · -- differenced phase, one order down
          have hN'1 : 1 ≤ N - h' := by omega
          have hcastNh' : ((N - h' - 1 : ℕ) : ℝ) + (h' : ℝ) = ((N - 1 : ℕ) : ℝ) := by
            have h1 : (N - h' - 1) + h' = N - 1 := by omega
            calc ((N - h' - 1 : ℕ) : ℝ) + (h' : ℝ)
                = (((N - h' - 1) + h' : ℕ) : ℝ) := by push_cast; ring
              _ = ((N - 1 : ℕ) : ℝ) := by rw [h1]
          have hspan_incl : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h' - 1 : ℕ) : ℝ)),
              x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ))
                ∧ x + (h':ℝ) ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) := by
            intro x hx
            rcases hx with ⟨hx1, hx2⟩
            refine ⟨⟨hx1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
          set Gd : ℕ → ℝ → ℝ := fun i x => G i (x + (h':ℝ)) - G i x with hGddef
          have hchain' : ∀ i < k, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h' - 1 : ℕ) : ℝ)),
              HasDerivAt (Gd i) (Gd (i + 1) x) x := by
            intro i hik x hx
            obtain ⟨hx1, hx2⟩ := hspan_incl x hx
            have hd1 : HasDerivAt (G i) (G (i + 1) (x + (h':ℝ))) (x + (h':ℝ)) :=
              hchain i (by omega) _ hx2
            have hd2 : HasDerivAt (G i) (G (i + 1) x) x := hchain i (by omega) x hx1
            have hshift : HasDerivAt (fun y => G i (y + (h':ℝ)))
                (G (i + 1) (x + (h':ℝ))) x := HasDerivAt.comp_add_const x _ hd1
            simp only [hGddef]
            exact hshift.sub hd2
          have hslopeGd : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h' - 1 : ℕ) : ℝ)),
              (h':ℝ) * lam ≤ Gd k x ∧ Gd k x ≤ hgrow * ((h':ℝ) * lam) := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := hspan_incl x hx
            have hlt : x < x + (h':ℝ) := by linarith
            have hsub : Set.Icc x (x + (h':ℝ))
                ⊆ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) :=
              Set.Icc_subset_Icc hx1.1 hx2.2
            have hcont : ContinuousOn (G k) (Set.Icc x (x + (h':ℝ))) := fun y hy =>
              (hchain k (by omega) y (hsub hy)).continuousAt.continuousWithinAt
            have hdd : ∀ y ∈ Set.Ioo x (x + (h':ℝ)),
                HasDerivAt (G k) (G (k + 1) y) y :=
              fun y hy => hchain k (by omega) y (hsub (Set.mem_Icc_of_Ioo hy))
            obtain ⟨ξ, hξ, hval⟩ :=
              exists_hasDerivAt_eq_slope (G k) (G (k + 1)) hlt hcont hdd
            have hξspan : ξ ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) :=
              hsub (Set.mem_Icc_of_Ioo hξ)
            have hpos : (0:ℝ) < (x + (h':ℝ)) - x := by linarith
            rw [eq_div_iff (ne_of_gt hpos)] at hval
            have hxdiff : (x + (h':ℝ)) - x = (h':ℝ) := by ring
            rw [hxdiff] at hval
            have hlo1 := hlo ξ hξspan
            have hhi1 := hhi ξ hξspan
            constructor
            · simp only [hGddef]
              calc (h':ℝ) * lam = lam * (h':ℝ) := by ring
                _ ≤ G (k + 1) ξ * (h':ℝ) := mul_le_mul_of_nonneg_right hlo1 hch'0.le
                _ = G k (x + (h':ℝ)) - G k x := hval
            · simp only [hGddef]
              calc G k (x + (h':ℝ)) - G k x = G (k + 1) ξ * (h':ℝ) := hval.symm
                _ ≤ hgrow * lam * (h':ℝ) := mul_le_mul_of_nonneg_right hhi1 hch'0.le
                _ = hgrow * ((h':ℝ) * lam) := by ring
          have hlam'0 : 0 < (h':ℝ) * lam := mul_pos hch'0 hlam0
          have hIH := ih Gd x₀ (N - h') hN'1 hlam'0 hsmall hgrow1 hchain'
            (fun x hx => (hslopeGd x hx).1) (fun x hx => (hslopeGd x hx).2)
          have hcorr_eq : weylCorr a N h' = ∑ n ∈ Finset.range (N - h'),
              Complex.exp (((2 * Real.pi * Gd 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) := by
            rw [hadef, weylCorr_phase]
          rw [hcorr_eq]
          have h1 : (hgrow ^ 2 * ((h':ℝ) * lam)) ^ e' = B ^ e' * (h':ℝ) ^ e' := by
            rw [show hgrow ^ 2 * ((h':ℝ) * lam) = B * (h':ℝ) by rw [hBdef]; ring,
              Real.mul_rpow hB0.le hch'0.le]
          have h2 : ((h':ℝ) * lam) ^ (-γ) ≤ lam ^ (-γ) := by
            rw [Real.mul_rpow hch'0.le hlam0.le]
            exact mul_le_of_le_one_left (Real.rpow_nonneg hlam0.le _)
              (Real.rpow_le_one_of_one_le_of_nonpos hch'1 (by linarith))
          have hNh'le : ((N - h' : ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.sub_le N h'
          have hNh'0 : (0:ℝ) ≤ ((N - h' : ℕ):ℝ) := Nat.cast_nonneg _
          have hX1 : ((N - h' : ℕ):ℝ) * (B ^ e' * (h':ℝ) ^ e')
              ≤ (N:ℝ) * B ^ e' * (H:ℝ) ^ e' := by
            have hf1 : (0:ℝ) ≤ B ^ e' := Real.rpow_nonneg hB0.le _
            have hf2 : (0:ℝ) ≤ (h':ℝ) ^ e' := Real.rpow_nonneg hch'0.le _
            calc ((N - h' : ℕ):ℝ) * (B ^ e' * (h':ℝ) ^ e')
                ≤ (N:ℝ) * (B ^ e' * (h':ℝ) ^ e') :=
                  mul_le_mul_of_nonneg_right hNh'le (mul_nonneg hf1 hf2)
              _ ≤ (N:ℝ) * (B ^ e' * (H:ℝ) ^ e') := by
                  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
                  exact mul_le_mul_of_nonneg_left hh'e_le_He hf1
              _ = (N:ℝ) * B ^ e' * (H:ℝ) ^ e' := by ring
          have hX2 : ((N - h' : ℕ):ℝ) ^ β * ((h':ℝ) * lam) ^ (-γ)
              ≤ (N:ℝ) ^ β * lam ^ (-γ) := by
            have hf3 : ((N - h' : ℕ):ℝ) ^ β ≤ (N:ℝ) ^ β :=
              Real.rpow_le_rpow hNh'0 hNh'le hβ0
            have hf4 : (0:ℝ) ≤ ((h':ℝ) * lam) ^ (-γ) := Real.rpow_nonneg hlam'0.le _
            calc ((N - h' : ℕ):ℝ) ^ β * ((h':ℝ) * lam) ^ (-γ)
                ≤ (N:ℝ) ^ β * ((h':ℝ) * lam) ^ (-γ) :=
                  mul_le_mul_of_nonneg_right hf3 hf4
              _ ≤ (N:ℝ) ^ β * lam ^ (-γ) :=
                  mul_le_mul_of_nonneg_left h2
                    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          rw [h1] at hIH
          linarith only [hIH, hX1, hX2]
        · -- `h'λ > 1`: the trivial correlation bound is absorbed by the first term
          have htrivC := norm_weylCorr_le a hanorm N h'
          have hg2 : (1:ℝ) ≤ hgrow ^ 2 := by
            rw [sq]
            calc (1:ℝ) = 1 * 1 := by ring
              _ ≤ hgrow * hgrow := mul_le_mul hgrow1 hgrow1 zero_le_one hg0.le
          have hch'H : (h':ℝ) ≤ (H:ℝ) := by exact_mod_cast hh'H
          have hBH1 : (1:ℝ) ≤ B * (H:ℝ) := by
            have hstep : (h':ℝ) * lam ≤ B * (H:ℝ) := by
              rw [hBdef]
              have hf1 : (0:ℝ) ≤ ((H:ℝ) - (h':ℝ)) * lam :=
                mul_nonneg (by linarith) hlam0.le
              have hf2 : (0:ℝ) ≤ (hgrow ^ 2 - 1) * (lam * (H:ℝ)) :=
                mul_nonneg (by linarith) (mul_nonneg hlam0.le (by positivity))
              linarith only [hf1, hf2]
            linarith only [hbig, hstep]
          have hBHe1 : (1:ℝ) ≤ B ^ e' * (H:ℝ) ^ e' := by
            rw [← Real.mul_rpow hB0.le (Nat.cast_nonneg H)]
            calc (1:ℝ) = (B * (H:ℝ)) ^ (0:ℝ) := (Real.rpow_zero _).symm
              _ ≤ (B * (H:ℝ)) ^ e' := Real.rpow_le_rpow_of_exponent_le hBH1 he'0.le
          have hterm2 : (0:ℝ) ≤ (N:ℝ) ^ β * lam ^ (-γ) :=
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
              (Real.rpow_nonneg hlam0.le _)
          have hNle : (N:ℝ) ≤ (N:ℝ) * (B ^ e' * (H:ℝ) ^ e') :=
            le_mul_of_one_le_right (Nat.cast_nonneg N) hBHe1
          calc ‖weylCorr a N h'‖ ≤ (N:ℝ) := htrivC
            _ ≤ (N:ℝ) * (B ^ e' * (H:ℝ) ^ e') := hNle
            _ ≤ 256 * ((N:ℝ) * B ^ e' * (H:ℝ) ^ e' + (N:ℝ) ^ β * lam ^ (-γ)) := by
                have h0x : (0:ℝ) ≤ (N:ℝ) * (B ^ e' * (H:ℝ) ^ e') :=
                  le_trans (Nat.cast_nonneg N) hNle
                linarith only [hterm2, h0x]
      -- summing the correlations over the window
      have hsum : ∑ h' ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h'‖
          ≤ (H:ℝ) * (256 * ((N:ℝ) * B ^ e' * (H:ℝ) ^ e' + (N:ℝ) ^ β * lam ^ (-γ))) := by
        refine le_trans (Finset.sum_le_sum hcorr) ?_
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hcard : ((H - 1 + 1 - 1 : ℕ) : ℝ) ≤ (H:ℝ) := by
          have : H - 1 + 1 - 1 ≤ H := by omega
          exact_mod_cast this
        have hrhs0 : (0:ℝ) ≤ 256 * ((N:ℝ) * B ^ e' * (H:ℝ) ^ e'
            + (N:ℝ) ^ β * lam ^ (-γ)) := by
          have hf1 : (0:ℝ) ≤ (N:ℝ) * B ^ e' * (H:ℝ) ^ e' :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hB0.le _))
              (Real.rpow_nonneg (Nat.cast_nonneg H) _)
          have hf2 : (0:ℝ) ≤ (N:ℝ) ^ β * lam ^ (-γ) :=
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
              (Real.rpow_nonneg hlam0.le _)
          linarith
        exact mul_le_mul_of_nonneg_right hcard hrhs0
      -- the assembled square bound
      have hassemble : (H:ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2
          ≤ 4 * (N:ℝ) ^ 2 + 1024 * (N:ℝ) ^ 2 * B ^ e' * (H:ℝ) ^ e' * (H:ℝ)
            + 1024 * (N:ℝ) * ((N:ℝ) ^ β * lam ^ (-γ)) * (H:ℝ) := by
        refine le_trans hW ?_
        have h4N : (0:ℝ) ≤ 4 * (N:ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsum h4N
        linarith only [hmul]
      -- shared: the third raw term is exactly `H·1024·V²`
      have hterm3 : 1024 * (N:ℝ) * ((N:ℝ) ^ β * lam ^ (-γ)) * (H:ℝ)
          = (H:ℝ) * (1024 * V ^ 2) := by
        rw [hV2, h2β', h2γ']
        rw [show (1:ℝ) + β = 1 + β from rfl]
        rw [show (N:ℝ) ^ ((1:ℝ) + β) = (N:ℝ) ^ (1:ℝ) * (N:ℝ) ^ β from
          Real.rpow_add hNpos 1 β, Real.rpow_one]
        ring
      rcases le_or_gt (⌈H₀⌉₊) N with hcase | hcase
      · -- no cap: `H = ⌈H₀⌉` sits within a factor two of the balance point
        have hHeq : H = ⌈H₀⌉₊ := by rw [hHdef]; exact min_eq_left hcase
        have hH₀H : H₀ ≤ (H:ℝ) := by
          rw [hHeq]; exact Nat.le_ceil H₀
        have hH2H₀ : (H:ℝ) ≤ 2 * H₀ := by
          rw [hHeq]
          have h1 := Nat.ceil_lt_add_one hH₀pos.le
          linarith [hH₀1]
        have hH₀e' : H₀ ^ e' = B ^ (-(s * e')) := by
          rw [hH₀def, ← Real.rpow_mul hB0.le, neg_mul]
        have hBcollapse : B ^ e' * B ^ (-(s * e')) = B ^ (2 * E) := by
          rw [← Real.rpow_add hB0, hexp_id]
        have hHe'le : (H:ℝ) ^ e' ≤ 2 * B ^ (-(s * e')) := by
          calc (H:ℝ) ^ e'
              ≤ (2 * H₀) ^ e' :=
                Real.rpow_le_rpow (Nat.cast_nonneg H) hH2H₀ he'0.le
            _ = 2 ^ e' * H₀ ^ e' := Real.mul_rpow (by norm_num) hH₀pos.le
            _ ≤ 2 * H₀ ^ e' := by
                have h2e : (2:ℝ) ^ e' ≤ 2 ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith [he'half])
                rw [Real.rpow_one] at h2e
                exact mul_le_mul_of_nonneg_right h2e (Real.rpow_nonneg hH₀pos.le _)
            _ = 2 * B ^ (-(s * e')) := by rw [hH₀e']
        have hterm1 : 4 * (N:ℝ) ^ 2 ≤ (H:ℝ) * (4 * (N:ℝ) ^ 2 * B ^ (2 * E)) := by
          have hH₀eq2E : H₀ = B ^ (-(2 * E)) := by rw [hH₀def, hs2E]
          have h1 : B ^ (-(2 * E)) ≤ (H:ℝ) := hH₀eq2E ▸ hH₀H
          have hprod : B ^ (-(2 * E)) * B ^ (2 * E) = 1 := by
            rw [← Real.rpow_add hB0]; norm_num
          have hB2E0 : (0:ℝ) ≤ B ^ (2 * E) := Real.rpow_nonneg hB0.le _
          have h2 : (1:ℝ) ≤ (H:ℝ) * B ^ (2 * E) := by
            calc (1:ℝ) = B ^ (-(2 * E)) * B ^ (2 * E) := hprod.symm
              _ ≤ (H:ℝ) * B ^ (2 * E) := mul_le_mul_of_nonneg_right h1 hB2E0
          have h3 := mul_le_mul_of_nonneg_left h2
            (by positivity : (0:ℝ) ≤ 4 * (N:ℝ) ^ 2)
          linarith only [h3]
        have hterm2 : 1024 * (N:ℝ) ^ 2 * B ^ e' * (H:ℝ) ^ e' * (H:ℝ)
            ≤ (H:ℝ) * (2048 * (N:ℝ) ^ 2 * B ^ (2 * E)) := by
          have h1 : B ^ e' * (H:ℝ) ^ e' ≤ 2 * B ^ (2 * E) := by
            calc B ^ e' * (H:ℝ) ^ e'
                ≤ B ^ e' * (2 * B ^ (-(s * e'))) :=
                  mul_le_mul_of_nonneg_left hHe'le (Real.rpow_nonneg hB0.le _)
              _ = 2 * (B ^ e' * B ^ (-(s * e'))) := by ring
              _ = 2 * B ^ (2 * E) := by rw [hBcollapse]
          have h2 := mul_le_mul_of_nonneg_left h1
            (by positivity : (0:ℝ) ≤ 1024 * (N:ℝ) ^ 2 * (H:ℝ))
          linarith only [h2]
        have hsum3 : 4 * (N:ℝ) ^ 2 + 1024 * (N:ℝ) ^ 2 * B ^ e' * (H:ℝ) ^ e' * (H:ℝ)
            + 1024 * (N:ℝ) * ((N:ℝ) ^ β * lam ^ (-γ)) * (H:ℝ)
            ≤ (H:ℝ) * (4 * (N:ℝ) ^ 2 * B ^ (2 * E)
              + 2048 * (N:ℝ) ^ 2 * B ^ (2 * E) + 1024 * V ^ 2) := by
          linarith only [hterm1, hterm2, hterm3]
        have hin : 4 * (N:ℝ) ^ 2 * B ^ (2 * E) + 2048 * (N:ℝ) ^ 2 * B ^ (2 * E)
            + 1024 * V ^ 2 ≤ (256 * (U + V)) ^ 2 := by
          linarith only [hU2, sq_nonneg U, sq_nonneg V, mul_nonneg hU0 hV0]
        have hfinal2 : (H:ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2
            ≤ (H:ℝ) * ((256 * (U + V)) ^ 2) :=
          le_trans hassemble (le_trans hsum3
            (mul_le_mul_of_nonneg_left hin hHpos.le))
        have hS2 : ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤ (256 * (U + V)) ^ 2 :=
          le_of_mul_le_mul_left hfinal2 hHpos
        have hRHS0 : (0:ℝ) ≤ 256 * (U + V) := by linarith only [hU0, hV0]
        calc ‖∑ n ∈ Finset.range N, a n‖
            = Real.sqrt (‖∑ n ∈ Finset.range N, a n‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt ((256 * (U + V)) ^ 2) := Real.sqrt_le_sqrt hS2
          _ = 256 * (U + V) := Real.sqrt_sq hRHS0
      · -- cap: `H = N` below the balance point; everything collapses to the `V`-term
        have hHeq : H = N := by rw [hHdef]; exact min_eq_right (le_of_lt hcase)
        have hHcast : (H:ℝ) = (N:ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hHeq
        have hNH₀ : (N:ℝ) ≤ H₀ := by
          have h3 : N + 1 ≤ ⌈H₀⌉₊ := hcase
          have h4 : ((N:ℝ)) + 1 ≤ (⌈H₀⌉₊:ℝ) := by exact_mod_cast h3
          have h2 := Nat.ceil_lt_add_one hH₀pos.le
          linarith
        have hNpow : (N:ℝ) ^ (1 + e') ≤ B ^ (-e') := by
          calc (N:ℝ) ^ (1 + e')
              ≤ H₀ ^ (1 + e') :=
                Real.rpow_le_rpow (Nat.cast_nonneg N) hNH₀ (by linarith)
            _ = B ^ (-e') := by
                rw [hH₀def, ← Real.rpow_mul hB0.le]
                congr 1
                linarith only [hs_eq]
        have hmid1 : B ^ e' * (N:ℝ) ^ (1 + e') ≤ 1 := by
          calc B ^ e' * (N:ℝ) ^ (1 + e')
              ≤ B ^ e' * B ^ (-e') :=
                mul_le_mul_of_nonneg_left hNpow (Real.rpow_nonneg hB0.le _)
            _ = 1 := by rw [← Real.rpow_add hB0]; norm_num
        have hNe'N : (N:ℝ) ^ e' * (N:ℝ) = (N:ℝ) ^ (1 + e') := by
          rw [show (1:ℝ) + e' = e' + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
        have hterm2B : 1024 * (N:ℝ) ^ 2 * B ^ e' * (H:ℝ) ^ e' * (H:ℝ)
            ≤ (H:ℝ) * (1024 * (N:ℝ)) := by
          rw [hHcast]
          have h1 := mul_le_mul_of_nonneg_left hmid1
            (by positivity : (0:ℝ) ≤ 1024 * (N:ℝ) ^ 2)
          calc 1024 * (N:ℝ) ^ 2 * B ^ e' * (N:ℝ) ^ e' * (N:ℝ)
              = 1024 * (N:ℝ) ^ 2 * (B ^ e' * ((N:ℝ) ^ e' * (N:ℝ))) := by ring
            _ = 1024 * (N:ℝ) ^ 2 * (B ^ e' * (N:ℝ) ^ (1 + e')) := by rw [hNe'N]
            _ ≤ 1024 * (N:ℝ) ^ 2 * 1 := h1
            _ = (N:ℝ) * (1024 * (N:ℝ)) := by ring
        have hNleV2 : (N:ℝ) ≤ V ^ 2 := by
          rw [hV2, h2β', h2γ']
          have h1 : (N:ℝ) ^ (1:ℝ) ≤ (N:ℝ) ^ (1 + β) :=
            Real.rpow_le_rpow_of_exponent_le hN1cast (by linarith)
          rw [Real.rpow_one] at h1
          have h2 : (N:ℝ) * 1 ≤ (N:ℝ) ^ ((1:ℝ) + β) * lam ^ (-γ) :=
            mul_le_mul h1 hlamexp1 zero_le_one
              (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          linarith only [h2]
        have hsum3 : 4 * (N:ℝ) ^ 2 + 1024 * (N:ℝ) ^ 2 * B ^ e' * (H:ℝ) ^ e' * (H:ℝ)
            + 1024 * (N:ℝ) * ((N:ℝ) ^ β * lam ^ (-γ)) * (H:ℝ)
            ≤ (H:ℝ) * (4 * (N:ℝ) + 1024 * (N:ℝ) + 1024 * V ^ 2) := by
          have hterm1B : 4 * (N:ℝ) ^ 2 = (H:ℝ) * (4 * (N:ℝ)) := by
            rw [hHcast]; ring
          linarith only [hterm1B, hterm2B, hterm3]
        have hin : 4 * (N:ℝ) + 1024 * (N:ℝ) + 1024 * V ^ 2 ≤ (256 * (U + V)) ^ 2 := by
          linarith only [hNleV2, sq_nonneg U, sq_nonneg V, mul_nonneg hU0 hV0]
        have hfinal2 : (H:ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2
            ≤ (H:ℝ) * ((256 * (U + V)) ^ 2) :=
          le_trans hassemble (le_trans hsum3
            (mul_le_mul_of_nonneg_left hin hHpos.le))
        have hS2 : ‖∑ n ∈ Finset.range N, a n‖ ^ 2 ≤ (256 * (U + V)) ^ 2 :=
          le_of_mul_le_mul_left hfinal2 hHpos
        have hRHS0 : (0:ℝ) ≤ 256 * (U + V) := by linarith only [hU0, hV0]
        calc ‖∑ n ∈ Finset.range N, a n‖
            = Real.sqrt (‖∑ n ∈ Finset.range N, a n‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt ((256 * (U + V)) ^ 2) := Real.sqrt_le_sqrt hS2
          _ = 256 * (U + V) := Real.sqrt_sq hRHS0

end RHTower.Sieve
