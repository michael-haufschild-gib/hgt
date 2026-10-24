import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumAllLengths
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOne
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTwelveOne

/-!
# The sharp S₂ family and Guth–Maynard Proposition 12.1

The all-length three-term Heath–Brown estimate survives power lifting and
dyadic covering. The sharp abstract assembly therefore gives middle exponent
`2-1/k` for every positive integer k, yielding the exact Proposition 12.1
large-value estimate after the existing smoothing and separation reductions.
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard
open RHTower.Sieve Finset
noncomputable section

/-- The sharp Proposition 6.1 family, with middle exponent `2-1/k`. -/
theorem prop61_zeta_sharp (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T →
      IsSeparated (T ^ ε) W → (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) → W.Nonempty →
      ‖gmS2 w N W‖ ≤ C * T ^ (9 * ε) *
        (N ^ 2 * (W.card : ℝ) ^ 2
          + T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ))
          + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) := by
  classical
  obtain ⟨C₆₁, hC₆₁, h61⟩ := gmS2_le_sixOne_single w hε hε1
  have ha4 : (4 : ℝ) ≤ (32 : ℝ) ^ (4 * k) := by
    have h1 : (32 : ℝ) ^ 1 ≤ (32 : ℝ) ^ (4 * k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [pow_one] at h1
    linarith only [h1]
  have hb23 : (2 : ℝ) / 3 ≤ 4 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith only [this]
  obtain ⟨δ, hδ, D, hD, hblk⟩ :=
    exists_blockConst_divisor_le (ε := ε) (a := (32 : ℝ) ^ (4 * k)) (b := 4 * (k : ℝ)) hε ha4 hb23
  obtain ⟨H, hH, hHB⟩ := heathBrownPairSumBound_holds ε hε
  let Cδ := max D H
  have hCδ : 0 ≤ Cδ := hD.trans (le_max_left _ _)
  have hDC : D ≤ Cδ := le_max_left _ _
  have hHC : H ≤ Cδ := le_max_right _ _
  have hbig : (0 : ℝ) ≤ 1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith only [hCδ]))
      (by linarith only [hCδ])
  refine ⟨1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁, by linarith only [hbig, hC₆₁], ?_⟩
  intro T N W hT hN hNT hsep hmem hWne
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT]
  have hT0 : (0 : ℝ) < T := by linarith only [hT]
  have hN0 : (0 : ℝ) < N := by linarith only [hN]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcard1 : (1 : ℝ) ≤ (W.card : ℝ) := by
    have : 1 ≤ W.card := Finset.card_pos.mpr hWne
    exact_mod_cast this
  have hTε1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hTε0 : (0 : ℝ) ≤ T ^ ε := Real.rpow_nonneg hT0.le _
  have h8Tε : (1 : ℝ) ≤ 8 * T ^ ε := by linarith only [hTε1]
  have hTe6 : (T ^ ε) ^ 6 = T ^ (6 * ε) := by
    rw [← Real.rpow_natCast (T ^ ε) 6, ← Real.rpow_mul hT0.le,
      show ε * ((6 : ℕ) : ℝ) = 6 * ε from by push_cast; ring]
  have hTsum : T ^ (6 * ε) * (T ^ ε * (T ^ ε * T ^ ε)) = T ^ (9 * ε) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0,
      show 6 * ε + (ε + (ε + ε)) = 9 * ε from by ring]
  have hprod : (T ^ ε) ^ 6 * (T ^ ε * (T ^ ε * T ^ ε)) = T ^ (9 * ε) := by
    rw [hTe6]; exact hTsum
  -- `W` is 1-separated and of diameter at most `T`
  have hW1 : IsSeparated 1 W := fun t ht t' ht' hne => hTε1.trans (hsep t ht t' ht' hne)
  -- (6.1) at one dyadic block
  obtain ⟨M, j, hM1, hjM, hMle, hS2⟩ := h61 T N W hT1 hN hsep hmem
  -- the auxiliary scale `T' = 2 (2T)^{1+ε}`
  have h2T : (1 : ℝ) ≤ 2 * T := by linarith only [hT]
  have hrpow1 : 2 * T ≤ (2 * T) ^ (1 + ε) := by
    have := Real.rpow_le_rpow_of_exponent_le h2T (by linarith only [hε] : (1 : ℝ) ≤ 1 + ε)
    rwa [Real.rpow_one] at this
  have hNrpow : N ≤ (2 * T) ^ (1 + ε) := by linarith only [hrpow1, hNT, hT]
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, T' = 2 * (2 * T) ^ (1 + ε) := ⟨_, rfl⟩
  have hT'0 : (0 : ℝ) < T' := by
    have : (0 : ℝ) < (2 * T) ^ (1 + ε) := Real.rpow_pos_of_pos (by positivity) _
    rw [hT'def]; linarith only [this]
  -- `T' ≤ 8 T · T^ε`
  have hT'le : T' ≤ 8 * (T * T ^ ε) := by
    have hsplit : (2 * T) ^ (1 + ε) = 2 ^ (1 + ε) * T ^ (1 + ε) :=
      Real.mul_rpow (by norm_num) hT0.le
    have h2e : (2 : ℝ) ^ (1 + ε) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith only [hε1] : (1 : ℝ) + ε ≤ 2)
      calc (2 : ℝ) ^ (1 + ε) ≤ 2 ^ (2 : ℝ) := this
        _ = 4 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hTe : T ^ (1 + ε) = T * T ^ ε := by
      rw [Real.rpow_add hT0, Real.rpow_one]
    calc
      T' = 2 * (2 ^ (1 + ε) * (T * T ^ ε)) := by rw [hT'def, hsplit, hTe]
      _ ≤ 2 * (4 * (T * T ^ ε)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2e (mul_nonneg hT0.le hTε0)) (by norm_num)
      _ = 8 * (T * T ^ ε) := by ring
  -- the bracket, at `T'` and at `T`
  obtain ⟨X₂, hX₂def⟩ : ∃ X₂ : ℝ, X₂ = N ^ 2 * (W.card : ℝ) ^ 2
      + T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ))
      + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) := ⟨_, rfl⟩
  rw [← hX₂def]
  have hcard0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hX₂0 : 0 ≤ X₂ := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := Real.rpow_nonneg hcard0 _
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have h3 : (0 : ℝ) ≤ T ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT0.le _
    rw [hX₂def]; positivity
  have hTpow6 : (T ^ ε) ^ 6 ≤ T ^ (9 * ε) := by
    rw [← Real.rpow_natCast (T ^ ε) 6, ← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith only [hε])
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- the block `{1}`: only the first term of (6.4) is needed
    have hsub : dyadicSegmentBlock M j ⊆ ({1} : Finset ℕ) := by
      intro n hn
      have h := dyadicSegmentBlock_subset_Ico M j hn
      rw [Finset.mem_Ico, hj0] at h
      simp only [pow_zero] at h
      have hn1 : n = 1 := by omega
      simp [hn1]
    have hone : hbPairSum W ({1} : Finset ℕ) (fun _ => ((1 : ℝ) : ℂ)) = (W.card : ℝ) ^ 2 := by
      have hph : ∀ t : ℝ, hbPoly ({1} : Finset ℕ) (fun _ => ((1 : ℝ) : ℂ)) t = 1 := by
        intro t
        simp [hbPoly, hbPhase]
      unfold hbPairSum
      simp only [hph, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    have hXle : hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))
        ≤ (W.card : ℝ) ^ 2 := by
      rw [← hone]
      exact hbPairSum_ofReal_mono_support W hsub (fun n _ => zero_le_one)
    have hdiv : N ^ 2 / 2 ^ j = N ^ 2 := by rw [hj0]; norm_num
    rw [hdiv] at hS2
    have hbound : ‖gmS2 w N W‖ ≤ C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2) := by
      refine hS2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact mul_le_mul_of_nonneg_left hXle (by positivity)
    have hstep : C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2) ≤
        (1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁) * T ^ (9 * ε) * X₂ := by
      have h1 : N ^ 2 * (W.card : ℝ) ^ 2 ≤ X₂ := by
        have h1' : (0 : ℝ) ≤ T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by
          have : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := Real.rpow_nonneg hcard0 _
          positivity
        have h2' : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) := by
          have ha : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
          have hb : (0 : ℝ) ≤ T ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT0.le _
          positivity
        rw [hX₂def]; linarith only [h1', h2']
      have h2 : C₆₁ * (T ^ ε) ^ 6 ≤ (1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁) * T ^ (9 * ε) := by
        have hle : C₆₁ ≤ 1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁ := by
          linarith only [hbig]
        have h9 : (0 : ℝ) ≤ T ^ (9 * ε) := Real.rpow_nonneg hT0.le _
        calc C₆₁ * (T ^ ε) ^ 6 ≤ C₆₁ * T ^ (9 * ε) :=
              mul_le_mul_of_nonneg_left hTpow6 hC₆₁
          _ ≤ _ := mul_le_mul_of_nonneg_right hle h9
      have h3 : (0 : ℝ) ≤ C₆₁ * (T ^ ε) ^ 6 := by positivity
      have h4 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2 := by positivity
      calc C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2)
          ≤ C₆₁ * (T ^ ε) ^ 6 * X₂ := mul_le_mul_of_nonneg_left h1 h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hX₂0
    exact hbound.trans hstep
  · -- the generic block: lift, cover, Heath-Brown at every length
    obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = (2 : ℝ) ^ j := ⟨_, rfl⟩
    have hM₀0 : (0 : ℝ) < M₀ := by rw [hM₀def]; positivity
    have hM₀M : M₀ ≤ (M : ℝ) := by
      have h : ((2 ^ j : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hjM
      rw [hM₀def]
      push_cast at h
      exact h
    have hMT' : M₀ ≤ T' / N := by
      have h1 : (1 : ℝ) ≤ (2 * T) ^ (1 + ε) / N := (one_le_div hN0).mpr hNrpow
      have h2 : (M : ℝ) ≤ 2 * ((2 * T) ^ (1 + ε) / N) := by
        linarith only [hMle, h1]
      calc M₀ ≤ (M : ℝ) := hM₀M
        _ ≤ 2 * ((2 * T) ^ (1 + ε) / N) := h2
        _ = T' / N := by rw [hT'def]; ring
    obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = 2 ^ j - 1 := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 2 * 2 ^ j - 1 := ⟨_, rfl⟩
    have h2j : 2 ≤ 2 ^ j := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjpos
    have hA1 : 1 ≤ A := by rw [hAdef]; omega
    have hBA : B ≤ 3 * A := by rw [hAdef, hBdef]; omega
    obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = A ^ k := ⟨_, rfl⟩
    have hP1 : 1 ≤ P := by rw [hPdef]; exact Nat.one_le_pow _ _ (by omega)
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = 2 * k := ⟨_, rfl⟩
    have hcover : B ^ k ≤ 2 ^ m * P := by
      calc B ^ k ≤ (3 * A) ^ k := Nat.pow_le_pow_left hBA k
        _ = 3 ^ k * A ^ k := by rw [mul_pow]
        _ ≤ 4 ^ k * A ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) k)
        _ = 2 ^ m * P := by rw [hmdef, hPdef, pow_mul]; norm_num
    -- the divisor bound on the lifted range
    obtain ⟨Dv, hDvdef⟩ : ∃ Dv : ℝ, Dv = divisorBoundConst δ * ((B ^ k : ℕ) : ℝ) ^ δ := ⟨_, rfl⟩
    have hDv0 : 0 ≤ Dv := by
      have := (divisorBoundConst_pos hδ).le
      rw [hDvdef]; positivity
    have hDvB : ∀ u ∈ Finset.Ioc (A ^ k) (B ^ k), (u.divisors.card : ℝ) ≤ Dv := by
      intro u hu
      rw [Finset.mem_Ioc] at hu
      have hu0 : u ≠ 0 := by
        have hpk : 0 < A ^ k := by positivity
        omega
      have h1 := card_divisors_le_rpow hδ hu0
      have h2 : ((u : ℕ) : ℝ) ^ δ ≤ ((B ^ k : ℕ) : ℝ) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hu.2) hδ.le
      rw [hDvdef]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (divisorBoundConst_pos hδ).le)
    -- (6.2): the `k`-th power lift
    have hS : dyadicSegmentBlock M j ⊆ Finset.Ioc A B := by
      rw [hAdef, hBdef]; exact dyadicSegmentBlock_subset_Ioc M j
    have hcoefS : ∀ n ∈ dyadicSegmentBlock M j, ‖((1 : ℝ) : ℂ)‖ ≤ (n : ℝ) ^ (-(0 : ℝ)) := by
      intro n _
      rw [neg_zero, Real.rpow_zero]
      simp
    have hlift := hbPairSum_le_power_lift W hk hS (σ := 0) (a := fun _ => ((1 : ℝ) : ℂ))
      hcoefS hDvB
    have hcoef2 : (fun u : ℕ => (((u : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ)) = fun _ : ℕ => ((1 : ℝ) : ℂ) := by
      funext u
      rw [neg_zero, Real.rpow_zero]
    rw [hcoef2] at hlift
    -- (6.3): monotone support, then the dyadic cover with the all-lengths bound
    have hmono : hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) ≤
        hbPairSum W (Finset.Ioc P (2 ^ m * P)) (fun _ => ((1 : ℝ) : ℂ)) := by
      refine hbPairSum_ofReal_mono_support W ?_ (fun n _ => zero_le_one)
      have hcover' : B ^ k ≤ 2 ^ m * A ^ k := by rw [← hPdef]; exact hcover
      rw [hPdef]
      exact Finset.Ioc_subset_Ioc_right hcover'
    have hcoef1 : ∀ n : ℕ, ‖((1 : ℝ) : ℂ)‖ ≤ 1 := by intro n; simp
    have hblocks (L : ℕ) (hL : 1 ≤ L) :
        hbPairSum W (Finset.Ioc L (2 * L)) (fun _ => ((1 : ℝ) : ℂ)) ≤
          (H * T ^ ε) * heathBrownMajorant W.card L T := by
      rw [hbPairSum_eq_sum_exp]
      exact hHB W L (fun _ => ((1 : ℝ) : ℂ)) T 0 hT hL hcoef1
        (fun t ht => by simpa only [zero_add] using hmem t ht) hW1
    have hcov := hbPairSum_Ioc_two_pow_le_of_blocks hT0.le
      (mul_nonneg hH hTε0) hblocks hP1 m
    unfold heathBrownMajorant at hcov
    -- sizes: `M ≤ 8T²`, hence the lifted lengths are below `32^{4k} T^{4k}`
    have hrpow2 : (2 * T) ^ (1 + ε) ≤ 4 * T ^ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le h2T (by linarith only [hε1] : (1 : ℝ) + ε ≤ 2)
      rwa [show ((2 : ℝ) * T) ^ (2 : ℝ) = 4 * T ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring] at h
    have hT2 : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ hT1
    have hMbound : (M : ℝ) ≤ 8 * T ^ 2 := by
      have hdiv : (2 * T) ^ (1 + ε) / N ≤ (2 * T) ^ (1 + ε) :=
        div_le_self (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * T) (1 + ε)) hN
      linarith only [hMle, hdiv, hrpow2, hT2]
    have hAM : ((A : ℕ) : ℝ) ≤ M₀ := by
      have h1 : ((A : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
        have : A ≤ 2 ^ j := by rw [hAdef]; omega
        exact_mod_cast this
      rw [hM₀def]
      push_cast at h1
      exact h1
    have hPM : ((P : ℕ) : ℝ) ≤ M₀ ^ k := by
      rw [hPdef]
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hAM k
    have hP2M : ((P : ℕ) : ℝ) ^ 2 ≤ M₀ ^ (2 * k) := by
      have he : M₀ ^ (2 * k) = (M₀ ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
      rw [he]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hPM 2
    -- the two length bounds feeding the constant lemma
    have hT4k : T ^ (2 * k) ≤ T ^ (4 * (k : ℝ)) := by
      rw [← Real.rpow_natCast T (2 * k)]
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      push_cast; linarith only [hkR]
    have hBk : ((B ^ k : ℕ) : ℝ) ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
      have hB16 : ((B : ℕ) : ℝ) ≤ 16 * T ^ 2 := by
        have h1 : ((B : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
          have : B ≤ 2 * M := by
            have : 2 ^ j ≤ M := hjM
            rw [hBdef]; omega
          exact_mod_cast this
        linarith only [h1, hMbound]
      have h1 : ((B ^ k : ℕ) : ℝ) ≤ (16 * T ^ 2) ^ k := by
        push_cast
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB16 k
      have h2 : (16 * T ^ 2 : ℝ) ^ k = 16 ^ k * T ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]
      have h3 : (16 : ℝ) ^ k ≤ (32 : ℝ) ^ (4 * k) := by
        refine le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (16:ℝ) ≤ 32) k) ?_
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc ((B ^ k : ℕ) : ℝ) ≤ 16 ^ k * T ^ (2 * k) := by rw [← h2]; exact h1
        _ ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
            exact mul_le_mul h3 hT4k (by positivity) (by positivity)
    -- (6.3) at the paper's block length `M₀`
    obtain ⟨Cm, hCmdef⟩ : ∃ Cm : ℝ, Cm = H * T ^ ε := ⟨_, rfl⟩
    have hCm0 : 0 ≤ Cm := by rw [hCmdef]; positivity
    have hc54 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hcard0 _
    have hTleT' : T ≤ T' := by
      have : (0 : ℝ) < (2 * T) ^ (1 + ε) := Real.rpow_pos_of_pos (by positivity) _
      rw [hT'def]; linarith only [hrpow1, this]
    have hTT' : T ^ ((1 : ℝ) / 2) ≤ T' ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hT0.le hTleT' (by norm_num)
    have hmaj : (W.card : ℝ) ^ 2 * ((P : ℕ) : ℝ) + (W.card : ℝ) * ((P : ℕ) : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((P : ℕ) : ℝ) ≤
        (W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k := by
      have h₁ := mul_le_mul_of_nonneg_left hPM (sq_nonneg (W.card : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hP2M hcard0
      have h₃ := mul_le_mul (mul_le_mul_of_nonneg_left hTT' hc54) hPM
        (Nat.cast_nonneg _) (mul_nonneg hc54 (Real.rpow_nonneg hT'0.le _))
      linarith only [h₁, h₂, h₃]
    have hDv2k : (0 : ℝ) ≤ Dv ^ (2 * k) := pow_nonneg hDv0 (2 * k)
    have h63 : Dv ^ (2 * k) *
          hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) ≤
        (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) *
          ((W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k) := by
      have hstep := hmono.trans hcov
      rw [← hCmdef] at hstep
      have h8m : (0 : ℝ) ≤ (8 : ℝ) ^ m * Cm := by positivity
      calc Dv ^ (2 * k) * hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ))
          ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm *
              ((W.card : ℝ) ^ 2 * ((P : ℕ) : ℝ) + (W.card : ℝ) * ((P : ℕ) : ℝ) ^ 2
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((P : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep hDv2k
        _ ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm *
              ((W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmaj h8m) hDv2k
        _ = _ := by ring
    -- The sharp three-term assembly preserves the middle exponent.
    have h61' : ‖gmS2 w N W‖ ≤ C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 / M₀) *
        hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) := by
      rw [hM₀def, mul_assoc]
      exact hS2
    have hC₆₁' : (0 : ℝ) ≤ C₆₁ * (T ^ ε) ^ 6 := mul_nonneg hC₆₁ (pow_nonneg hTε0 6)
    have hC'0 : (0 : ℝ) ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm) :=
      mul_nonneg hDv2k (mul_nonneg (pow_nonneg (by norm_num) m) hCm0)
    have hY0 : (0 : ℝ) ≤ Dv ^ (2 * k) *
        hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) :=
      mul_nonneg hDv2k (hbPairSum_nonneg _ _ _)
    have hmain := prop61_abstract (W := (W.card : ℝ)) (N := N) (M := M₀) (T := T')
      (S₂ := ‖gmS2 w N W‖)
      (X := hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)))
      (Y := Dv ^ (2 * k) * hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)))
      (C := C₆₁ * (T ^ ε) ^ 6) (C' := Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm))
      hk (by linarith only [hcard1]) hN0 hM₀0 hT'0 hMT' hC₆₁' hC'0 hY0 h61' hlift h63
    -- the bracket at `T'` against the bracket at `T`
    have hexp0 : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
    have hexp1 : 1 / (2 * (k : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith only [hkR])]
      linarith only [hkR]
    have hhalf : T' ^ (1 / (2 * (k : ℝ))) ≤ 8 * (T ^ (1 / (2 * (k : ℝ))) * T ^ ε) :=
      rpow_le_of_le_mul hT0 hT'0 hT'le hexp0 hexp1 hTε1
    have hbr : N ^ 2 * (W.card : ℝ) ^ 2 + T' * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ))
          + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ)))
        ≤ 8 * T ^ ε * X₂ := by
      rw [hX₂def]
      exact bracket_mono (N := N) (c := (W.card : ℝ)) (T := T) (T' := T') (Tε := T ^ ε)
        (a := (W.card : ℝ) ^ (2 - 1 / (k : ℝ)))
        (b := (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))))
        (s := T ^ (1 / (2 * (k : ℝ)))) (s' := T' ^ (1 / (2 * (k : ℝ))))
        hN0.le hcard0 (Real.rpow_nonneg hcard0 _) (Real.rpow_nonneg hcard0 _)
        (Real.rpow_nonneg hT0.le _) hT0.le h8Tε hT'le hhalf
    -- the constants are `T^{O(ε)}`
    have hCδ3 := (hblk T hT1).2 (B ^ k) hBk
    have hCmle : Cm ≤ 2 * Cδ * T ^ ε := by
      rw [hCmdef]
      exact mul_le_mul_of_nonneg_right (by linarith only [hHC, hCδ]) hTε0
    have hDv2 : Dv ^ 2 ≤ Cδ * T ^ ε := by
      rw [hDvdef]
      exact hCδ3.trans (mul_le_mul_of_nonneg_right hDC hTε0)
    have hroot : (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) ^ (1 / (k : ℝ)) ≤
        Cδ * T ^ ε * (64 * (max 1 (2 * Cδ) * T ^ ε)) :=
      lifted_root_le hk hmdef hDv0 hCm0 hCδ hTε1 hDv2 hCmle
    -- collect
    have ha' : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := Real.rpow_nonneg hcard0 _
    have hb' : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have hs' : (0 : ℝ) ≤ T' ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT'0.le _
    have t1 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ T' * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) :=
      mul_nonneg (mul_nonneg hT'0.le hN0.le) ha'
    have t3 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
        T' ^ (1 / (2 * (k : ℝ))) := mul_nonneg (mul_nonneg (sq_nonneg _) hb') hs'
    have hBR0 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2
        + T' * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ))
        + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ))) := by
      linarith only [t1, t2, t3]
    exact prop61_constant_step (S := ‖gmS2 w N W‖) (C₆₁ := C₆₁) (Cδ := Cδ) (E := T ^ ε)
      (RT := (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) ^ (1 / (k : ℝ)))
      (BRv := N ^ 2 * (W.card : ℝ) ^ 2 + T' * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ))
        + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ))))
      (Xv := X₂) (P6 := (T ^ ε) ^ 6) (P9 := T ^ (9 * ε))
      hC₆₁ hCδ hTε0 (pow_nonneg hTε0 6) (Real.rpow_nonneg hT0.le _) (by linarith only [hmain, norm_nonneg (gmS2 w N W)]) hroot hbr hBR0 hX₂0
      hprod

end
end RHTower.GuthMaynard

namespace RHTower.GuthMaynard
noncomputable section

/-- The exact diagonal `S₂` family required by Proposition 12.1. -/
theorem propSixOneBound_sharp (w : CGLRealSmoothBump) {k : ℕ} (hk : 1 ≤ k) :
    PropSixOneBound w k k := by
  intro ε hε
  let e := min (ε / 9) 1
  have he : 0 < e := lt_min (by positivity) one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have he9 : 9 * e ≤ ε := by
    have h : e ≤ ε / 9 := min_le_left _ _
    linarith only [h]
  have heε : e ≤ ε := by linarith only [he, he9]
  obtain ⟨C, hC, hb⟩ := prop61_zeta_sharp w he he1 hk
  refine ⟨C, hC, fun T N W hT hN hNT hmem hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hN0 : 0 ≤ N := by linarith only [hN]
  have hW0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ (W.card : ℝ) ^ (2 : ℝ) * N ^ (2 : ℝ) +
      T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
      N ^ (2 : ℝ) * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
        T ^ (1 / (2 * (k : ℝ))) := by positivity
  rcases W.eq_empty_or_nonempty with hW | hW
  · subst W
    rw [gmS2_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT0 _)) hB
  have hsep' := hsep.mono (Real.rpow_le_rpow_of_exponent_le hT1 heε)
  have h := hb T N W hT hN hNT hsep' hmem hW
  simp only [← Real.rpow_two] at h
  rw [mul_comm (N ^ (2 : ℝ)) ((W.card : ℝ) ^ (2 : ℝ))] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 he9) hC) hB)

/-- Guth–Maynard Proposition 12.1, for every integer `k ≥ 1`. -/
theorem propTwelveOne_unconditional {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ σ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T ^ (5 / 6 : ℝ) ≤ N → (N : ℝ) ≤ T → 7 / 10 ≤ σ →
      (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) +
        T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3))) :=
  propTwelveOne_of_S_bounds cglStandardBump hk
    (propSixOneBound_sharp cglStandardBump.toCGLRealSmoothBump hk) propElevenTwoBound_zeta hε

end
end RHTower.GuthMaynard
