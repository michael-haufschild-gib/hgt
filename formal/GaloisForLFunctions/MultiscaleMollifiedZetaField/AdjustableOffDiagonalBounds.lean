import GaloisForLFunctions.RHTower.ZetaGateFarPairError

/-!
# Adjustable scales in the twisted second moment

The taper and frequency split vary independently of the number of integrations
by parts. Their exponents determine the direct and dual off-diagonal savings.
This keeps the square-root length boundary visible in the estimates.
-/

noncomputable section

open Finset
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A carrier whose frequency scale fits inside the taper has the full taper
saving in every derivative, including mixed Leibniz terms. -/
theorem windowCarrierJetConst_le_scaled (K : ℕ) {η L v : ℝ}
    (hη : 0 < η) (hL : 0 < L)
    (hscale : 33 * (1 + |v|) * η ≤ 132 * L) :
    windowCarrierJetConst K η L v ≤ jetStarK K / η ^ K := by
  have hbase : 33 * (1 + |v|) / L ≤ 132 / η := by
    apply (div_le_div_iff₀ hL hη).mpr
    exact hscale
  unfold windowCarrierJetConst jetStarK
  rw [Finset.sum_div]
  apply sum_le_sum
  intro j hj
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 33 * (1 + |v|) / L)
    hbase (K - j)
  have hb := blockWindowConst_nonneg j
  calc
    (K.choose j : ℝ) * (blockWindowConst j / η ^ j) *
        ((K - j).factorial * (33 * (1 + |v|) / L) ^ (K - j))
      ≤ (K.choose j : ℝ) * (blockWindowConst j / η ^ j) *
        ((K - j).factorial * (132 / η) ^ (K - j)) := by gcongr
    _ = (K.choose j : ℝ) * blockWindowConst j *
        ((K - j).factorial * (132 : ℝ) ^ (K - j)) / η ^ K := by
      rw [div_pow]
      have he : η ^ j * η ^ (K - j) = η ^ K := by
        rw [← pow_add, Nat.add_sub_cancel' hjK]
      field_simp
      rw [← he]
      ring

/-- Power scales `η=T^a`, `V=T^b` preserve the derivative saving whenever
`a+b≤1` and the window stays above height `T/2`. -/
theorem windowCarrierJetConst_le_rpow (K : ℕ) {T a b L : ℝ}
    (hT : 1 ≤ T) (hb : 0 ≤ b) (hab : a + b ≤ 1) (hL : T / 2 ≤ L) :
    windowCarrierJetConst K (T ^ a) L (T ^ b) ≤
      jetStarK K * T ^ (-a * K) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hV : 1 ≤ T ^ b := Real.one_le_rpow hT hb
  have hprod : T ^ a * T ^ b ≤ T := by
    rw [← Real.rpow_add hT0]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hab
  have hscale : 33 * (1 + |T ^ b|) * T ^ a ≤ 132 * L := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hT0 b)]
    have hh := mul_le_mul_of_nonneg_left (show 1 + T ^ b ≤ 2 * T ^ b by linarith only [hV]) hη.le
    nlinarith only [hh, hprod, hL]
  have h := windowCarrierJetConst_le_scaled K hη (by linarith only [hT0, hL]) hscale
  convert h using 1
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le,
    ← Real.rpow_neg hT0.le]
  congr 1
  ring

/-- The two coefficient indices cost at most `T^(θ K)` after `K`
integrations by parts. The displacement can range throughout `[1/4,1/2]`. -/
theorem pair_rpow_le_length {T θ σ : ℝ} {K h k : ℕ}
    (hT : 1 ≤ T) (hσ : 0 ≤ σ) (hh : 0 < h) (hk : 0 < k)
    (hhT : (h : ℝ) ≤ T ^ θ) (hkT : (k : ℝ) ≤ T ^ θ) :
    ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ) ≤ T ^ (θ * K) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhk : (1 : ℝ) ≤ (h : ℝ) * k := by nlinarith only [hh1, hk1]
  calc
    ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ)
      ≤ ((h : ℝ) * k) ^ ((K : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hhk (sub_le_self _ hσ)
    _ ≤ (T ^ θ * T ^ θ) ^ ((K : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul hhT hkT (Nat.cast_nonneg _) (Real.rpow_nonneg hT0.le _)) (by positivity)
    _ = T ^ (θ * K) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_mul hT0.le]
      congr 1
      ring

/-- The direct off-diagonal has the exponent dictated by the taper and
mollifier length, with a constant depending only on the integration order. -/
theorem exists_directOffDiag_rpow_bound (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T θ a d p q : ℝ) (h k : ℕ),
      1 ≤ T → 0 < d → d ≤ 1 / 8 → p ≤ q → 0 < h → 0 < k →
      (h : ℝ) ≤ T ^ θ → (k : ℝ) ≤ T ^ θ →
      (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) T p q (T ^ a) h k P) ≤
        (q - p + 2 * T ^ a) * C * T ^ ((K : ℝ) * (1 / 2 + θ - a) + 1) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow
    (A := (K : ℝ) / 2 + 1) (by positivity)
  let Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))
  refine ⟨blockWindowConst K * CA * 2 ^ K * Z ^ 2,
    mul_nonneg (mul_nonneg (mul_nonneg (blockWindowConst_nonneg K) hCA0)
      (by positivity)) (sq_nonneg _), ?_⟩
  intro T θ a d p q h k hT hd hd8 hpq hh hk hhT hkT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hlen : 0 ≤ q - p + 2 * T ^ a := by linarith only [hpq, hη]
  have hσ : 0 ≤ 1 / 2 - d := by linarith only [hd8]
  have hbound := tsum_directOffDiagTerm_le K hCA0 hCA
    (σ₀ := 1 / 2 - d) (by linarith only [hd8]) hT0 hη hpq hh hk
  have hZ : (∑' n : ℕ,
      ((n : ℝ) + 1) ^ (-((K : ℝ) / 2 + 1 + (1 / 2 - d) - (K : ℝ) / 2))) ^ 2 ≤ Z ^ 2 := by
    exact pow_le_pow_left₀ (tsum_succ_rpow_neg_nonneg _)
      (tsum_succ_rpow_neg_le (by norm_num) (by linarith only [hd8])) 2
  have hpowers := pair_rpow_le_length hT hσ hh hk hhT hkT (K := K)
  have hC0 := directOffDiagConst_nonneg K (A := (K : ℝ) / 2 + 1) hCA0 hT0 hη hpq
  have halg : T ^ ((K : ℝ) / 2 + 1) / (T ^ a) ^ K * T ^ (θ * K) =
      T ^ ((K : ℝ) * (1 / 2 + θ - a) + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_sub hT0,
      ← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ directOffDiagConst K CA ((K : ℝ) / 2 + 1) T p q (T ^ a) *
        ((h : ℝ) * k) ^ ((K : ℝ) / 2 - (1 / 2 - d)) *
        (∑' n : ℕ, ((n : ℝ) + 1) ^
          (-((K : ℝ) / 2 + 1 + (1 / 2 - d) - (K : ℝ) / 2))) ^ 2 :=
      hbound
    _ ≤ directOffDiagConst K CA ((K : ℝ) / 2 + 1) T p q (T ^ a) *
        T ^ (θ * K) * Z ^ 2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpowers hC0) hZ
        (sq_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg hT0.le _))
    _ = (q - p + 2 * T ^ a) * (blockWindowConst K * CA * 2 ^ K * Z ^ 2) *
        (T ^ ((K : ℝ) / 2 + 1) / (T ^ a) ^ K * T ^ (θ * K)) := by
      unfold directOffDiagConst
      ring
    _ = _ := by rw [halg]

/-- Every strict gap between the taper exponent and `1/2+θ` yields
arbitrary power saving for the direct off-diagonal, uniformly in both indices. -/
theorem exists_directOffDiag_power_saving {θ a : ℝ} (hgap : 1 / 2 + θ < a) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T d p q : ℝ) (h k : ℕ),
      1 ≤ T → 0 < d → d ≤ 1 / 8 → p ≤ q → 0 < h → 0 < k →
      (h : ℝ) ≤ T ^ θ → (k : ℝ) ≤ T ^ θ →
      (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) T p q (T ^ a) h k P) ≤
        (q - p + 2 * T ^ a) * C * T ^ (-B) := by
  have hg : 0 < a - (1 / 2 + θ) := sub_pos.mpr hgap
  obtain ⟨K, hK⟩ := exists_nat_gt ((B + 1) / (a - (1 / 2 + θ)))
  have horder : (K : ℝ) * (1 / 2 + θ - a) + 1 ≤ -B := by
    have hh := (div_lt_iff₀ hg).mp hK
    nlinarith only [hh]
  obtain ⟨C, hC, hc⟩ := exists_directOffDiag_rpow_bound K
  refine ⟨C, hC, ?_⟩
  intro T d p q h k hT hd hd8 hpq hh hk hhT hkT
  refine (hc T θ a d p q h k hT hd hd8 hpq hh hk hhT hkT).trans ?_
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT horder)
    (mul_nonneg (by linarith only [hpq, hη]) hC)

end GaloisForLFunctions.MultiscaleMollifiedZetaField

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.windowCarrierJetConst_le_rpow
#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_directOffDiag_power_saving
