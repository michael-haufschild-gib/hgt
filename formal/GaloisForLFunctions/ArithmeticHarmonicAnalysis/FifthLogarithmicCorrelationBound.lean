import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DifferencedLogarithmicFifthDualSum
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FifthLogarithmicCorrelationPowers

/-! # The fifth-derivative logarithmic correlation bound

The actual stationary-phase transformation and its fifth-derivative dual sum
bound logarithmic correlations on every dyadic source interval. All endpoint
and remainder estimates are explicit.
-/

noncomputable section
open Complex RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- In the fifth-derivative regime, the full logarithmic correlation has two
oscillatory terms and the three stationary-phase remainder terms. -/
theorem norm_sum_diffLog_fifth_le_B {T : ℝ} (hT : 0 < T) {N L h : ℕ} (hN : 2 ≤ N) (hh : 1 ≤ h)
    (h2h : 2 * h ≤ N) (hL : L ≤ N) (hX : 7 * (N : ℝ) ^ 9 ≤ (T * h) ^ 4) :
    ‖∑ n ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log ((N : ℝ) + n + h)
        - Real.log ((N : ℝ) + n))) : ℝ) : ℂ) * I)‖
      ≤ 10 ^ 24 * ((T * h) ^ (11 / 30 : ℝ) * (N : ℝ) ^ (-(1 / 5) : ℝ) + (T * h) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (-(13 / 16) : ℝ)
          + T * h / (N : ℝ) ^ 2 + ((N : ℝ) ^ 3 / (T * h)) ^ (1 / 2 : ℝ)
          + (T * h) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = N := ⟨_, rfl⟩
  obtain ⟨hR, hhR⟩ : ∃ r : ℝ, r = h := ⟨_, rfl⟩
  rw [← hn, ← hhR]
  rw [← hn, ← hhR] at hX
  have hn2 : 2 ≤ n := by rw [hn]; exact_mod_cast hN
  have hn0 : 0 < n := by linarith
  have hR1 : 1 ≤ hR := by rw [hhR]; exact_mod_cast hh
  have hR0 : 0 < hR := by linarith
  have hRn : 2 * hR ≤ n := by rw [hn, hhR]; exact_mod_cast h2h
  have hLn : (L : ℝ) ≤ n := by rw [hn]; exact_mod_cast hL
  obtain ⟨X, hXd⟩ : ∃ X, X = T * hR := ⟨_, rfl⟩
  rw [← hXd]
  rw [← hXd] at hX
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hXn : n ^ 2 ≤ X := by
    have h8 : (n ^ 2) ^ 4 ≤ X ^ 4 := by
      calc (n ^ 2) ^ 4 = n ^ 8 * 1 := by ring
        _ ≤ n ^ 8 * (7 * n) :=
          mul_le_mul_of_nonneg_left (by linarith only [hn2]) (pow_nonneg hn0.le 8)
        _ = 7 * n ^ 9 := by ring
        _ ≤ X ^ 4 := hX
    exact le_of_pow_le_pow_left₀ (by norm_num) hX0.le h8
  -- the interval and the frequency shift
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = n - 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = n + L - 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : n / 2 ≤ a := by rw [ha]; linarith
  have han : a ≤ n := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith [Nat.cast_nonneg (α := ℝ) L]
  have hbn : b ≤ 2 * n := by rw [hb]; linarith
  have hRa : hR ≤ a := by rw [ha]; linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈X / (a * (a + hR))⌉₊ := ⟨_, rfl⟩
  have hk1 : X / (a * (a + hR)) ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hk2 : (k : ℝ) < X / (a * (a + hR)) + 1 := by
    rw [hk]; exact Nat.ceil_lt_add_one (div_nonneg hX0.le (by positivity))
  -- Endpoint bounds for the dual interval and the stationary-phase remainder.
  have hαv : diffPhase1 T hR k a = k - X / (a * (a + hR)) := by
    rw [diffPhase1_eq ha0 hR0.le, hXd]
  have hβv : diffPhase1 T hR k b = k - X / (b * (b + hR)) := by
    rw [diffPhase1_eq hb0 hR0.le, hXd]
  have haa := block_aa_ge ha2 hn0.le hR0.le
  have hfreq : X / (a * (a + hR)) ≤ 4 * (X / n ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left haa (by positivity : (0 : ℝ) ≤ 4 * (X / n ^ 2))
    have e : 4 * (X / n ^ 2) * (n ^ 2 / 4) = X := by field_simp
    linarith
  have hP3one : 1 ≤ X / n ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hba : X / (b * (b + hR)) ≤ X / (a * (a + hR)) :=
    div_le_div_of_nonneg_left hX0.le (by positivity)
      (mul_le_mul hab (by linarith : a + hR ≤ b + hR) (by positivity) hb0.le)
  have hβα : diffPhase1 T hR k b - diffPhase1 T hR k a + 1 ≤ 5 * (X / n ^ 2) := by
    rw [hαv, hβv]
    have : 0 ≤ X / (b * (b + hR)) := by positivity
    linarith
  have hβα0 : 0 ≤ diffPhase1 T hR k b - diffPhase1 T hR k a + 1 := by
    rw [hαv, hβv]; linarith
  have hMle : (((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ))
      ≤ 5 * (X / n ^ 2) := by
    have hβ0 : 0 ≤ diffPhase1 T hR k b := by rw [hβv]; linarith
    have h1 := Nat.ceil_lt_add_one hβ0
    have h2 := Nat.lt_floor_add_one (diffPhase1 T hR k a)
    rcases le_total (⌊diffPhase1 T hR k a⌋₊ + 1) ⌈diffPhase1 T hR k b⌉₊ with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      push_cast
      linarith
  have hK : ((2 * k + 1 : ℕ) : ℝ) ≤ 11 * (X / n ^ 2) := by push_cast; linarith
  have hdualNum := fifthBlock_dual_numeric
    (γ := 12 * ((b + hR / 2) * (b * (b + hR)) ^ 4) /
      ((a + hR / 2) * (a * (a + hR)) ^ 4)) hn0 hX0 (by positivity)
    (fifthBlock_gamma_le hn0 ha2 hab hbn hR0.le hRn) (by positivity) hMle
    (fifthBlock_lam_ge hX0 hn0 ha2 hR0.le)
    (fifthBlock_lam_le hX0 hn0 ha2 han hR0.le hRn)
    (block_lam₂_ge hX0 hn0 hb0 hbn hR0.le hRn)
  have herrorNum := fifthBlock_B_error_le hn0 hX0 hXn
    (block_lam₂_ge hX0 hn0 hb0 hbn hR0.le hRn)
    (by positivity) (block_lam₃_le hX0 hn0 ha2)
    (by positivity) (block_rho_le hn0 ha2 hab hbn hR0.le hRn) hK hβα
  set A' : ℤ := (N : ℤ) - 1 with hA'
  set B' : ℤ := (N : ℤ) + L - 1 with hB'
  have hA'c : ((A' : ℤ) : ℝ) = a := by rw [hA', ha, hn]; push_cast; ring
  have hB'c : ((B' : ℤ) : ℝ) = b := by rw [hB', hb, hn]; push_cast; ring
  have hAB : A' ≤ B' := by rw [hA', hB']; omega
  -- An integer frequency shift leaves the source exponential sum unchanged.
  have hsum : ∑ n' ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log (n + n' + hR)
        - Real.log (n + n'))) : ℝ) : ℂ) * I)
      = ∑ m ∈ Finset.Ioc A' B', Complex.exp (((2 * Real.pi * diffPhase T hR k m : ℝ) : ℂ) * I) := by
    have hB'' : B' = A' + L := by rw [hA', hB']; ring
    rw [hB'', sum_Ioc_int_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : (((A' + 1 + j : ℤ)) : ℝ) = n + j := by rw [hA', hn]; push_cast; ring
    rw [hcast]
    simp only [diffPhase]
    have e : T * (Real.log (n + j + hR) - Real.log (n + j)) + k * (n + j)
        = T * (Real.log (n + j + hR) - Real.log (n + j)) + ((k * (N + j) : ℕ) : ℝ) := by
      rw [hn]; push_cast; ring
    rw [e, cexp_two_pi_add_nat]
  rw [hsum]
  -- Apply the stationary-phase transformation to the actual logarithmic phase.
  have hIcc : ∀ y ∈ Set.Icc ((A' : ℤ) : ℝ) ((B' : ℤ) : ℝ), 0 < y ∧ a ≤ y ∧ y ≤ b := by
    intro y hy
    rw [hA'c, hB'c] at hy
    exact ⟨lt_of_lt_of_le ha0 hy.1, hy.1, hy.2⟩
  have hα : 0 ≤ diffPhase1 T hR k ((A' : ℤ) : ℝ) := by
    rw [hA'c, diffPhase1_eq ha0 hR0.le, ← hXd]
    linarith
  have hβk : diffPhase1 T hR k ((B' : ℤ) : ℝ) ≤ k := by
    rw [hB'c, diffPhase1_eq hb0 hR0.le]
    have : 0 ≤ T * hR / (b * (b + hR)) := by positivity
    linarith
  have hKB : 2 * diffPhase1 T hR k ((B' : ℤ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hB := norm_sum_sub_bDualSum_le (f := diffPhase T hR k) (f' := diffPhase1 T hR k)
    (f'' := diffPhase2 T hR) (f''' := diffPhase3 T hR) hAB (lam₂ := 2 * X / (b + hR) ^ 3)
    (lam₃ := 6 * X / a ^ 4) (ρ := ((b + hR) / a) ^ 3)
    (δ := n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)) (K := 2 * k + 1)
    (fun y hy => hasDerivAt_diffPhase (hIcc y hy).1 hR0.le)
    (fun y hy => hasDerivAt_diffPhase1 (hIcc y hy).1 hR0.le)
    (fun y hy => hasDerivAt_diffPhase2 (hIcc y hy).1 hR0.le)
    (by positivity)
    (fun y hy => by
      obtain ⟨hy0, _, hyb⟩ := hIcc y hy
      refine le_trans ?_ (diffPhase2_ge hT.le hy0 hR0.le)
      have h1 : 2 * X / (b + hR) ^ 3 ≤ 2 * X / (y + hR) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by linarith) (by linarith) 3)
      rw [hXd, ← mul_assoc] at h1
      rw [hXd, ← mul_assoc]
      exact h1)
    (fun y hy => by
      obtain ⟨hy0, hya, _⟩ := hIcc y hy
      refine (diffPhase2_le hT.le hy0 hR0.le).trans ?_
      have e : ((b + hR) / a) ^ 3 * (2 * X / (b + hR) ^ 3) = 2 * X / a ^ 3 := by
        field_simp
      have h1 : 2 * X / y ^ 3 ≤ 2 * X / a ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha0.le hya 3)
      rw [hXd, ← mul_assoc] at h1 e
      rw [hXd, ← mul_assoc, e]
      exact h1)
    (fun y hy => by
      obtain ⟨hy0, hya, _⟩ := hIcc y hy
      refine (abs_diffPhase3_le hT.le hy0 hR0.le).trans ?_
      have h1 : 6 * X / y ^ 4 ≤ 6 * X / a ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha0.le hya 4)
      rw [hXd, ← mul_assoc] at h1
      rw [hXd, ← mul_assoc]
      exact h1)
    (by positivity) hα hKB (by norm_num) (fun ν : ℕ => dualX T hR (k - ν))
    (fun ν h1 h2 => by
      rw [hA'c, diffPhase1_eq ha0 hR0.le] at h1
      rw [hB'c, diffPhase1_eq hb0 hR0.le] at h2
      have hu0 : 0 < (k : ℝ) - ν := by
        have : 0 < T * hR / (b * (b + hR)) := by positivity
        linarith
      refine ⟨?_, diffPhase1_dualX hT hR0 hu0 |>.trans (by ring)⟩
      rw [hA'c, hB'c]
      refine dualX_mem_Icc hT hR0 hu0 ha0.le hb0.le ?_ ?_
      · rw [le_div_iff₀ hu0]
        have h1' : (k : ℝ) - ν < T * hR / (a * (a + hR)) := by linarith
        rw [lt_div_iff₀ (by positivity)] at h1'
        calc a * (a + hR) * ((k : ℝ) - ν) = ((k : ℝ) - ν) * (a * (a + hR)) := by ring
          _ ≤ T * hR := h1'.le
      · rw [div_le_iff₀ hu0]
        have h2' : T * hR / (b * (b + hR)) < (k : ℝ) - ν := by linarith
        rw [div_lt_iff₀ (by positivity)] at h2'
        calc T * hR ≤ ((k : ℝ) - ν) * (b * (b + hR)) := h2'.le
          _ = b * (b + hR) * ((k : ℝ) - ν) := by ring)
  rw [hA'c, hB'c] at hB
  -- The fifth derivative bounds the transformed sum.
  have hlam1 : (a + hR / 2) * (a * (a + hR)) ^ 4 ≤ (T * hR) ^ 4 := by
    rw [← hXd]
    have := fifthBlock_lam_le hX0 hn0 ha2 han hR0.le hRn
    rw [div_le_iff₀ (by positivity)] at this
    have e : 7 * (n ^ 9 / X ^ 4) * X ^ 4 = 7 * n ^ 9 := by field_simp
    linarith
  have hD := norm_dualSum_diffPhase_fifth_le (k := k) hT hR0 hRa hab hlam1
  have hl2e : 2 * T * hR / (b + hR) ^ 3 = 2 * X / (b + hR) ^ 3 := by rw [hXd]; ring
  rw [hl2e, ← hXd] at hD
  -- assemble
  set S := ∑ m ∈ Finset.Ioc A' B', Complex.exp (((2 * Real.pi * diffPhase T hR k m : ℝ) : ℂ) * I)
  set D := ∑ ν ∈ Finset.Ioo ⌊diffPhase1 T hR k a⌋₊ ⌈diffPhase1 T hR k b⌉₊,
      bDualTerm (diffPhase T hR k) (diffPhase2 T hR) (fun ν : ℕ => dualX T hR (k - ν)) ν
  have htri : ‖S‖ ≤ ‖S - D‖ + ‖D‖ := by
    have := norm_add_le (S - D) D
    rwa [sub_add_cancel] at this
  have hP3 : 0 ≤ X / n ^ 2 := by positivity
  have hP4 : 0 ≤ (n ^ 3 / X) ^ (1 / 2 : ℝ) := by positivity
  have hP5 : 0 ≤ X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ) := by positivity
  linarith only [htri, hB, hD, hdualNum, herrorNum, hP3, hP4, hP5]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_sum_diffLog_fifth_le_B
