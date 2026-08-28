import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-!
# Fine continuous-circuit nets at twentieth operator resolution

The quarter-net used for asymptotic circuit occupation is too coarse for a sharp finite-window
majorant.  A fixed `1/20` operator net keeps the same near-Hilbert gate budget while shrinking each
projective spectral tube to radius `1/10`.  Its explicit entropy still lies below the anchored
Boolean projective carrier eventually.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def exactTwentiethCircuitNet (n R : ℕ) :
    Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  if hR : 0 < R then
    Classical.choose
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 20 : ℝ)) (by norm_num))
  else
    {1}

theorem exactTwentiethCircuitNet_cover {n R : ℕ}
    (A : TwoQubitArchitecture n R)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ∃ W ∈ exactTwentiethCircuitNet n R,
      dist
          ((A.contraction gates :
            Matrix.unitaryGroup (Fin n → Bool) ℂ) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (1 / 20 : ℝ) := by
  classical
  by_cases hR : 0 < R
  · rw [exactTwentiethCircuitNet, dif_pos hR]
    exact (Classical.choose_spec
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 20 : ℝ)) (by norm_num))).1 A gates
  · have hR0 : R = 0 := Nat.eq_zero_of_not_pos hR
    subst R
    refine ⟨1, ?_, ?_⟩
    · simp [exactTwentiethCircuitNet]
    · simp [TwoQubitArchitecture.contraction]

theorem exactTwentiethCircuitNet_card_real_le (n R : ℕ) :
    ((exactTwentiethCircuitNet n R).card : ℝ) ≤
      1 + ((n * n : ℕ) : ℝ) ^ R *
        (1 + 80 * (R : ℝ)) ^ (32 * R) := by
  classical
  by_cases hR : 0 < R
  · have hcard := (Classical.choose_spec
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 20 : ℝ)) (by norm_num))).2
    have hformula :
        ((exactTwentiethCircuitNet n R).card : ℝ) ≤
          ((n * n : ℕ) : ℝ) ^ R *
            (1 + 80 * (R : ℝ)) ^ (32 * R) := by
      rw [exactTwentiethCircuitNet, dif_pos hR]
      norm_num [Nat.cast_mul, div_eq_mul_inv] at hcard ⊢
      ring_nf at hcard ⊢
      exact hcard
    linarith
  · have hR0 : R = 0 := Nat.eq_zero_of_not_pos hR
    subst R
    simp [exactTwentiethCircuitNet]

noncomputable def atMostTwentiethCircuitNet (n s : ℕ) :
    Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  (Finset.range (s + 1)).biUnion (exactTwentiethCircuitNet n)

def atMostTwentiethCircuitEntropyBound (n s : ℕ) : ℝ :=
  ∑ R ∈ Finset.range (s + 1),
    (1 + ((n * n : ℕ) : ℝ) ^ R *
      (1 + 80 * (R : ℝ)) ^ (32 * R))

theorem atMostTwentiethCircuitNet_card_real_le (n s : ℕ) :
    ((atMostTwentiethCircuitNet n s).card : ℝ) ≤
      atMostTwentiethCircuitEntropyBound n s := by
  classical
  have hcardNat :
      (atMostTwentiethCircuitNet n s).card ≤
        ∑ R ∈ Finset.range (s + 1),
          (exactTwentiethCircuitNet n R).card :=
    Finset.card_biUnion_le
  have hcardReal :
      ((atMostTwentiethCircuitNet n s).card : ℝ) ≤
        ∑ R ∈ Finset.range (s + 1),
          ((exactTwentiethCircuitNet n R).card : ℝ) := by
    exact_mod_cast hcardNat
  refine hcardReal.trans ?_
  rw [atMostTwentiethCircuitEntropyBound]
  exact Finset.sum_le_sum fun R _ => exactTwentiethCircuitNet_card_real_le n R

theorem atMostTwentiethCircuitNet_cover
    {n s : ℕ} (C : TwoQubitCircuit n) (hC : C.gateCount ≤ s) :
    ∃ W ∈ atMostTwentiethCircuitNet n s,
      dist
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (1 / 20 : ℝ) := by
  classical
  obtain ⟨W, hW, hdist⟩ :=
    exactTwentiethCircuitNet_cover C.architecture C.gates
  refine ⟨W, ?_, hdist⟩
  rw [atMostTwentiethCircuitNet, Finset.mem_biUnion]
  exact ⟨C.gateCount, Finset.mem_range.mpr (by omega), hW⟩

private theorem four_mul_add_lt_two_pow_twentieth
    {n : ℕ} (hn : 13 ≤ n) :
    4 * n + 12 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn13 ih =>
      rw [pow_succ]
      have hlarge : 4 ≤ 2 ^ n := by
        have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        omega
      omega

private theorem le_two_pow_of_thirteen
    {n : ℕ} (hn : 13 ≤ n) : n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn13 ih =>
      rw [pow_succ]
      omega

private theorem nearHilbertTwentiethCircuitBudget_entropy_majorant
    {n : ℕ} (hn : 13 ≤ n) :
    atMostTwentiethCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) ≤
      (2 : ℝ) ^
        ((34 * n + 224) * nearHilbertContinuousCircuitBudget n + n + 2) := by
  let s := nearHilbertContinuousCircuitBudget n
  let A := 34 * n + 224
  have hs_le : s ≤ 2 ^ n := by
    dsimp [s, nearHilbertContinuousCircuitBudget]
    exact Nat.div_le_self _ _
  have hn_two_pow : n ≤ 2 ^ n := le_two_pow_of_thirteen hn
  have hnn : n * n ≤ 2 ^ (2 * n) := by
    calc
      n * n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hn_two_pow hn_two_pow
      _ = 2 ^ (2 * n) := by
        rw [← pow_add]
        congr 1
        omega
  have hbaseR {R : ℕ} (hR : R ≤ s) :
      1 + 80 * R ≤ 2 ^ (n + 7) := by
    have hRpow : R ≤ 2 ^ n := hR.trans hs_le
    calc
      1 + 80 * R ≤ 128 * 2 ^ n := by omega
      _ = 2 ^ (n + 7) := by
        rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_add]
        congr 1
        omega
  have hterm {R : ℕ} (hRmem : R ∈ Finset.range (s + 1)) :
      1 + ((n * n : ℕ) : ℝ) ^ R *
          (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
        (2 : ℝ) ^ (A * s + 1) := by
    have hR : R ≤ s := by simpa using Finset.mem_range.mp hRmem
    have hfirst :
        ((n * n : ℕ) : ℝ) ^ R ≤ (2 : ℝ) ^ ((2 * n) * R) := by
      have hnnR : (((n * n : ℕ) : ℝ)) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
        exact_mod_cast hnn
      calc
        ((n * n : ℕ) : ℝ) ^ R ≤ (((2 ^ (2 * n) : ℕ) : ℝ)) ^ R :=
          pow_le_pow_left₀ (by positivity) hnnR R
        _ = (2 : ℝ) ^ ((2 * n) * R) := by
          push_cast
          rw [← pow_mul]
    have hsecond :
        (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ ((n + 7) * (32 * R)) := by
      have hbaseReal :
          (1 : ℝ) + 80 * (R : ℝ) ≤ ((2 ^ (n + 7) : ℕ) : ℝ) := by
        exact_mod_cast hbaseR hR
      calc
        (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
            (((2 ^ (n + 7) : ℕ) : ℝ)) ^ (32 * R) :=
          pow_le_pow_left₀ (by positivity) hbaseReal _
        _ = (2 : ℝ) ^ ((n + 7) * (32 * R)) := by
          push_cast
          rw [← pow_mul]
    have hproduct :
        ((n * n : ℕ) : ℝ) ^ R *
            (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (A * s) := by
      calc
        ((n * n : ℕ) : ℝ) ^ R *
              (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
            (2 : ℝ) ^ ((2 * n) * R) *
              (2 : ℝ) ^ ((n + 7) * (32 * R)) :=
          mul_le_mul hfirst hsecond (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (A * R) := by
          rw [← pow_add]
          congr 1
          dsimp [A]
          ring
        _ ≤ (2 : ℝ) ^ (A * s) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left A hR)
    calc
      1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 80 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (A * s) + (2 : ℝ) ^ (A * s) :=
        add_le_add (one_le_pow₀ (by norm_num)) hproduct
      _ = (2 : ℝ) ^ (A * s + 1) := by rw [pow_succ]; ring
  have hsum :
      atMostTwentiethCircuitEntropyBound n s ≤
        (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := by
    rw [atMostTwentiethCircuitEntropyBound]
    calc
      ∑ R ∈ Finset.range (s + 1),
          (1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 80 * (R : ℝ)) ^ (32 * R)) ≤
          ∑ R ∈ Finset.range (s + 1), (2 : ℝ) ^ (A * s + 1) :=
        Finset.sum_le_sum fun R hR => hterm hR
      _ = (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := by simp
  have hs_succ : s + 1 ≤ 2 ^ (n + 1) := by
    calc
      s + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right hs_le 1
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hs_succ_real : (((s + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (n + 1) := by
    have : (((s + 1 : ℕ) : ℝ)) ≤ (((2 ^ (n + 1) : ℕ) : ℝ)) := by
      exact_mod_cast hs_succ
    simpa using this
  calc
    atMostTwentiethCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) =
        atMostTwentiethCircuitEntropyBound n s := by rfl
    _ ≤ (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := hsum
    _ ≤ (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (A * s + 1) :=
      mul_le_mul_of_nonneg_right hs_succ_real (by positivity)
    _ = (2 : ℝ) ^ (A * s + n + 2) := by
      rw [← pow_add]
      congr 1
      omega

theorem eventually_nearHilbertTwentiethCircuitEntropy_lt_projectiveBooleanCarrier :
    ∀ᶠ n : ℕ in Filter.atTop,
      atMostTwentiethCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
        ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 13] with n hn
  let s := nearHilbertContinuousCircuitBudget n
  let A := 34 * n + 224
  have hA : A ≤ 48 * (n + 1) := by
    dsimp [A]
    omega
  have hdiv : (64 * (n + 1)) * s ≤ 2 ^ n := by
    dsimp [s, nearHilbertContinuousCircuitBudget]
    exact Nat.mul_div_le _ _
  have hbudget : 4 * (A * s) ≤ 3 * 2 ^ n := by
    calc
      4 * (A * s) ≤ 4 * (48 * (n + 1) * s) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right s hA)
      _ = 3 * ((64 * (n + 1)) * s) := by ring
      _ ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 hdiv
  have hsmall := four_mul_add_lt_two_pow_twentieth hn
  have hexponent : A * s + n + 2 < 2 ^ n - 1 := by
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    omega
  have hmajor := nearHilbertTwentiethCircuitBudget_entropy_majorant hn
  have hpowlt :
      (2 : ℝ) ^ (A * s + n + 2) < (2 : ℝ) ^ (2 ^ n - 1) :=
    pow_lt_pow_right₀ (by norm_num) hexponent
  calc
    atMostTwentiethCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) ≤
        (2 : ℝ) ^ (A * s + n + 2) := by simpa [A, s] using hmajor
    _ < (2 : ℝ) ^ (2 ^ n - 1) := hpowlt
    _ = ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by norm_cast

end

end GaloisForLFunctions.HTGeometry
