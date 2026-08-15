import GaloisForLFunctions.RHTower.Sieve.ZetaLineRate

/-!
# Littlewood's estimate at every prefix

The dyadic architecture of Littlewood's bound never uses the right endpoint of the range: the
per-block derivative-test estimate already holds on an arbitrary terminal subinterval of a block.
Splitting a general prefix `[1, M)` at the last complete dyadic block therefore gives the same
bound for every `M` below the canonical truncation point, with the same constants.

Prefix uniformity is what Abel summation needs in order to move the estimate from the line
`Re s = 1` to a shifted abscissa.
-/

namespace RHTower.Sieve

open Finset

private theorem log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private theorem log_natCast_mono {a b : ℕ} (h : a ≤ b) :
    Real.log ((a : ℕ) : ℝ) ≤ Real.log ((b : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

private theorem two_pow_merge_prefix (m : ℕ) (j : ℕ) (c : ℝ) :
    ((2 ^ m : ℕ) : ℝ) ^ j * ((2 ^ m : ℕ) : ℝ) ^ (c : ℝ)
      = (2 : ℝ) ^ (((m : ℝ) * (j : ℝ)) + (m : ℝ) * c) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℕ) := by push_cast; ring
  rw [hcast, ← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_natCast ((2 : ℝ) ^ ((m : ℕ) : ℝ)) j,
    ← Real.rpow_mul h2.le, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]

/-- **Dyadic tail with a free right endpoint.** -/
theorem dirichlet_tail_dyadic_prefix {t : ℝ} {A : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) :
    ∀ R M : ℕ, A ≤ M → M ≤ A * 2 ^ R →
      (∀ r, r < R → ∀ N, A * 2 ^ r ≤ N → N ≤ A * 2 ^ (r + 1) →
          ‖∑ n ∈ Finset.Ico (A * 2 ^ r) N, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ ε) →
      ‖∑ n ∈ Finset.Ico A M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ (R : ℝ) * ε := by
  intro R
  induction R with
  | zero =>
      intro M hAM hMA _
      have hM : M = A := by
        have : M ≤ A := by simpa using hMA
        omega
      subst hM
      simp
  | succ R ih =>
      intro M hAM hMA hb
      have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      rcases le_or_gt M (A * 2 ^ R) with hcase | hcase
      · have hmain := ih M hAM hcase (fun r hr => hb r (by omega))
        have hstep : (R : ℝ) * ε ≤ ((R + 1 : ℕ) : ℝ) * ε := by
          push_cast
          nlinarith [hε0, hRnn]
        linarith
      · have hAR : A ≤ A * 2 ^ R := by
          calc A = A * 1 := (Nat.mul_one A).symm
            _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A Nat.one_le_two_pow
        have hARM : A * 2 ^ R ≤ M := le_of_lt hcase
        have hsplit :
            (∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
              + (∑ n ∈ Finset.Ico (A * 2 ^ R) M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
            = ∑ n ∈ Finset.Ico A M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) :=
          Finset.sum_Ico_consecutive _ hAR hARM
        have hhead := ih (A * 2 ^ R) hAR le_rfl (fun r hr => hb r (by omega))
        have htailblock := hb R (by omega) M hARM hMA
        rw [← hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have : (R : ℝ) * ε + ε = ((R + 1 : ℕ) : ℝ) * ε := by
          push_cast
          ring
        linarith [hhead, htailblock, this.le, this.ge]

/-- **Two-regime bound at a free prefix.** -/
theorem norm_dirichlet_partial_two_regime_prefix {t : ℝ} {A S R M : ℕ} (hA : 1 ≤ A)
    (hSR : S ≤ R) {ε : ℝ} (hε0 : 0 ≤ ε) (hM : M ≤ A * 2 ^ R)
    (hb : ∀ r, S ≤ r → r < R → ∀ N, A * 2 ^ r ≤ N → N ≤ A * 2 ^ (r + 1) →
        ‖∑ n ∈ Finset.Ico (A * 2 ^ r) N, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ ε) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hC : 1 ≤ A * 2 ^ S := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ S := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hRSnn : (0 : ℝ) ≤ ((R - S : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases le_or_gt M (A * 2 ^ S) with hcase | hcase
  · -- everything is harmonic
    rcases lt_or_ge 1 M with hMpos | hMsmall
    · have hhead := norm_dirichlet_head_le (A := M) (t := t) (le_of_lt hMpos)
      have hmono : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ) :=
        log_natCast_mono (Nat.sub_le_sub_right hcase 1)
      have hmul : 0 ≤ ((R - S : ℕ) : ℝ) * ε := mul_nonneg hRSnn hε0
      linarith
    · have hempty : Finset.Ico 1 M = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, norm_zero]
      have hlog := log_natCast_nonneg (A * 2 ^ S - 1)
      have hmul : 0 ≤ ((R - S : ℕ) : ℝ) * ε := mul_nonneg hRSnn hε0
      linarith
  · have hCM : A * 2 ^ S ≤ M := le_of_lt hcase
    have hsplit :
        (∑ n ∈ Finset.Ico 1 (A * 2 ^ S), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
          + (∑ n ∈ Finset.Ico (A * 2 ^ S) M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
        = ∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) :=
      Finset.sum_Ico_consecutive _ hC hCM
    have hshift0 : ∀ j, A * 2 ^ S * 2 ^ j = A * 2 ^ (S + j) := by
      intro j
      rw [mul_assoc, ← pow_add]
    have hshift : ∀ j, A * 2 ^ S * 2 ^ (j + 1) = A * 2 ^ (S + j + 1) := by
      intro j
      rw [mul_assoc, ← pow_add, Nat.add_assoc]
    have hpow : A * 2 ^ S * 2 ^ (R - S) = A * 2 ^ R := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    have htail := dirichlet_tail_dyadic_prefix (t := t) (A := A * 2 ^ S) (ε := ε) hε0
      (R - S) M hCM (by rw [hpow]; exact hM)
      (fun j hj N hN1 hN2 => by
        have hjR : S + j < R := by omega
        rw [hshift0 j] at hN1 ⊢
        rw [hshift j] at hN2
        exact hb (S + j) (by omega) hjR N hN1 hN2)
    have hhead := norm_dirichlet_head_le hC t
    rw [← hsplit]
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add hhead htail

/-- **Littlewood's shape at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_shape_prefix {t : ℝ} (ht : 0 < t) {A S R M : ℕ}
    (hA : 1 ≤ A) (hSR : S ≤ R) (k : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) (hM : M ≤ A * 2 ^ R)
    (hk : ∀ r, S ≤ r → r < R → 2 ≤ k r)
    (hfac : ∀ r, S ≤ r → r < R → Nat.factorial (k r - 1) ≤ A * 2 ^ r)
    (hlow : ∀ r, S ≤ r → r < R → 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r, S ≤ r → r < R →
      t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
        * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeep : ∀ r, S ≤ r → r < R →
      3 * (2 : ℝ) ^ (k r) * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  refine norm_dirichlet_partial_two_regime_prefix hA hSR hε.le hM
    fun r hrS hrR N hN1 hN2 => ?_
  have hN : 1 ≤ A * 2 ^ r := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hspan : A * 2 ^ (r + 1) = 2 * (A * 2 ^ r) := by ring
  rw [hspan] at hN2
  refine le_trans
    (dirichlet_block_saving_of_small_factorial ht hN hN1 (by omega) (hk r hrS hrR)
      (hfac r hrS hrR) (hlow r hrS hrR) (hhigh r hrS hrR)) ?_
  exact block_saving_le_of_log_ge hN hε (hdeep r hrS hrR)

/-- **Endpoint reduction at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_endpoints_prefix {t : ℝ} (ht : 0 < t) {A S R M : ℕ}
    (hA : 1 ≤ A) (hSR : S < R) (k : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560)
    (hM : M ≤ A * 2 ^ R)
    (hkanti : ∀ r, S ≤ r → r < R → k r ≤ k S)
    (hktop : ∀ r, S ≤ r → r < R → 2 ≤ k r)
    (hfacS : Nat.factorial (k S - 1) ≤ A * 2 ^ S)
    (hlowTop : 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r, S ≤ r → r < R →
      t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
        * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ (k S) * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hlogpos : 0 ≤ Real.log (2560 / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  have hNmono : ∀ r r' : ℕ, r ≤ r' → A * 2 ^ r ≤ A * 2 ^ r' := fun r r' h =>
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) h)
  have hNpos : ∀ r : ℕ, 1 ≤ A * 2 ^ r := fun r => by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  refine norm_dirichlet_partial_littlewood_shape_prefix ht hA (by omega) k hε hM hktop ?_ ?_
    hhigh ?_
  · intro r hrS hrR
    calc Nat.factorial (k r - 1) ≤ Nat.factorial (k S - 1) :=
          Nat.factorial_le (by have := hkanti r hrS hrR; omega)
      _ ≤ A * 2 ^ S := hfacS
      _ ≤ A * 2 ^ r := hNmono S r hrS
  · intro r hrS hrR
    have hle : A * 2 ^ r ≤ A * 2 ^ (R - 1) := hNmono r (R - 1) (by omega)
    have hleR : ((A * 2 ^ r : ℕ) : ℝ) ≤ ((A * 2 ^ (R - 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have h0 : (0 : ℝ) ≤ ((A * 2 ^ r : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
        ≤ 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hleR (by norm_num)) ?_
          positivity
      _ ≤ t := hlowTop
  · intro r hrS hrR
    have hkle : k r ≤ k S := hkanti r hrS hrR
    have hpow : (2 : ℝ) ^ (k r) ≤ (2 : ℝ) ^ (k S) := pow_le_pow_right₀ (by norm_num) hkle
    have hlogle : Real.log ((A * 2 ^ S : ℕ) : ℝ) ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast hNpos S
      · exact_mod_cast hNmono S r hrS
    calc 3 * (2 : ℝ) ^ (k r) * Real.log (2560 / ε)
        ≤ 3 * (2 : ℝ) ^ (k S) * Real.log (2560 / ε) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogpos
          exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ) := hdeepS
      _ ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ) := hlogle

/-- **Constant order at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_const_prefix {t : ℝ} (ht : 0 < t) {A S R K M : ℕ}
    (hA : 1 ≤ A) (hSR : S < R) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hM : M ≤ A * 2 ^ R)
    (hfacS : Nat.factorial (K - 1) ≤ A * 2 ^ S)
    (hlowTop : 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhighS : t ≤ 2 * Real.pi * 2 ^ K * ((A * 2 ^ S : ℕ) : ℝ) ^ (K - 1)
      * ((A * 2 ^ S : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hNpos : ∀ r : ℕ, 1 ≤ A * 2 ^ r := fun r => by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  refine norm_dirichlet_partial_littlewood_endpoints_prefix ht hA hSR (fun _ => K) hε hε' hM
    (fun _ _ _ => le_refl K) (fun _ _ _ => hK) hfacS hlowTop ?_ hdeepS
  intro r hrS _
  refine le_trans hhighS ?_
  exact schedule_upper_bound_mono hK (hNpos S)
    (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hrS))

/-- **Power-of-two shape at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_pow_two_prefix {t : ℝ} (ht : 0 < t) {S R K M : ℕ}
    (hSR : S < R) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hM : M ≤ 2 ^ (R + 1))
    (hfacS : Nat.factorial (K - 1) ≤ 2 ^ (S + 1))
    (hhighS : t ≤ 2 * Real.pi * 2 ^ K * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
      * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ ((S : ℝ) + 1) * Real.log 2)
    (hlowTop : 8 * Real.pi * ((2 ^ R : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((S : ℝ) + 1) * Real.log 2 + ((R - S : ℕ) : ℝ) * ε := by
  have hbaseS : 2 * 2 ^ S = 2 ^ (S + 1) := by ring
  have hbaseTop : 2 * 2 ^ (R - 1) = 2 ^ R := by
    obtain ⟨j, rfl⟩ : ∃ j, R = j + 1 := ⟨R - 1, by omega⟩
    simp [pow_succ]
    ring
  have hbaseR : 2 * 2 ^ R = 2 ^ (R + 1) := by ring
  have hlogS : Real.log ((2 ^ (S + 1) : ℕ) : ℝ) = ((S : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlogSm : Real.log ((2 ^ (S + 1) - 1 : ℕ) : ℝ) ≤ ((S : ℝ) + 1) * Real.log 2 := by
    rw [← hlogS]
    exact log_natCast_mono (Nat.sub_le _ _)
  have hmain := norm_dirichlet_partial_littlewood_const_prefix (t := t) (A := 2) (S := S)
    (R := R) (K := K) (M := M) ht (by norm_num) hSR hε hε' hK
    (by rw [hbaseR]; exact hM)
    (by rw [hbaseS]; exact hfacS)
    (by rw [hbaseTop]; exact hlowTop)
    (by rw [hbaseS]; exact hhighS)
    (by rw [hbaseS, hlogS]; exact hdeepS)
  rw [hbaseS] at hmain
  refine le_trans hmain ?_
  have : 1 + Real.log ((2 ^ (S + 1) - 1 : ℕ) : ℝ) ≤ 1 + ((S : ℝ) + 1) * Real.log 2 := by
    linarith
  linarith

/-- **Exponent shape at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_exponent_prefix {t : ℝ} (ht : 0 < t) {S R K M : ℕ}
    (hSR : S < R) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hM : M ≤ 2 ^ (R + 1))
    (hfacS : Nat.factorial (K - 1) ≤ 2 ^ (S + 1))
    (hlowTop : 8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3) ≤ t)
    (hhighS : t ≤ 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1)
      - ((S : ℝ) + 1) / 3) * (2 : ℝ) ^ K)
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ ((S : ℝ) + 1) * Real.log 2) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((S : ℝ) + 1) * Real.log 2 + ((R - S : ℕ) : ℝ) * ε := by
  have hKcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    have : 1 ≤ K := by omega
    push_cast [Nat.cast_sub this]
    ring
  refine norm_dirichlet_partial_littlewood_pow_two_prefix ht hSR hε hε' hK hM hfacS ?_ hdeepS ?_
  · refine le_trans hhighS (le_of_eq ?_)
    have h1 : ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1) * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)
        = (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3) := by
      rw [two_pow_merge_prefix (S + 1) (K - 1) (-(1 / 3) : ℝ)]
      congr 1
      push_cast [hKcast]
      ring
    calc 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
          * (2 : ℝ) ^ K
        = 2 * Real.pi * (2 : ℝ) ^ K
            * ((2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)) := by ring
      _ = 2 * Real.pi * (2 : ℝ) ^ K
            * (((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
              * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) := by rw [h1]
      _ = 2 * Real.pi * (2 : ℝ) ^ K * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
            * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by ring
  · refine le_trans (le_of_eq ?_) hlowTop
    have hcast : ((2 ^ R : ℕ) : ℝ) = (2 : ℝ) ^ (R : ℕ) := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) R, ← Real.rpow_mul (by norm_num)]
    congr 2
    ring

/-- **Assembled bound at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_assembled_prefix {t : ℝ} (ht8 : 8 * Real.pi ≤ t)
    {K M : ℕ} (hK : 2 ≤ K) (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560)
    (hσ1 : 1 ≤ splitExponent t K)
    (hSR : splitExponent t K - 1 < topExponent t)
    (hM : M ≤ 2 ^ (topExponent t + 1))
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K))
    (hdeep : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε)
      ≤ ((splitExponent t K : ℕ) : ℝ) * Real.log 2) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 * ε := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht8
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ, σ = splitExponent t K := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = topExponent t := ⟨_, rfl⟩
  rw [← hσdef] at hσ1 hSR hfac hdeep
  rw [← hRdef] at hSR hM
  have hScast : ((σ - 1 : ℕ) : ℝ) + 1 = (σ : ℝ) := by
    have hval : ((σ - 1 : ℕ) : ℝ) = (σ : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ σ := hσ1
      push_cast [Nat.cast_sub h1]
      ring
    rw [hval]
    ring
  have hhigh : t ≤ 2 * Real.pi
      * (2 : ℝ) ^ ((((σ - 1 : ℕ) : ℝ) + 1) * ((K : ℝ) - 1) - (((σ - 1 : ℕ) : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K := by
    have hform : 2 * Real.pi
        * (2 : ℝ) ^ ((((σ - 1 : ℕ) : ℝ) + 1) * ((K : ℝ) - 1) - (((σ - 1 : ℕ) : ℝ) + 1) / 3)
          * (2 : ℝ) ^ K
        = 2 * Real.pi * (2 : ℝ) ^ ((σ : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) := by
      rw [hScast, ← Real.rpow_natCast (2 : ℝ) K, mul_assoc (2 * Real.pi),
        ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    rw [hform, hσdef]
    exact le_two_pow_splitExponent ht hK
  have hmain := norm_dirichlet_partial_littlewood_exponent_prefix (t := t) ht (S := σ - 1)
    (R := R) (K := K) (M := M) hSR hε hε' hK hM (by rwa [Nat.sub_add_cancel hσ1])
    (by rw [hRdef]; exact topExponent_bound ht8) hhigh (by rw [hScast]; exact hdeep)
  refine le_trans hmain ?_
  have hxnn := splitExponent_arg_nonneg hK hbig
  have hσle : (σ : ℝ)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) + 1 := by
    rw [hσdef]
    exact splitExponent_le hxnn
  have hRle : (R : ℝ) ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := by
    rw [hRdef]
    exact topExponent_le ht8
  have hRS : ((R - (σ - 1) : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast Nat.sub_le R (σ - 1)
  have hhead : (((σ - 1 : ℕ) : ℝ) + 1) * Real.log 2
      ≤ ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2 := by
    rw [hScast]
    exact mul_le_mul_of_nonneg_right hσle hlog2.le
  have htail : ((R - (σ - 1) : ℕ) : ℝ) * ε
      ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 * ε :=
    mul_le_mul_of_nonneg_right (le_trans hRS hRle) hε.le
  linarith

/-- **Canonical accuracy at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_canonical_prefix {t : ℝ} (ht8 : 8 * Real.pi ≤ t)
    {K M : ℕ} (hK : 2 ≤ K) (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t)
    (hσ1 : 1 ≤ splitExponent t K)
    (hSR : splitExponent t K - 1 < topExponent t)
    (hM : M ≤ 2 ^ (topExponent t + 1))
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
            * targetEps (splitExponent t K) K :=
  norm_dirichlet_partial_littlewood_assembled_prefix ht8 hK hbig
    (targetEps_pos _ _) (targetEps_le _ _) hσ1 hSR hM hfac
    (le_of_eq (targetEps_deep (splitExponent t K) K))

/-- **Littlewood's capstone at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_capstone_prefix {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    {K M : ℕ} (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi)))
    (hM : M ≤ 2 ^ (topExponent t + 1)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
            * targetEps (splitExponent t K) K := by
  have hπ := Real.pi_pos
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hlt := two_pow_lt_of_factorial_cond hK ht hcond
  have hσ1 : 1 ≤ splitExponent t K := one_le_splitExponent hK hlt
  have hSR : splitExponent t K - 1 < topExponent t :=
    splitExponent_sub_one_lt_topExponent hK ht16 hlt.le hσ1
  have hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K) :=
    factorial_le_two_pow_splitExponent hK hcond.le
  exact norm_dirichlet_partial_littlewood_canonical_prefix (by linarith) hK hlt.le hσ1 hSR hM hfac

/-- **Closed-form bound at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_explicit_prefix {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    {K M : ℕ} (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi)))
    (hM : M ≤ 2 ^ (topExponent t + 1)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2 + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
          * (2560 * Real.exp (-((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
              / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3))))) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hlt := two_pow_lt_of_factorial_cond hK ht hcond
  have hcap := norm_dirichlet_partial_littlewood_capstone_prefix ht16 hK hcond hM
  refine le_trans hcap ?_
  have hhead : ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
      ≤ Real.log 2 + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
    have heq : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) * Real.log 2
        = (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3) := by
      have h1 : Real.log 2 ≠ 0 := hlog2.ne'
      have h2 : ((K : ℝ) - 4 / 3) ≠ 0 := hden.ne'
      field_simp
    have hmono : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3)
        ≤ Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
      refine div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [hlog2, hKR]
    rw [add_mul, one_mul, heq]
    linarith
  have hlogtail : 0 ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := by
    have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
    have hone : (1 : ℝ) ≤ t / (8 * Real.pi) := by
      rw [le_div_iff₀ h8π]
      linarith
    have := Real.log_nonneg hone
    positivity
  have htail := mul_le_mul_of_nonneg_left (targetEps_splitExponent_le (t := t) hK) hlogtail
  linarith

/-- **Balanced form at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_balanced_prefix {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    {K M : ℕ} (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi)))
    (hbal : Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)))
    (hM : M ≤ 2 ^ (topExponent t + 1)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2 + 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hMle : Real.log (t / (8 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ h8π h2π]
    nlinarith
  have hexp := norm_dirichlet_partial_littlewood_explicit_prefix ht16 hK hcond hM
  have htail := tail_le_head (L := Real.log (t / (2 * Real.pi)))
    (M := Real.log (t / (8 * Real.pi))) hK hLnn hMle hbal
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by
    have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hsum : Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
      + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
      = 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
    field_simp
    ring
  linarith [hexp, htail, hsum]

/-- **Threshold form at a free prefix.** -/
theorem littlewood_threshold_prefix (K : ℕ) (hK : 2 ≤ K) :
    ∀ t : ℝ,
      max (16 * Real.pi)
          (2 * Real.pi * Real.exp (max (largenessBound K) (balanceBound K) + 1)) ≤ t →
      ∀ M : ℕ, M ≤ 2 ^ (topExponent t + 1) →
      ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
  intro t hT M hM
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (largenessBound K) (balanceBound K) + 1 := ⟨_, rfl⟩
  rw [← hCdef] at hT
  have ht16 : 16 * Real.pi ≤ t := le_trans (le_max_left _ _) hT
  have htexp : 2 * Real.pi * Real.exp C ≤ t := le_trans (le_max_right _ _) hT
  have hL : C ≤ Real.log (t / (2 * Real.pi)) := by
    have hquot : Real.exp C ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith
    have := Real.log_le_log (Real.exp_pos C) hquot
    rwa [Real.log_exp] at this
  have hlarge : largenessBound K < Real.log (t / (2 * Real.pi)) := by
    have := le_max_left (largenessBound K) (balanceBound K)
    rw [hCdef] at hL
    linarith
  have hbalance : balanceBound K ≤ Real.log (t / (2 * Real.pi)) := by
    have := le_max_right (largenessBound K) (balanceBound K)
    rw [hCdef] at hL
    linarith
  refine norm_dirichlet_partial_littlewood_balanced_prefix ht16 hK ?_ ?_ hM
  · exact hlarge
  · have hden : (0 : ℝ) < 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) := by
      have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      have : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
      positivity
    rw [le_div_iff₀ hden]
    rw [balanceBound] at hbalance
    nlinarith [hbalance]

/-- **The order chosen from `t`, at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_order_prefix {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) {M : ℕ}
    (hM : M ≤ 2 ^ (topExponent t + 1)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2
        + 2 * Real.log (t / (2 * Real.pi)) / ((littlewoodOrder t : ℝ) - 4 / 3) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have ht0 : 0 < t := by linarith
  have hK := two_le_littlewoodOrder ht
  have hthr := orderThreshold_littlewoodOrder_le ht
  refine littlewood_threshold_prefix (littlewoodOrder t) hK t (max_le ht16 ?_) M hM
  have hrw : max (largenessBound (littlewoodOrder t)) (balanceBound (littlewoodOrder t)) + 1
      = orderThreshold (littlewoodOrder t) := rfl
  rw [hrw, ← le_div_iff₀' h2π]
  have h := Real.exp_le_exp.mpr hthr
  rwa [Real.exp_log (by positivity)] at h

/-- **Littlewood's exponent at a free prefix.** -/
theorem norm_dirichlet_partial_littlewood_rate_prefix {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)))
    (hden : 4 / 3 < orderLowerBound (Real.log (t / (2 * Real.pi)))) {M : ℕ}
    (hM : M ≤ 2 ^ (topExponent t + 1)) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2
        + 2 * Real.log (t / (2 * Real.pi))
            / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  refine le_trans (norm_dirichlet_partial_littlewood_order_prefix ht16 ht2 hM) ?_
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlow := orderLowerBound_lt ht2
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hd1 : (0 : ℝ) < orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3 := by linarith
  have hd2 : (0 : ℝ) < ((littlewoodOrder t : ℕ) : ℝ) - 4 / 3 := by linarith
  have hstep : 2 * Real.log (t / (2 * Real.pi)) / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3)
      ≤ 2 * Real.log (t / (2 * Real.pi))
          / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
    rw [div_le_div_iff₀ hd2 hd1]
    nlinarith [hLnn, hlow]
  linarith

end RHTower.Sieve
