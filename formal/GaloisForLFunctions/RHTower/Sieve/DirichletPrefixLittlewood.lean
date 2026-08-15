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

end RHTower.Sieve
