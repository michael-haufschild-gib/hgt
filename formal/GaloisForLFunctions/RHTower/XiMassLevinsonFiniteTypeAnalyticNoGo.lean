import GaloisForLFunctions.RHTower.PrimeSourceCancellationBudget
import GaloisForLFunctions.RHTower.XiMassLevinsonRoughTailHorizon
import GaloisForLFunctions.RHTower.XiMassLevinsonFiniteOrderPolynomialNoGo

/-!
# Fixed finite-type analytic-symbol no-go for T1

This module closes the fixed entire finite-exponential-type escape left by the finite-order
polynomial obstruction. If an entire symbol `F` gives the true logarithmic prime coefficient on
all sufficiently large literal T1 windows `N^(49 : ℕ) < n ≤ N^(100 : ℕ)`, then `F - id` vanishes at all but
finitely many prime logarithms. Corpus prime-log uniqueness forces `F = id`; an exterior prime
square in a literal T1 window then contradicts true-prime support.

The capstone permits an arbitrary scale-dependent normalized mollifier supported through `N^(49 : ℕ)`.
Rough-tail divisor rigidity removes every mollifier coefficient except its unit coefficient, so
the same obstruction applies. Thus viable T1 analytic symbols must vary in exponential type with
scale, become non-entire/singular, subtract prime powers explicitly, or cease to factor through one
fixed logarithmic symbol.
-/

open Complex Finset

namespace RHTower.Sieve

noncomputable section

def finiteTypeAnalyticCriticalHeadCoeff (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  F (Real.log n : ℂ) * (((1 / Real.sqrt n : ℝ)) : ℂ)

def finiteTypeAnalyticMollifiedCriticalDetectorCoeff
    (F : ℂ → ℂ) (moll : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ q ∈ n.divisors, finiteTypeAnalyticCriticalHeadCoeff F (n / q) * moll q

/-- On a rough tail, every normalized aperture-supported mollifier disappears coefficientwise. -/
theorem finiteTypeAnalyticMollifiedCriticalDetectorCoeff_eq_head_of_rough
    {F : ℂ → ℂ} {moll : ℕ → ℂ} {M n : ℕ}
    (hmoll_one : moll 1 = 1) (hsupport : ∀ q, M < q → moll q = 0)
    (hn : 0 < n) (hrough : IsApertureRough M n) :
    finiteTypeAnalyticMollifiedCriticalDetectorCoeff F moll n =
      finiteTypeAnalyticCriticalHeadCoeff F n := by
  rw [finiteTypeAnalyticMollifiedCriticalDetectorCoeff]
  rw [Finset.sum_eq_single 1]
  · simp [finiteTypeAnalyticCriticalHeadCoeff, hmoll_one]
  · intro q hqmem hqne
    by_cases hqM : q ≤ M
    · exact (hqne (apertureRough_divisor_eq_one hn hrough
        (Nat.dvd_of_mem_divisors hqmem) hqM)).elim
    · simp [hsupport q (by omega)]
  · simp [Nat.one_mem_divisors.mpr hn.ne']

/-- Subtracting the identity preserves finite exponential type, with explicit constants. -/
theorem norm_sub_id_le_exponentialType
    {F : ℂ → ℂ} {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) :
    ∀ z : ℂ, ‖F z - z‖ ≤ (C + 1) * Real.exp ((A + 1) * ‖z‖) := by
  intro z
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg z
  have harg : A * ‖z‖ ≤ (A + 1) * ‖z‖ := by nlinarith
  have hexpA : Real.exp (A * ‖z‖) ≤ Real.exp ((A + 1) * ‖z‖) :=
    Real.exp_le_exp.mpr harg
  have hnorm_exp_self : ‖z‖ ≤ Real.exp ‖z‖ := by
    linarith [Real.add_one_le_exp ‖z‖]
  have hselfarg : ‖z‖ ≤ (A + 1) * ‖z‖ := by nlinarith
  have hnorm_exp : ‖z‖ ≤ Real.exp ((A + 1) * ‖z‖) :=
    hnorm_exp_self.trans (Real.exp_le_exp.mpr hselfarg)
  calc
    ‖F z - z‖ ≤ ‖F z‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ C * Real.exp (A * ‖z‖) + ‖z‖ := add_le_add (hgrow z) le_rfl
    _ ≤ C * Real.exp ((A + 1) * ‖z‖) + Real.exp ((A + 1) * ‖z‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hexpA hC0) hnorm_exp
    _ = (C + 1) * Real.exp ((A + 1) * ‖z‖) := by ring

/-- **Affine prime-log rigidity.** An entire finite-exponential-type function agreeing with the
identity at all but finitely many prime logarithms is the identity everywhere. -/
theorem eq_id_of_exponentialType_of_cofinite_primeLog_eq
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖))
    (E : Finset ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∉ E →
      F (Real.log p : ℂ) = (Real.log p : ℂ)) :
    F = id := by
  let G : ℂ → ℂ := fun z => F z - z
  have hGdiff : Differentiable ℂ G := hF.sub differentiable_id
  have hGgrow : ∀ z : ℂ,
      ‖G z‖ ≤ (C + 1) * Real.exp ((A + 1) * ‖z‖) := by
    simpa only [G] using norm_sub_id_le_exponentialType hA hC hgrow
  have hGprime : ∀ p : ℕ, p.Prime → p ∉ E → G (Real.log p : ℂ) = 0 := by
    intro p hp hpE
    simp only [G, hprime p hp hpE, sub_self]
  have hGzero : G = 0 :=
    GaloisForLFunctions.RHTower.PrimeCancellation.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
        hGdiff (by linarith : 0 ≤ A + 1) (by linarith : 1 ≤ C + 1)
        hGgrow E hGprime
  funext z
  have hz := congrFun hGzero z
  simpa only [G, Pi.zero_apply, sub_eq_zero, id_eq] using hz

/-- Every sufficiently large natural index belongs to a literal T1 moving window whose scale
lies beyond an arbitrary prescribed threshold. -/
theorem exists_t1AfeScale_ge_of_dyadic_cutoff_le
    (B : ℕ) {n : ℕ}
    (hn : 2 ^ (100 * (Nat.log 2 B + 1)) ≤ n) :
    ∃ N : ℕ, B ≤ N ∧ N ^ (49 : ℕ) < n ∧ n ≤ N ^ (100 : ℕ) := by
  let k : ℕ := Nat.log 2 n
  let q : ℕ := (k + 100) / 100
  let N : ℕ := 2 ^ q
  have hn0 : n ≠ 0 := by
    have hcutpos : 0 < 2 ^ (100 * (Nat.log 2 B + 1)) := pow_pos (by omega) _
    exact ne_of_gt (hcutpos.trans_le hn)
  have hkB : 100 * (Nat.log 2 B + 1) ≤ k := by
    have hmono := Nat.log_mono_right (b := 2) hn
    rw [Nat.log_pow (by omega : 1 < 2)] at hmono
    exact hmono
  have hk : 100 ≤ k := by omega
  have hqpos : 0 < q := by
    simp only [q]
    omega
  have hlogBq : Nat.log 2 B + 1 ≤ q := by
    simp only [q]
    omega
  have hBN : B ≤ N := by
    have hlt : B < 2 ^ (Nat.log 2 B + 1) :=
      Nat.lt_pow_succ_log_self (by omega) B
    have hpow : 2 ^ (Nat.log 2 B + 1) ≤ 2 ^ q :=
      Nat.pow_le_pow_right (n := 2) (by omega) hlogBq
    exact (Nat.le_of_lt hlt).trans (by simpa only [N] using hpow)
  have hlowerExp : q * 49 < k := by
    simp only [q]
    omega
  have hupperExp : k + 1 ≤ q * 100 := by
    simp only [q]
    omega
  have hpowlog : 2 ^ k ≤ n := by
    simpa only [k] using Nat.pow_log_le_self 2 hn0
  have hbelow : N ^ (49 : ℕ) < n := by
    calc
      N ^ (49 : ℕ) = 2 ^ (q * 49) := by simp only [N, pow_mul]
      _ < 2 ^ k := Nat.pow_lt_pow_right (by omega) hlowerExp
      _ ≤ n := hpowlog
  have habove : n ≤ N ^ (100 : ℕ) := by
    calc
      n ≤ 2 ^ (k + 1) := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) n)
      _ ≤ 2 ^ (q * 100) := Nat.pow_le_pow_right (by omega) hupperExp
      _ = N ^ (100 : ℕ) := by simp only [N, pow_mul]
  exact ⟨N, hBN, hbelow, habove⟩

/-- No fixed entire finite-exponential-type log-symbol is coefficient-faithful to true-prime
half-density on every positive integer beyond an arbitrary rough aperture. -/
theorem no_fixedEntireFiniteExponentialType_truePrimeRoughTail (M : ℕ) :
    ¬ ∃ (F : ℂ → ℂ) (A C : ℝ),
      Differentiable ℂ F ∧ 0 ≤ A ∧ 1 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      (∀ n : ℕ, 0 < n → IsApertureRough M n →
        finiteTypeAnalyticCriticalHeadCoeff F n = truePrimeLogHalfDensityCoeff n) := by
  rintro ⟨F, A, C, hF, hA, hC, hgrow, hcorrect⟩
  let E : Finset ℕ := Finset.range (M + 1)
  have hprime : ∀ p : ℕ, p.Prime → p ∉ E →
      F (Real.log p : ℂ) = (Real.log p : ℂ) := by
    intro p hp hpE
    have hMp : M < p := by
      have : ¬p < M + 1 := by simpa only [E, Finset.mem_range] using hpE
      omega
    have heq := hcorrect p hp.pos (prime_isApertureRough hp hMp)
    rw [finiteTypeAnalyticCriticalHeadCoeff,
      truePrimeLogHalfDensityCoeff, if_pos hp] at heq
    exact mul_right_cancel₀ (one_div_sqrt_nat_cast_ne_zero hp.pos) heq
  have hFid : F = id :=
    eq_id_of_exponentialType_of_cofinite_primeLog_eq hF hA hC hgrow E hprime
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
  have hMp : M < p := by omega
  have hp2pos : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  have hp2rough : IsApertureRough M (p ^ (2 : ℕ)) := prime_sq_isApertureRough hp hMp
  have hp2not : ¬(p ^ (2 : ℕ)).Prime := Nat.Prime.not_prime_pow (by norm_num)
  have heq := hcorrect (p ^ (2 : ℕ)) hp2pos hp2rough
  rw [finiteTypeAnalyticCriticalHeadCoeff, hFid, id_eq,
    truePrimeLogHalfDensityCoeff, if_neg hp2not] at heq
  have hlogpos : 0 < Real.log (((p ^ (2 : ℕ) : ℕ) : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < p ^ (2 : ℕ) by nlinarith [hp.two_le]))
  exact (mul_ne_zero (by exact_mod_cast (ne_of_gt hlogpos))
    (one_div_sqrt_nat_cast_ne_zero hp2pos)) heq

/-- Identity log-symbol necessarily detects a prime square, while true-prime density does not. -/
theorem finiteTypeAnalyticCriticalHeadCoeff_id_ne_truePrime_at_prime_sq
    {p : ℕ} (hp : p.Prime) :
    finiteTypeAnalyticCriticalHeadCoeff id (p ^ (2 : ℕ)) ≠
      truePrimeLogHalfDensityCoeff (p ^ (2 : ℕ)) := by
  have hp2pos : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  have hp2not : ¬(p ^ (2 : ℕ)).Prime := Nat.Prime.not_prime_pow (by norm_num)
  rw [finiteTypeAnalyticCriticalHeadCoeff, id_eq,
    truePrimeLogHalfDensityCoeff, if_neg hp2not]
  have hp2gt : 1 < p ^ (2 : ℕ) := by nlinarith [hp.two_le]
  have hlogpos : 0 < Real.log (((p ^ (2 : ℕ) : ℕ) : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast hp2gt)
  exact mul_ne_zero (by exact_mod_cast (ne_of_gt hlogpos))
    (one_div_sqrt_nat_cast_ne_zero hp2pos)

/-- **T1 fixed finite-type analytic-symbol no-go at the actual AFE schedule.** Beyond every prescribed
scale threshold, no fixed entire finite-exponential-type log-symbol is coefficient-faithful to
true-prime half-density throughout the moving rough windows `N^(49 : ℕ) < n ≤ N^(100 : ℕ)`. -/
theorem no_fixedEntireFiniteExponentialType_truePrime_eventually_t1AfeWindows (N₀ : ℕ) :
    ¬ ∃ (F : ℂ → ℂ) (A C : ℝ),
      Differentiable ℂ F ∧ 0 ≤ A ∧ 1 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      (∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ n : ℕ, 0 < n →
        IsApertureRough (N ^ (49 : ℕ)) n → n ≤ N ^ (100 : ℕ) →
        finiteTypeAnalyticCriticalHeadCoeff F n = truePrimeLogHalfDensityCoeff n) := by
  rintro ⟨F, A, C, hF, hA, hC, hgrow, hcorrect⟩
  let B : ℕ := max N₀ 2
  let cutoff : ℕ := 2 ^ (100 * (Nat.log 2 B + 1))
  let E : Finset ℕ := Finset.range cutoff
  have hprime : ∀ p : ℕ, p.Prime → p ∉ E →
      F (Real.log p : ℂ) = (Real.log p : ℂ) := by
    intro p hp hpE
    have hpbig : cutoff ≤ p := by
      have : ¬p < cutoff := by simpa only [E, Finset.mem_range] using hpE
      omega
    obtain ⟨N, hBN, hlow, hupp⟩ :=
      exists_t1AfeScale_ge_of_dyadic_cutoff_le B (by simpa only [cutoff] using hpbig)
    have hN₀N : N₀ ≤ N := (le_max_left N₀ 2).trans (by simpa only [B] using hBN)
    have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans (by simpa only [B] using hBN)
    have heq := hcorrect N hN₀N hN2 p hp.pos (prime_isApertureRough hp hlow) hupp
    rw [finiteTypeAnalyticCriticalHeadCoeff,
      truePrimeLogHalfDensityCoeff, if_pos hp] at heq
    exact mul_right_cancel₀ (one_div_sqrt_nat_cast_ne_zero hp.pos) heq
  have hFid : F = id :=
    eq_id_of_exponentialType_of_cofinite_primeLog_eq hF hA hC hgrow E hprime
  let N : ℕ := max N₀ 4
  let i : Fin 1 := ⟨0, by omega⟩
  let p : ℕ := vinogradovBertrandPrimeReservoir (N ^ (49 : ℕ)) 1 i
  have hp : p.Prime := by
    simpa only [p, i] using vinogradovBertrandPrimeReservoir_prime (N ^ (49 : ℕ)) 1 i
  have hlow : N ^ (49 : ℕ) < p := by
    simpa only [p, i] using lt_vinogradovBertrandPrimeReservoir (N ^ (49 : ℕ)) 1 i
  have hpR : p ≤ 2 ^ (0 + 1) * (N ^ (49 : ℕ) + 2) := by
    have hreservoir := vinogradovBertrandPrimeReservoir_add_two_le (N ^ (49 : ℕ)) 1 i
    exact (Nat.le_add_right p 2).trans (by simpa only [p, i] using hreservoir)
  have hupp : p ^ (2 : ℕ) ≤ N ^ (100 : ℕ) :=
    (Nat.pow_le_pow_left hpR 2).trans
      (finiteOrderBertrandReservoir_square_le_t1AfeWindow
        (d := 0) (N := N) (by
          have hfour : 2 ^ (0 + 2) = 4 := by norm_num
          rw [hfour]
          simpa only [N] using le_max_right N₀ 4))
  have hN₀N : N₀ ≤ N := by simpa only [N] using le_max_left N₀ 4
  have hN2 : 2 ≤ N := (by omega : 2 ≤ 4).trans (by simpa only [N] using le_max_right N₀ 4)
  have hp2pos : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  have hp2rough : IsApertureRough (N ^ (49 : ℕ)) (p ^ (2 : ℕ)) :=
    prime_sq_isApertureRough hp hlow
  have heq := hcorrect N hN₀N hN2 (p ^ (2 : ℕ)) hp2pos hp2rough hupp
  rw [hFid] at heq
  exact finiteTypeAnalyticCriticalHeadCoeff_id_ne_truePrime_at_prime_sq hp heq

/-- **Detector-native T1 no-go.** Even an arbitrary scale-dependent normalized mollifier with
the literal support cutoff `N^(49 : ℕ)` cannot make one fixed entire finite-exponential-type symbol
coefficient-faithful on all sufficiently large T1 AFE windows. -/
theorem no_fixedEntireFiniteExponentialType_normalizedMollified_truePrime_eventually_t1AfeWindows
    (N₀ : ℕ) :
    ¬ ∃ (F : ℂ → ℂ) (A C : ℝ) (moll : ℕ → ℕ → ℂ),
      Differentiable ℂ F ∧ 0 ≤ A ∧ 1 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      (∀ N : ℕ, moll N 1 = 1) ∧
      (∀ N q : ℕ, N ^ (49 : ℕ) < q → moll N q = 0) ∧
      (∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ n : ℕ, 0 < n →
        IsApertureRough (N ^ (49 : ℕ)) n → n ≤ N ^ (100 : ℕ) →
        finiteTypeAnalyticMollifiedCriticalDetectorCoeff F (moll N) n =
          truePrimeLogHalfDensityCoeff n) := by
  rintro ⟨F, A, C, moll, hF, hA, hC, hgrow, hmoll_one, hsupport, hcorrect⟩
  apply no_fixedEntireFiniteExponentialType_truePrime_eventually_t1AfeWindows N₀
  refine ⟨F, A, C, hF, hA, hC, hgrow, ?_⟩
  intro N hN₀ hN2 n hn hrough hnupper
  have hcollapse :=
    finiteTypeAnalyticMollifiedCriticalDetectorCoeff_eq_head_of_rough
      (F := F) (moll := moll N) (M := N ^ (49 : ℕ)) (n := n)
      (hmoll_one N) (hsupport N) hn hrough
  exact hcollapse.symm.trans (hcorrect N hN₀ hN2 n hn hrough hnupper)

end

end RHTower.Sieve
