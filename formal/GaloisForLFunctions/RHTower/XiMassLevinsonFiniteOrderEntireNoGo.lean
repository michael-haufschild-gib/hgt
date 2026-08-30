import GaloisForLFunctions.RHTower.PrimeLogFiniteOrderUniqueness
import GaloisForLFunctions.RHTower.XiMassLevinsonFiniteTypeAnalyticNoGo

/-!
# Fixed finite-order entire-symbol no-go for T1

Prime-log correctness makes the difference between a fixed entire detector symbol and the identity
vanish at all but finitely many prime logarithms. Finite-order prime-log uniqueness forces that
difference to vanish everywhere. A rough exterior prime square then contradicts true-prime support.

The capstone retains arbitrary scale-dependent normalized mollifiers supported through the literal
T1 aperture `N^49`. Thus every viable fixed entire T1 symbol must have infinite order; alternatives
must be scale-varying, singular/non-entire, or explicitly prime-power-aware.
-/

open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- A finite-order entire function agreeing with the identity at all but finitely many prime
logarithms is the identity everywhere. -/
theorem EntireFiniteOrder.eq_id_of_cofinite_primeLog_eq
    (F : EntireFiniteOrder) (E : Finset ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∉ E → F (Real.log p : ℂ) = (Real.log p : ℂ)) :
    (fun z : ℂ ↦ F z) = id := by
  let G : EntireFiniteOrder := F.sub entireFiniteOrderId
  have hGprime : ∀ p : ℕ, p.Prime → p ∉ E → G (Real.log p : ℂ) = 0 := by
    intro p hp hpE
    simp only [G, EntireFiniteOrder.sub_apply, entireFiniteOrderId_apply,
      hprime p hp hpE, sub_self]
  have hGzero : (fun z : ℂ ↦ G z) = 0 := G.eq_zero_of_cofinite_primeLog_zeros E hGprime
  funext z
  have hz := congrFun hGzero z
  simpa only [G, Pi.zero_apply, EntireFiniteOrder.sub_apply,
    entireFiniteOrderId_apply, sub_eq_zero, id_eq] using hz

/-- No fixed finite-order entire log-symbol is coefficient-faithful to true-prime half-density on
every sufficiently large literal T1 moving window. -/
theorem no_fixedEntireFiniteOrder_truePrime_eventually_t1AfeWindows (N₀ : ℕ) :
    ¬ ∃ F : EntireFiniteOrder,
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ n : ℕ, 0 < n →
        IsApertureRough (N ^ 49) n → n ≤ N ^ 100 →
        finiteTypeAnalyticCriticalHeadCoeff F n = truePrimeLogHalfDensityCoeff n := by
  rintro ⟨F, hcorrect⟩
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
  have hFid : (fun z : ℂ ↦ F z) = id :=
    _root_.RHTower.Sieve.EntireFiniteOrder.eq_id_of_cofinite_primeLog_eq F E hprime
  have hFid' : F.toFun = id := hFid
  let N : ℕ := max N₀ 4
  let i : Fin 1 := ⟨0, by omega⟩
  let p : ℕ := vinogradovBertrandPrimeReservoir (N ^ 49) 1 i
  have hp : p.Prime := by
    simpa only [p, i] using vinogradovBertrandPrimeReservoir_prime (N ^ 49) 1 i
  have hlow : N ^ 49 < p := by
    simpa only [p, i] using lt_vinogradovBertrandPrimeReservoir (N ^ 49) 1 i
  have hpR : p ≤ 2 ^ (0 + 1) * (N ^ 49 + 2) := by
    have hreservoir := vinogradovBertrandPrimeReservoir_add_two_le (N ^ 49) 1 i
    exact (Nat.le_add_right p 2).trans (by simpa only [p, i] using hreservoir)
  have hupp : p ^ 2 ≤ N ^ 100 :=
    (Nat.pow_le_pow_left hpR 2).trans
      (finiteOrderBertrandReservoir_square_le_t1AfeWindow
        (d := 0) (N := N) (by
          have hfour : 2 ^ (0 + 2) = 4 := by norm_num
          rw [hfour]
          simpa only [N] using le_max_right N₀ 4))
  have hN₀N : N₀ ≤ N := by simpa only [N] using le_max_left N₀ 4
  have hN2 : 2 ≤ N :=
    (by omega : 2 ≤ 4).trans (by simpa only [N] using le_max_right N₀ 4)
  have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hp2rough : IsApertureRough (N ^ 49) (p ^ 2) :=
    prime_sq_isApertureRough hp hlow
  have heq := hcorrect N hN₀N hN2 (p ^ 2) hp2pos hp2rough hupp
  rw [hFid'] at heq
  exact finiteTypeAnalyticCriticalHeadCoeff_id_ne_truePrime_at_prime_sq hp heq

/-- **Detector-native finite-order T1 no-go.** Arbitrary normalized scale-dependent mollification
inside `N^49` cannot make one fixed finite-order entire symbol coefficient-faithful throughout all
sufficiently large T1 AFE windows. -/
theorem no_fixedEntireFiniteOrder_normalizedMollified_truePrime_eventually_t1AfeWindows
    (N₀ : ℕ) :
    ¬ ∃ (F : EntireFiniteOrder) (moll : ℕ → ℕ → ℂ),
      (∀ N : ℕ, moll N 1 = 1) ∧
      (∀ N q : ℕ, N ^ 49 < q → moll N q = 0) ∧
      (∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ n : ℕ, 0 < n →
        IsApertureRough (N ^ 49) n → n ≤ N ^ 100 →
        finiteTypeAnalyticMollifiedCriticalDetectorCoeff F (moll N) n =
          truePrimeLogHalfDensityCoeff n) := by
  rintro ⟨F, moll, hmoll_one, hsupport, hcorrect⟩
  apply no_fixedEntireFiniteOrder_truePrime_eventually_t1AfeWindows N₀
  refine ⟨F, ?_⟩
  intro N hN₀ hN2 n hn hrough hnupper
  have hcollapse :=
    finiteTypeAnalyticMollifiedCriticalDetectorCoeff_eq_head_of_rough
      (F := F) (moll := moll N) (M := N ^ 49) (n := n)
      (hmoll_one N) (hsupport N) hn hrough
  exact hcollapse.symm.trans (hcorrect N hN₀ hN2 n hn hrough hnupper)

end

end RHTower.Sieve
