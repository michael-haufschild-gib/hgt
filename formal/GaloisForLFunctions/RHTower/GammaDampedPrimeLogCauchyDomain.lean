import GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank
import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import Mathlib.Analysis.PSeries

/-!
# Gamma damping crosses the complete prime-log Cauchy core

The prime-only positive half-weight leaves every nonzero finite packet of distinct upper-half-plane
Cauchy sections outside `ell²`.  The canonical doubled-frequency Gamma diagonal contributes exactly
the missing inverse-prime factor.  Its exponential bound, together with Cauchy decay at infinity,
makes every finite packet summable at the critical half-weight.

The capstone theorem records the exact carrier transition: Gamma sewing repairs the full finite
Cauchy core, while the corresponding prime-only packet is summable exactly when it is zero.  This
is a domain theorem, not positivity of the completed Weil form and not RH.
-/

open Filter

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

def invNatLogSq (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)

lemma summable_invNatLogSq : Summable invNatLogSq := by
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · have hbase : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    apply (hbase.mul_left ((Real.log 2) ^ (-2 : ℤ))).congr
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [invNatLogSq]
    · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      simp only [invNatLogSq, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      rw [zpow_neg, zpow_ofNat]
      field_simp
  · filter_upwards with n
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hlogle : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hnpos hn1pos (by exact_mod_cast Nat.le_succ n)
    dsimp [invNatLogSq]
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul (by exact_mod_cast Nat.le_succ n)
        (sq_le_sq₀ hlogpos.le (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1))) |>.2 hlogle)
        (sq_nonneg _) (by positivity)

lemma summable_prime_invNatLogSq :
    Summable (fun p : Nat.Primes => invNatLogSq p) :=
  summable_invNatLogSq.subtype Nat.Prime

def gammaDampedPrimeLogCauchyPacketEnergy {n : ℕ}
    (z c : Fin n → ℂ) (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    Complex.normSq
      (∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹)

lemma eventually_gammaDampedPrimeLogCauchyPacketEnergy_le {n : ℕ}
    (z c : Fin n → ℂ) :
    ∀ᶠ p : Nat.Primes in cofinite,
      gammaDampedPrimeLogCauchyPacketEnergy z c p ≤
        4 * Real.sqrt 2 * (∑ j, ‖c j‖) ^ 2 * invNatLogSq p := by
  let B : ℝ := 2 * (∑ j, ‖z j‖) + 1
  have htail := tendsto_primeLogSupport_cofinite.eventually_ge_atTop B
  filter_upwards [htail] with p hp
  have ht : 0 < primeLogSupport p := primeLogSupport_pos p
  have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hpacket :
      ‖∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹‖ ≤
        2 * (∑ j, ‖c j‖) / primeLogSupport p := by
    calc
      ‖∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹‖ ≤
          ∑ j, ‖c j * (z j - (primeLogSupport p : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖c j‖ * (2 / primeLogSupport p) := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [norm_mul, norm_inv]
        gcongr
        have hzsum : ‖z j‖ ≤ ∑ k, ‖z k‖ :=
          Finset.single_le_sum (fun k _ => norm_nonneg (z k)) (Finset.mem_univ j)
        have hhalf : primeLogSupport p / 2 ≤
            primeLogSupport p - ‖z j‖ := by
          dsimp [B] at hp
          linarith
        have hrev : primeLogSupport p - ‖z j‖ ≤
            ‖z j - (primeLogSupport p : ℂ)‖ := by
          calc
            primeLogSupport p - ‖z j‖ ≤
                ‖(primeLogSupport p : ℂ) - z j‖ := by
              simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using
                (norm_sub_norm_le (primeLogSupport p : ℂ) (z j))
            _ = ‖z j - (primeLogSupport p : ℂ)‖ := norm_sub_rev _ _
        have hden : primeLogSupport p / 2 ≤
            ‖z j - (primeLogSupport p : ℂ)‖ := hhalf.trans hrev
        rw [show 2 / primeLogSupport p = (primeLogSupport p / 2)⁻¹ by field_simp]
        simpa only [one_div] using
          (one_div_le_one_div_of_le (by positivity : 0 < primeLogSupport p / 2) hden)
      _ = (∑ j, ‖c j‖) * (2 / primeLogSupport p) := by rw [Finset.sum_mul]
      _ = 2 * (∑ j, ‖c j‖) / primeLogSupport p := by ring
  have hchar := semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
    (primeLogSupport p)
  have hexp : Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
    rw [primeLogSupport, Real.exp_neg, Real.exp_log hpReal]
  rw [hexp] at hchar
  have hsq : Complex.normSq
      (∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹) ≤
        (2 * (∑ j, ‖c j‖) / primeLogSupport p) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hpacket
  dsimp [gammaDampedPrimeLogCauchyPacketEnergy, invNatLogSq]
  rw [show Real.log (p : ℝ) = primeLogSupport p by rfl]
  have hchar0 : 0 ≤ semilocalArchimedeanCharacteristic (2 * primeLogSupport p) := by
    exact (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le
  calc
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        Complex.normSq (∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹) ≤
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (2 * (∑ j, ‖c j‖) / primeLogSupport p) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hchar0
    _ ≤ (Real.sqrt 2 * (p : ℝ)⁻¹) *
        (2 * (∑ j, ‖c j‖) / primeLogSupport p) ^ 2 := by
          gcongr
    _ = 4 * Real.sqrt 2 * (∑ j, ‖c j‖) ^ 2 *
        (1 / ((p : ℝ) * primeLogSupport p ^ 2)) := by
          field_simp
          ring

theorem summable_gammaDampedPrimeLogCauchyPacketEnergy {n : ℕ}
    (z c : Fin n → ℂ) :
    Summable (gammaDampedPrimeLogCauchyPacketEnergy z c) := by
  have hmajor := summable_prime_invNatLogSq.mul_left
    (4 * Real.sqrt 2 * (∑ j, ‖c j‖) ^ 2)
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [eventually_gammaDampedPrimeLogCauchyPacketEnergy_le z c] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact hp
  · dsimp [gammaDampedPrimeLogCauchyPacketEnergy]
    exact mul_nonneg
      (Real.rpow_nonneg (Real.cosh_pos _).le _)
      (Complex.normSq_nonneg _)

/-- **Exact critical-half-weight carrier transition.**  Gamma damping places every finite Cauchy
packet in the prime Hilbert domain.  For distinct upper-half-plane nodes, deleting that damping
leaves a summable critical-half-weight packet exactly when all coefficients vanish. -/
theorem gammaDampedPrimeLogCauchyPacket_critical_carrierTransition {n : ℕ}
    (z c : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im) :
    Summable (gammaDampedPrimeLogCauchyPacketEnergy z c) ∧
      (Summable (primeLogCauchyPacketTransportEnergy z c (1 / 2 : ℝ)) ↔ c = 0) := by
  exact ⟨summable_gammaDampedPrimeLogCauchyPacketEnergy z c,
    summable_primeLogCauchyPacketTransportEnergy_iff z c hz hzUpper (by norm_num)⟩

end

end RHTower
