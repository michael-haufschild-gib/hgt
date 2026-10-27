import GaloisForLFunctions.ArithmeticCompensationTheory.TheBalancedRegimeAndTheOmittedResidueClassLaw
import GaloisForLFunctions.BezoutValuationIncidence.ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# Multi-Modulus Kloosterman Packet Dispersion and Simultaneous Prime-Row Bias Cancellation

`ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram` proved that on each single prime modulus
`p`, the Kloosterman cosine coefficients `C_m(p)` of `reciprocityZeroMeanKernel p` are order-sharp
(`∑_{m=1}^{p-1} C_m(p)² ≍ p⁴`, `max |C_m(p)| ≍ p^{3/2}`), ruling out any single-modulus sub-Weil
saving, while two distinct primes `p₁ ≠ p₂` enjoy Chinese-remainder orthogonality over `p₁ p₂`. In
parallel, `TheBalancedRegimeAndTheOmittedResidueClassLaw` showed that centring `Λ` by `1` kills the
rank-one block mass at every Guth–Maynard short-window exponent `17/30 < α < 1`, while leaving an
explicit single-modulus omitted-residue-class bias cancelled by `omittedClassCorrector p Q`.

This module establishes the **multi-modulus dispersion and simultaneous compensation laws** uniting
both theories:

1. **Dual Unitary Parseval Identity on `ℤ/pℤ`
   (`sum_Ico_reciprocityLinearCoeff_sq_eq_kloosterman`):**
   Although `W_K(p, n)` is expanded in inverse-phase Kloosterman modes `C_m(p) cos(2π m n̄_p / p)` on
   `(ℤ/pℤ)ˣ` and in linear-phase additive modes `α_p(h) e(h n / p)` on `ℤ/pℤ`, unitary Parseval
   equates their `ℓ²` energies identically:
   `∑_{h=1}^{p-1} α_p(h)² = (1 / p) ∑_{n=1}^{p-1} W_K(p, n)² = ∑_{m=1}^{p-1} C_m(p)²`.

2. **Two-Sided Montgomery–Vaughan Multi-Modulus Kloosterman Packet Quasi-Isometry
   (`abs_sum_window_kloostermanPacket_sq_sub_le`, `sum_window_kloostermanPacket_sq_le_weil`,
   `sum_window_kloostermanPacket_sq_ge_fourthPower`):**
   Embedding the linear Fourier modes `(h, p)` (`p ∈ S`, `1 ≤ h < p`) into `fareySet Q₀` (`p ≤ Q₀`)
   separates all frequencies across distinct primes and residues by `1 / (Q₀(Q₀ - 1))`. Applying the
   two-sided Montgomery–Vaughan cosecant law yields, on **every** shifted window `(A, A + K]`,
   `|∑_{A < n ≤ A + K} (∑_{p ∈ S} a_p W_K(p, n))² - K ∑_{p ∈ S} a_p² ‖C(p)‖₂²|
     ≤ Q₀(Q₀ - 1) ∑_{p ∈ S} a_p² ‖C(p)‖₂²`.
   This simultaneously delivers a log-free `(K + Q₀² - 1)(π⁴ / 576) ∑ a_p² (p - 1) p³` upper
   dispersion bound (with zero `|S|` loss for `K ≫ Q₀²`) and an unconditional `(K - Q₀(Q₀ - 1))`
   `p⁴`-order non-cancellation lower bound for primes `p ≥ 67`.

3. **Multi-Modulus Prime Pronic Gram Bilinear Dispersion
   (`abs_sum_primeGram_rankThree_remainder_le`):**
   Coupling multi-modulus packet dispersion with the rank-three prime pronic Gram law bounds any
   bilinear form `∑_{p ∈ S} ∑_{q ∈ T} a_p b_q (𝒢^{ec}(p, q) - ℳ₃(N, p, q))` on prime sets
   `S` (`p ≤ Q₀`) and `T ⊆ (A, A + K]` (`p ≠ q`) with full square-root dispersion across both prime
   variables.

4. **Simultaneous Multi-Prime Omitted-Class CRT Cancellation and `17/30` Transfer
   (`sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean_of_ne`,
   `tendsto_mul_kernelStatistic_centredPrimeBlock_add_packetCorrector`,
   `eventually_packetCorrectedPrimeBlock_seventeenThirtieths`):**
   For distinct primes `q ≠ p`, `omittedClassWeight q` and `𝔅(p, ·) - m_p` are CRT-orthogonal over
   `range (q * p)`, forcing `Q · Λ_p(omittedClassCorrector q Q) → 0`. Consequently, the multi-prime
   packet corrector `packetOmittedCorrector S Q = ∑_{q ∈ S} omittedClassCorrector q Q` cancels the
   omitted-residue-class main term `Q · Λ_p → 0` **simultaneously at every `p ∈ S`** with `O(1/Q²)`
   block-mass perturbation, preserving the unconditional Guth–Maynard `17/30 < α < 1` short-window
   block-mass bound on `centredPrimeBlock Q + packetOmittedCorrector S Q`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

set_option autoImplicit false

/-! ## §1. Dual Unitary Parseval Identity Between Linear and Kloosterman Modes of `W_K(p, ·)` -/

/-- Exact unitary Parseval identity on `ℤ/pℤ` for the linear Fourier coefficients
`reciprocityLinearCoeff p h` (`1 ≤ h < p`) of `reciprocityZeroMeanKernel p`. -/
theorem mul_sum_Ico_reciprocityLinearCoeff_sq_eq_sum_kernel_sq {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * ∑ h ∈ Ico 1 p, reciprocityLinearCoeff p h ^ 2 =
      ∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n ^ 2 := by
  set F : ℕ → ℂ := fun n => (reciprocityZeroMeanKernel p n : ℂ)
  have horth : ∑ n ∈ range p, F n * conj (F n) =
      (((p : ℝ) * ∑ h ∈ Ico 1 p, reciprocityLinearCoeff p h ^ 2 : ℝ) : ℂ) := by
    have hexpand : ∀ n ∈ range p, F n * conj (F n) =
        ∑ h₁ ∈ Ico 1 p, ∑ h₂ ∈ Ico 1 p,
          (reciprocityLinearCoeff p h₁ : ℂ) * (reciprocityLinearCoeff p h₂ : ℂ) *
            (stdRoot p ^ h₁ * conj (stdRoot p ^ h₂)) ^ n := by
      intro n _
      dsimp [F]
      rw [reciprocityZeroMeanKernel_eq_sum_linear_exp hp n, map_sum, sum_mul]
      refine sum_congr rfl fun h₁ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun h₂ _ => ?_
      rw [map_mul, Complex.conj_ofReal, mul_pow, ← pow_mul, ← map_pow, ← pow_mul]
      ring
    rw [sum_congr rfl hexpand, sum_comm]
    have hh1 : ∀ h₁ ∈ Ico 1 p,
        ∑ n ∈ range p, ∑ h₂ ∈ Ico 1 p,
            (reciprocityLinearCoeff p h₁ : ℂ) * (reciprocityLinearCoeff p h₂ : ℂ) *
              (stdRoot p ^ h₁ * conj (stdRoot p ^ h₂)) ^ n =
          (p : ℂ) * (reciprocityLinearCoeff p h₁ : ℂ) ^ 2 := by
      intro h₁ hh₁
      rw [sum_comm]
      have hh2 : ∀ h₂ ∈ Ico 1 p,
          ∑ n ∈ range p,
              (reciprocityLinearCoeff p h₁ : ℂ) * (reciprocityLinearCoeff p h₂ : ℂ) *
                (stdRoot p ^ h₁ * conj (stdRoot p ^ h₂)) ^ n =
            if h₁ = h₂ then (p : ℂ) * (reciprocityLinearCoeff p h₁ : ℂ) ^ 2 else 0 := by
        intro h₂ hh₂
        rw [← mul_sum, sum_range_stdRoot_mul_conj_pow hp.pos (mem_Ico.mp hh₁).2 (mem_Ico.mp hh₂).2]
        split_ifs with heq
        · subst heq; ring
        · ring
      rw [sum_congr rfl hh2, sum_ite_eq (Ico 1 p) h₁, if_pos hh₁]
    rw [sum_congr rfl hh1, ← mul_sum]
    push_cast
    rfl
  have hphys : ∑ n ∈ range p, F n * conj (F n) =
      ((∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n ^ 2 : ℝ) : ℂ) := by
    dsimp [F]
    rw [← sum_range_add_sum_Ico _ hp.pos, sum_range_one, reciprocityZeroMeanKernel_zero,
      Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
  exact Complex.ofReal_injective (horth.symm.trans hphys)

/-- **Dual Unitary Parseval Identity (`α_p` vs `C_m(p)`):**
For every prime `p`, the linear-phase Fourier `ℓ²` energy of `W_K(p, ·)` on `ℤ/pℤ` equals its
inverse-phase Kloosterman `ℓ²` energy on `(ℤ/pℤ)ˣ`:
`∑_{h=1}^{p-1} α_p(h)² = ∑_{m=1}^{p-1} C_m(p)²`. -/
theorem sum_Ico_reciprocityLinearCoeff_sq_eq_kloosterman {p : ℕ} (hp : p.Prime) :
    ∑ h ∈ Ico 1 p, reciprocityLinearCoeff p h ^ 2 =
      ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  apply mul_left_cancel₀ hp0
  rw [mul_sum_Ico_reciprocityLinearCoeff_sq_eq_sum_kernel_sq hp,
    mul_sum_Ico_reciprocityKloostermanCoeff_sq_eq_sum_kernel_sq hp]
  refine sum_congr rfl fun n hn => ?_
  have hnd : ¬ p ∣ n := fun hd =>
    absurd (Nat.le_of_dvd (mem_Ico.mp hn).1 hd) (not_le_of_gt (mem_Ico.mp hn).2)
  rw [reciprocityZeroMeanKernel_of_not_dvd hnd]

/-! ## §2. Two-Sided Montgomery–Vaughan Multi-Modulus Kloosterman Packet Quasi-Isometry -/

/-- A multi-modulus weighted packet of zero-mean reciprocity kernels:
`F_{S, a}(n) = ∑_{p ∈ S} a_p W_K(p, n)`. -/
def kloostermanPacket (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, a p * reciprocityZeroMeanKernel p n

/-- The disjoint Farey index packet `{(h, p) : p ∈ S, 1 ≤ h < p}` associated to a finite modulus set
`S`. -/
def primeFareyPacket (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.biUnion fun p => (Ico 1 p).image fun h => (h, p)

/-- Every pair `(h, p)` in `primeFareyPacket S` for primes `p ≤ Q₀` is a reduced Farey fraction in
`fareySet Q₀`. -/
theorem primeFareyPacket_subset_fareySet {S : Finset ℕ} {Q₀ : ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀) :
    primeFareyPacket S ⊆ fareySet Q₀ := by
  intro r hr
  obtain ⟨p, hpS, hrp⟩ := mem_biUnion.mp hr
  obtain ⟨h, hh, rfl⟩ := mem_image.mp hrp
  obtain ⟨hp, hpQ⟩ := hS p hpS
  obtain ⟨hh1, hhp⟩ := mem_Ico.mp hh
  have hcop : Nat.Coprime h p :=
    (hp.coprime_iff_not_dvd.mpr fun hd =>
      absurd (Nat.le_of_dvd hh1 hd) (not_le_of_gt hhp)).symm
  exact mem_fareySet.mpr ⟨⟨hh1, le_trans hhp.le hpQ⟩, ⟨hp.pos, hpQ⟩, hhp.le, hcop⟩

/-- Conversion between `stdRoot p ^ (h * n)` and `circleFreq (n * (h / p))`. -/
theorem stdRoot_pow_eq_circleFreq (p h n : ℕ) :
    stdRoot p ^ (h * n) = circleFreq ((n : ℝ) * ((h : ℝ) / (p : ℝ))) := by
  rw [stdRoot_pow, circleFreq]
  congr 1
  push_cast
  ring

private theorem pairwiseDisjoint_primeFareyFibres (S : Finset ℕ) :
    (S : Set ℕ).PairwiseDisjoint (fun p => (Ico 1 p).image fun h => (h, p)) := by
  intro p _ p' _ hne
  simp only [Function.onFun]
  rw [disjoint_left]
  intro r hr hr'
  obtain ⟨h, _, rfl⟩ := mem_image.mp hr
  obtain ⟨h', _, heq⟩ := mem_image.mp hr'
  exact hne (congrArg Prod.snd heq).symm

/-- Exact additive Farey exponential representation of `kloostermanPacket S a n`. -/
theorem kloostermanPacket_eq_sum_primeFareyPacket {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : ℕ → ℝ) (n : ℕ) :
    (kloostermanPacket S a n : ℂ) =
      ∑ r ∈ primeFareyPacket S,
        ((a r.2 * reciprocityLinearCoeff r.2 r.1 : ℝ) : ℂ) *
          circleFreq ((n : ℝ) * ((r.1 : ℝ) / (r.2 : ℝ))) := by
  rw [primeFareyPacket, sum_biUnion (pairwiseDisjoint_primeFareyFibres S)]
  unfold kloostermanPacket
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_image fun h₁ _ h₂ _ heq => congrArg Prod.fst heq]
  rw [Complex.ofReal_mul, reciprocityZeroMeanKernel_eq_sum_linear_exp (hS p hp) n, mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [stdRoot_pow_eq_circleFreq, Complex.ofReal_mul]
  ring

/-- The Farey packet coefficient `ℓ²` norm equals `∑_{p ∈ S} a_p² ∑_{m=1}^{p-1} C_m(p)²`. -/
theorem sum_primeFareyPacket_coeff_sq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℝ) :
    ∑ r ∈ primeFareyPacket S, ‖((a r.2 * reciprocityLinearCoeff r.2 r.1 : ℝ) : ℂ)‖ ^ 2 =
      ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
  rw [primeFareyPacket, sum_biUnion (pairwiseDisjoint_primeFareyFibres S)]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_image fun h₁ _ h₂ _ heq => congrArg Prod.fst heq]
  rw [← sum_Ico_reciprocityLinearCoeff_sq_eq_kloosterman (hS p hp), mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- **Two-Sided Montgomery–Vaughan Multi-Modulus Kloosterman Packet Equidistribution Law:**
For any finite set `S` of primes `p ≤ Q₀` (`Q₀ ≥ 2`), any real weights `a : ℕ → ℝ`, and any
consecutive integer window `Icc (A + 1) (A + K)`,
`|∑_{A < n ≤ A + K} (∑_{p ∈ S} a_p W_K(p, n))² - K ∑_{p ∈ S} a_p² ∑_{m=1}^{p-1} C_m(p)²|
  ≤ Q₀(Q₀ - 1) ∑_{p ∈ S} a_p² ∑_{m=1}^{p-1} C_m(p)²`. -/
theorem abs_sum_window_kloostermanPacket_sq_sub_le {S : Finset ℕ} {Q₀ : ℕ} (hQ₀ : 2 ≤ Q₀)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀) (a : ℕ → ℝ) (A K : ℕ) :
    |∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 -
        (K : ℝ) * ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2| ≤
      (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) *
        ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
  classical
  have hQR : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
  have hδ : (0 : ℝ) < 1 / ((Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) := by
    have : (0 : ℝ) < (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) := by nlinarith
    positivity
  have hsub := primeFareyPacket_subset_fareySet hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  set α : ↥(primeFareyPacket S) → ℝ := fun r => ((r : ℕ × ℕ).1 : ℝ) / ((r : ℕ × ℕ).2 : ℝ)
  set b : ↥(primeFareyPacket S) → ℂ :=
    fun r => ((a (r : ℕ × ℕ).2 * reciprocityLinearCoeff (r : ℕ × ℕ).2 (r : ℕ × ℕ).1 : ℝ) : ℂ)
  have hsep : ∀ r s : ↥(primeFareyPacket S), r ≠ s →
      1 / ((Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) ≤ toIntDist (α r - α s) := by
    intro r s hrs
    exact fareySet_sep_sharp hQ₀ s (hsub s.2) r (hsub r.2) fun h => hrs (Subtype.ext h.symm)
  have hmv := abs_sum_window_norm_sq_sub_le α hδ hsep b A K
  have hsum_b : ∑ r : ↥(primeFareyPacket S), ‖b r‖ ^ 2 =
      ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
    rw [Finset.sum_coe_sort (primeFareyPacket S)
      (fun r : ℕ × ℕ => ‖((a r.2 * reciprocityLinearCoeff r.2 r.1 : ℝ) : ℂ)‖ ^ 2)]
    exact sum_primeFareyPacket_coeff_sq hSp a
  have hsum_win : ∑ n ∈ Icc (A + 1) (A + K),
        ‖∑ r : ↥(primeFareyPacket S), b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 =
      ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 := by
    refine sum_congr rfl fun n _ => ?_
    have dinner : ∑ r : ↥(primeFareyPacket S), b r * circleFreq ((n : ℝ) * α r) =
        (kloostermanPacket S a n : ℂ) := by
      rw [Finset.sum_coe_sort (primeFareyPacket S) (fun r : ℕ × ℕ =>
        ((a r.2 * reciprocityLinearCoeff r.2 r.1 : ℝ) : ℂ) *
          circleFreq ((n : ℝ) * ((r.1 : ℝ) / (r.2 : ℝ))))]
      exact (kloostermanPacket_eq_sum_primeFareyPacket hSp a n).symm
    rw [dinner, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsum_win, hsum_b, one_div, inv_inv] at hmv
  exact hmv

/-- **Sharp Log-Free Montgomery–Vaughan Upper Dispersion Bound for Kloosterman Packets:**
For any set `S` of primes `p ≤ Q₀` (`Q₀ ≥ 2`), weights `a : ℕ → ℝ`, and window `Icc (A + 1) (A + K)`,
`∑_{A < n ≤ A + K} (∑_{p ∈ S} a_p W_K(p, n))²
  ≤ ((K + Q₀² - 1) · π⁴ / 576) ∑_{p ∈ S} a_p² (p - 1) p³`. -/
theorem sum_window_kloostermanPacket_sq_le_weil {S : Finset ℕ} {Q₀ : ℕ} (hQ₀ : 2 ≤ Q₀)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀) (a : ℕ → ℝ) (A K : ℕ) :
    ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 ≤
      ((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
        ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3) := by
  have hQR : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
  have hup := (abs_le.mp (abs_sum_window_kloostermanPacket_sq_sub_le hQ₀ hS a A K)).2
  set E : ℝ := ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2
  have hE0 : 0 ≤ E := sum_nonneg fun p _ =>
    mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
  have hstep1 : ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 ≤
      ((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * E := by
    have hQsq : (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) ≤ (Q₀ : ℝ) ^ 2 - 1 := by nlinarith
    have hmul : (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) * E ≤ ((Q₀ : ℝ) ^ 2 - 1) * E :=
      mul_le_mul_of_nonneg_right hQsq hE0
    linarith
  have hweil : E ≤ (Real.pi ^ 4 / 576) * ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3) := by
    dsimp [E]
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hc := sum_Ico_reciprocityKloostermanCoeff_sq_le (hS p hp).1
    have hrew : Real.pi ^ 4 / 576 * (a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) =
        a p ^ 2 * (Real.pi ^ 4 / 576 * ((p : ℝ) - 1) * (p : ℝ) ^ 3) := by ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  have hKQ : 0 ≤ (K : ℝ) + (Q₀ : ℝ) ^ 2 - 1 := by nlinarith
  calc ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2
      ≤ ((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * E := hstep1
    _ ≤ ((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          ((Real.pi ^ 4 / 576) * ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hweil hKQ
    _ = ((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
          ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3) := by ring

/-- **Multi-Modulus Non-Cancellation / Quasi-Isometry Lower Bound (`p ≥ 67`, `K ≥ Q₀(Q₀ - 1)`):**
No nontrivial linear combination of `W_K(p, ·)` across primes `67 ≤ p ≤ Q₀` can destructively
cancel on any window longer than `Q₀(Q₀ - 1)`:
`((K - Q₀(Q₀ - 1)) / 5120000) ∑_{p ∈ S} a_p² p⁴ ≤ ∑_{A < n ≤ A + K} (∑_{p ∈ S} a_p W_K(p, n))²`. -/
theorem sum_window_kloostermanPacket_sq_ge_fourthPower {S : Finset ℕ} {Q₀ A K : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ 67 ≤ p ∧ p ≤ Q₀)
    (hK : Q₀ * (Q₀ - 1) ≤ K) (a : ℕ → ℝ) :
    (((K : ℝ) - (Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) / 5120000) * ∑ p ∈ S, a p ^ 2 * (p : ℝ) ^ 4 ≤
      ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 := by
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀ := fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩
  have hlo := (abs_le.mp (abs_sum_window_kloostermanPacket_sq_sub_le hQ₀ hS' a A K)).1
  set E : ℝ := ∑ p ∈ S, a p ^ 2 * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2
  have hKR : (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) ≤ K := by
    have hcast : ((Q₀ * (Q₀ - 1) : ℕ) : ℝ) = (Q₀ : ℝ) * ((Q₀ : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [← hcast]
    exact_mod_cast hK
  have hE_ge : (1 / 5120000 : ℝ) * ∑ p ∈ S, a p ^ 2 * (p : ℝ) ^ 4 ≤ E := by
    dsimp [E]
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hc := sum_Ico_reciprocityKloostermanCoeff_sq_ge (hS p hp).1 (hS p hp).2.1
    have hrew : (1 / 5120000 : ℝ) * (a p ^ 2 * (p : ℝ) ^ 4) =
        a p ^ 2 * ((p : ℝ) ^ 4 / 5120000) := by ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  have hstep : ((K : ℝ) - (Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) * E ≤
      ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 := by linarith
  calc (((K : ℝ) - (Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) / 5120000) * ∑ p ∈ S, a p ^ 2 * (p : ℝ) ^ 4
      = ((K : ℝ) - (Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) *
          ((1 / 5120000 : ℝ) * ∑ p ∈ S, a p ^ 2 * (p : ℝ) ^ 4) := by ring
    _ ≤ ((K : ℝ) - (Q₀ : ℝ) * ((Q₀ : ℝ) - 1)) * E :=
        mul_le_mul_of_nonneg_left hE_ge (sub_nonneg.mpr hKR)
    _ ≤ ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 := hstep

/-- **Exact CRT Diagonal + Terminal-Block Expansion of `∑_{n < M} kloostermanPacket S a n ^ 2`:**
Over `[0, M)`, every off-diagonal pair `p₁ ≠ p₂` in `S` collapses modulo `p₁ p₂` to its terminal
residue block `range (M % (p₁ * p₂))` of length strictly less than `p₁ p₂`. -/
theorem sum_range_kloostermanPacket_sq_eq_diagonal_add_terminal {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ range M, kloostermanPacket S a n ^ 2 =
      ∑ p ∈ S, a p ^ 2 * (∑ n ∈ range M, reciprocityZeroMeanKernel p n ^ 2) +
        ∑ p₁ ∈ S, ∑ p₂ ∈ S.erase p₁, a p₁ * a p₂ *
          ∑ r ∈ range (M % (p₁ * p₂)),
            reciprocityZeroMeanKernel p₁ r * reciprocityZeroMeanKernel p₂ r := by
  have hexp : ∀ n ∈ range M, kloostermanPacket S a n ^ 2 =
      ∑ p₁ ∈ S, ∑ p₂ ∈ S,
        a p₁ * a p₂ * (reciprocityZeroMeanKernel p₁ n * reciprocityZeroMeanKernel p₂ n) := by
    intro n _
    unfold kloostermanPacket
    rw [sq, sum_mul]
    refine sum_congr rfl fun p₁ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun p₂ _ => ?_
    ring
  rw [sum_congr rfl hexp, sum_comm]
  have houter : ∀ p₁ ∈ S,
      ∑ n ∈ range M, ∑ p₂ ∈ S,
          a p₁ * a p₂ * (reciprocityZeroMeanKernel p₁ n * reciprocityZeroMeanKernel p₂ n) =
        a p₁ ^ 2 * (∑ n ∈ range M, reciprocityZeroMeanKernel p₁ n ^ 2) +
          ∑ p₂ ∈ S.erase p₁, a p₁ * a p₂ *
            ∑ r ∈ range (M % (p₁ * p₂)),
              reciprocityZeroMeanKernel p₁ r * reciprocityZeroMeanKernel p₂ r := by
    intro p₁ hp₁
    rw [sum_comm, ← add_sum_erase _ _ hp₁]
    congr 1
    · rw [← mul_sum]
      refine congrArg₂ _ (by ring) (sum_congr rfl fun n _ => by ring)
    · refine sum_congr rfl fun p₂ hp₂ => ?_
      have hne : p₁ ≠ p₂ := (ne_of_mem_erase hp₂).symm
      rw [← mul_sum,
        sum_range_mul_reciprocityZeroMeanKernel_eq_terminal (hS p₁ hp₁)
          (hS p₂ (mem_of_mem_erase hp₂)) hne M]
  rw [sum_congr rfl houter, sum_add_distrib]

/-! ## §3. Multi-Modulus Prime Pronic Gram Bilinear Dispersion Law -/

/-- The explicit rank-three separable main term of `pmRamanujanEnergyCenteredGram p q` isolated in
`abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le`. -/
def rankThreePrimeGramMain (N p q : ℕ) : ℝ :=
  (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
    (p : ℝ) * rowBeta N (unitRow p) -
    (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) * (1 / (q : ℝ))

/-- **Multi-Modulus Prime Pronic Gram Bilinear Dispersion Theorem:**
For any prime packet `S` (`p ≤ Q₀`, `Q₀ ≥ 2`), any prime window `T ⊆ Icc (A + 1) (A + K)` with
`p ≠ q` for `p ∈ S, q ∈ T` (e.g., `Q₀ ≤ A`), and arbitrary real weights `a, b : ℕ → ℝ`, the
rank-three remainder of `pmRamanujanEnergyCenteredGram` satisfies the log-free dispersed bound
`|∑_{p ∈ S} ∑_{q ∈ T} a_p b_q (𝒢^{ec}(p, q) - rankThreePrimeGramMain N p q)|
  ≤ √((K + Q₀² - 1)(π⁴ / 576) ∑_{p ∈ S} a_p² (p - 1) p³) · √(∑_{q ∈ T} (b_q / q)²)
    + (3 / 4) (∑_{p ∈ S} |a_p| p³) (∑_{q ∈ T} |b_q| / q²)`. -/
theorem abs_sum_primeGram_rankThree_remainder_le {N Q₀ A K : ℕ} {S T : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀)
    (hT : ∀ q ∈ T, q.Prime ∧ q ≤ N ∧ q ∈ Icc (A + 1) (A + K))
    (hpq : ∀ p ∈ S, ∀ q ∈ T, p ≠ q) (a b : ℕ → ℝ) :
    |∑ p ∈ S, ∑ q ∈ T, a p * b q *
        (pmRamanujanEnergyCenteredGram p q - rankThreePrimeGramMain N p q)| ≤
      Real.sqrt (((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
          ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) *
        Real.sqrt (∑ q ∈ T, (b q / (q : ℝ)) ^ 2) +
      (3 / 4) * (∑ p ∈ S, |a p| * (p : ℝ) ^ 3) * (∑ q ∈ T, |b q| / (q : ℝ) ^ 2) := by
  set E : ℕ → ℕ → ℝ := fun p q =>
    pmRamanujanEnergyCenteredGram p q - rankThreePrimeGramMain N p q -
      reciprocityZeroMeanKernel p q / (q : ℝ)
  have hsplit : ∑ p ∈ S, ∑ q ∈ T, a p * b q *
        (pmRamanujanEnergyCenteredGram p q - rankThreePrimeGramMain N p q) =
      (∑ q ∈ T, (b q / (q : ℝ)) * kloostermanPacket S a q) +
        ∑ p ∈ S, ∑ q ∈ T, a p * b q * E p q := by
    have h1 : ∑ p ∈ S, ∑ q ∈ T, a p * b q *
          (pmRamanujanEnergyCenteredGram p q - rankThreePrimeGramMain N p q) =
        ∑ p ∈ S, ∑ q ∈ T, (a p * b q * (reciprocityZeroMeanKernel p q / (q : ℝ)) +
          a p * b q * E p q) := by
      refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
      dsimp [E]
      ring
    rw [h1]
    simp_rw [sum_add_distrib]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    unfold kloostermanPacket
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    ring
  have hkloos : |∑ q ∈ T, (b q / (q : ℝ)) * kloostermanPacket S a q| ≤
      Real.sqrt (((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
          ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) *
        Real.sqrt (∑ q ∈ T, (b q / (q : ℝ)) ^ 2) := by
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt T (fun q => |b q / (q : ℝ)|)
      (fun q => |kloostermanPacket S a q|)
    simp only [sq_abs] at hCS
    have habs : |∑ q ∈ T, (b q / (q : ℝ)) * kloostermanPacket S a q| ≤
        ∑ q ∈ T, |b q / (q : ℝ)| * |kloostermanPacket S a q| := by
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact sum_congr rfl fun q _ => abs_mul _ _
    have hsub_T : T ⊆ Icc (A + 1) (A + K) := fun q hq => (hT q hq).2.2
    have hT_le_win : ∑ q ∈ T, kloostermanPacket S a q ^ 2 ≤
        ∑ n ∈ Icc (A + 1) (A + K), kloostermanPacket S a n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub_T fun _ _ _ => sq_nonneg _
    have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀ := fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩
    have hwin := hT_le_win.trans (sum_window_kloostermanPacket_sq_le_weil hQ₀ hS' a A K)
    calc |∑ q ∈ T, (b q / (q : ℝ)) * kloostermanPacket S a q|
        ≤ Real.sqrt (∑ q ∈ T, (b q / (q : ℝ)) ^ 2) *
            Real.sqrt (∑ q ∈ T, kloostermanPacket S a q ^ 2) := habs.trans hCS
      _ ≤ Real.sqrt (∑ q ∈ T, (b q / (q : ℝ)) ^ 2) *
            Real.sqrt (((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
              ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hwin) (Real.sqrt_nonneg _)
      _ = Real.sqrt (((K : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * (Real.pi ^ 4 / 576) *
            ∑ p ∈ S, a p ^ 2 * (((p : ℝ) - 1) * (p : ℝ) ^ 3)) *
          Real.sqrt (∑ q ∈ T, (b q / (q : ℝ)) ^ 2) := mul_comm _ _
  have herr : |∑ p ∈ S, ∑ q ∈ T, a p * b q * E p q| ≤
      (3 / 4) * (∑ p ∈ S, |a p| * (p : ℝ) ^ 3) * (∑ q ∈ T, |b q| / (q : ℝ) ^ 2) := by
    calc |∑ p ∈ S, ∑ q ∈ T, a p * b q * E p q|
        ≤ ∑ p ∈ S, |∑ q ∈ T, a p * b q * E p q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ∑ q ∈ T, |a p * b q * E p q| :=
          sum_le_sum fun p _ => abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ∑ q ∈ T,
            (|a p| * (p : ℝ) ^ 3) * ((3 / 4) * (|b q| / (q : ℝ) ^ 2)) := by
          refine sum_le_sum fun p hp => sum_le_sum fun q hq => ?_
          have hE_le : |E p q| ≤ 3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
            dsimp [E, rankThreePrimeGramMain]
            exact abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le
              (hS p hp).1 (hT q hq).1 (hpq p hp q hq) (hS p hp).2.1 (hT q hq).2.1
          rw [abs_mul, abs_mul]
          calc |a p| * |b q| * |E p q|
              ≤ |a p| * |b q| * (3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left hE_le (by positivity)
            _ = (|a p| * (p : ℝ) ^ 3) * ((3 / 4) * (|b q| / (q : ℝ) ^ 2)) := by ring
      _ = (3 / 4) * (∑ p ∈ S, |a p| * (p : ℝ) ^ 3) * (∑ q ∈ T, |b q| / (q : ℝ) ^ 2) := by
          simp_rw [← mul_sum]
          rw [← sum_mul]
          ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hkloos herr)

/-! ## §4. Simultaneous Multi-Prime Omitted-Class CRT Cancellation and `17/30` Transfer -/

/-- **Cross-Modulus CRT Orthogonality of `omittedClassWeight`:**
For distinct primes `q ≠ p`, `omittedClassWeight q` and `bernoulliKernel p · - primeKernelMean p`
have coprime periods `q, p` and zero period means, so their product sums to `0` over `range (q * p)`. -/
theorem sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean_of_ne
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    ∑ r ∈ range (q * p),
      omittedClassWeight q r * (bernoulliKernel p r - primeKernelMean p) = 0 := by
  have hcop : q.Coprime p := (Nat.coprime_primes hq hp).mpr hqp
  have hper_q : Function.Periodic (omittedClassWeight q) q := omittedClassWeight_add_period q
  have hper_p : Function.Periodic (fun n => bernoulliKernel p n - primeKernelMean p) p :=
    fun n => by dsimp only; rw [bernoulliKernel_add_period]
  rw [RHTower.DeletionCoprimeWords.coprime_period_sum_mul hq.pos hp.pos hcop hper_q hper_p,
    sum_range_omittedClassWeight hq, zero_mul]

/-- **Quantitative Cross-Modulus Decay of `omittedClassCorrector q Q` at `p ≠ q`:**
For distinct primes `q ≠ p` and `Q ≥ 1`,
`|kernelStatistic (2 * Q) (omittedClassCorrector q Q) p| ≤ ((q * p³) / 2 + p³) / Q²`. -/
theorem abs_kernelStatistic_omittedClassCorrector_of_ne_le
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) {Q : ℕ} (hQ : 1 ≤ Q) :
    |kernelStatistic (2 * Q) (omittedClassCorrector q Q) p| ≤
      ((q : ℝ) * (p : ℝ) ^ 3 / 2 + (p : ℝ) ^ 3) / (Q : ℝ) ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set g : ℕ → ℝ := fun n =>
    omittedClassWeight q n * (bernoulliKernel p n - primeKernelMean p)
  have hgper : ∀ n, g (n + q * p) = g n := by
    intro n
    dsimp [g]
    have hq_step : omittedClassWeight q (n + q * p) = omittedClassWeight q n := by
      have hper : Function.Periodic (omittedClassWeight q) q := omittedClassWeight_add_period q
      simpa [mul_comm q p, add_assoc] using hper.nat_mul p n
    have hp_step : bernoulliKernel p (n + q * p) = bernoulliKernel p n := by
      have hper : Function.Periodic (bernoulliKernel p) p := bernoulliKernel_add_period p
      simpa [add_assoc] using hper.nat_mul q n
    rw [hq_step, hp_step]
  have hg0 : ∑ r ∈ range (q * p), g r = 0 :=
    sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean_of_ne hq hp hqp
  have hgb : ∀ n, |g n| ≤ (p : ℝ) ^ 2 / 4 := by
    intro n
    dsimp [g]
    rw [abs_mul]
    calc |omittedClassWeight q n| * |bernoulliKernel p n - primeKernelMean p|
        ≤ 1 * ((p : ℝ) ^ 2 / 4) :=
          mul_le_mul (abs_omittedClassWeight_le hq n) (abs_bernoulliKernel_sub_mean_le hp n)
            (abs_nonneg _) zero_le_one
      _ = (p : ℝ) ^ 2 / 4 := one_mul _
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  have hsplit : kernelStatistic (2 * Q) (omittedClassCorrector q Q) p =
      ∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2 +
        ∑ n ∈ Ioc Q (2 * Q), omittedClassWeight q n / (n : ℝ) ^ 3 * cubicKernel p n := by
    rw [kernelStatistic, ← sum_subset hsub fun n _ hn' => by
      have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
      simp [omittedClassCorrector, this], ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [omittedClassCorrector, if_pos (mem_Ioc.mp hn)]
    dsimp [g]
    ring
  have hquad : |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2| ≤
      ((q : ℝ) * (p : ℝ) ^ 3 / 2) / (Q : ℝ) ^ 2 := by
    have hper := abs_sum_Ioc_div_sq_le_of_periodic (Nat.mul_pos hq.pos hp.pos) hgper hg0
      (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2 / 4) hgb Q
    calc |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2|
        ≤ 2 * ((q * p : ℕ) : ℝ) * ((p : ℝ) ^ 2 / 4) / ((Q : ℝ) + 1) ^ 2 := hper
      _ = ((q : ℝ) * (p : ℝ) ^ 3 / 2) / ((Q : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ ((q : ℝ) * (p : ℝ) ^ 3 / 2) / (Q : ℝ) ^ 2 := by gcongr; linarith
  have hcub : |∑ n ∈ Ioc Q (2 * Q), omittedClassWeight q n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
      (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
    have hterm : ∀ n ∈ Ioc Q (2 * Q),
        |omittedClassWeight q n / (n : ℝ) ^ 3 * cubicKernel p n| ≤ (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn'.1.le
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
      calc |omittedClassWeight q n| / (n : ℝ) ^ 3 * |cubicKernel p n|
          ≤ 1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
            mul_le_mul (div_le_div₀ zero_le_one (abs_omittedClassWeight_le hq n)
              (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3))
              (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
        _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 := by ring
    calc |∑ n ∈ Ioc Q (2 * Q), omittedClassWeight q n / (n : ℝ) ^ 3 * cubicKernel p n|
        ≤ ∑ _n ∈ Ioc Q (2 * Q), (p : ℝ) ^ 3 / (Q : ℝ) ^ 3 :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]
          field_simp
  rw [hsplit]
  calc |∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2 +
          ∑ n ∈ Ioc Q (2 * Q), omittedClassWeight q n / (n : ℝ) ^ 3 * cubicKernel p n|
      ≤ ((q : ℝ) * (p : ℝ) ^ 3 / 2) / (Q : ℝ) ^ 2 + (p : ℝ) ^ 3 / (Q : ℝ) ^ 2 :=
        (abs_add_le _ _).trans (add_le_add hquad hcub)
    _ = ((q : ℝ) * (p : ℝ) ^ 3 / 2 + (p : ℝ) ^ 3) / (Q : ℝ) ^ 2 := by ring

/-- Cross-modulus asymptotics: for distinct primes `q ≠ p`, `Q · Λ_p(omittedClassCorrector q Q) → 0`. -/
theorem tendsto_mul_kernelStatistic_omittedClassCorrector_of_ne
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (omittedClassCorrector q Q) p)
      atTop (𝓝 0) := by
  set C : ℝ := (q : ℝ) * (p : ℝ) ^ 3 / 2 + (p : ℝ) ^ 3
  have hlim : Tendsto (fun Q : ℕ => C * (1 / (Q : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rwa [mul_zero] at h
  refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hQ0]
  calc (Q : ℝ) * |kernelStatistic (2 * Q) (omittedClassCorrector q Q) p|
      ≤ (Q : ℝ) * (C / (Q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (abs_kernelStatistic_omittedClassCorrector_of_ne_le hq hp hqp hQ) hQ0.le
    _ = C * (1 / (Q : ℝ)) := by field_simp

/-- The multi-prime omitted-residue-class packet corrector `∑_{q ∈ S} omittedClassCorrector q Q`. -/
def packetOmittedCorrector (S : Finset ℕ) (Q n : ℕ) : ℝ :=
  ∑ q ∈ S, omittedClassCorrector q Q n

/-- Linearity of `kernelStatistic` across `packetOmittedCorrector S Q`. -/
theorem kernelStatistic_packetOmittedCorrector (S : Finset ℕ) (N Q p : ℕ) :
    kernelStatistic N (packetOmittedCorrector S Q) p =
      ∑ q ∈ S, kernelStatistic N (omittedClassCorrector q Q) p := by
  simp only [kernelStatistic, packetOmittedCorrector]
  have hterm : ∀ n ∈ Icc 1 N,
      (∑ q ∈ S, omittedClassCorrector q Q n) / (n : ℝ) ^ 2 *
          (bernoulliKernel p n - primeKernelMean p) +
        (∑ q ∈ S, omittedClassCorrector q Q n) / (n : ℝ) ^ 3 * cubicKernel p n =
      ∑ q ∈ S, (omittedClassCorrector q Q n / (n : ℝ) ^ 2 *
          (bernoulliKernel p n - primeKernelMean p) +
        omittedClassCorrector q Q n / (n : ℝ) ^ 3 * cubicKernel p n) := by
    intro n _
    rw [sum_div, sum_mul, sum_div, sum_mul, ← sum_add_distrib]
  rw [sum_congr rfl hterm, sum_comm]

/-- **Simultaneous Multi-Prime Omitted-Residue-Class Bias Cancellation:**
For any finite prime set `S : Finset ℕ` (`∀ q ∈ S, q.Prime`), adding `packetOmittedCorrector S Q`
to `centredPrimeBlock Q` cancels the single-modulus omitted-class main term `Q · Λ_p → 0`
**simultaneously at every `p ∈ S`**, without cross-prime interference. -/
theorem tendsto_mul_kernelStatistic_centredPrimeBlock_add_packetCorrector
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hpS : p ∈ S) :
    Tendsto (fun Q : ℕ => (Q : ℝ) *
      kernelStatistic (2 * Q)
        (fun n => centredPrimeBlock Q n + packetOmittedCorrector S Q n) p)
      atTop (𝓝 0) := by
  have hp : p.Prime := hS p hpS
  have hdiag := tendsto_mul_kernelStatistic_centredPrimeBlock_add_corrector hp
  have hoff : Tendsto (fun Q : ℕ =>
      ∑ q ∈ S.erase p, (Q : ℝ) * kernelStatistic (2 * Q) (omittedClassCorrector q Q) p)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (S.erase p) fun q hq =>
      tendsto_mul_kernelStatistic_omittedClassCorrector_of_ne
        (hS q (mem_of_mem_erase hq)) hp (ne_of_mem_erase hq)
  have htot := hdiag.add hoff
  rw [add_zero] at htot
  refine htot.congr fun Q => ?_
  rw [ArithmeticCompensationTheory.kernelStatistic_add,
    ArithmeticCompensationTheory.kernelStatistic_add,
    kernelStatistic_packetOmittedCorrector, ← add_sum_erase _ _ hpS, ← mul_sum]
  ring

/-- The multi-prime packet corrector has inverse-square dyadic block mass at most
`(2 ∑_{q ∈ S} q) / (Q + 1)²`. -/
theorem abs_sum_packetOmittedCorrector_div_sq_le {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (Q : ℕ) :
    |∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2| ≤
      (2 * ∑ q ∈ S, (q : ℝ)) / ((Q : ℝ) + 1) ^ 2 := by
  have hswap : ∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2 =
      ∑ q ∈ S, ∑ n ∈ Ioc Q (2 * Q), omittedClassCorrector q Q n / (n : ℝ) ^ 2 := by
    unfold packetOmittedCorrector
    simp_rw [sum_div]
    exact sum_comm
  rw [hswap]
  calc |∑ q ∈ S, ∑ n ∈ Ioc Q (2 * Q), omittedClassCorrector q Q n / (n : ℝ) ^ 2|
      ≤ ∑ q ∈ S, |∑ n ∈ Ioc Q (2 * Q), omittedClassCorrector q Q n / (n : ℝ) ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S, 2 * (q : ℝ) / ((Q : ℝ) + 1) ^ 2 :=
        sum_le_sum fun q hq => abs_sum_omittedClassCorrector_div_sq_le (hS q hq) Q
    _ = (2 * ∑ q ∈ S, (q : ℝ)) / ((Q : ℝ) + 1) ^ 2 := by
        rw [← sum_div, ← mul_sum]

/-- **Simultaneous Multi-Prime Bias Cancellation at the Guth–Maynard `17/30` Exponent:**
For any finite prime set `S`, any `17/30 < α < 1`, and any `ε > 0`, the packet-corrected centred
prime block `c'_S(Q) := centredPrimeBlock Q + packetOmittedCorrector S Q` simultaneously satisfies:
1. `Q · Λ_p(c'_S(Q)) → 0` for **every** `p ∈ S` (`|Q · Λ_p(c'_S(Q))| ≤ ε` eventually in `Q`); and
2. `|∑_{Q < n ≤ 2Q} c'_S(Q, n) / n²| ≤ 2 ε / Q` eventually in `Q` from the Guth–Maynard `17/30`
   short-window transfer. -/
theorem eventually_packetCorrectedPrimeBlock_seventeenThirtieths
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop,
      (∀ p ∈ S, |(Q : ℝ) * kernelStatistic (2 * Q)
        (fun n => centredPrimeBlock Q n + packetOmittedCorrector S Q n) p| ≤ ε) ∧
      |∑ n ∈ Ioc Q (2 * Q),
        (centredPrimeBlock Q n + packetOmittedCorrector S Q n) / (n : ℝ) ^ 2| ≤
        2 * ε / (Q : ℝ) := by
  have hbias_all : ∀ᶠ Q : ℕ in atTop, ∀ p ∈ S,
      |(Q : ℝ) * kernelStatistic (2 * Q)
        (fun n => centredPrimeBlock Q n + packetOmittedCorrector S Q n) p| ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro p hpS
    have ht := (tendsto_mul_kernelStatistic_centredPrimeBlock_add_packetCorrector hS hpS).abs
    rw [abs_zero] at ht
    exact ht.eventually (eventually_le_nhds hε)
  have hgm := eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1
    (by positivity : 0 < ε / 2)
  set M_S : ℝ := 2 * ∑ q ∈ S, (q : ℝ)
  have hcorr_ev : ∀ᶠ Q : ℕ in atTop, M_S / (Q : ℝ) ≤ (2 - Real.sqrt 2 / 2) * ε := by
    have h2 : 0 < (2 - Real.sqrt 2 / 2) * ε := by
      have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      nlinarith
    have hlim : Tendsto (fun Q : ℕ => M_S * (1 / (Q : ℝ))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M_S
      rwa [mul_zero] at h
    exact (hlim.eventually (eventually_le_nhds h2)).mono fun Q hQ => by
      simpa [div_eq_mul_inv] using hQ
  filter_upwards [hbias_all, hgm, hcorr_ev, eventually_ge_atTop 1] with Q hQb hQg hQc hQ1
  refine ⟨hQb, ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hsplit : ∑ n ∈ Ioc Q (2 * Q),
        (centredPrimeBlock Q n + packetOmittedCorrector S Q n) / (n : ℝ) ^ 2 =
      (∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2) +
        ∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [centredPrimeBlock, if_pos (mem_Ioc.mp hn), add_div]
  have hp_mass : |∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2| ≤
      (2 - Real.sqrt 2 / 2) * ε / (Q : ℝ) := by
    have h1 := abs_sum_packetOmittedCorrector_div_sq_le hS Q
    have hM0 : 0 ≤ M_S := by dsimp [M_S]; positivity
    calc |∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2|
        ≤ M_S / ((Q : ℝ) + 1) ^ 2 := h1
      _ ≤ M_S / (Q : ℝ) ^ 2 := by gcongr; linarith
      _ = (M_S / (Q : ℝ)) / (Q : ℝ) := by rw [div_div, sq]
      _ ≤ ((2 - Real.sqrt 2 / 2) * ε) / (Q : ℝ) :=
          div_le_div_of_nonneg_right hQc hQ0.le
  rw [hsplit]
  calc |(∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2) +
          ∑ n ∈ Ioc Q (2 * Q), packetOmittedCorrector S Q n / (n : ℝ) ^ 2|
      ≤ Real.sqrt 2 * (ε / 2) / (Q : ℝ) + (2 - Real.sqrt 2 / 2) * ε / (Q : ℝ) :=
        (abs_add_le _ _).trans (add_le_add hQg.2.2.2 hp_mass)
    _ = 2 * ε / (Q : ℝ) := by ring

end GaloisForLFunctions.ArithmeticCompensationTheory
