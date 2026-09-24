import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval
import GaloisForLFunctions.RHTower.MobiusMertensPrimeRemovalTentLaw
import Mathlib.Tactic

/-!
# Cyclic high-frequency bound for the dyadic Möbius window

A cyclic prefix has Fourier multiplier `(1 - χ(-k))⁻¹`.  On an odd cycle,
doubling is a permutation, so every high-frequency primitive has a dyadic
window energy controlled by Parseval.  This theorem is purely finite and
applies to any coefficient sequence.  The literal odd-Möbius source and the
complementary low-frequency energy are treated separately.
-/

open Finset Complex
open scoped BigOperators

namespace RHTower

private theorem norm_sub_sq_le (x y : ℂ) :
    ‖x - y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  have h := norm_sub_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Dyadic dilation on an odd cyclic group has operator norm at most two. -/
theorem cyclic_dilation_window_energy_le
    (N : ℕ) [NeZero N] (hodd : Odd N) (P : ZMod N → ℂ) :
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 * ∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ) := by
  have hc : Nat.Coprime 2 N := by simpa using hodd
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime 2 hc
  have heq : (∑ n : ZMod N, ‖P (2 * n)‖ ^ (2 : ℕ)) =
      ∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ) := by
    simpa [u, ZMod.coe_unitOfCoprime] using
      (Fintype.sum_equiv u.mulLeft (fun n : ZMod N => ‖P (2 * n)‖ ^ (2 : ℕ))
        (fun n : ZMod N => ‖P n‖ ^ (2 : ℕ)) (by intro n; simp [u, ZMod.coe_unitOfCoprime]))
  calc
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      ∑ n : ZMod N, (2 * ‖P (2 * n)‖ ^ (2 : ℕ) + 2 * ‖P n‖ ^ (2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact norm_sub_sq_le _ _
    _ = 4 * ∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, heq]
      ring

/-- A spectral gap gives a sharp cyclic antiderivative budget for the dyadic window. -/
theorem cyclic_high_mode_dilation_energy_le
    (N : ℕ) [NeZero N] (hodd : Odd N) (τ : ℝ) (hτ : 0 < τ)
    (Ψ : ZMod N → ℂ)
    (hgap : ∀ k, Ψ k ≠ 0 → τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖) :
    let P : ZMod N → ℂ := ZMod.dft.symm (fun k => Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k)))
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 / ((N : ℝ) * τ ^ (2 : ℕ)) *
        (∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ)) := by
  dsimp only
  let b : ZMod N → ℂ := fun k => Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k))
  let P : ZMod N → ℂ := ZMod.dft.symm b
  have hP := cyclic_dilation_window_energy_le N hodd P
  have hparse := GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval N P
  have hDFT : ZMod.dft P = b := by
    exact LinearEquiv.apply_symm_apply _ _
  rw [hDFT] at hparse
  simp only [Complex.normSq_eq_norm_sq] at hparse
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hτ2 : (0 : ℝ) < τ ^ (2 : ℕ) := pow_pos hτ _
  have hterm : ∀ k : ZMod N, ‖b k‖ ^ (2 : ℕ) ≤ ‖Ψ k‖ ^ (2 : ℕ) / τ ^ (2 : ℕ) := by
    intro k
    by_cases hk : Ψ k = 0
    · simp [b, hk]
    · have hden := hgap k hk
      have hden0 : 0 < ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := hτ.trans_le hden
      have hden2 : τ ^ (2 : ℕ) ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ ^ (2 : ℕ) := by
        nlinarith
      change ‖Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k))‖ ^ (2 : ℕ) ≤ _
      rw [norm_div, div_pow]
      apply (div_le_div_iff₀ (pow_pos hden0 _) hτ2).2
      exact mul_le_mul_of_nonneg_left hden2 (sq_nonneg _)
  have hsum : (∑ k : ZMod N, ‖b k‖ ^ (2 : ℕ)) ≤
      (∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ)) / τ ^ (2 : ℕ) := by
    calc
      _ ≤ ∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ) / τ ^ (2 : ℕ) :=
        Finset.sum_le_sum (by intro k _; exact hterm k)
      _ = _ := by rw [Finset.sum_div]
  have hbound : (∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ)) ≤
      (∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ)) / ((N : ℝ) * τ ^ (2 : ℕ)) := by
    have hNτ : (0 : ℝ) < (N : ℝ) * τ ^ (2 : ℕ) := mul_pos hN hτ2
    apply (le_div_iff₀ hNτ).2
    have hsum' : (∑ k : ZMod N, ‖b k‖ ^ (2 : ℕ)) * τ ^ (2 : ℕ) ≤
        ∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ) :=
      (le_div_iff₀ hτ2).mp hsum
    calc
      (∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ)) * ((N : ℝ) * τ ^ (2 : ℕ)) =
          ((N : ℝ) * ∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ)) * τ ^ (2 : ℕ) := by ring
      _ = (∑ k : ZMod N, ‖b k‖ ^ (2 : ℕ)) * τ ^ (2 : ℕ) := by rw [← hparse]
      _ ≤ _ := hsum'
  calc
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 * ∑ n : ZMod N, ‖P n‖ ^ (2 : ℕ) := hP
    _ ≤ 4 * ((∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ)) /
          ((N : ℝ) * τ ^ (2 : ℕ))) := by gcongr
    _ = _ := by ring

/-- The inverse-DFT primitive has the prescribed cyclic discrete derivative. -/
theorem cyclic_spectral_primitive_diff
    (N : ℕ) [NeZero N] (τ : ℝ) (hτ : 0 < τ)
    (Ψ : ZMod N → ℂ)
    (hgap : ∀ k, Ψ k ≠ 0 → τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖)
    (n : ZMod N) :
    let P : ZMod N → ℂ := ZMod.dft.symm (fun k => Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k)))
    P n - P (n - 1) = ZMod.dft.symm Ψ n := by
  dsimp only
  let b : ZMod N → ℂ := fun k => Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k))
  have hchar (k : ZMod N) :
      ZMod.stdAddChar (k * (n - 1)) =
        ZMod.stdAddChar (k * n) * ZMod.stdAddChar (-k) := by
    rw [show k * (n - 1) = k * n + (-k) by ring, AddChar.map_add_eq_mul]
  have hmul (k : ZMod N) :
      ((1 : ℂ) - ZMod.stdAddChar (-k)) * b k = Ψ k := by
    by_cases hk : Ψ k = 0
    · simp [b, hk]
    · have hnorm := hgap k hk
      have hd0 : 0 < ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := hτ.trans_le hnorm
      have hd : ((1 : ℂ) - ZMod.stdAddChar (-k)) ≠ 0 := (norm_pos_iff.mp hd0)
      change ((1 : ℂ) - ZMod.stdAddChar (-k)) *
        (Ψ k / ((1 : ℂ) - ZMod.stdAddChar (-k))) = Ψ k
      field_simp
  simp only [ZMod.invDFT_apply, smul_eq_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hchar]
  change ZMod.stdAddChar (k * n) * b k -
    (ZMod.stdAddChar (k * n) * ZMod.stdAddChar (-k)) * b k =
    ZMod.stdAddChar (k * n) * Ψ k
  rw [← hmul k]
  ring

/-- Retain Fourier modes on which the cyclic derivative multiplier has norm at least `τ`. -/
noncomputable def cyclicHighCut (N : ℕ) [NeZero N] (τ : ℝ)
    (Ψ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  if τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ then Ψ k else 0

theorem cyclicHighCut_gap (N : ℕ) [NeZero N] (τ : ℝ)
    (Ψ : ZMod N → ℂ) :
    ∀ k, cyclicHighCut N τ Ψ k ≠ 0 →
      τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
  intro k hk
  by_contra h
  have hlt : ¬τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := h
  exact hk (by simp [cyclicHighCut, hlt])

theorem cyclicHighCut_energy_le (N : ℕ) [NeZero N] (τ : ℝ)
    (Ψ : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖cyclicHighCut N τ Ψ k‖ ^ (2 : ℕ)) ≤
      ∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ) := by
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : τ ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖
  · simp [cyclicHighCut, h]
  · simp [cyclicHighCut, h]

/-- The high-pass dyadic window costs only `4/(N τ²)` times source Fourier energy. -/
theorem cyclic_high_cut_dilation_energy_le
    (N : ℕ) [NeZero N] (hodd : Odd N) (τ : ℝ) (hτ : 0 < τ)
    (Ψ : ZMod N → ℂ) :
    let P : ZMod N → ℂ :=
      ZMod.dft.symm (fun k => cyclicHighCut N τ Ψ k /
        ((1 : ℂ) - ZMod.stdAddChar (-k)))
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 / ((N : ℝ) * τ ^ (2 : ℕ)) *
        (∑ k : ZMod N, ‖Ψ k‖ ^ (2 : ℕ)) := by
  dsimp only
  have hbase := cyclic_high_mode_dilation_energy_le N hodd τ hτ
    (cyclicHighCut N τ Ψ) (cyclicHighCut_gap N τ Ψ)
  have henergy := cyclicHighCut_energy_le N τ Ψ
  have hfactor : 0 ≤ 4 / ((N : ℝ) * τ ^ (2 : ℕ)) := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left henergy hfactor)

/-- After Parseval, the high-pass dyadic window costs `4 τ⁻²` times the literal
coefficient energy. No arithmetic estimate is used. -/
theorem cyclic_high_cut_dilation_energy_le_source
    (N : ℕ) [NeZero N] (hodd : Odd N) (τ : ℝ) (hτ : 0 < τ)
    (f : ZMod N → ℂ) :
    let P : ZMod N → ℂ :=
      ZMod.dft.symm (fun k => cyclicHighCut N τ (ZMod.dft f) k /
        ((1 : ℂ) - ZMod.stdAddChar (-k)))
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 / τ ^ (2 : ℕ) * (∑ j : ZMod N, ‖f j‖ ^ (2 : ℕ)) := by
  dsimp only
  have hbase := cyclic_high_cut_dilation_energy_le N hodd τ hτ (ZMod.dft f)
  have hparse := GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval N f
  simp only [Complex.normSq_eq_norm_sq] at hparse
  calc
    _ ≤ 4 / ((N : ℝ) * τ ^ (2 : ℕ)) *
        (∑ k : ZMod N, ‖ZMod.dft f k‖ ^ (2 : ℕ)) := hbase
    _ = 4 / τ ^ (2 : ℕ) * (∑ j : ZMod N, ‖f j‖ ^ (2 : ℕ)) := by
      rw [hparse]
      have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

/-- The literal odd-Möbius coefficients on one cyclic period. -/
noncomputable def cyclicOddMobiusSource (N : ℕ) [NeZero N] (j : ZMod N) : ℂ :=
  mobiusPrimeFreeCoefficient 2 j.val

theorem norm_cyclicOddMobiusSource_le_one (N : ℕ) [NeZero N] (j : ZMod N) :
    ‖cyclicOddMobiusSource N j‖ ≤ 1 := by
  unfold cyclicOddMobiusSource mobiusPrimeFreeCoefficient
  split_ifs
  · exact norm_mobiusComplexCoefficient_le_one _
  · simp

/-- The literal source's high modes have an unconditional `4N/τ²` dyadic
window budget.  The remaining low modes are the arithmetic RH target. -/
theorem cyclicOddMobiusHighPass_energy_le
    (N : ℕ) [NeZero N] (hodd : Odd N) (τ : ℝ) (hτ : 0 < τ) :
    let P : ZMod N → ℂ :=
      ZMod.dft.symm (fun k => cyclicHighCut N τ (ZMod.dft (cyclicOddMobiusSource N)) k /
        ((1 : ℂ) - ZMod.stdAddChar (-k)))
    (∑ n : ZMod N, ‖P (2 * n) - P n‖ ^ (2 : ℕ)) ≤
      4 / τ ^ (2 : ℕ) * (N : ℝ) := by
  dsimp only
  have hbase := cyclic_high_cut_dilation_energy_le_source N hodd τ hτ (cyclicOddMobiusSource N)
  have hterm : ∀ j : ZMod N, ‖cyclicOddMobiusSource N j‖ ^ (2 : ℕ) ≤ (1 : ℝ) := by
    intro j
    have h := norm_cyclicOddMobiusSource_le_one N j
    nlinarith [norm_nonneg (cyclicOddMobiusSource N j)]
  have hsum : (∑ j : ZMod N, ‖cyclicOddMobiusSource N j‖ ^ (2 : ℕ)) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _j : ZMod N, (1 : ℝ) := Finset.sum_le_sum (by intro j _; exact hterm j)
      _ = (N : ℝ) := by simp
  have hfactor : 0 ≤ 4 / τ ^ (2 : ℕ) := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left hsum hfactor)

/-- Below half the cycle, the literal odd-Möbius source window is exactly the
Mertens prefix. This is the source landing needed for the low-mode reduction. -/
theorem cyclicOddMobiusSource_window_eq_mertens (X m : ℕ) (hm : 2 * m ≤ X) :
    (∑ u ∈ Finset.Ioc m (2 * m),
      cyclicOddMobiusSource (2 * X + 1) (u : ZMod (2 * X + 1))) =
      mobiusMertensPartialSum (2 * m) := by
  have hprime : Nat.Prime 2 := Nat.prime_two
  rw [mobiusMertensPartialSum_eq_primeWindow hprime]
  unfold mobiusPrimeWindowPartialSum
  have hset : Finset.Ioc m (2 * m) = Finset.Ico (2 * m / 2 + 1) (2 * m + 1) := by
    ext u
    simp only [Finset.mem_Ioc, Finset.mem_Ico,
      Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u < 2 * m + 1 := (Finset.mem_Ico.mp hu).2
  have huX : u < 2 * X + 1 := by omega
  simp [cyclicOddMobiusSource, ZMod.val_natCast_of_lt huX]

end RHTower
