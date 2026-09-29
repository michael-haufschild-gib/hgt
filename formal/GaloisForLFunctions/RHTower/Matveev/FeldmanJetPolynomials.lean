import GaloisForLFunctions.RHTower.Matveev.FeldmanCommonDivisor
import GaloisForLFunctions.RHTower.Matveev.ExponentialPolynomialZeros
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Fel'dman's auxiliary polynomials and their jets

For `k ≤ N` let

`g_k(X) = ∏_{i ≤ N, i ≠ k} (X + i + 1)`.

Its `σ`-th Hasse derivative at `z` is the coefficient of `Y^σ` in `g_k(z + Y)`, which by Vieta's
formula is the elementary symmetric sum

`g_k^{[σ]}(z) = Σ_{t ⊆ {0,…,N} ∖ {k}, |t| = N − σ} ∏_{i ∈ t} (z + i + 1)`.

At a natural number `x` every term is the product of the block `x + 1, …, x + N + 1` with
`σ + 1` members deleted, so for `σ < S` all jets are divisible by Fel'dman's common divisor
`D(N + 1, S)`.  On the complex side `|g_k^{[σ]}(z)| ≤ 2^N (|z| + N + 1)^N`, and the jets satisfy
`d/dz g_k^{[σ]} = (σ + 1) g_k^{[σ + 1]}`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Polynomial Finset

/-- Fel'dman's auxiliary polynomial `g_k(X) = ∏_{i ≤ N, i ≠ k} (X + i + 1)` over `ℂ`. -/
def feldmanPoly (N k : ℕ) : ℂ[X] := ∏ i ∈ (range (N + 1)).erase k, (X + C ((i : ℂ) + 1))

/-- The `σ`-th Hasse jet `g_k^{[σ]}(z)`. -/
def feldmanJet (N k σ : ℕ) (z : ℂ) : ℂ := (hasseDeriv σ (feldmanPoly N k)).eval z

theorem card_erase_range {N k : ℕ} (hk : k ≤ N) : #((range (N + 1)).erase k) = N := by
  rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
  omega

theorem natDegree_feldmanPoly {N k : ℕ} (hk : k ≤ N) : (feldmanPoly N k).natDegree = N := by
  unfold feldmanPoly
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
  exact card_erase_range hk

/-- **Vieta form of the jets.** -/
theorem feldmanJet_eq_sum {N k σ : ℕ} (hk : k ≤ N) (hσ : σ ≤ N) (z : ℂ) :
    feldmanJet N k σ z =
      ∑ t ∈ powersetCard (N - σ) ((range (N + 1)).erase k), ∏ i ∈ t, (z + ((i : ℂ) + 1)) := by
  rw [feldmanJet, ← taylor_coeff, taylor_apply, feldmanPoly, Polynomial.prod_comp]
  have hlin : ∀ i : ℕ, (X + C ((i : ℂ) + 1)).comp (X + C z) = X + C (z + ((i : ℂ) + 1)) := by
    intro i
    simp only [add_comp, X_comp, C_comp, C_add]
    ring
  simp only [hlin]
  rw [prod_X_add_C_coeff _ _ (by rw [card_erase_range hk]; exact hσ), card_erase_range hk]

/-- Above the degree the jets vanish. -/
theorem feldmanJet_eq_zero {N k σ : ℕ} (hk : k ≤ N) (hσ : N < σ) (z : ℂ) :
    feldmanJet N k σ z = 0 := by
  have hdeg : (feldmanPoly N k).natDegree < σ := by rw [natDegree_feldmanPoly hk]; exact hσ
  rw [feldmanJet, hasseDeriv_eq_zero_of_lt_natDegree _ _ hdeg, eval_zero]

/-- The natural-number value of a jet at a natural point. -/
def feldmanJetNat (N k σ x : ℕ) : ℕ :=
  if σ ≤ N then ∑ t ∈ powersetCard (N - σ) ((range (N + 1)).erase k), ∏ i ∈ t, (x + i + 1)
  else 0

theorem feldmanJet_natCast {N k : ℕ} (hk : k ≤ N) (σ x : ℕ) :
    feldmanJet N k σ (x : ℂ) = (feldmanJetNat N k σ x : ℂ) := by
  unfold feldmanJetNat
  split_ifs with hσ
  · rw [feldmanJet_eq_sum hk hσ]
    push_cast
    exact sum_congr rfl fun t _ => prod_congr rfl fun i _ => by ring
  · rw [feldmanJet_eq_zero hk (by omega)]
    simp

/-- **Divisibility of the jets by Fel'dman's common divisor.** -/
theorem feldmanDivisor_dvd_feldmanJetNat {N S k σ : ℕ} (hσS : σ < S) (x : ℕ) :
    feldmanDivisor (N + 1) S ∣ feldmanJetNat N k σ x := by
  unfold feldmanJetNat
  split_ifs with hσ
  · refine dvd_sum fun t ht => ?_
    obtain ⟨hts, htcard⟩ := mem_powersetCard.mp ht
    have hsub : t.image (· + 1) ⊆ Icc 1 (N + 1) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      have := mem_range.mp (mem_of_mem_erase (hts hi))
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hcard : #(t.image (· + 1)) = N - σ := by
      rw [card_image_of_injective _ (add_left_injective 1), htcard]
    have hprod : ∏ i ∈ t, (x + i + 1) = ∏ j ∈ t.image (· + 1), (x + j) := by
      rw [prod_image fun a _ b _ h => by simpa using h]
      exact prod_congr rfl fun i _ => by ring
    rw [hprod]
    exact feldmanDivisor_dvd_prod x hsub (by rw [hcard]; omega)
  · exact dvd_zero _

/-- **Size of the jets.** -/
theorem norm_feldmanJet_le {N k : ℕ} (hk : k ≤ N) (σ : ℕ) (z : ℂ) :
    ‖feldmanJet N k σ z‖ ≤ 2 ^ N * (‖z‖ + N + 1) ^ N := by
  have hbase : (1 : ℝ) ≤ ‖z‖ + N + 1 := by
    have := norm_nonneg z
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  by_cases hσ : σ ≤ N
  · rw [feldmanJet_eq_sum hk hσ]
    calc ‖∑ t ∈ powersetCard (N - σ) ((range (N + 1)).erase k), ∏ i ∈ t, (z + ((i : ℂ) + 1))‖
        ≤ ∑ t ∈ powersetCard (N - σ) ((range (N + 1)).erase k),
            ‖∏ i ∈ t, (z + ((i : ℂ) + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ powersetCard (N - σ) ((range (N + 1)).erase k), (‖z‖ + N + 1) ^ N := by
          refine sum_le_sum fun t ht => ?_
          obtain ⟨hts, htcard⟩ := mem_powersetCard.mp ht
          rw [norm_prod]
          calc ∏ i ∈ t, ‖z + ((i : ℂ) + 1)‖ ≤ ∏ _i ∈ t, (‖z‖ + N + 1) := by
                refine prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => ?_
                have hiN : (i : ℝ) ≤ N := by
                  exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase (hts hi)))
                calc ‖z + ((i : ℂ) + 1)‖ ≤ ‖z‖ + ‖((i : ℂ) + 1)‖ := norm_add_le _ _
                  _ = ‖z‖ + ((i : ℝ) + 1) := by
                      rw [show ((i : ℂ) + 1) = ((i + 1 : ℕ) : ℂ) by push_cast; ring,
                        Complex.norm_natCast]
                      push_cast
                      ring
                  _ ≤ ‖z‖ + N + 1 := by linarith
            _ = (‖z‖ + N + 1) ^ #t := prod_const _
            _ ≤ (‖z‖ + N + 1) ^ N := pow_le_pow_right₀ hbase (by rw [htcard]; omega)
      _ = (#(powersetCard (N - σ) ((range (N + 1)).erase k)) : ℝ) * (‖z‖ + N + 1) ^ N := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ N * (‖z‖ + N + 1) ^ N := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [card_powersetCard, card_erase_range hk]
          exact_mod_cast Nat.choose_le_two_pow N (N - σ)
  · rw [feldmanJet_eq_zero hk (by omega), norm_zero]
    positivity

/-- **Derivative of the jets.** `d/dz g_k^{[σ]} = (σ + 1) g_k^{[σ + 1]}`. -/
theorem hasDerivAt_feldmanJet (N k σ : ℕ) (z : ℂ) :
    HasDerivAt (feldmanJet N k σ) (((σ : ℂ) + 1) * feldmanJet N k (σ + 1) z) z := by
  have h := (hasseDeriv σ (feldmanPoly N k)).hasDerivAt z
  have hcomp : derivative (hasseDeriv σ (feldmanPoly N k)) =
      ((σ : ℂ) + 1) • hasseDeriv (σ + 1) (feldmanPoly N k) := by
    rw [← hasseDeriv_one]
    have := congrArg (fun L : ℂ[X] →ₗ[ℂ] ℂ[X] => L (feldmanPoly N k)) (hasseDeriv_comp 1 σ)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    rw [this, add_comm 1 σ, Nat.choose_one_right, ← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    rfl
  rw [hcomp, eval_smul, smul_eq_mul] at h
  exact h

theorem differentiable_feldmanJet (N k σ : ℕ) : Differentiable ℂ (feldmanJet N k σ) :=
  fun z => (hasDerivAt_feldmanJet N k σ z).differentiableAt

/-- The value jet at a natural point is the full product. -/
theorem feldmanJetNat_zero {N k : ℕ} (hk : k ≤ N) (x : ℕ) :
    feldmanJetNat N k 0 x = ∏ i ∈ (range (N + 1)).erase k, (x + i + 1) := by
  unfold feldmanJetNat
  rw [if_pos (Nat.zero_le N), Nat.sub_zero]
  set s := (range (N + 1)).erase k with hs
  have hcard : #s = N := card_erase_range hk
  rw [← hcard, powersetCard_self, sum_singleton]

/-- Over a field of characteristic zero the value jet is the Lagrange-type basis polynomial. -/
theorem feldmanJetNat_zero_eq_eval_lagrangeShift {K : Type*} [Field K] [CharZero K] {N k : ℕ}
    (hk : k ≤ N) (x : ℕ) :
    ((feldmanJetNat N k 0 x : ℕ) : K) = (lagrangeShift (K := K) N k).eval (x : K) := by
  rw [feldmanJetNat_zero hk, lagrangeShift, eval_prod]
  push_cast
  refine prod_congr rfl fun i _ => ?_
  simp only [eval_add, eval_X, eval_C]
  ring

end GaloisForLFunctions.RHTower.Matveev
