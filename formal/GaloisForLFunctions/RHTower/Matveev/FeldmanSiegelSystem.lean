import GaloisForLFunctions.RHTower.Matveev.FeldmanAuxiliaryBounds
import Mathlib.NumberTheory.SiegelsLemma

/-!
# The Siegel system for Fel'dman's auxiliary function

The integer value `A_{σ,τ}(x)` is linear in the unknowns:

`A_{σ,τ}(x) = Σ_{k,l} a_{σ,τ,x}(k,l) C(k,l)`,
`a_{σ,τ,x}(k,l) = (g_k^{[σ]}(x)/D) ∏_{j<m} γ_j(l)^{τ_j} ∏_j p_j^{l_j x}`.

Imposing `A_{σ,τ}(x) = 0` for `x < X₀`, `σ < S` and `τ ∈ [0, S)^m` gives `X₀ S^{m+1}` equations in
`U = (N + 1) q^{m+1}` unknowns.  When `2 X₀ S^{m+1} ≤ U`, Siegel's lemma provides a nonzero
integer solution with `|C(k,l)| ≤ U · max(1, a)` for every bound `a` of the coefficients.
The coefficients satisfy `|a_{σ,τ,x}(k,l)| ≤ 2^N (x + N + 1)^N / D · (2qB)^{|τ|} · e^{x q W₊}`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

attribute [local instance] Matrix.seminormedAddCommGroup

variable {m : ℕ} (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)

/-- The coefficient of the unknown `C(k, l)` in `A_{σ,τ}(x)`. -/
def feldmanCoeff (N q S σ : ℕ) (τ : Fin m → ℕ) (x : ℕ) (kl : FeldmanIndex N q m) : ℤ :=
  ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℤ) *
    (∏ j, feldmanGamma b kl.expo j ^ τ j) * ∏ j, (p j : ℤ) ^ (kl.expo j * x)

theorem feldmanArith_eq_sum {N q S : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ)
    (x : ℕ) : feldmanArith p b N q S C σ τ x = ∑ kl, feldmanCoeff p b N q S σ τ x kl * C kl := by
  unfold feldmanArith feldmanCoeff
  exact sum_congr rfl fun kl _ => by ring

theorem card_feldmanIndex (N q : ℕ) :
    Fintype.card (FeldmanIndex N q m) = (N + 1) * q ^ (m + 1) := by
  simp [FeldmanIndex, Fintype.card_prod, Fintype.card_pi]

/-- **Siegel's lemma for the Fel'dman system.** -/
theorem exists_feldmanSiegel {N q S X₀ : ℕ} (hX₀ : 0 < X₀) (hS : 0 < S)
    (hcount : 2 * (X₀ * S ^ (m + 1)) ≤ (N + 1) * q ^ (m + 1)) {Amax : ℝ} (hAmax : 0 ≤ Amax)
    (hA : ∀ x < X₀, ∀ σ < S, ∀ τ : Fin m → ℕ, (∀ j, τ j < S) → ∀ kl,
      |(feldmanCoeff p b N q S σ τ x kl : ℝ)| ≤ Amax) :
    ∃ C : FeldmanIndex N q m → ℤ, C ≠ 0 ∧
      (∀ x < X₀, ∀ σ < S, ∀ τ : Fin m → ℕ, (∀ j, τ j < S) →
        feldmanArith p b N q S C σ τ x = 0) ∧
      ∀ kl, |(C kl : ℝ)| ≤ (((N + 1) * q ^ (m + 1) : ℕ) : ℝ) * max 1 Amax := by
  classical
  let A : Matrix (Fin X₀ × Fin S × (Fin m → Fin S)) (FeldmanIndex N q m) ℤ :=
    fun i kl => feldmanCoeff p b N q S i.2.1 (fun j => (i.2.2 j : ℕ)) i.1 kl
  have hcardα : Fintype.card (Fin X₀ × Fin S × (Fin m → Fin S)) = X₀ * S ^ (m + 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, prod_const, card_univ]
    ring
  have hcardβ := card_feldmanIndex (m := m) N q
  have hpos : 0 < Fintype.card (Fin X₀ × Fin S × (Fin m → Fin S)) := by
    rw [hcardα]
    positivity
  have hlt : Fintype.card (Fin X₀ × Fin S × (Fin m → Fin S)) <
      Fintype.card (FeldmanIndex N q m) := by
    rw [hcardα, hcardβ]
    have : 0 < X₀ * S ^ (m + 1) := by positivity
    omega
  obtain ⟨t, ht0, htA, htnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hlt hpos
  refine ⟨t, ht0, fun x hx σ hσ τ hτ => ?_, fun kl => ?_⟩
  · have h := congrFun htA (⟨x, hx⟩, ⟨σ, hσ⟩, fun j => ⟨τ j, hτ j⟩)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, A] at h
    rw [feldmanArith_eq_sum]
    exact h
  · have hnormA : ‖A‖ ≤ Amax := (Matrix.norm_le_iff hAmax).mpr fun i kl => by
      rw [Int.norm_eq_abs]
      exact hA _ i.1.isLt _ i.2.1.isLt _ (fun j => (i.2.2 j).isLt) kl
    set cα := Fintype.card (Fin X₀ × Fin S × (Fin m → Fin S)) with hcα
    set cβ := Fintype.card (FeldmanIndex N q m) with hcβ
    have hcαβ : (cα : ℝ) ≤ (cβ : ℝ) - cα := by
      have : 2 * cα ≤ cβ := by rw [hcardα, hcardβ]; exact hcount
      have : (2 * cα : ℝ) ≤ cβ := by exact_mod_cast this
      linarith
    have hden : (0 : ℝ) < (cβ : ℝ) - cα := by
      have : (0 : ℝ) < cα := by exact_mod_cast hpos
      linarith
    have hexp : (cα : ℝ) / ((cβ : ℝ) - cα) ≤ 1 := (div_le_one hden).mpr hcαβ
    have hβ1 : (1 : ℝ) ≤ cβ := by exact_mod_cast hpos.trans hlt
    have hbase : (1 : ℝ) ≤ (cβ : ℝ) * max 1 ‖A‖ :=
      one_le_mul_of_one_le_of_one_le hβ1 (le_max_left _ _)
    have ht : ‖t‖ ≤ (cβ : ℝ) * max 1 Amax :=
      calc ‖t‖ ≤ ((cβ : ℝ) * max 1 ‖A‖) ^ ((cα : ℝ) / ((cβ : ℝ) - cα)) := htnorm
        _ ≤ ((cβ : ℝ) * max 1 ‖A‖) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
        _ = (cβ : ℝ) * max 1 ‖A‖ := Real.rpow_one _
        _ ≤ (cβ : ℝ) * max 1 Amax :=
            mul_le_mul_of_nonneg_left (max_le_max le_rfl hnormA) (Nat.cast_nonneg _)
    rw [← hcardβ, ← Int.norm_eq_abs]
    exact (norm_le_pi_norm t kl).trans ht

/-! ## Size of the coefficients -/

variable {p b}

theorem abs_prod_feldmanGamma_pow_le (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {q : ℕ} (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q)
    (τ : Fin m → ℕ) :
    |((∏ j, feldmanGamma b l j ^ τ j : ℤ) : ℝ)| ≤
      (2 * q * (b (Fin.last m) : ℝ)) ^ (∑ j, τ j) := by
  rw [Int.cast_prod, abs_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
  rw [Int.cast_pow, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_feldmanGamma_le hB hb l hl j) _

/-- The `S`-unit factor is at most `e^{x q W₊}`. -/
theorem prod_pow_expo_le (hp : ∀ j, 1 ≤ p j) {N q : ℕ} (kl : FeldmanIndex N q m) (x : ℕ) :
    ((∏ j, (p j : ℤ) ^ (kl.expo j * x) : ℤ) : ℝ) ≤ Real.exp (x * (q * totalLogSum p)) := by
  have heq : Real.exp (x * (q * totalLogSum p)) = ∏ j, (p j : ℝ) ^ (q * x) := by
    rw [totalLogSum, mul_sum, mul_sum, Real.exp_sum]
    refine prod_congr rfl fun j _ => ?_
    rw [show (x : ℝ) * ((q : ℝ) * Real.log (p j)) = ((q * x : ℕ) : ℝ) * Real.log (p j) by
      push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by exact_mod_cast (Nat.succ_le_iff.mp (hp j)))]
  rw [heq]
  push_cast
  refine prod_le_prod (fun _ _ => by positivity) fun j _ =>
    pow_le_pow_right₀ (by exact_mod_cast hp j) ?_
  exact Nat.mul_le_mul_right _ (expo_lt kl j).le

/-- **Size of the coefficients.** -/
theorem abs_feldmanCoeff_le (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q S σ : ℕ} (hσS : σ < S) (τ : Fin m → ℕ) (x : ℕ)
    (kl : FeldmanIndex N q m) :
    |(feldmanCoeff p b N q S σ τ x kl : ℝ)| ≤
      2 ^ N * ((x : ℝ) + N + 1) ^ N / (feldmanDivisor (N + 1) S : ℝ) *
        (2 * q * (b (Fin.last m) : ℝ)) ^ (∑ j, τ j) * Real.exp (x * (q * totalLogSum p)) := by
  have hk : (kl.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp kl.1.isLt
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hjet : ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℝ) =
      (feldmanJetNat N kl.1 σ x : ℝ) / feldmanDivisor (N + 1) S :=
    Nat.cast_div (feldmanDivisor_dvd_feldmanJetNat hσS x) hD.ne'
  have hjetle : (feldmanJetNat N kl.1 σ x : ℝ) ≤ 2 ^ N * ((x : ℝ) + N + 1) ^ N := by
    have h := norm_feldmanJet_le hk σ (x : ℂ)
    rwa [feldmanJet_natCast hk, Complex.norm_natCast, Complex.norm_natCast] at h
  have hunit : (0 : ℝ) ≤ ((∏ j, (p j : ℤ) ^ (kl.expo j * x) : ℤ) : ℝ) := by positivity
  rw [feldmanCoeff, Int.cast_mul, Int.cast_mul, abs_mul, abs_mul, Int.cast_natCast, hjet,
    abs_of_nonneg hunit, abs_of_nonneg (by positivity)]
  refine mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right hjetle hD.le)
    (abs_prod_feldmanGamma_pow_le hB hb kl.expo (expo_lt kl) τ) (abs_nonneg _)
    (by positivity)) (prod_pow_expo_le hp kl x) (by positivity) (by positivity)

end GaloisForLFunctions.RHTower.Matveev
