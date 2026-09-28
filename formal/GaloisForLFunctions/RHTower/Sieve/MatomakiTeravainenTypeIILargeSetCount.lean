import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLargeAmplitudeCount
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIWindowTransfer

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-! # Type-II large-amplitude set

This module closes the cardinality part of the `T₁` branch of Proposition 4.2. It improves the
paper's sufficient `T^(50 eps)` estimate to `T^(21 eps)` by applying the already available Huxley
schedule uniformly to both literal factors. -/

/-- The exact `T₁` set: at least one Type-II factor exceeds its large-amplitude threshold. -/
noncomputable def matomakiTeravainenTypeIILargeAmplitudeSet
    (Tset : Finset ℝ) (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
    (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ) (rho : ℝ) : Finset ℝ :=
  Tset.filter fun t =>
    (A₁ : ℝ) ^ (-rho) ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ t ∨
    (A₂ : ℝ) ^ (-rho) ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ t

/-- Before constant absorption, the exact two-factor `T₁` count with its sharper exponent. -/
theorem exists_matomakiTeravainen_typeII_T1_large_set_count_divisor_bounded
    {eps mu Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (hCprod : 0 < Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    let L : ℕ := ⌈1 / mu⌉₊
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      T ^ mu ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * eps) →
      T / (Cprod * (1 + |Real.log T|) ^ k) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (Cprod * (1 + |Real.log T|) ^ k) →
      (∀ n : Fin N₁,
        ‖a₁ n‖ ≤ C₁ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₁)) →
      (∀ n : Fin N₂,
        ‖a₂ n‖ ≤ C₂ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₂)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      ((matomakiTeravainenTypeIILargeAmplitudeSet S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)).card : ℝ) ≤
        (L + 3 : ℝ) * T ^
          (2 * (10 * eps + eps ^ 2 / 20) - eps ^ 2 / 5) := by
  let L : ℕ := ⌈1 / mu⌉₊
  let kappa : ℝ := eps ^ 2 / 20
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  obtain ⟨Tcount₁, hTcount₁, hcount₁⟩ :=
    exists_matomakiTeravainen_large_amplitude_count_divisor_bounded
      heps (hepss.trans (by norm_num)) hkappa hC₁ w₁ L
  obtain ⟨Tcount₂, hTcount₂, hcount₂⟩ :=
    exists_matomakiTeravainen_large_amplitude_count_divisor_bounded
      heps (hepss.trans (by norm_num)) hkappa hC₂ w₂ L
  obtain ⟨Tprod, hTprod, hprod⟩ :=
    exists_matomakiTeravainen_polylog_product_window hCprod heps k
  let T₀ : ℝ := max 2 (max Tcount₁ (max Tcount₂ Tprod))
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S hT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂
    hA₁mu hA₁hi hprodLo hprodHi hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread
  have hTgt : 1 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hT)
  have hTc₁ : Tcount₁ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTc₂ : Tcount₂ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hT
  have hTp : Tprod ≤ T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) hT
  have hprodWindow := hprod T ((A₁ : ℝ) * (A₂ : ℝ)) hTp hprodLo hprodHi
  have hlong := matomakiTeravainen_typeII_long_factor_window
    hTgt (by positivity : 0 < (A₁ : ℝ)) hprodWindow.1 hprodWindow.2
    hA₁mu hA₁hi (by linarith) (by linarith)
  have hA₂mu : T ^ mu ≤ (A₂ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hTgt.le hmuhi).trans hlong.1
  obtain ⟨ell, hell, hellL, hshortLo, hshortHi⟩ :=
    exists_pow_mem_matomakiTeravainen_huxley_window_bounded hTgt hA₁
      heps hepss hmu hA₁mu hA₁hi
  have hshortLo' : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
      ((A₁ ^ ell : ℕ) : ℝ) := by
    have hpow : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ T ^ ((9 : ℝ) / 11) :=
      Real.rpow_le_rpow_of_exponent_le hTgt.le (by linarith)
    simpa only [Nat.cast_pow] using hpow.trans hshortLo
  have hshortHi' : ((A₁ ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) := by
    simpa only [Nat.cast_pow] using hshortHi
  have hlongLo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
      ((A₂ ^ 1 : ℕ) : ℝ) := by simpa using hlong.1
  have hlongHi : ((A₂ ^ 1 : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) := by
    simpa using hlong.2
  have hrhoLo : 5 * eps + kappa ≤ 10 * eps := by
    dsimp only [kappa]
    nlinarith [sq_nonneg eps]
  have hrhoHi : 10 * eps + kappa ≤ 23 / 100 - 5 * eps := by
    dsimp only [kappa]
    nlinarith [sq_nonneg eps]
  let S₁ : Finset ℝ := S.filter fun t =>
    (A₁ : ℝ) ^ (-(10 * eps)) ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ t
  let S₂ : Finset ℝ := S.filter fun t =>
    (A₂ : ℝ) ^ (-(10 * eps)) ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ t
  have hcard₁ := hcount₁ T N₁ A₁ ell (10 * eps) a₁ S₁ hTc₁
    hN₁ hNA₁ hA₁ hell hellL hshortLo' hshortHi' hrhoLo hrhoHi
    hpoint₁ hsupp₁
    (by
      intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
    (by
      intro x hx y hy
      exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
    (by intro t ht; exact (Finset.mem_filter.1 ht).2)
  have hcard₂ := hcount₂ T N₂ A₂ 1 (10 * eps) a₂ S₂ hTc₂
    hN₂ hNA₂ hA₂ (by norm_num) (by
      dsimp only [L]
      exact Nat.one_le_ceil_iff.2 (by positivity))
    hlongLo hlongHi hrhoLo hrhoHi hpoint₂ hsupp₂
    (by
      intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
    (by
      intro x hx y hy
      exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
    (by intro t ht; exact (Finset.mem_filter.1 ht).2)
  have hlargeEq :
      matomakiTeravainenTypeIILargeAmplitudeSet S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps) = S₁ ∪ S₂ := by
    ext t
    simp only [matomakiTeravainenTypeIILargeAmplitudeSet, S₁, S₂, Finset.mem_filter,
      Finset.mem_union]
    tauto
  have hcardUnion :
      ((matomakiTeravainenTypeIILargeAmplitudeSet S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)).card : ℝ) ≤
        (S₁.card : ℝ) + (S₂.card : ℝ) := by
    rw [hlargeEq]
    exact_mod_cast Finset.card_union_le S₁ S₂
  have hellBound : (ell + 1 : ℝ) ≤ (L + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hellL 1
  have hpow0 : 0 ≤ T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) :=
    Real.rpow_nonneg (by linarith) _
  have hcard₂' : (S₂.card : ℝ) ≤
      2 * T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) := by
    norm_num at hcard₂ ⊢
    exact hcard₂
  calc
    ((matomakiTeravainenTypeIILargeAmplitudeSet S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)).card : ℝ)
        ≤ (S₁.card : ℝ) + (S₂.card : ℝ) := hcardUnion
    _ ≤ (ell + 1 : ℝ) * T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) +
        2 * T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) :=
      add_le_add hcard₁ hcard₂'
    _ ≤ (L + 1 : ℝ) * T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) +
        2 * T ^ (2 * (10 * eps + kappa) - eps ^ 2 / 5) := by
      gcongr
    _ = (L + 3 : ℝ) * T ^
        (2 * (10 * eps + eps ^ 2 / 20) - eps ^ 2 / 5) := by
      dsimp only [kappa]
      ring

/-- Literal divisor-bounded Type-II data gives `|T₁| ≤ T^(21 eps)`, strengthening the paper's
sufficient `T^(50 eps)` bound. No raising degree, coefficient energy, or large-value premise
remains. -/
theorem exists_matomakiTeravainen_typeII_T1_large_set_count_power
    {eps mu Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (hCprod : 0 < Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      T ^ mu ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * eps) →
      T / (Cprod * (1 + |Real.log T|) ^ k) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (Cprod * (1 + |Real.log T|) ^ k) →
      (∀ n : Fin N₁,
        ‖a₁ n‖ ≤ C₁ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₁)) →
      (∀ n : Fin N₂,
        ‖a₂ n‖ ≤ C₂ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₂)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      ((matomakiTeravainenTypeIILargeAmplitudeSet S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)).card : ℝ) ≤
        T ^ (21 * eps) := by
  let L : ℕ := ⌈1 / mu⌉₊
  obtain ⟨Tcount, hTcount, hcount⟩ :=
    exists_matomakiTeravainen_typeII_T1_large_set_count_divisor_bounded
      heps hepss hmu hmulo hmuhi hCprod hC₁ hC₂ k w₁ w₂
  have hexp : 2 * (10 * eps + eps ^ 2 / 20) - eps ^ 2 / 5 < 21 * eps := by
    nlinarith [sq_nonneg eps]
  have habsorbEvent := eventually_const_mul_rpow_polylog_le_rpow
    (C := (L + 3 : ℝ)) (α := 2 * (10 * eps + eps ^ 2 / 20) - eps ^ 2 / 5)
    (β := 21 * eps) 0 hexp
  obtain ⟨Tabsorb, habsorb⟩ := eventually_atTop.1 habsorbEvent
  let T₀ : ℝ := max Tcount Tabsorb
  refine ⟨T₀, hTcount.trans (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S hT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂
    hA₁mu hA₁hi hprodLo hprodHi hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread
  have hc := hcount T N₁ A₁ a₁ N₂ A₂ a₂ S (le_trans (le_max_left _ _) hT)
    hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread
  have ha := habsorb T (le_trans (le_max_right _ _) hT)
  have ha' :
      (⌈1 / mu⌉₊ + 3 : ℝ) *
          T ^ (2 * (10 * eps + eps ^ 2 / 20) - eps ^ 2 / 5) ≤
        T ^ (21 * eps) := by
    simpa only [L, Real.rpow_zero, pow_zero, mul_one] using ha
  exact hc.trans ha'

end

end RHTower.Sieve
