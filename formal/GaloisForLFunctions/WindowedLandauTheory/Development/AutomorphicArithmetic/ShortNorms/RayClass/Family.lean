import Mathlib

/-! The coefficients and pole-removed Dirichlet series of the ray class family. -/

noncomputable section

open Finset ArithmeticFunction

namespace GlobalTheory.Hk

/-- Partial zeta coefficients of a finite ray class family and their uniform estimates. -/
structure LFam where
  G : Type
  [ag : AddCommGroup G]
  [ft : Fintype G]
  B : ℝ
  κ : ℝ
  a : G → ℕ → ℝ
  lam : G → ℕ → ℝ
  B_ge : 4 ≤ B
  card_le : (Fintype.card G : ℝ) ≤ B
  κ_ge : 1 / B ≤ κ
  κ_le : κ ≤ 4
  a_nonneg : ∀ g n, 0 ≤ a g n
  a_zero : ∀ g, a g 0 = 0
  a_one : a 0 1 = 1
  a_one_ne : ∀ g, g ≠ 0 → a g 1 = 0
  count : ∀ (g : G) (x : ℝ), 1 ≤ x → |∑ n ∈ Icc 1 ⌊x⌋₊, a g n - κ * x| ≤ 10 * Real.sqrt x
  theta : ∀ (g : G) (t : ℝ), 0 < t → t ≤ 1 → |∑' n : ℕ, a g n * Real.exp (-(t * n)) - κ / t| ≤ B ^ 10 * t
  lam_nonneg : ∀ g n, 0 ≤ lam g n
  lam_le : ∀ n, ∑ g, lam g n ≤ 2 * Λ n
  conv : ∀ g n, a g n * Real.log n = ∑ h, ∑ p ∈ n.divisorsAntidiagonal, lam h p.1 * a (g - h) p.2
  sq : ∀ χ : AddChar G ℂ, χ * χ = 1 → ∀ n : ℕ,
    0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2 ∧
    ∑ g, a g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2

attribute [instance] LFam.ag LFam.ft

namespace LFam

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

def aChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.a g n : ℂ)

def lamChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.lam g n : ℂ)

open Classical in

def res : ℂ := if χ = 1 then ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) else 0

def mel (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x) * (x : ℂ) ^ (-s - 1)

open Classical in

def F (s : ℂ) : ℂ := if χ = 1 then 𝓕.res χ * s + (s - 1) * s * 𝓕.mel χ s else s * 𝓕.mel χ s

def psi (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.lamChi χ n

def ell (t : ℝ) : ℝ := Real.log (𝓕.B * (|t| + 2))

def ExcZ (c : ℝ) (Z : Finset ℝ) : Prop :=
  Z.card ≤ 1 ∧ (∀ β ∈ Z, 1 - c / 𝓕.ell 0 ≤ β ∧ β < 1 ∧ 𝓕.F χ β = 0 ∧ deriv (𝓕.F χ) β ≠ 0) ∧
    ∀ s : ℂ, 1 - c / 𝓕.ell s.im ≤ s.re → 𝓕.F χ s = 0 → ∃ β ∈ Z, s = (β : ℂ)

theorem two_lt_ell (t : ℝ) : 2 < 𝓕.ell t := by
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  have h8 : (8 : ℝ) ≤ 𝓕.B * (|t| + 2) := by nlinarith
  have h2 := Real.log_two_gt_d9
  have e : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) h8
  unfold ell
  linarith

theorem half_lt_re_of_region {c : ℝ} (hc : c ≤ 1) {s : ℂ} (hs : 1 - c / 𝓕.ell s.im ≤ s.re) : 1 / 2 < s.re := by
  have h := 𝓕.two_lt_ell s.im
  have : c / 𝓕.ell s.im < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

end LFam

end GlobalTheory.Hk
