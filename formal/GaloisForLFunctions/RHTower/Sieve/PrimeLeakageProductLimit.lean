import GaloisForLFunctions.RHTower.Sieve.ExpProfileRegularity

/-!
# The all-prime Weyl leakage product

Compressing the Weyl-transported natural-cone state back through the point/complement polarization
at every prime `p ≤ N` costs the factor `√(1 - L_p)`, so the total compression coefficient is

`∏_{p ≤ N} √(1 - L_p(f(log p / log N)))`.

This file proves that it converges to the squarefree Hellinger–Fock kernel

`exp( -½ ∫₀¹ (e^{f t} - 1)² dt/t )`.

Everything needed is already proved: `1 - L_p > 0` for every prime, so the product is an exponential
of a prime sum; that sum splits into the two vanishing remainders and the prime-profile sum; and the
prime-profile sum converges to the integral.  What is left here is the algebra of the split and one
application of continuity of `exp`.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

theorem sqrt_eq_exp_half_log_primeLeakageProductLimit {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem one_sub_primeLeakage_pos {p : ℕ} (hp : 2 ≤ p) {z F : ℝ} (hz : z ≤ F) :
    0 < 1 - primeLeakage p z := by
  have hLθ := primeLeakage_le_theta hp hz
  have hθ := theta_lt_one F
  linarith

/-- The Lipschitz constant of a weight vanishing at the origin is nonnegative. -/
theorem lipschitz_const_nonneg {f : ℝ → ℝ} {Lf : ℝ}
    (hflip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) : 0 ≤ Lf := by
  have h := hflip 1 0
  have habs : (0 : ℝ) ≤ |f 1 - f 0| := abs_nonneg _
  simp only [abs_one, sub_zero, mul_one] at h
  nlinarith [habs, h]

/-! ## The logarithm of the leakage product splits -/

theorem log_one_sub_primeLeakage_eq (f : ℝ → ℝ) {N p : ℕ} (hp : 2 ≤ p) :
    Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))
      = leakageLogDefectTerm f N p - leakageExpansionTerm f N p
        - expProfile f (Real.log p / Real.log N) / (p : ℝ) := by
  rw [leakageLogDefectTerm, if_pos hp, leakageExpansionTerm, if_pos hp, expProfile]
  ring

theorem sum_log_one_sub_primeLeakage (f : ℝ → ℝ) (N : ℕ) :
    ∑ p ∈ Nat.primesLE N,
        Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))
      = (∑ p ∈ Nat.primesLE N, leakageLogDefectTerm f N p)
        - (∑ p ∈ Nat.primesLE N, leakageExpansionTerm f N p)
        - primeProfileSum (expProfile f) N := by
  rw [primeProfileSum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact log_one_sub_primeLeakage_eq f (Nat.mem_primesLE.1 hp).2.two_le

/-- The leakage product is the exponential of half the logarithmic prime sum. -/
theorem prod_sqrt_one_sub_primeLeakage {f : ℝ → ℝ} {F : ℝ} (hfb : ∀ t, |f t| ≤ F) (N : ℕ) :
    ∏ p ∈ Nat.primesLE N,
        Real.sqrt (1 - primeLeakage p (f (Real.log p / Real.log N)))
      = Real.exp ((∑ p ∈ Nat.primesLE N,
          Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))) / 2) := by
  have hterm : ∀ p ∈ Nat.primesLE N,
      Real.sqrt (1 - primeLeakage p (f (Real.log p / Real.log N)))
        = Real.exp (Real.log (1 - primeLeakage p (f (Real.log p / Real.log N))) / 2) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.1 hp).2.two_le
    have hzF : f (Real.log p / Real.log N) ≤ F :=
      le_trans (le_abs_self _) (hfb (Real.log p / Real.log N))
    exact sqrt_eq_exp_half_log_primeLeakageProductLimit (one_sub_primeLeakage_pos hp2 hzF)
  rw [Finset.prod_congr rfl hterm, ← Real.exp_sum, Finset.sum_div]

/-! ## The limit -/

/-- **Equation (14).**  The all-prime Weyl compression coefficient converges to the squarefree
Hellinger–Fock kernel. -/
theorem tendsto_prod_sqrt_one_sub_primeLeakage {f : ℝ → ℝ} {F Lf : ℝ}
    (hf : Continuous f) (hf0 : f 0 = 0) (hfb : ∀ t, |f t| ≤ F)
    (hflip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesLE N,
        Real.sqrt (1 - primeLeakage p (f (Real.log p / Real.log N))))
      atTop
      (𝓝 (Real.exp (-((∫ t in (0 : ℝ)..1, expProfile f t / t) / 2)))) := by
  have hFnn : (0 : ℝ) ≤ F := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hLf := lipschitz_const_nonneg hflip
  have hE1 : (1 : ℝ) ≤ Real.exp F := Real.one_le_exp hFnn
  -- the prime-profile sum converges
  have hprofile : Tendsto (fun N : ℕ => primeProfileSum (expProfile f) N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, expProfile f t / t)) := by
    refine tendsto_primeProfileSum
      (L := 2 * (Real.exp F - 1) * Real.exp F * Lf)
      (C := max ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2)) ?_ ?_
      (continuous_expProfile hf) (fun s t => expProfile_lipschitz hfb hflip s t)
      (fun t ht => expProfile_le_linear hfb hf0 hflip ht)
    · have hexp : (0 : ℝ) < Real.exp F := Real.exp_pos F
      have : (0 : ℝ) ≤ Real.exp F - 1 := by linarith
      positivity
    · exact le_trans (sq_nonneg _) (le_max_left _ _)
  -- the two remainders vanish
  have hexpand := tendsto_sum_leakageExpansion hf hf0 hfb
  have hdefect := tendsto_sum_leakageLogDefect hf hf0 hfb
  -- the logarithmic prime sum converges
  have hlogsum : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N,
      Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))) atTop
      (𝓝 (-(∫ t in (0 : ℝ)..1, expProfile f t / t))) := by
    have hcomb := (hdefect.sub hexpand).sub hprofile
    have hval : (0 : ℝ) - 0 - (∫ t in (0 : ℝ)..1, expProfile f t / t)
        = -(∫ t in (0 : ℝ)..1, expProfile f t / t) := by ring
    rw [hval] at hcomb
    refine hcomb.congr ?_
    intro N
    exact (sum_log_one_sub_primeLeakage f N).symm
  -- exponentiate
  have hhalf := hlogsum.div_const 2
  have hexp := (Real.continuous_exp.tendsto
    (-(∫ t in (0 : ℝ)..1, expProfile f t / t) / 2)).comp hhalf
  simp only [Function.comp_def] at hexp
  have hval2 : Real.exp (-(∫ t in (0 : ℝ)..1, expProfile f t / t) / 2)
      = Real.exp (-((∫ t in (0 : ℝ)..1, expProfile f t / t) / 2)) := by
    congr 1
    ring
  rw [hval2] at hexp
  refine hexp.congr ?_
  intro N
  exact (prod_sqrt_one_sub_primeLeakage hfb N).symm

end

end RHTower.Sieve
