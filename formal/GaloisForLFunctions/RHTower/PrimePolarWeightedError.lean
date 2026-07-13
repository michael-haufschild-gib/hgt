import GaloisForLFunctions.RHTower.MovingTentGridLipschitz
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone

/-!
# Absolute convergence of the weighted moving-tent error series

The outer-summation convergence of `prime-polar-moving-tent-divisor-tomography` §3 (eqs. 18–19).  The
weighted error series `∑_k (Λ(k)/√k)·E_{k,L}(s)` — whose sum is the holomorphic correction `H_L(s)` —
converges absolutely on `Re s > 1/2`.

Each `‖E_{k,L}(s)‖` is bounded by `C'·k^{-Re s}` (from `E_kL_bound` with the natural cutoff
`N = ⌈k·e^{2L}⌉`, using `‖k^{1-s}‖ = k^{1-Re s}` and `⌈k·e^{2L}⌉ ≤ k(e^{2L}+1)`), so the weighted term
is bounded by `C'·Λ(k)·k^{-(Re s + 1/2)}`, whose sum is the absolutely convergent von Mangoldt series
`vonMangoldt_shifted_summable` at `Re s > 1/2`.  The Weierstrass comparison then gives summability.
-/

open HTGeometry ArithmeticFunction

namespace RHTower

/-- **The weighted moving-tent error series converges absolutely** (§3, eqs. 18–19).  For `Re s > 1/2`,
`∑_k (Λ(k)/√k)·‖E_{k,L}(s)‖ < ∞`, where `E_{k,L}(s) = ∑_{j<⌈k e^{2L}⌉} τ_L(log(j/k))·j^{-s} −
k^{1-s}·I_L(s)` is the source Dirichlet-series error at scale `k`.  This is the majorant that makes the
correction `H_L(s) = ∑_k (Λ(k)/√k)·E_{k,L}(s)` well defined and holomorphic on `Re s > 1/2`. -/
theorem weighted_E_summable (L : ℝ) (hL : 0 ≤ L) (s : ℂ) (hs : s ≠ 1) (hσ : 1 / 2 < s.re) :
    Summable (fun k : ℕ => (Λ k / Real.sqrt k) *
      ‖(∑ j ∈ Finset.range (Nat.ceil ((k : ℝ) * Real.exp (2 * L))),
          (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s))
        - (k : ℂ) ^ (1 - s) * (rectangularWindowAmplitude L (s - 1)) ^ 2‖) := by
  obtain ⟨C, hC0, hCb⟩ := E_kL_bound L hL s hs
  set C' : ℝ := C * (Real.exp (2 * L) + 1) / 2 with hC'
  have hmaj : Summable (fun k : ℕ => C' * ((Λ k) * (k : ℝ) ^ (-(s.re + 1 / 2)))) :=
    (vonMangoldt_shifted_summable s.re hσ).mul_left C'
  refine Summable.of_nonneg_of_le (fun k =>
    mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)) (norm_nonneg _))
    (fun k => ?_) hmaj
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; simp
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    set Nof : ℕ := Nat.ceil ((k : ℝ) * Real.exp (2 * L)) with hNof
    have hNle : Real.exp (2 * L) ≤ (Nof : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hkR, mul_comm]; exact Nat.le_ceil _
    have hNub : (Nof : ℝ) ≤ (k : ℝ) * (Real.exp (2 * L) + 1) := by
      have h1 : (Nof : ℝ) < (k : ℝ) * Real.exp (2 * L) + 1 := Nat.ceil_lt_add_one (by positivity)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith [Real.exp_pos (2 * L)]
    have hb := hCb k Nof hk hNle
    rw [Complex.norm_natCast_cpow_of_pos hk, Complex.sub_re, Complex.one_re] at hb
    have hpow : (k : ℝ) ^ (1 - s.re) * (k : ℝ) / (k : ℝ) ^ 2 = (k : ℝ) ^ (-s.re) := by
      rw [show (1 : ℝ) - s.re = -s.re + 1 by ring, Real.rpow_add hkR, Real.rpow_one]
      field_simp
    have hEnorm : ‖(∑ j ∈ Finset.range Nof,
        (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s))
        - (k : ℂ) ^ (1 - s) * (rectangularWindowAmplitude L (s - 1)) ^ 2‖
        ≤ C' * (k : ℝ) ^ (-s.re) := by
      refine hb.trans ?_
      have hstep : (k : ℝ) ^ (1 - s.re) * ((Nof : ℝ) * C / (2 * (k : ℝ) ^ 2))
          ≤ (k : ℝ) ^ (1 - s.re) * ((k : ℝ) * (Real.exp (2 * L) + 1) * C / (2 * (k : ℝ) ^ 2)) := by
        gcongr
      refine hstep.trans (le_of_eq ?_)
      rw [hC', show (k : ℝ) ^ (1 - s.re) * ((k : ℝ) * (Real.exp (2 * L) + 1) * C / (2 * (k : ℝ) ^ 2))
          = C * (Real.exp (2 * L) + 1) / 2 * ((k : ℝ) ^ (1 - s.re) * (k : ℝ) / (k : ℝ) ^ 2) by ring,
        hpow]
    calc (Λ k / Real.sqrt k) * ‖_‖
        ≤ (Λ k / Real.sqrt k) * (C' * (k : ℝ) ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left hEnorm
            (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))
      _ = C' * ((Λ k) * (k : ℝ) ^ (-(s.re + 1 / 2))) := by
          rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkR.le,
            show -(s.re + 1 / 2) = -(1 / 2) + (-s.re) by ring, Real.rpow_add hkR]
          ring

end RHTower
