import GaloisForLFunctions.RHTower.ZetaWeightedTracePrime

/-!
# The weighted trace of the zeta Gram matrix

For grid weights `0 ≤ W_k ≤ 1` the diagonal entries split as `G_kk = G^μ_kk + G^Π_kk + G^P_kk` (Zeta23's
`GentryA_diag_eq`), and

* `|Σ_k W_k G^μ_kk − 2πaL Σ_k W_k μ(τ_k)| ≤ d (K∫φ̂²|r| + 10∫φ̂²r²)/T`   (`abs_weighted_mu_part_sub_le`),
* `|Σ_k W_k G^Π_kk| ≤ d ((6√X/T) 2πaL + (12√X/T²)∫φ̂²r²)`   (`abs_weighted_Pi_part_le`),

from the per-point bounds `mu_part_bound`, `Pi_part_bound`.  Together with the prime part
(`abs_weighted_P_part_le_band`) this gives the weighted trace (`abs_weighted_trace_sub_le`):

`|Σ_k W_k G_kk − 2πaL Σ_k W_k μ(τ_k)| ≤ d·E_μ + d·E_Π + |Σ_k W_k G^P_kk|`.
-/

open MeasureTheory Real Finset
open Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem tau_ge_T (hp : 0 < p.L) (k : ℕ) : p.T ≤ p.tau k := by
  unfold Setting.tau Setting.h
  have : 0 ≤ (k : ℝ) * (2 * π / p.L) := by positivity
  push_cast
  linarith

/-- **The weighted μ-part of the trace.** -/
theorem abs_weighted_mu_part_sub_le (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hT : 2 ≤ p.T) {W : ℕ → ℝ} (hW0 : ∀ k, 0 ≤ W k) (hW1 : ∀ k, W k ≤ 1) :
    |∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
        - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, W k * Zeta23.mu (p.tau k)|
      ≤ p.d * ((K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / p.T) := by
  have hL := hF.L_pos
  set C : ℝ := K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2) with hC
  have hC0 : 0 ≤ C := by
    have h1 : 0 ≤ ∫ r, F.phiHat r ^ 2 * |r| := integral_nonneg fun r => by positivity
    have h2 : 0 ≤ ∫ r, F.phiHat r ^ 2 * r ^ 2 := integral_nonneg fun r => by positivity
    positivity
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range p.d, |W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
        - 2 * π * F.a * p.L * (W k * Zeta23.mu (p.tau k))|
      ≤ ∑ k ∈ Finset.range p.d, C / p.T := by
        refine Finset.sum_le_sum fun k _ => ?_
        have htk := tau_ge_T hL k
        have hb := mu_part_bound hΓ hF hK (t := p.tau k) (by linarith)
        rw [show W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
            - 2 * π * F.a * p.L * (W k * Zeta23.mu (p.tau k))
            = W k * ((∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
              - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)) by ring, abs_mul, abs_of_nonneg (hW0 k)]
        calc W k * |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
              - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)|
            ≤ 1 * (C / p.tau k) := mul_le_mul (hW1 k) hb (abs_nonneg _) zero_le_one
          _ ≤ C / p.T := by
            rw [one_mul]
            exact div_le_div_of_nonneg_left hC0 (by linarith) htk
    _ = p.d * (C / p.T) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The weighted Π-part of the trace.** -/
theorem abs_weighted_Pi_part_le (hF : LocalHypsCore cϱ p F) (hT : 2 ≤ p.T) {W : ℕ → ℝ}
    (hW0 : ∀ k, 0 ≤ W k) (hW1 : ∀ k, W k ≤ 1) :
    |∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))|
      ≤ p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2) := by
  have hL := hF.L_pos
  have ha : 0 ≤ F.a := by
    have h := hF.phiHat_sq_integral
    have h0 : 0 ≤ ∫ r, F.phiHat r ^ 2 := integral_nonneg fun r => sq_nonneg _
    rw [h] at h0
    by_contra hneg; push Not at hneg
    have : 2 * π * F.a * p.L < 0 := by
      have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity : (0:ℝ) < 2 * π) hneg) hL
      linarith
    linarith
  have hI : 0 ≤ ∫ r, F.phiHat r ^ 2 * r ^ 2 := integral_nonneg fun r => by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range p.d, |W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))|
      ≤ ∑ k ∈ Finset.range p.d, ((6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have htk := tau_ge_T hL k
        have hb := Pi_part_bound hF (t := p.tau k) (by linarith)
        rw [abs_mul, abs_of_nonneg (hW0 k)]
        refine (mul_le_mul (hW1 k) hb (abs_nonneg _) zero_le_one).trans ?_
        rw [one_mul]
        have hT0 : 0 < p.T := by linarith
        have h1 : 6 * Real.sqrt p.X / p.tau k ≤ 6 * Real.sqrt p.X / p.T :=
          div_le_div_of_nonneg_left (by positivity) hT0 htk
        have h2 : 12 * Real.sqrt p.X / p.tau k ^ 2 ≤ 12 * Real.sqrt p.X / p.T ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hT0.le htk 2)
        have h3 : 0 ≤ 2 * π * F.a * p.L := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_right h1 h3) (mul_le_mul_of_nonneg_right h2 hI)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The weighted trace.**  `Σ_k W_k G_kk` differs from `2πaL Σ_k W_k μ(τ_k)` by the weighted μ-, Π- and P-errors. -/
theorem abs_weighted_trace_sub_le (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hT : 2 ≤ p.T) {W : ℕ → ℝ} (hW0 : ∀ k, 0 ≤ W k) (hW1 : ∀ k, W k ≤ 1) :
    |∑ k ∈ Finset.range p.d, W k * GentryA p F k k
        - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, W k * Zeta23.mu (p.tau k)|
      ≤ p.d * ((K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / p.T)
        + p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2)
        + |∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))| := by
  have hL := hF.L_pos
  have hdec : ∑ k ∈ Finset.range p.d, W k * GentryA p F k k
      = ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
        + ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have htk := tau_ge_T hL k
    rw [GentryA_diag_eq hΓ hF k (by linarith)]
    ring
  have h1 := abs_weighted_mu_part_sub_le hΓ hF hK0 hK hT hW0 hW1
  have h2 := abs_weighted_Pi_part_le hF hT hW0 hW1
  rw [hdec]
  set A := ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
  set B := ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
  set C := ∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))
  set D := 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, W k * Zeta23.mu (p.tau k)
  have e : A + B + C - D = (A - D) + B + C := by ring
  rw [e]
  have t1 := abs_add_le (A - D) B
  have t2 := abs_add_le (A - D + B) C
  linarith

/-- **Weight deficit.**  If `0 ≤ W_k` and `W_k ≥ 1 − η` on a set `S` of indices, then
`Σ_{k<d} (1 − W_k) ≤ #(range d ∖ S) + η d`. -/
theorem sum_one_sub_le_of_bulk {W : ℕ → ℝ} {η : ℝ} (hη : 0 ≤ η) {d : ℕ}
    (S : Finset ℕ) (hS : ∀ k ∈ S, 1 - η ≤ W k) (hW0 : ∀ k, 0 ≤ W k) :
    ∑ k ∈ Finset.range d, (1 - W k) ≤ ((Finset.range d \ S).card : ℝ) + η * d := by
  have hsplit := Finset.sum_sdiff (s₁ := Finset.range d ∩ S) (s₂ := Finset.range d)
    (f := fun k => 1 - W k) Finset.inter_subset_left
  rw [← hsplit]
  have h1 : ∑ k ∈ Finset.range d \ (Finset.range d ∩ S), (1 - W k) ≤ ((Finset.range d \ S).card : ℝ) := by
    rw [Finset.sdiff_inter_self_left]
    calc ∑ k ∈ Finset.range d \ S, (1 - W k) ≤ ∑ k ∈ Finset.range d \ S, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by linarith [hW0 k]
      _ = _ := by simp
  have h2 : ∑ k ∈ Finset.range d ∩ S, (1 - W k) ≤ η * d := by
    calc ∑ k ∈ Finset.range d ∩ S, (1 - W k) ≤ ∑ k ∈ Finset.range d ∩ S, η :=
          Finset.sum_le_sum fun k hk => by linarith [hS k (Finset.mem_inter.1 hk).2]
      _ = η * (Finset.range d ∩ S).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ η * d := by
          apply mul_le_mul_of_nonneg_left _ hη
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := Finset.range d) (s₂ := S))
          rw [Finset.card_range] at this
          exact_mod_cast this
  linarith

namespace FejerWeight

variable {b s₀ s₁ : ℝ}

/-- The Jackson window is uniformly close to one at distance `D` inside the interval. -/
theorem one_sub_le_jacksonWindow_of_dist (hb : 0 < b) {D s : ℝ} (hD : 0 < D) (h0 : s₀ + D ≤ s)
    (h1 : s + D ≤ s₁) :
    1 - (jacksonMass b)⁻¹ * (32 / (3 * b ^ 2 * D ^ 3)) ≤ jacksonWindow b s₀ s₁ s := by
  have hk := jacksonMass_pos hb
  have hW := one_sub_le_jacksonWindow hb (s₀ := s₀) (s₁ := s₁) (s := s) (by linarith) (by linarith)
  have ha : 16 / (3 * b ^ 2 * (s₁ - s) ^ 3) ≤ 16 / (3 * b ^ 2 * D ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le (by linarith) 3) (by positivity))
  have hb' : 16 / (3 * b ^ 2 * (s - s₀) ^ 3) ≤ 16 / (3 * b ^ 2 * D ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le (by linarith) 3) (by positivity))
  have hsum := add_le_add ha hb'
  have e : 16 / (3 * b ^ 2 * D ^ 3) + 16 / (3 * b ^ 2 * D ^ 3) = 32 / (3 * b ^ 2 * D ^ 3) := by ring
  rw [e] at hsum
  have := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hk.le)
  linarith

end FejerWeight

end RHTower
