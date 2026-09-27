import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates

/-!
# The critical boundedness horizon of the cubic Möbius packets

Let `K(N) = ⌈((N+1)/4) log(N+1)⌉`.  For all large `N`, uniformly in `0 ≤ δ ≤ 1`,

`2^{5+δ} Σ_{k ≥ K(N)} C(4+δ+k, k) c_k(N)² ≤ C [E(N)² log(N+1)^5 + log(N+1)^3/(N+1)] → 0`,

with `E(x) = exp(-(log x)^{1/3}/108)`.  For `k ≥ 6(N+1)` split the packet at
`H = ⌊(N-3)/2⌋`.  On `(H, N]` the kernel is nondecreasing and `|M(n)| ≪ N E(N)`, so summation by
parts gives `≪ E(N) (N+1)^{-2-δ} e^{-2k/(N+1)}`; on `[1, H]` the telescoping low-edge bound gives
`≤ 16 (N+1)^{-1-δ} e^{-4k/(N+1)}/k`.  The weight `w_k ≤ e^5 k^{4+δ}` and the geometric tails
`Σ_{k ≥ K} k^p x^k ≤ (N+1) K^p x^K` finish the estimate.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.DiscretePacket

open CubicGamma MobiusRenewalPacketEnergy

/-- The critical horizon `K(N) = ⌈((N+1)/4) log(N+1)⌉`. -/
def criticalHorizon (N : ℕ) : ℕ := ⌈((N : ℝ) + 1) / 4 * Real.log ((N : ℝ) + 1)⌉₊

/-- The error profile `E(N)² log(N+1)^5 + log(N+1)^3/(N+1)`. -/
def criticalTailProfile (N : ℕ) : ℝ :=
  mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5 + Real.log ((N : ℝ) + 1) ^ 3 / ((N : ℝ) + 1)

theorem mertensSaving_le_one {x : ℝ} (hx : 1 ≤ x) : mertensSaving x ≤ 1 := by
  unfold mertensSaving deningerMertensSaving
  rw [Real.exp_le_one_iff, neg_nonpos]
  have := Real.log_nonneg hx
  positivity

/-- The two-part packet bound in the critical range `k ≥ 6(N+1)`. -/
theorem abs_cubicPacket_critical_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N k : ℕ, 8 ≤ N → 6 * ((N : ℝ) + 1) ≤ k →
      |cubicPacket δ N k| ≤
        16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k +
        C₁ * mertensSaving N * ((N : ℝ) + 1) ^ (-(2 + δ)) *
          Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
  obtain ⟨CW, hCW, hwin⟩ := exists_abs_abelMertens_window
  refine ⟨2 * CW, by positivity, fun δ hδ0 hδ1 N k hN hk => ?_⟩
  have hN1 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  set H : ℕ := (N - 3) / 2 with hH
  have hH1 : 2 * H + 3 ≤ N := by omega
  have hH2 : N ≤ 2 * H + 4 := by omega
  have hH2' : 2 ≤ H := by omega
  have hHN : H ≤ N := by omega
  have hHr1 : 2 * (H : ℝ) + 3 ≤ N := by exact_mod_cast hH1
  have hHr2 : (N : ℝ) ≤ 2 * H + 4 := by exact_mod_cast hH2
  -- split at `H`
  have hsplit : cubicPacket δ N k = ∑ n ∈ Ioc 0 H, ((μ n : ℤ) : ℝ) * packetKernel δ k n +
      ∑ n ∈ Ioc H N, ((μ n : ℤ) : ℝ) * packetKernel δ k n := by
    unfold cubicPacket
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le H) hHN]
  -- low part
  have hlow : |∑ n ∈ Ioc 0 H, ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
      16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k := by
    have h := abs_sum_low_packetKernel_le hδ0 hδ1 hk1 (le_refl H)
      (show 6 * ((H : ℝ) + 1) ≤ k by linarith)
    refine h.trans ?_
    have hH4 : ((N : ℝ) + 1) / 4 ≤ (H : ℝ) + 2 := by linarith
    have hH5 : (H : ℝ) + 2 ≤ ((N : ℝ) + 1) / 2 := by linarith
    have hp1 : ((H : ℝ) + 2) ^ (-(1 + δ)) ≤ 16 * ((N : ℝ) + 1) ^ (-(1 + δ)) := by
      calc ((H : ℝ) + 2) ^ (-(1 + δ)) ≤ (((N : ℝ) + 1) / 4) ^ (-(1 + δ)) :=
            rpow_neg_le_of_le (by positivity) hH4 (by linarith)
        _ = (4 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (-(1 + δ)) := by
            rw [Real.div_rpow hX.le (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 4 by norm_num),
              Real.rpow_neg hX.le]
            field_simp
        _ ≤ 16 * ((N : ℝ) + 1) ^ (-(1 + δ)) := by
            gcongr
            calc (4 : ℝ) ^ (1 + δ) ≤ 4 ^ ((2 : ℕ) : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
              _ = 16 := by rw [Real.rpow_natCast]; norm_num
    have hp2 : Real.exp (-(2 * k / ((H : ℝ) + 2))) ≤ Real.exp (-(4 * k / ((N : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, div_le_div_iff₀ hX (by positivity)]
      nlinarith
    have hE0 : 0 ≤ Real.exp (-(2 * k / ((H : ℝ) + 2))) := (Real.exp_pos _).le
    have hr0 : 0 ≤ ((H : ℝ) + 2) ^ (-(1 + δ)) := Real.rpow_nonneg (by positivity) _
    calc ((H : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((H : ℝ) + 2))) / k
        ≤ 16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k := by
          gcongr
      _ = _ := rfl
  -- high part
  have hhigh : |∑ n ∈ Ioc H N, ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
      2 * CW * mertensSaving N * ((N : ℝ) + 1) ^ (-(2 + δ)) *
        Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
    have h := abs_sum_Ioc_moebius_mul_le_of_monotone (fun n => packetKernel δ k n)
      (show H < N by omega) (B := CW * N * mertensSaving N)
      (fun n hn1 hn2 => hwin n N (by omega) hn2 (by omega))
      (packetKernel_nonneg k (by push_cast; linarith))
      (fun n hn1 hn2 => packetKernel_nat_le_succ hδ1 (by omega) (by
        have : (2 * n : ℝ) ≤ k := by
          have : (n : ℝ) ≤ N := by exact_mod_cast hn2.le
          linarith
        exact_mod_cast this))
    refine h.trans ?_
    have hg := packetKernel_le (δ := δ) k (show (1 : ℝ) ≤ N by linarith)
    have hNX : (N : ℝ) * ((N : ℝ) + 1) ^ (-(3 + δ)) ≤ ((N : ℝ) + 1) ^ (-(2 + δ)) := by
      have e : ((N : ℝ) + 1) ^ (-(2 + δ)) = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-(3 + δ)) := by
        rw [show -(2 + δ) = 1 + -(3 + δ) by ring, Real.rpow_add hX, Real.rpow_one]
      rw [e]
      gcongr
      linarith
    have hE := mertensSaving_pos (N : ℝ)
    have hex := Real.exp_pos (-(2 * k / ((N : ℝ) + 1)))
    calc 2 * (CW * N * mertensSaving N) * packetKernel δ k N
        ≤ 2 * (CW * N * mertensSaving N) *
            (((N : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((N : ℝ) + 1)))) := by
          gcongr
      _ = 2 * CW * mertensSaving N * ((N : ℝ) * ((N : ℝ) + 1) ^ (-(3 + δ))) *
            Real.exp (-(2 * k / ((N : ℝ) + 1))) := by ring
      _ ≤ _ := by gcongr
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hlow hhigh)

/-- `e^{-λ/(N+1)} e^{p/K} ≤ e^{-2/(N+1)}` for `λ ≥ 4`, `p ≤ 5`, `K ≥ 6(N+1)`. -/
theorem exp_mul_exp_le_contraction {N K : ℕ} {lam p : ℝ} (hlam : 4 ≤ lam)
    (hp : p ≤ 5) (hK : 6 * ((N : ℝ) + 1) ≤ K) :
    Real.exp (-(lam / ((N : ℝ) + 1))) * Real.exp (p / K) ≤ contraction N := by
  have hX : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hK0 : (0 : ℝ) < K := by linarith
  unfold contraction
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : p / K ≤ 2 / ((N : ℝ) + 1) := by
    rw [div_le_div_iff₀ hK0 hX]
    nlinarith
  have h2 : 4 / ((N : ℝ) + 1) ≤ lam / ((N : ℝ) + 1) := div_le_div_of_nonneg_right hlam hX.le
  have h3 : 4 / ((N : ℝ) + 1) = 2 / ((N : ℝ) + 1) + 2 / ((N : ℝ) + 1) := by ring
  linarith

/-- The geometric tail at rate `λ ≥ 4`: `Σ_{k ≥ K} k^p e^{-λk/(N+1)} ≤ (N+1) K^p e^{-λK/(N+1)}`. -/
theorem critical_rpow_tail {N K : ℕ} (hN : 1 ≤ N) {lam p : ℝ} (hlam : 4 ≤ lam) (hp0 : 0 ≤ p)
    (hp : p ≤ 5) (hK : 6 * ((N : ℝ) + 1) ≤ K) :
    Summable (fun j : ℕ => ((j + K : ℕ) : ℝ) ^ p *
        Real.exp (-(lam / ((N : ℝ) + 1))) ^ (j + K)) ∧
      ∑' j : ℕ, ((j + K : ℕ) : ℝ) ^ p * Real.exp (-(lam / ((N : ℝ) + 1))) ^ (j + K) ≤
        (K : ℝ) ^ p * Real.exp (-(lam / ((N : ℝ) + 1))) ^ K * ((N : ℝ) + 1) := by
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    exact_mod_cast this
  have hρ := exp_mul_exp_le_contraction (N := N) hlam hp hK
  have hc1 := contraction_lt_one N
  obtain ⟨hs, hle⟩ := rpow_mul_pow_tail hp0 (Real.exp_pos _) hK1 (hρ.trans_lt hc1)
  refine ⟨hs, hle.trans ?_⟩
  have hpos : 0 < 1 - contraction N := by linarith
  have hden : 1 - contraction N ≤ 1 - Real.exp (-(lam / ((N : ℝ) + 1))) * Real.exp (p / K) := by
    linarith
  have hinv : (1 - Real.exp (-(lam / ((N : ℝ) + 1))) * Real.exp (p / K))⁻¹ ≤ (N : ℝ) + 1 :=
    (inv_anti₀ hpos hden).trans (inv_one_sub_contraction_le hN)
  have h0 : 0 ≤ (K : ℝ) ^ p * Real.exp (-(lam / ((N : ℝ) + 1))) ^ K := by positivity
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hinv h0

/-- `(X^{-(q+δ)})² (Xℓ)^{2q+δ} ≤ ℓ^{2q+1}` for `X, ℓ ≥ 1`, `0 ≤ δ ≤ 1`. -/
theorem sq_rpow_neg_mul_rpow_le {X ℓ q δ : ℝ} (hX : 1 ≤ X) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (X ^ (-(q + δ))) ^ 2 * (X * ℓ) ^ (2 * q + δ) ≤ ℓ ^ (2 * q + 1) := by
  have hX0 : 0 < X := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  rw [Real.mul_rpow hX0.le hℓ0.le, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  have e : X ^ (-(q + δ) * ((2 : ℕ) : ℝ)) * (X ^ (2 * q + δ) * ℓ ^ (2 * q + δ)) =
      X ^ (-δ) * ℓ ^ (2 * q + δ) := by
    rw [← mul_assoc, ← Real.rpow_add hX0]
    congr 2
    push_cast
    ring
  rw [e]
  have h1 : X ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  have h2 : ℓ ^ (2 * q + δ) ≤ ℓ ^ (2 * q + 1) :=
    Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)
  have h3 : 0 ≤ ℓ ^ (2 * q + δ) := Real.rpow_nonneg hℓ0.le _
  calc X ^ (-δ) * ℓ ^ (2 * q + δ) ≤ 1 * ℓ ^ (2 * q + 1) :=
        mul_le_mul h1 h2 h3 zero_le_one
    _ = _ := one_mul _

/-- Weighted packet square in the critical range, as two geometric profiles. -/
theorem weighted_cubicPacket_critical_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N k : ℕ, 8 ≤ N → 6 * ((N : ℝ) + 1) ≤ k →
      binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 ≤
        512 * Real.exp 5 * (((N : ℝ) + 1) ^ (-(1 + δ))) ^ 2 *
            ((k : ℝ) ^ (2 + δ) * Real.exp (-(8 / ((N : ℝ) + 1))) ^ k) +
          2 * Real.exp 5 * C₁ ^ 2 * mertensSaving N ^ 2 * (((N : ℝ) + 1) ^ (-(2 + δ))) ^ 2 *
            ((k : ℝ) ^ (4 + δ) * Real.exp (-(4 / ((N : ℝ) + 1))) ^ k) := by
  obtain ⟨C₁, hC₁, hpk⟩ := abs_cubicPacket_critical_le
  refine ⟨C₁, hC₁, fun δ hδ0 hδ1 N k hN hk6 => ?_⟩
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hc := hpk δ hδ0 hδ1 N k hN hk6
  have ha0 : 0 ≤ 16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k := by
    positivity
  have hb0 : 0 ≤ C₁ * mertensSaving N * ((N : ℝ) + 1) ^ (-(2 + δ)) *
      Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
    have := mertensSaving_pos (N : ℝ)
    positivity
  have hsq : cubicPacket δ N k ^ 2 ≤
      2 * (16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k) ^ 2 +
        2 * (C₁ * mertensSaving N * ((N : ℝ) + 1) ^ (-(2 + δ)) *
          Real.exp (-(2 * k / ((N : ℝ) + 1)))) ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs] at h1
    refine h1.trans ?_
    have := two_mul_le_add_sq (16 * ((N : ℝ) + 1) ^ (-(1 + δ)) *
      Real.exp (-(4 * k / ((N : ℝ) + 1))) / k) (C₁ * mertensSaving N *
        ((N : ℝ) + 1) ^ (-(2 + δ)) * Real.exp (-(2 * k / ((N : ℝ) + 1))))
    nlinarith
  have hw := binomialWeight_le_rpow hδ0 hδ1 hk1
  have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
  have hx₁ : Real.exp (-(4 * k / ((N : ℝ) + 1))) ^ 2 = Real.exp (-(8 / ((N : ℝ) + 1))) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hx₂ : Real.exp (-(2 * k / ((N : ℝ) + 1))) ^ 2 = Real.exp (-(4 / ((N : ℝ) + 1))) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hk42 : (k : ℝ) ^ (4 + δ) = (k : ℝ) ^ (2 + δ) * (k : ℝ) ^ 2 := by
    rw [show (4 : ℝ) + δ = (2 + δ) + ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hk0, Real.rpow_natCast]
  have hkk : (k : ℝ) ^ 2 ≠ 0 := by positivity
  calc binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2
      ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) *
          (2 * (16 * ((N : ℝ) + 1) ^ (-(1 + δ)) * Real.exp (-(4 * k / ((N : ℝ) + 1))) / k) ^ 2 +
            2 * (C₁ * mertensSaving N * ((N : ℝ) + 1) ^ (-(2 + δ)) *
              Real.exp (-(2 * k / ((N : ℝ) + 1)))) ^ 2) :=
        mul_le_mul hw hsq (sq_nonneg _) (hw0.trans hw)
    _ = _ := by
        rw [div_pow, ← hx₁, ← hx₂, hk42]
        field_simp
        ring

/-- The horizon `K(N)` against `X = N+1` and `ℓ = log(N+1)`, once `N+1 ≥ e^{24}`. -/
theorem criticalHorizon_bounds {N : ℕ} (hN : Real.exp 24 ≤ (N : ℝ) + 1) :
    24 ≤ Real.log ((N : ℝ) + 1) ∧
      ((N : ℝ) + 1) / 4 * Real.log ((N : ℝ) + 1) ≤ criticalHorizon N ∧
      (criticalHorizon N : ℝ) ≤ ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) ∧
      6 * ((N : ℝ) + 1) ≤ criticalHorizon N := by
  have hX1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hℓ : 24 ≤ Real.log ((N : ℝ) + 1) := by
    rw [← Real.log_exp 24]
    exact Real.log_le_log (Real.exp_pos _) hN
  have hlow : ((N : ℝ) + 1) / 4 * Real.log ((N : ℝ) + 1) ≤ criticalHorizon N := Nat.le_ceil _
  have hup : (criticalHorizon N : ℝ) < ((N : ℝ) + 1) / 4 * Real.log ((N : ℝ) + 1) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine ⟨hℓ, hlow, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- `e^{-λ/X}^K ≤ e^{-λℓ/4}` when `K ≥ (X/4) ℓ`. -/
theorem exp_pow_horizon_le {X ℓ lam : ℝ} (hX : 0 < X) (hlam : 0 ≤ lam) {K : ℕ}
    (hK : X / 4 * ℓ ≤ K) : Real.exp (-(lam / X)) ^ K ≤ Real.exp (-(lam * ℓ / 4)) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h : lam * ℓ / 4 ≤ lam * K / X := by
    rw [le_div_iff₀ hX]
    nlinarith
  have e : (K : ℝ) * -(lam / X) = -(lam * K / X) := by ring
  rw [e]
  linarith

/-- Bookkeeping for one geometric part of the critical tail. -/
theorem tail_part_le {A B T Kp e X P Q R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he0 : 0 ≤ e) (hX0 : 0 ≤ X) (hQ : 0 ≤ Q)
    (hT : T ≤ Kp * e * X) (hKp : Kp ≤ P) (hBP : B * P ≤ Q) (heX : e * X ≤ R) :
    A * B * T ≤ A * Q * R := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have heX0 : 0 ≤ e * X := mul_nonneg he0 hX0
  calc A * B * T ≤ A * B * (Kp * e * X) := mul_le_mul_of_nonneg_left hT hAB
    _ = A * (B * Kp) * (e * X) := by ring
    _ ≤ A * (B * P) * (e * X) := by gcongr
    _ ≤ A * Q * (e * X) := by gcongr
    _ ≤ A * Q * R := by gcongr

theorem mix_le {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    a * v + b * u ≤ (a + b) * (u + v) := by
  nlinarith [mul_nonneg ha hu, mul_nonneg hb hv]

/-- **Critical horizon (6a).**  For all large `N`, uniformly in `0 ≤ δ ≤ 1`,
`2^{5+δ} Σ_{k ≥ K(N)} w_k c_k² ≤ C [E(N)² log(N+1)^5 + log(N+1)^3/(N+1)]`. -/
theorem cubicPacket_criticalTail_le :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N : ℕ, N₀ ≤ N →
      2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
        cubicPacket δ N (j + criticalHorizon N) ^ 2 ≤ C * criticalTailProfile N := by
  obtain ⟨C₁, hC₁, hpoint⟩ := weighted_cubicPacket_critical_le
  refine ⟨64 * (512 * Real.exp 5 + 2 * Real.exp 5 * C₁ ^ 2), by positivity,
    max 8 ⌈Real.exp 24⌉₊, fun δ hδ0 hδ1 N hN => ?_⟩
  have hN8 : 8 ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := by omega
  have hNe : Real.exp 24 ≤ (N : ℝ) + 1 := by
    have h := Nat.le_ceil (Real.exp 24)
    have : (⌈Real.exp 24⌉₊ : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
    linarith
  obtain ⟨hℓ24, hKlow, hKup, hK6⟩ := criticalHorizon_bounds hNe
  have hX0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hX1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hℓ1 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 1) := by linarith
  -- abbreviations as plain functions of the data
  have hterm0 : ∀ j : ℕ, 0 ≤ binomialWeight (5 + δ) (j + criticalHorizon N) *
      cubicPacket δ N (j + criticalHorizon N) ^ 2 :=
    fun j => mul_nonneg (binomialWeight_nonneg (by linarith) _) (sq_nonneg _)
  have hpt : ∀ j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
      cubicPacket δ N (j + criticalHorizon N) ^ 2 ≤
        512 * Real.exp 5 * (((N : ℝ) + 1) ^ (-(1 + δ))) ^ 2 *
            (((j + criticalHorizon N : ℕ) : ℝ) ^ (2 + δ) *
              Real.exp (-(8 / ((N : ℝ) + 1))) ^ (j + criticalHorizon N)) +
          2 * Real.exp 5 * C₁ ^ 2 * mertensSaving N ^ 2 * (((N : ℝ) + 1) ^ (-(2 + δ))) ^ 2 *
            (((j + criticalHorizon N : ℕ) : ℝ) ^ (4 + δ) *
              Real.exp (-(4 / ((N : ℝ) + 1))) ^ (j + criticalHorizon N)) := by
    intro j
    refine hpoint δ hδ0 hδ1 N _ hN8 ?_
    push_cast
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨hs₁, ht₁⟩ := critical_rpow_tail hN1 (lam := 8) (p := 2 + δ)
    (by norm_num) (by linarith) (by linarith) hK6
  obtain ⟨hs₂, ht₂⟩ := critical_rpow_tail hN1 (lam := 4) (p := 4 + δ)
    (by norm_num) (by linarith) (by linarith) hK6
  have hsumm := Summable.of_nonneg_of_le hterm0 hpt ((hs₁.mul_left _).add (hs₂.mul_left _))
  have htail := hsumm.tsum_le_tsum hpt ((hs₁.mul_left _).add (hs₂.mul_left _))
  rw [(hs₁.mul_left _).tsum_add (hs₂.mul_left _), tsum_mul_left, tsum_mul_left] at htail
  -- the horizon exponentials
  have hx₁ : Real.exp (-(8 / ((N : ℝ) + 1))) ^ criticalHorizon N * ((N : ℝ) + 1) ≤
      1 / ((N : ℝ) + 1) := by
    have h := exp_pow_horizon_le hX0 (lam := 8) (by norm_num) hKlow
    have he : Real.exp (-(8 * Real.log ((N : ℝ) + 1) / 4)) = 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [show 8 * Real.log ((N : ℝ) + 1) / 4 = (2 : ℕ) * Real.log ((N : ℝ) + 1) by
        push_cast; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hX0, one_div]
    rw [he] at h
    calc Real.exp (-(8 / ((N : ℝ) + 1))) ^ criticalHorizon N * ((N : ℝ) + 1)
        ≤ 1 / ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1) := by gcongr
      _ = 1 / ((N : ℝ) + 1) := by field_simp
  have hx₂ : Real.exp (-(4 / ((N : ℝ) + 1))) ^ criticalHorizon N * ((N : ℝ) + 1) ≤ 1 := by
    have h := exp_pow_horizon_le hX0 (lam := 4) (by norm_num) hKlow
    have he : Real.exp (-(4 * Real.log ((N : ℝ) + 1) / 4)) = ((N : ℝ) + 1)⁻¹ := by
      rw [show 4 * Real.log ((N : ℝ) + 1) / 4 = Real.log ((N : ℝ) + 1) by ring, Real.exp_neg,
        Real.exp_log hX0]
    rw [he] at h
    calc Real.exp (-(4 / ((N : ℝ) + 1))) ^ criticalHorizon N * ((N : ℝ) + 1)
        ≤ ((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ hX0.ne'
  have hKp₁ : (criticalHorizon N : ℝ) ^ (2 + δ) ≤
      (((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)) ^ (2 * 1 + δ) := by
    rw [show (2 : ℝ) * 1 + δ = 2 + δ by ring]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hKup (by linarith)
  have hKp₂ : (criticalHorizon N : ℝ) ^ (4 + δ) ≤
      (((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)) ^ (2 * 2 + δ) := by
    rw [show (2 : ℝ) * 2 + δ = 4 + δ by ring]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hKup (by linarith)
  have hq₁ := sq_rpow_neg_mul_rpow_le (q := 1) hX1 hℓ1 hδ0 hδ1
  have hq₂ := sq_rpow_neg_mul_rpow_le (q := 2) hX1 hℓ1 hδ0 hδ1
  rw [show 2 * (1 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq₁
  rw [show 2 * (2 : ℝ) + 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq₂
  have hE0 := mertensSaving_pos (N : ℝ)
  have hpart₁ := tail_part_le (A := 512 * Real.exp 5) (by positivity) (sq_nonneg _)
    (by positivity) hX0.le (by positivity) ht₁ hKp₁ hq₁
    hx₁
  have hpart₂ := tail_part_le (A := 2 * Real.exp 5 * C₁ ^ 2 * mertensSaving N ^ 2)
    (by positivity) (sq_nonneg _) (by positivity)
    hX0.le (by positivity) ht₂ hKp₂ hq₂ hx₂
  have h2le : (2 : ℝ) ^ (5 + δ) ≤ 64 := by
    calc (2 : ℝ) ^ (5 + δ) ≤ 2 ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hmix := mix_le (a := 512 * Real.exp 5) (b := 2 * Real.exp 5 * C₁ ^ 2)
    (u := mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5)
    (v := Real.log ((N : ℝ) + 1) ^ 3 / ((N : ℝ) + 1)) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have hsum0 : 0 ≤ ∑' j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
      cubicPacket δ N (j + criticalHorizon N) ^ 2 := tsum_nonneg hterm0
  calc 2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
        cubicPacket δ N (j + criticalHorizon N) ^ 2
      ≤ 64 * (512 * Real.exp 5 * Real.log ((N : ℝ) + 1) ^ 3 * (1 / ((N : ℝ) + 1)) +
          2 * Real.exp 5 * C₁ ^ 2 * mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5 * 1) :=
        mul_le_mul h2le (htail.trans (add_le_add hpart₁ hpart₂)) hsum0 (by norm_num)
    _ = 64 * (512 * Real.exp 5 * (Real.log ((N : ℝ) + 1) ^ 3 / ((N : ℝ) + 1)) +
          2 * Real.exp 5 * C₁ ^ 2 * (mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5)) := by
        ring
    _ ≤ 64 * ((512 * Real.exp 5 + 2 * Real.exp 5 * C₁ ^ 2) *
          (mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5 +
            Real.log ((N : ℝ) + 1) ^ 3 / ((N : ℝ) + 1))) := by gcongr
    _ = _ := by unfold criticalTailProfile; ring

/-- The profile `E(N)² log(N+1)^5 + log(N+1)^3/(N+1)` tends to zero. -/
theorem tendsto_criticalTailProfile : Tendsto criticalTailProfile atTop (𝓝 0) := by
  have hX : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- second summand
  have h2 : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) ^ 3 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp hX
    refine h.congr fun N => ?_
    simp
  -- first summand, squeezed by `32 E(N) (log N)^5`
  have h1 : Tendsto (fun N : ℕ => mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5)
      atTop (𝓝 0) := by
    have hbase := ((tendsto_mertensSaving_mul_log_pow 5).comp tendsto_natCast_atTop_atTop).const_mul
      32
    rw [mul_zero] at hbase
    refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (sq_nonneg _)
      (pow_nonneg (Real.log_nonneg (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)) 5)) ?_ hbase
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hE0 := mertensSaving_pos (N : ℝ)
    have hE1 := mertensSaving_le_one (show (1 : ℝ) ≤ N by linarith)
    have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log N := by
      rw [← Real.log_rpow (by linarith), show ((N : ℝ) ^ (2 : ℝ)) = (N : ℝ) ^ 2 by
        rw [← Real.rpow_natCast]; norm_num]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have hl0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hp : Real.log ((N : ℝ) + 1) ^ 5 ≤ 32 * Real.log N ^ 5 := by
      calc Real.log ((N : ℝ) + 1) ^ 5 ≤ (2 * Real.log N) ^ 5 := pow_le_pow_left₀ hl0 hlog 5
        _ = 32 * Real.log N ^ 5 := by ring
    simp only [Function.comp_apply]
    calc mertensSaving N ^ 2 * Real.log ((N : ℝ) + 1) ^ 5
        ≤ mertensSaving N * Real.log ((N : ℝ) + 1) ^ 5 := by
          gcongr
          nlinarith
      _ ≤ mertensSaving N * (32 * Real.log N ^ 5) := by gcongr
      _ = 32 * (mertensSaving N * Real.log N ^ 5) := by ring
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-- The tail beyond the critical horizon vanishes, uniformly in `0 ≤ δ ≤ 1`. -/
theorem cubicPacket_criticalTail_small :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N : ℕ, N₀ ≤ N →
      2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
        cubicPacket δ N (j + criticalHorizon N) ^ 2 ≤ ε := by
  intro ε hε
  obtain ⟨C, hC, N₀, h⟩ := cubicPacket_criticalTail_le
  have hev := (tendsto_order.mp tendsto_criticalTailProfile).2 (ε / C) (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine ⟨max N₀ N₁, fun δ hδ0 hδ1 N hN => ?_⟩
  refine (h δ hδ0 hδ1 N (le_of_max_le_left hN)).trans ?_
  have := hN₁ N (le_of_max_le_right hN)
  calc C * criticalTailProfile N ≤ C * (ε / C) := by gcongr
    _ = ε := by field_simp

end RHTower.DiscretePacket
