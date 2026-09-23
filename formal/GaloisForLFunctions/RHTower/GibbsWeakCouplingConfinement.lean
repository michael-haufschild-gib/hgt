import Mathlib
import GaloisForLFunctions.RHTower.GibbsClusterRepulsion

/-!
# Weak-coupling confinement of the parity cluster

At weak coupling the entire zero set of the squarefree Gibbs gas is confined to a small
disk about the parity point, for **every** number of primes.  The mechanism is a single
perturbation estimate: the free gas is `w^k` in the shifted variable `w = z + 1`, and the
Boltzmann corrections are controlled by `|e^{-u} - 1| ≤ u`, so

  `‖P_S(-1+w, x) - w^k‖ ≤ x·m·(2 + ‖w‖)^k`,   `m = ∏ S`.

Since `t ↦ t/(2+t)` increases, `x·m < (ρ/(2+ρ))^k` already forces every zero into
`‖z+1‖ < ρ`; with `ρ = 1` this gives Hurwitz stability for all `k`.  The confinement
radius is sharp: the quantitative totient law bounds the parity current by
`φ(m)x + x²∏(1+p²)`, so the cluster cannot be smaller than order `(φ(m)x)^{1/k}`.

Neither Rouché's theorem nor the fundamental theorem of algebra is used.
-/

namespace RHTower.GibbsGas

open Real

/-- The gas at complex activity. -/
noncomputable def gibbsDiagC (S : Finset ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  ∑ T ∈ S.powerset, z ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) : ℝ) : ℂ)

/-- At real activity the complex gas is the real gas. -/
theorem gibbsDiagC_ofReal (S : Finset ℕ) (x t : ℝ) :
    gibbsDiagC S x ((t : ℝ) : ℂ) = ((gibbsDiag S x t : ℝ) : ℂ) := by
  rw [gibbsDiagC, gibbsDiag, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  push_cast
  ring

/-- **The free gas in the shifted variable**: at zero coupling the parity point is a
`k`-fold zero, `∑_{T ⊆ S} (w-1)^{|T|} = w^k`. -/
theorem sum_sub_one_pow_card (S : Finset ℕ) (w : ℂ) :
    ∑ T ∈ S.powerset, (w - 1) ^ T.card = w ^ S.card := by
  have h := Finset.prod_add (fun _ : ℕ => w - 1) (fun _ : ℕ => (1 : ℂ)) S
  have hw : (w - 1) + (1 : ℂ) = w := by ring
  simp only [hw, Finset.prod_const, one_pow, mul_one] at h
  exact h.symm

/-- **The perturbation estimate.**  The gas differs from the free gas `w^k` by at most
`x·m·(2+‖w‖)^k` in the shifted variable. -/
theorem norm_gibbsDiagC_shift_sub_pow_le (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p)
    (x : ℝ) (hx : 0 ≤ x) (w : ℂ) :
    ‖gibbsDiagC S x (-1 + w) - w ^ S.card‖
      ≤ x * ((2 + ‖w‖) ^ S.card * ∏ p ∈ S, (p : ℝ)) := by
  classical
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hsub : gibbsDiagC S x (-1 + w) - w ^ S.card
      = ∑ T ∈ S.powerset, (w - 1) ^ T.card
          * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 : ℝ) : ℂ) := by
    rw [gibbsDiagC, ← sum_sub_one_pow_card S w, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    push_cast
    ring
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ T ∈ S.powerset,
      ‖(w - 1) ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 : ℝ) : ℂ)‖
        ≤ x * ∏ p ∈ T, ((1 + ‖w‖) * (p : ℝ)) := by
    intro T _
    have hTpos : (0 : ℝ) ≤ ∏ p ∈ T, (p : ℝ) :=
      Finset.prod_nonneg fun p _ => Nat.cast_nonneg p
    have hy : 0 ≤ x * ∏ p ∈ T, (p : ℝ) := mul_nonneg hx hTpos
    have hexp : |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1| ≤ x * ∏ p ∈ T, (p : ℝ) := by
      have h1 : Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      have h2 : 1 - (x * ∏ p ∈ T, (p : ℝ))
          ≤ Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) := by
        have h3 := Real.add_one_le_exp (-(x * ∏ p ∈ T, (p : ℝ)))
        linarith
      rw [abs_le]
      constructor <;> linarith
    have hnorm : ‖(w - 1) ^ T.card‖ ≤ (1 + ‖w‖) ^ T.card := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖w‖ := by rw [norm_one]; ring
    have hprod : ∏ p ∈ T, ((1 + ‖w‖) * (p : ℝ))
        = (1 + ‖w‖) ^ T.card * ∏ p ∈ T, (p : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hprod]
    have h3 : (0 : ℝ) ≤ (1 + ‖w‖) ^ T.card := by positivity
    calc ‖(w - 1) ^ T.card‖ * |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1|
        ≤ (1 + ‖w‖) ^ T.card * (x * ∏ p ∈ T, (p : ℝ)) :=
          mul_le_mul hnorm hexp (abs_nonneg _) h3
      _ = x * ((1 + ‖w‖) ^ T.card * ∏ p ∈ T, (p : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hexpand : ∑ T ∈ S.powerset, ∏ p ∈ T, ((1 + ‖w‖) * (p : ℝ))
      = ∏ p ∈ S, ((1 + ‖w‖) * (p : ℝ) + 1) := by
    have h := Finset.prod_add (fun p : ℕ => (1 + ‖w‖) * (p : ℝ))
      (fun _ : ℕ => (1 : ℝ)) S
    simp only [Finset.prod_const, one_pow, mul_one] at h
    exact h.symm
  rw [hexpand]
  have hle : ∏ p ∈ S, ((1 + ‖w‖) * (p : ℝ) + 1)
      ≤ ∏ p ∈ S, ((2 + ‖w‖) * (p : ℝ)) := by
    refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
    nlinarith [hw0, hp1]
  refine le_trans (mul_le_mul_of_nonneg_left hle hx) ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **Confinement of the zero set, for every `k`.**  Weak coupling forces every zero of
the gas into the open disk of radius `ρ` about the parity point. -/
theorem gibbsDiagC_ne_zero_of_le_norm (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p)
    (x : ℝ) (hx : 0 ≤ x) {ρ : ℝ} (hρ : 0 < ρ)
    (hweak : x * (∏ p ∈ S, (p : ℝ)) < (ρ / (2 + ρ)) ^ S.card)
    (z : ℂ) (hz : ρ ≤ ‖z + 1‖) :
    gibbsDiagC S x z ≠ 0 := by
  intro hzero
  have hzw : z = -1 + (z + 1) := by ring
  have hb := norm_gibbsDiagC_shift_sub_pow_le S hS x hx (z + 1)
  rw [← hzw, hzero, zero_sub, norm_neg, norm_pow] at hb
  set n : ℝ := ‖z + 1‖ with hn
  have hn0 : 0 < n := lt_of_lt_of_le hρ hz
  have h2n : (0 : ℝ) < 2 + n := by linarith
  have h2ρ : (0 : ℝ) < 2 + ρ := by linarith
  have hpow : (n / (2 + n)) ^ S.card ≤ x * ∏ p ∈ S, (p : ℝ) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [hb]
  have hmono : ρ / (2 + ρ) ≤ n / (2 + n) := by
    rw [div_le_div_iff₀ h2ρ h2n]
    nlinarith [hz]
  have hchain := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ρ / (2 + ρ)) hmono S.card
  linarith [hweak, hpow, hchain]

/-- **Weak-coupling Hurwitz stability, for every `k`.**  If `x·m < 3^{-k}` then every zero
of the gas lies in the disk `‖z+1‖ < 1`, hence strictly in the left half-plane. -/
theorem gibbs_weak_coupling_stable (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p)
    (x : ℝ) (hx : 0 ≤ x)
    (hweak : x * (∏ p ∈ S, (p : ℝ)) < (1 / 3 : ℝ) ^ S.card)
    (z : ℂ) (hzero : gibbsDiagC S x z = 0) :
    ‖z + 1‖ < 1 ∧ z.re < 0 := by
  have hlt : ‖z + 1‖ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    refine gibbsDiagC_ne_zero_of_le_norm S hS x hx one_pos ?_ z hcon hzero
    have h13 : (1 : ℝ) / (2 + 1) = 1 / 3 := by norm_num
    rw [h13]
    exact hweak
  refine ⟨hlt, ?_⟩
  have hsq : Complex.normSq (z + 1) < 1 := by
    have h := Complex.normSq_eq_norm_sq (z + 1)
    nlinarith [norm_nonneg (z + 1), hlt, h]
  rw [Complex.normSq_apply] at hsq
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at hsq
  nlinarith [sq_nonneg z.im, sq_nonneg z.re, hsq]

/-- **Quantitative grading.**  A zero confined to distance `ρ` from the parity point is at
distance at least `2 − ρ` from the opposite point, so it contributes a cancellation factor
at most `ρ/(2−ρ)`. -/
theorem norm_one_sub_ge_of_norm_one_add_le (ζ : ℂ) {ρ : ℝ} (h : ‖1 + ζ‖ ≤ ρ) :
    2 - ρ ≤ ‖1 - ζ‖ := by
  have hrw : (1 : ℂ) - ζ = 2 - (1 + ζ) := by ring
  have h2 : ‖(2 : ℂ)‖ - ‖1 + ζ‖ ≤ ‖2 - (1 + ζ)‖ := norm_sub_norm_le _ _
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rw [hrw]
  rw [hnorm2] at h2
  linarith

/-- **The quantitative totient law.**  The finite parity current is `(−1)^{k+1}·φ(m)·x` up
to an error of order `x²`, so the confinement radius of the cluster is sharp. -/
theorem abs_gibbs_current_sub_totient_le (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p)
    (hk : 1 ≤ S.card) (x : ℝ) (hx : 0 ≤ x)
    (hxE : x * (∏ p ∈ S, (p : ℝ)) ≤ 1) :
    |gibbsDiag S x (-1) - (-1) ^ (S.card + 1) * (∏ p ∈ S, ((p : ℝ) - 1)) * x|
      ≤ x ^ (2 : ℕ) * ∏ p ∈ S, (1 + (p : ℝ) ^ (2 : ℕ)) := by
  classical
  have hEnonneg : (0 : ℝ) ≤ ∏ p ∈ S, (p : ℝ) :=
    Finset.prod_nonneg fun p _ => Nat.cast_nonneg p
  -- the two exact sums
  have hzero : ∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card = 0 := by
    have h := Finset.prod_add (fun _ : ℕ => (-1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) S
    simp only [Finset.prod_const, one_pow, mul_one] at h
    rw [← h]
    have hz : ((-1 : ℝ) + 1) = 0 := by norm_num
    rw [hz, zero_pow (by omega : S.card ≠ 0)]
  have hlin : ∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card * (∏ p ∈ T, (p : ℝ))
      = ∏ p ∈ S, (1 - (p : ℝ)) := by
    have h := Finset.prod_add (fun p : ℕ => (-1 : ℝ) * (p : ℝ)) (fun _ : ℕ => (1 : ℝ)) S
    simp only [Finset.prod_const, one_pow, mul_one] at h
    have hL : ∀ p : ℕ, (-1 : ℝ) * (p : ℝ) + 1 = 1 - (p : ℝ) := by intro p; ring
    simp only [hL] at h
    rw [h]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  -- the pointwise second-order estimate
  have hterm : ∀ T ∈ S.powerset,
      |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 + x * ∏ p ∈ T, (p : ℝ)|
        ≤ x ^ (2 : ℕ) * ∏ p ∈ T, (p : ℝ) ^ (2 : ℕ) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hTpos : (0 : ℝ) ≤ ∏ p ∈ T, (p : ℝ) :=
      Finset.prod_nonneg fun p _ => Nat.cast_nonneg p
    have hge1 : (1 : ℝ) ≤ ∏ p ∈ S \ T, (p : ℝ) := by
      calc (1 : ℝ) = ∏ _p ∈ S \ T, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ p ∈ S \ T, (p : ℝ) :=
            Finset.prod_le_prod (fun p _ => zero_le_one) (fun p hp => by
              have hps := hS p (Finset.mem_sdiff.mp hp).1
              exact_mod_cast hps)
    have hTE : ∏ p ∈ T, (p : ℝ) ≤ ∏ p ∈ S, (p : ℝ) := by
      rw [← Finset.prod_sdiff hT]
      nlinarith [hge1, hTpos]
    have hy1 : x * ∏ p ∈ T, (p : ℝ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hTE hx) hxE
    have hy0 : 0 ≤ x * ∏ p ∈ T, (p : ℝ) := mul_nonneg hx hTpos
    have habs : |(-(x * ∏ p ∈ T, (p : ℝ)))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg hy0]
      exact hy1
    have hb := Real.abs_exp_sub_one_sub_id_le habs
    have hsq : ∏ p ∈ T, (p : ℝ) ^ (2 : ℕ) = (∏ p ∈ T, (p : ℝ)) ^ (2 : ℕ) := by
      rw [← Finset.prod_pow]
    rw [hsq]
    calc |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 + x * ∏ p ∈ T, (p : ℝ)|
        = |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 - (-(x * ∏ p ∈ T, (p : ℝ)))| := by
          ring_nf
      _ ≤ (-(x * ∏ p ∈ T, (p : ℝ))) ^ (2 : ℕ) := hb
      _ = x ^ (2 : ℕ) * (∏ p ∈ T, (p : ℝ)) ^ (2 : ℕ) := by ring
  -- assemble
  have hsplit : gibbsDiag S x (-1) - (-1) ^ (S.card + 1) * (∏ p ∈ S, ((p : ℝ) - 1)) * x
      = ∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card
          * (Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 + x * ∏ p ∈ T, (p : ℝ)) := by
    have hexp : ∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card
        * (Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 + x * ∏ p ∈ T, (p : ℝ))
        = gibbsDiag S x (-1) - (∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card)
          + x * ∑ T ∈ S.powerset, ((-1 : ℝ)) ^ T.card * (∏ p ∈ T, (p : ℝ)) := by
      rw [gibbsDiag, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    rw [hexp, hzero, hlin, sub_zero]
    have hsign : ∏ p ∈ S, (1 - (p : ℝ))
        = (-1) ^ S.card * ∏ p ∈ S, ((p : ℝ) - 1) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => by ring
    rw [hsign]
    have hpar : ((-1 : ℝ)) ^ (S.card + 1) = -((-1 : ℝ)) ^ S.card := by
      rw [pow_succ]
      ring
    rw [hpar]
    ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb2 : ∀ T ∈ S.powerset,
      |((-1 : ℝ)) ^ T.card
        * (Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 + x * ∏ p ∈ T, (p : ℝ))|
        ≤ x ^ (2 : ℕ) * ∏ p ∈ T, (p : ℝ) ^ (2 : ℕ) := by
    intro T hT
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hterm T hT
  refine le_trans (Finset.sum_le_sum hb2) ?_
  rw [← Finset.mul_sum]
  have hexpand : ∑ T ∈ S.powerset, ∏ p ∈ T, (p : ℝ) ^ (2 : ℕ)
      = ∏ p ∈ S, ((p : ℝ) ^ (2 : ℕ) + 1) := by
    have h := Finset.prod_add (fun p : ℕ => (p : ℝ) ^ (2 : ℕ)) (fun _ : ℕ => (1 : ℝ)) S
    simp only [Finset.prod_const, one_pow, mul_one] at h
    exact h.symm
  rw [hexpand]
  have hcomm : ∏ p ∈ S, ((p : ℝ) ^ (2 : ℕ) + 1) = ∏ p ∈ S, (1 + (p : ℝ) ^ (2 : ℕ)) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [hcomm]

end RHTower.GibbsGas
