import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The oscillating smooth power is paid exactly at the zeros of ζ

For `0 < ε ≤ 1/2` and `t ∈ ℝ` let `c_{ε,t}(d) = d^{-ε} cos(t log d)`, the real part of `d^{ρ−1}`,
`ρ = 1 − ε + it`. Its receiver is bounded **if and only if** `ζ(1 − ε + it) = 0`
(`receiverBounded_oscillatingSmoothPower_iff`). Hence the Riemann hypothesis is the statement that
no oscillating smooth power below half damping is paid
(`riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower`), and at half damping the
paid frequencies are exactly the ordinates of the zeros on the critical line.

* **The prefix asymptotic.** By the Dirichlet hyperbola method at `x = √n`,
  `Σ_{d ≤ n} d^{ρ−1} ⌊n/d⌋ = ζ(2 − ρ) n + ζ(ρ) n^ρ/ρ + O(n^{(1−ε)/2})`
  (`norm_cpowFloorSum_sub_le`), so the centred prefix of `c_{ε,t}` is
  `A(n) = Re(ζ(ρ) n^ρ/ρ) + O(n^{(1−ε)/2})` (`abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le`).
  The three main terms of order `n^{(1+Re ρ)/2}` cancel to `n^{ρ/2}(√n − ⌊√n⌋)/ρ`, and every
  partial sum is controlled by the rate `‖Σ_{d ≤ x} d^{-w} − x^{1−w}/(1−w) − ζ(w)‖ ≤ C_w x^{-Re w}`
  (`norm_cpowPartialSum_sub_le`).
* **Sufficiency.** At a zero the main term vanishes and `A(n) = O(n^{(1−ε)/2})` has finite pronic
  energy, since `(1 − ε)/2 < 1/2`.
* **Necessity.** Away from a zero the main term `n^{1−ε} Re(a n^{it})`, `a = ζ(ρ)/ρ`, carries at
  least the logarithmic energy `Σ_n Re(a n^{it})²/(2n) = (|a|²/4) H_T + O(1)`: the oscillating part
  `Re(a² Σ n^{-(1−2it)})` stays bounded for `t ≠ 0`.
-/

open Finset Filter Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Partial sums of `d^{-w}` with a rate -/

/-- The complex partial sums `P_w(N) = Σ_{d ≤ N} d^{-w}`. -/
def cpowPartialSum (w : ℂ) (N : ℕ) : ℂ := ∑ d ∈ Icc 1 N, ((d : ℝ) : ℂ) ^ (-w)

/-- `u ↦ u^{1−w}` has derivative `(1 − w) u^{-w}`. -/
theorem hasDerivAt_ofReal_cpow_one_sub {w : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (1 - w)) ((1 - w) * ((x : ℝ) : ℂ) ^ (-w)) x := by
  have h := hasDerivAt_ofReal_cpow_neg (w := w - 1) hx
  have e1 : -(w - 1) = 1 - w := by ring
  rw [e1, show (1 : ℂ) - w - 1 = -w by ring] at h
  exact h

/-- On `[a, b]`, `0 < a`: `‖b^{-w} − u^{-w}‖ ≤ ‖w‖ a^{-1-Re w} (b − u)`. -/
theorem norm_ofReal_cpow_neg_sub_le {w : ℂ} (hw0 : 0 ≤ w.re) {a b u : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hub : u ≤ b) :
    ‖((b : ℝ) : ℂ) ^ (-w) - ((u : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-(1 + w.re)) * (b - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hau
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ (-w)) (f' := fun y => -w * ((y : ℝ) : ℂ) ^ (-w - 1))
    (a := u) (b := b) (C := ‖w‖ * a ^ (-(1 + w.re)))
    (fun y hy => (hasDerivAt_ofReal_cpow_neg (lt_of_lt_of_le hu0 hy.1)).hasDerivWithinAt)
    (fun y hy => by
      have hy0 : 0 < y := lt_of_lt_of_le hu0 hy.1
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hre : (-w - 1).re = -(1 + w.re) := by simp only [sub_re, neg_re, one_re]; ring
      rw [hre]
      exact Real.rpow_le_rpow_of_nonpos ha (hau.trans hy.1) (by linarith))
    b ⟨hub, le_rfl⟩
  exact h

/-- **One step of the strip remainder**: `‖g(M+1) − g(M)‖ ≤ ‖w‖ M^{-1-Re w}`, where
`g(N) = Σ_{d ≤ N} d^{-w} − N^{1−w}/(1−w)`. -/
theorem norm_czetaStripRemainder_succ_sub_le {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w ≠ 1) {M : ℕ}
    (hM : 1 ≤ M) :
    ‖czetaStripRemainder w (M + 1) - czetaStripRemainder w M‖ ≤ ‖w‖ * (M : ℝ) ^ (-(1 + w.re)) := by
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set a : ℂ := (((M : ℝ) + 1 : ℝ) : ℂ) ^ (-w) with ha
  set ψ : ℝ → ℂ := fun u => ((u : ℝ) : ℂ) ^ (1 - w) / (1 - w) - ((u : ℝ) : ℂ) * a with hψ
  have hderiv : ∀ u ∈ Set.Icc (M : ℝ) (M + 1), HasDerivWithinAt ψ
      ((1 - w) * ((u : ℝ) : ℂ) ^ (-w) / (1 - w) - ((1 : ℝ) : ℂ) * a) (Set.Icc (M : ℝ) (M + 1)) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hM0 hu.1
    have h1 := (hasDerivAt_ofReal_cpow_one_sub (w := w) hu0).div_const (1 - w)
    have h2 := ((hasDerivAt_id u).ofReal_comp).mul_const a
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico (M : ℝ) (M + 1),
      ‖(1 - w) * ((u : ℝ) : ℂ) ^ (-w) / (1 - w) - ((1 : ℝ) : ℂ) * a‖ ≤
        ‖w‖ * (M : ℝ) ^ (-(1 + w.re)) := by
    intro u hu
    rw [mul_div_cancel_left₀ _ h1w, Complex.ofReal_one, one_mul, norm_sub_rev]
    calc ‖a - ((u : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * (M : ℝ) ^ (-(1 + w.re)) * ((M : ℝ) + 1 - u) :=
          norm_ofReal_cpow_neg_sub_le hw0 hM0 hu.1 hu.2.le
      _ ≤ ‖w‖ * (M : ℝ) ^ (-(1 + w.re)) * 1 := by
          gcongr; linarith [hu.1]
      _ = _ := mul_one _
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound ((M : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  have hstep : czetaStripRemainder w (M + 1) - czetaStripRemainder w M =
      -(ψ ((M : ℝ) + 1) - ψ M) := by
    simp only [czetaStripRemainder, hψ, ha, sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
    push_cast
    ring
  rw [hstep, norm_neg]
  calc _ ≤ ‖w‖ * (M : ℝ) ^ (-(1 + w.re)) * ((M : ℝ) + 1 - M) := hmv
    _ = _ := by ring

/-- **The rate of the strip remainder**: `‖g(N) − ζ(w)‖ ≤ ‖w‖ (1 + 1/Re w) N^{-Re w}` for
`Re w > 0`, `w ≠ 1`. -/
theorem norm_czetaStripRemainder_sub_le {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖czetaStripRemainder w N - riemannZeta w‖ ≤ ‖w‖ * ((1 + 1 / w.re) * (N : ℝ) ^ (-w.re)) := by
  have htend : Tendsto (fun T : ℕ => czetaStripRemainder w T) atTop (𝓝 (riemannZeta w)) :=
    RHTower.tendsto_sum_cpow_sub_pow hw0 hw1
  have hbound : ∀ T : ℕ, N ≤ T → ‖czetaStripRemainder w N - czetaStripRemainder w T‖ ≤
      ‖w‖ * ∑ M ∈ Ico N T, (M : ℝ) ^ (-(1 + w.re)) := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base => simp
    | succ T hNT ih =>
      have h := norm_czetaStripRemainder_succ_sub_le hw0.le hw1 (hN.trans hNT)
      rw [sum_Ico_succ_top hNT, mul_add]
      calc ‖czetaStripRemainder w N - czetaStripRemainder w (T + 1)‖
          ≤ ‖czetaStripRemainder w N - czetaStripRemainder w T‖ +
              ‖czetaStripRemainder w T - czetaStripRemainder w (T + 1)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := add_le_add ih (by rw [norm_sub_rev]; exact h)
  have hsum : ∀ T : ℕ, ∑ M ∈ Ico N T, (M : ℝ) ^ (-(1 + w.re)) ≤
      (1 + 1 / w.re) * (N : ℝ) ^ (-w.re) := fun T =>
    (sum_le_sum_of_subset_of_nonneg (fun M hM => by
        simp only [mem_Ico, mem_Icc] at hM ⊢; omega)
      fun M _ _ => Real.rpow_nonneg (Nat.cast_nonneg M) _).trans
      (sum_Icc_rpow_neg_one_sub_le hw0 hN T)
  have hlim : Tendsto (fun T : ℕ => ‖czetaStripRemainder w N - czetaStripRemainder w T‖) atTop
      (𝓝 ‖czetaStripRemainder w N - riemannZeta w‖) :=
    ((tendsto_const_nhds (x := czetaStripRemainder w N)).sub htend).norm
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun T hT => ?_⟩)
  exact (hbound T hT).trans (mul_le_mul_of_nonneg_left (hsum T) (norm_nonneg _))

/-- The rate constant `C_w = (‖w‖(1 + 1/Re w) + 1) 2^{Re w}`. -/
def partialSumRate (w : ℂ) : ℝ := (‖w‖ * (1 + 1 / w.re) + 1) * (2 : ℝ) ^ w.re

theorem partialSumRate_nonneg {w : ℂ} (hw0 : 0 < w.re) : 0 ≤ partialSumRate w := by
  unfold partialSumRate
  have : 0 ≤ 1 + 1 / w.re := by have := one_div_pos.mpr hw0; linarith
  positivity

/-- **The partial sums of `d^{-w}` at a real cutoff.** For `Re w > 0`, `w ≠ 1`, `N ≥ 1` and
`N ≤ x ≤ N + 1`: `‖P_w(N) − x^{1−w}/(1−w) − ζ(w)‖ ≤ C_w x^{-Re w}`. -/
theorem norm_cpowPartialSum_sub_le {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) {N : ℕ} (hN : 1 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) :
    ‖cpowPartialSum w N - ((x : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w‖ ≤
      partialSumRate w * x ^ (-w.re) := by
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hNx
  set σ := w.re with hσ
  -- the real-cutoff correction
  have hcorr : ‖((x : ℝ) : ℂ) ^ (1 - w) / (1 - w) - ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w)‖ ≤
      (N : ℝ) ^ (-σ) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ (1 - w) / (1 - w))
      (f' := fun y => (1 - w) * ((y : ℝ) : ℂ) ^ (-w) / (1 - w)) (a := (N : ℝ)) (b := x)
      (C := (N : ℝ) ^ (-σ))
      (fun y hy => ((hasDerivAt_ofReal_cpow_one_sub (lt_of_lt_of_le hN0 hy.1)).div_const
        (1 - w)).hasDerivWithinAt)
      (fun y hy => by
        have hy0 : 0 < y := lt_of_lt_of_le hN0 hy.1
        rw [mul_div_cancel_left₀ _ h1w, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.neg_re]
        exact Real.rpow_le_rpow_of_nonpos hN0 hy.1 (by linarith))
      x ⟨hNx, le_rfl⟩
    calc _ ≤ (N : ℝ) ^ (-σ) * (x - N) := h
      _ ≤ (N : ℝ) ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hN0.le _)
      _ = _ := mul_one _
  -- `N^{-σ} ≤ 2^σ x^{-σ}`
  have hNx2 : (N : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ σ * x ^ (-σ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hhalf : x / 2 ≤ N := by linarith
    calc (N : ℝ) ^ (-σ) ≤ (x / 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
      _ = (2 : ℝ) ^ σ * x ^ (-σ) := by
          rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ]
          field_simp
  have hrate := norm_czetaStripRemainder_sub_le hw0 hw1 hN
  have heq : cpowPartialSum w N - ((x : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w =
      (czetaStripRemainder w N - riemannZeta w) -
        (((x : ℝ) : ℂ) ^ (1 - w) / (1 - w) - ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w)) := by
    simp only [czetaStripRemainder, cpowPartialSum]; ring
  rw [heq]
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  have h2 : 0 ≤ (2 : ℝ) ^ σ := by positivity
  calc _ ≤ ‖czetaStripRemainder w N - riemannZeta w‖ +
        ‖((x : ℝ) : ℂ) ^ (1 - w) / (1 - w) - ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ * ((1 + 1 / σ) * (N : ℝ) ^ (-σ)) + (N : ℝ) ^ (-σ) := add_le_add hrate hcorr
    _ = (‖w‖ * (1 + 1 / σ) + 1) * (N : ℝ) ^ (-σ) := by ring
    _ ≤ (‖w‖ * (1 + 1 / σ) + 1) * ((2 : ℝ) ^ σ * x ^ (-σ)) := by
        refine mul_le_mul_of_nonneg_left hNx2 ?_
        have : 0 ≤ 1 + 1 / σ := by have := one_div_pos.mpr hw0; linarith
        positivity
    _ = partialSumRate w * x ^ (-σ) := by rw [partialSumRate, ← hσ]; ring

/-! ### The hyperbola method for `d^{ρ−1}` -/

/-- **The Dirichlet hyperbola identity**, complex form: with `s = ⌊√n⌋`,
`Σ_{d ≤ n} f(d)⌊n/d⌋ = Σ_{d ≤ s} f(d)⌊n/d⌋ + Σ_{m ≤ s} (F(⌊n/m⌋) − F(s))`. -/
theorem sum_Icc_mul_div_eq_hyperbola_complex (f : ℕ → ℂ) (n : ℕ) :
    ∑ d ∈ Icc 1 n, f d * ((n / d : ℕ) : ℂ) =
      ∑ d ∈ Icc 1 (Nat.sqrt n), f d * ((n / d : ℕ) : ℂ) +
        ∑ m ∈ Icc 1 (Nat.sqrt n),
          (∑ d ∈ Icc 1 (n / m), f d - ∑ d ∈ Icc 1 (Nat.sqrt n), f d) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  rw [← hs]
  have hss : s * s ≤ n := by rw [hs]; exact Nat.sqrt_le n
  have hlt : n < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt n
  have hsn : s ≤ n := by rw [hs]; exact Nat.sqrt_le_self n
  have hsplit : Icc 1 n = Icc 1 s ∪ Ioc s n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 s) (Ioc s n) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  congr 1
  have hcount : ∀ d ∈ Ioc s n, f d * ((n / d : ℕ) : ℂ) =
      ∑ m ∈ Icc 1 s, if m * d ≤ n then f d else 0 := by
    intro d hd
    rw [mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hds : n / d ≤ s := by
      have h1 : n < (s + 1) * d := lt_of_lt_of_le hlt (Nat.mul_le_mul_left (s + 1) (by omega))
      have h2 : n / d < s + 1 := (Nat.div_lt_iff_lt_mul hd0).mpr h1
      omega
    have hfil : (Icc 1 s).filter (fun m => m * d ≤ n) = Icc 1 (n / d) := by
      ext m
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, (Nat.le_div_iff_mul_le hd0).mpr h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hds⟩, (Nat.le_div_iff_mul_le hd0).mp h2⟩
    rw [← sum_filter, sum_const, nsmul_eq_mul, hfil, Nat.card_Icc, Nat.add_sub_cancel, mul_comm]
  rw [sum_congr rfl hcount, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_Icc] at hm
  have hm0 : 0 < m := hm.1
  rw [← sum_filter]
  have hfil : (Ioc s n).filter (fun d => m * d ≤ n) = Ioc s (n / m) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hm0).mpr (by rw [Nat.mul_comm]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le hm0).mp h2
      exact ⟨⟨h1, h2.trans (Nat.div_le_self n m)⟩, by rw [Nat.mul_comm]; exact h3⟩
  rw [hfil]
  have hsm : s ≤ n / m :=
    (Nat.le_div_iff_mul_le hm0).mpr ((Nat.mul_le_mul_left s hm.2).trans hss)
  have hunion : Icc 1 (n / m) = Icc 1 s ∪ Ioc s (n / m) := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [hunion, sum_union (disjoint_left.mpr fun d h1 h2 => by
    simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  ring

/-- `(a/b)^z = a^z b^{-z}` for positive reals. -/
theorem ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    (((a / b : ℝ)) : ℂ) ^ z = ((a : ℝ) : ℂ) ^ z * ((b : ℝ) : ℂ) ^ (-z) := by
  have hab : 0 < a / b := div_pos ha hb
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hab.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log hab.le, ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
    Real.log_div ha.ne' hb.ne']
  congr 1
  push_cast
  ring

/-- The weighted floor sum `D_ρ(n) = Σ_{d ≤ n} d^{ρ−1} ⌊n/d⌋`. -/
def cpowFloorSum (ρ : ℂ) (n : ℕ) : ℂ := ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * ((n / d : ℕ) : ℂ)

/-- The rate constant of the floor-sum asymptotic. -/
def floorSumRate (ρ : ℂ) : ℝ :=
  1 / ‖ρ‖ + partialSumRate (2 - ρ) + partialSumRate ρ / ‖ρ‖ + 2 * partialSumRate (1 - ρ) +
    (1 + 1 / ρ.re)

/-- **The floor-sum asymptotic.** For `0 < Re ρ < 1` and `n ≥ 1`,
`‖D_ρ(n) − ζ(2 − ρ) n − ζ(ρ) n^ρ/ρ‖ ≤ K_ρ (√n)^{Re ρ}`. -/
theorem norm_cpowFloorSum_sub_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖cpowFloorSum ρ n - riemannZeta (2 - ρ) * n - riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ‖ ≤
      floorSumRate ρ * Real.sqrt n ^ ρ.re := by
  have hρ0' : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1' : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl 1 hρ1
  set σ := ρ.re with hσ
  have hnρ : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0'
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.sqrt_pos.mpr hn
  have hss : s * s ≤ n := by rw [hs]; exact Nat.sqrt_le n
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (n : ℝ) := ⟨_, rfl⟩
  rw [← hr]
  have hr2 : r ^ 2 = n := by rw [hr]; exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hsr : (s : ℝ) ≤ r := by rw [hs, hr]; exact Real.nat_sqrt_le_real_sqrt
  have hrs : r < s + 1 := by rw [hs, hr]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hr0 : 0 < r := lt_of_lt_of_le hs0 hsr
  have hr1 : (1 : ℝ) ≤ r := le_trans (by exact_mod_cast hs1) hsr
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  -- the exponents
  have hw1re : 0 < (1 - ρ).re := by simp only [sub_re, one_re]; linarith
  have hw1ne : (1 : ℂ) - ρ ≠ 1 := fun h => hρ0' (by linear_combination -h)
  have hw2re : 0 < (2 - ρ).re := by simp only [sub_re]; norm_num; linarith
  have hw2ne : (2 : ℂ) - ρ ≠ 1 := fun h => hρ1' (by linear_combination -h)
  set C₁ := partialSumRate (1 - ρ) with hC₁
  set C₂ := partialSumRate (2 - ρ) with hC₂
  set C₃ := partialSumRate ρ with hC₃
  have hC₁0 : 0 ≤ C₁ := partialSumRate_nonneg hw1re
  have hC₂0 : 0 ≤ C₂ := partialSumRate_nonneg hw2re
  have hC₃0 : 0 ≤ C₃ := partialSumRate_nonneg hρ0
  -- `F(N) = P_{1−ρ}(N)`
  have hF : ∀ N : ℕ, ∑ d ∈ Icc 1 N, ((d : ℝ) : ℂ) ^ (ρ - 1) = cpowPartialSum (1 - ρ) N :=
    fun N => by simp only [cpowPartialSum, neg_sub]
  -- the hyperbola split
  have hhyp := sum_Icc_mul_div_eq_hyperbola_complex (fun d => ((d : ℝ) : ℂ) ^ (ρ - 1)) n
  rw [← hs] at hhyp
  simp only [hF] at hhyp
  rw [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hhyp
  -- the head below `s`
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℂ, E1 = ∑ d ∈ Icc 1 s,
      ((d : ℝ) : ℂ) ^ (ρ - 1) * ((((n : ℝ) / d - ((n / d : ℕ) : ℝ)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hhead : ∑ d ∈ Icc 1 s, ((d : ℝ) : ℂ) ^ (ρ - 1) * ((n / d : ℕ) : ℂ) =
      (n : ℂ) * cpowPartialSum (2 - ρ) s - E1 := by
    rw [hE1, cpowPartialSum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hpow : ((d : ℝ) : ℂ) ^ (-(2 - ρ)) = ((d : ℝ) : ℂ) ^ (ρ - 1) / ((d : ℝ) : ℂ) := by
      rw [show -(2 - ρ) = ρ - 1 - 1 by ring, Complex.cpow_sub _ _ hdC, Complex.cpow_one]
    rw [hpow]
    push_cast
    field_simp
    ring
  have hE1b : ‖E1‖ ≤ (1 + 1 / σ) * r ^ σ := by
    rw [hE1]
    have hterm : ∀ d ∈ Icc 1 s, ‖((d : ℝ) : ℂ) ^ (ρ - 1) *
        ((((n : ℝ) / d - ((n / d : ℕ) : ℝ)) : ℝ) : ℂ)‖ ≤ (d : ℝ) ^ (-(1 - σ)) := by
      intro d hd
      have hd1 := (mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd0, Complex.norm_real, Real.norm_eq_abs]
      have h1 := abs_natDiv_sub_div_le n d hd1
      rw [abs_sub_comm] at h1
      have hre : (ρ - 1).re = -(1 - σ) := by simp only [sub_re, one_re, hσ]; ring
      rw [hre]
      calc (d : ℝ) ^ (-(1 - σ)) * |(n : ℝ) / d - ((n / d : ℕ) : ℝ)| ≤ (d : ℝ) ^ (-(1 - σ)) * 1 :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hd0.le _)
        _ = _ := mul_one _
    have hhead := RHTower.sum_rpow_neg_head_le (c := 1 - σ) (by linarith) (by linarith) s
    have hsσ : (s : ℝ) ^ σ ≤ r ^ σ := Real.rpow_le_rpow hs0.le hsr hρ0.le
    have h1σ : 1 ≤ r ^ σ := Real.one_le_rpow hr1 hρ0.le
    calc _ ≤ ∑ d ∈ Icc 1 s, ‖((d : ℝ) : ℂ) ^ (ρ - 1) *
          ((((n : ℝ) / d - ((n / d : ℕ) : ℝ)) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-(1 - σ)) := sum_le_sum hterm
      _ ≤ 1 + (s : ℝ) ^ (1 - (1 - σ)) / (1 - (1 - σ)) := hhead
      _ = 1 + (s : ℝ) ^ σ / σ := by rw [show 1 - (1 - σ) = σ by ring]
      _ ≤ (1 + 1 / σ) * r ^ σ := by
          rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((s : ℝ) ^ σ)]
          have : 1 / σ * (s : ℝ) ^ σ ≤ 1 / σ * r ^ σ :=
            mul_le_mul_of_nonneg_left hsσ (by positivity)
          linarith
  -- the expansions at the cutoff `r = √n`
  have hrs1 : r ≤ (s : ℝ) + 1 := hrs.le
  obtain ⟨e₂, he₂⟩ : ∃ e : ℂ, e = cpowPartialSum (2 - ρ) s - ((r : ℝ) : ℂ) ^ (ρ - 1) / (ρ - 1) -
      riemannZeta (2 - ρ) := ⟨_, rfl⟩
  have he₂b : ‖e₂‖ ≤ C₂ * r ^ (-(2 - σ)) := by
    have h := norm_cpowPartialSum_sub_le hw2re hw2ne hs1 hsr hrs1
    rw [show (1 : ℂ) - (2 - ρ) = ρ - 1 by ring] at h
    have hre : (2 - ρ).re = 2 - σ := by simp only [sub_re, hσ]; norm_num
    rw [hre] at h
    rw [he₂]; exact h
  obtain ⟨e₃, he₃⟩ : ∃ e : ℂ, e = cpowPartialSum ρ s - ((r : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ) -
      riemannZeta ρ := ⟨_, rfl⟩
  have he₃b : ‖e₃‖ ≤ C₃ * r ^ (-σ) := by
    rw [he₃]; exact norm_cpowPartialSum_sub_le hρ0 hρ1' hs1 hsr hrs1
  obtain ⟨e₄, he₄⟩ : ∃ e : ℂ, e = cpowPartialSum (1 - ρ) s - ((r : ℝ) : ℂ) ^ ρ / ρ -
      riemannZeta (1 - ρ) := ⟨_, rfl⟩
  have hre1 : (1 - ρ).re = 1 - σ := by simp only [sub_re, one_re, hσ]
  have he₄b : ‖e₄‖ ≤ C₁ * r ^ (-(1 - σ)) := by
    have h := norm_cpowPartialSum_sub_le hw1re hw1ne hs1 hsr hrs1
    rw [show (1 : ℂ) - (1 - ρ) = ρ by ring, hre1] at h
    rw [he₄]; exact h
  -- the long moduli
  obtain ⟨E3, hE3⟩ : ∃ E3 : ℂ, E3 = ∑ m ∈ Icc 1 s, (cpowPartialSum (1 - ρ) (n / m) -
      ((((n : ℝ) / m : ℝ)) : ℂ) ^ ρ / ρ - riemannZeta (1 - ρ)) := ⟨_, rfl⟩
  have hrσ : r * r ^ (-(1 - σ)) = r ^ σ := by
    rw [mul_comm, ← Real.rpow_add_one hr0.ne']; congr 1; ring
  have hE3b : ‖E3‖ ≤ C₁ * r ^ σ := by
    rw [hE3]
    have hterm : ∀ m ∈ Icc 1 s, ‖cpowPartialSum (1 - ρ) (n / m) -
        ((((n : ℝ) / m : ℝ)) : ℂ) ^ ρ / ρ - riemannZeta (1 - ρ)‖ ≤ C₁ * r ^ (-(1 - σ)) := by
      intro m hm
      obtain ⟨hm1, hms⟩ := mem_Icc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hsN : s ≤ n / m :=
        (Nat.le_div_iff_mul_le hm1).mpr ((Nat.mul_le_mul_left s hms).trans hss)
      have hN1 : 1 ≤ n / m := hs1.trans hsN
      have hle : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
      have hlt : (n : ℝ) / m ≤ ((n / m : ℕ) : ℝ) + 1 := by
        have := (abs_le.mp (abs_natDiv_sub_div_le n m hm1)).1
        linarith
      have h := norm_cpowPartialSum_sub_le hw1re hw1ne hN1 hle hlt
      rw [show (1 : ℂ) - (1 - ρ) = ρ by ring, hre1] at h
      have hxr : r ≤ (n : ℝ) / m := by
        rw [le_div_iff₀ hm0]
        have hmr : (m : ℝ) ≤ r := le_trans (by exact_mod_cast hms) hsr
        calc r * m ≤ r * r := mul_le_mul_of_nonneg_left hmr hr0.le
          _ = n := by rw [← sq, hr2]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC₁0)
      exact Real.rpow_le_rpow_of_nonpos hr0 hxr (by linarith)
    calc _ ≤ ∑ m ∈ Icc 1 s, ‖cpowPartialSum (1 - ρ) (n / m) -
          ((((n : ℝ) / m : ℝ)) : ℂ) ^ ρ / ρ - riemannZeta (1 - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Icc 1 s, C₁ * r ^ (-(1 - σ)) := sum_le_sum hterm
      _ = (s : ℝ) * (C₁ * r ^ (-(1 - σ))) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ r * (C₁ * r ^ (-(1 - σ))) :=
          mul_le_mul_of_nonneg_right hsr (mul_nonneg hC₁0 (Real.rpow_nonneg hr0.le _))
      _ = C₁ * r ^ σ := by rw [mul_left_comm, hrσ]
  have hsumF : ∑ m ∈ Icc 1 s, cpowPartialSum (1 - ρ) (n / m) =
      E3 + ((n : ℝ) : ℂ) ^ ρ / ρ * cpowPartialSum ρ s + (s : ℂ) * riemannZeta (1 - ρ) := by
    have hx : ∀ m ∈ Icc 1 s, ((((n : ℝ) / m : ℝ)) : ℂ) ^ ρ / ρ =
        ((n : ℝ) : ℂ) ^ ρ / ρ * ((m : ℝ) : ℂ) ^ (-ρ) := by
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [ofReal_div_cpow hn0 hm0]; ring
    rw [hE3, cpowPartialSum, mul_sum, ← sum_congr rfl hx]
    have h3 : (s : ℂ) * riemannZeta (1 - ρ) = ∑ _m ∈ Icc 1 s, riemannZeta (1 - ρ) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [h3, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  -- the cpow relations at `r = √n`
  set R : ℂ := ((r : ℝ) : ℂ) ^ ρ with hRdef
  have hRn : ‖R‖ = r ^ σ := Complex.norm_cpow_eq_rpow_re_of_pos hr0 ρ
  have hR0 : R ≠ 0 := by
    intro h; rw [h, norm_zero] at hRn; exact absurd hRn.symm (Real.rpow_pos_of_pos hr0 σ).ne'
  have h1 : ((r : ℝ) : ℂ) ^ (ρ - 1) = R / (r : ℂ) := by
    rw [Complex.cpow_sub _ _ hrC, Complex.cpow_one]
  have h2 : ((r : ℝ) : ℂ) ^ (1 - ρ) = (r : ℂ) / R := by
    rw [Complex.cpow_sub _ _ hrC, Complex.cpow_one]
  have hnr : ((n : ℝ) : ℂ) = (r : ℂ) * (r : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, hr2]
  have h3 : ((n : ℝ) : ℂ) ^ ρ = R * R := by
    rw [hnr, Complex.mul_cpow_ofReal_nonneg hr0.le hr0.le]
  have hnC : (n : ℂ) = (r : ℂ) * (r : ℂ) := by rw [← hnr, Complex.ofReal_natCast]
  have hρ1C : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1'
  have h1ρC : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1')
  -- the exact expansion
  have key : cpowFloorSum ρ n - riemannZeta (2 - ρ) * n - riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ =
      R * ((r : ℂ) - s) / ρ + (n : ℂ) * e₂ - E1 + E3 + ((n : ℝ) : ℂ) ^ ρ / ρ * e₃ - (s : ℂ) * e₄ := by
    have hD : cpowFloorSum ρ n = (n : ℂ) * cpowPartialSum (2 - ρ) s - E1 +
        (∑ m ∈ Icc 1 s, cpowPartialSum (1 - ρ) (n / m) - (s : ℂ) * cpowPartialSum (1 - ρ) s) := by
      rw [cpowFloorSum, hhyp, hhead]
    have hP2 : cpowPartialSum (2 - ρ) s = R / (r : ℂ) / (ρ - 1) + riemannZeta (2 - ρ) + e₂ := by
      rw [he₂, h1]; ring
    have hP3 : cpowPartialSum ρ s = (r : ℂ) / R / (1 - ρ) + riemannZeta ρ + e₃ := by
      rw [he₃, h2]; ring
    have hP4 : cpowPartialSum (1 - ρ) s = R / ρ + riemannZeta (1 - ρ) + e₄ := by
      rw [he₄]; ring
    rw [hD, hsumF, hP2, hP3, hP4, h3, hnC]
    field_simp
    ring
  -- the bounds
  have hnn : ‖(n : ℂ)‖ = r ^ 2 := by rw [Complex.norm_natCast, hr2]
  have hnρ' : ‖((n : ℝ) : ℂ) ^ ρ‖ = r ^ σ * r ^ σ := by rw [h3, norm_mul, hRn]
  have hb1 : ‖R * ((r : ℂ) - s) / ρ‖ ≤ r ^ σ / ‖ρ‖ := by
    rw [norm_div, norm_mul, hRn]
    have hrsn : ‖((r : ℂ) - s)‖ ≤ 1 := by
      have : ((r : ℂ) - s) = ((r - s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc r ^ σ * ‖((r : ℂ) - s)‖ / ‖ρ‖ ≤ r ^ σ * 1 / ‖ρ‖ := by
          gcongr
      _ = r ^ σ / ‖ρ‖ := by rw [mul_one]
  have hb2 : ‖(n : ℂ) * e₂‖ ≤ C₂ * r ^ σ := by
    rw [norm_mul, hnn]
    have hpow : r ^ 2 * r ^ (-(2 - σ)) = r ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0]; congr 1; push_cast; ring
    calc r ^ 2 * ‖e₂‖ ≤ r ^ 2 * (C₂ * r ^ (-(2 - σ))) :=
          mul_le_mul_of_nonneg_left he₂b (by positivity)
      _ = C₂ * (r ^ 2 * r ^ (-(2 - σ))) := by ring
      _ = C₂ * r ^ σ := by rw [hpow]
  have hb3 : ‖((n : ℝ) : ℂ) ^ ρ / ρ * e₃‖ ≤ C₃ / ‖ρ‖ * r ^ σ := by
    rw [norm_mul, norm_div, hnρ']
    have hpow : r ^ σ * r ^ (-σ) = 1 := by rw [← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero]
    calc r ^ σ * r ^ σ / ‖ρ‖ * ‖e₃‖ ≤ r ^ σ * r ^ σ / ‖ρ‖ * (C₃ * r ^ (-σ)) :=
          mul_le_mul_of_nonneg_left he₃b (by positivity)
      _ = C₃ / ‖ρ‖ * r ^ σ * (r ^ σ * r ^ (-σ)) := by ring
      _ = C₃ / ‖ρ‖ * r ^ σ := by rw [hpow, mul_one]
  have hb4 : ‖(s : ℂ) * e₄‖ ≤ C₁ * r ^ σ := by
    rw [norm_mul, Complex.norm_natCast]
    calc (s : ℝ) * ‖e₄‖ ≤ r * (C₁ * r ^ (-(1 - σ))) :=
          mul_le_mul hsr he₄b (norm_nonneg _) hr0.le
      _ = C₁ * r ^ σ := by rw [mul_left_comm, hrσ]
  rw [key]
  have htri : ‖R * ((r : ℂ) - s) / ρ + (n : ℂ) * e₂ - E1 + E3 + ((n : ℝ) : ℂ) ^ ρ / ρ * e₃ -
      (s : ℂ) * e₄‖ ≤ ‖R * ((r : ℂ) - s) / ρ‖ + ‖(n : ℂ) * e₂‖ + ‖E1‖ + ‖E3‖ +
        ‖((n : ℝ) : ℂ) ^ ρ / ρ * e₃‖ + ‖(s : ℂ) * e₄‖ := by
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    exact norm_add_le _ _
  refine htri.trans ?_
  have hfin : r ^ σ / ‖ρ‖ + C₂ * r ^ σ + (1 + 1 / σ) * r ^ σ + C₁ * r ^ σ + C₃ / ‖ρ‖ * r ^ σ +
      C₁ * r ^ σ = floorSumRate ρ * r ^ σ := by
    rw [floorSumRate, ← hC₁, ← hC₂, ← hC₃, ← hσ]; ring
  rw [← hfin]
  linarith [hb1, hb2, hE1b, hE3b, hb3, hb4]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
