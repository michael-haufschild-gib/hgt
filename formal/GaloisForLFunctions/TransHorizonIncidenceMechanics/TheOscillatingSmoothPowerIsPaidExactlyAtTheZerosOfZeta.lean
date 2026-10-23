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

/-! ### The oscillating smooth power -/

/-- The oscillating smooth power `c_{ε,t}(d) = d^{-ε} cos(t log d)`. -/
def oscillatingSmoothPower (ε t : ℝ) (d : ℕ) : ℝ := (d : ℝ) ^ (-ε) * Real.cos (t * Real.log d)

/-- The exponent `ρ = 1 − ε + it`. -/
def oscillationExponent (ε t : ℝ) : ℂ := ((1 - ε : ℝ) : ℂ) + (t : ℂ) * I

theorem oscillationExponent_re (ε t : ℝ) : (oscillationExponent ε t).re = 1 - ε := by
  simp [oscillationExponent]

theorem oscillationExponent_im (ε t : ℝ) : (oscillationExponent ε t).im = t := by
  simp [oscillationExponent]

/-- `c_{ε,t}(d) = Re d^{ρ−1}`. -/
theorem oscillatingSmoothPower_eq_re {ε : ℝ} (hε : 0 < ε) (t : ℝ) (d : ℕ) :
    oscillatingSmoothPower ε t d = (((d : ℝ) : ℂ) ^ (oscillationExponent ε t - 1)).re := by
  have hne : oscillationExponent ε t - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [sub_re, oscillationExponent_re, one_re, zero_re] at this
    linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [oscillatingSmoothPower, Real.zero_rpow (neg_ne_zero.mpr hε.ne'), Complex.zero_cpow hne]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hd0.ne'), ← Complex.ofReal_log hd0.le,
    Complex.exp_re, oscillatingSmoothPower, Real.rpow_def_of_pos hd0]
  simp only [oscillationExponent, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  congr 2 <;> ring

/-- The mean of the oscillating smooth power is `Re ζ(2 − ρ)`. -/
theorem hasSum_oscillatingSmoothPower_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasSum (fun d : ℕ => oscillatingSmoothPower ε t d / d)
      (riemannZeta (2 - oscillationExponent ε t)).re := by
  set ρ := oscillationExponent ε t with hρ
  have hre : 1 < (2 - ρ).re := by rw [sub_re, oscillationExponent_re]; norm_num; linarith
  have hsum : Summable (fun d : ℕ => 1 / (d : ℂ) ^ (2 - ρ)) := by
    have := Complex.summable_one_div_nat_cpow.mpr hre
    exact this
  have hz := (zeta_eq_tsum_one_div_nat_cpow hre) ▸ hsum.hasSum
  have h2ρ : (2 : ℂ) - ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
  refine (Complex.hasSum_re hz).congr_fun fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [oscillatingSmoothPower, Complex.zero_cpow h2ρ]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [oscillatingSmoothPower_eq_re hε, ← hρ]
  have h1 : 1 / (d : ℂ) ^ (2 - ρ) = ((d : ℝ) : ℂ) ^ (ρ - 1) / ((d : ℝ) : ℂ) := by
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, one_div, ← Complex.cpow_neg,
      show -(2 - ρ) = ρ - 1 - 1 by ring, Complex.cpow_sub _ _ hdC, Complex.cpow_one]
  rw [h1, show ((d : ℝ) : ℂ) = ((d : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]

/-- The prefix of `c_{ε,t}` is the real part of the floor-sum remainder. -/
theorem weightCenteredPrefix_oscillatingSmoothPower_eq {ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n =
      (cpowFloorSum (oscillationExponent ε t) n -
        riemannZeta (2 - oscillationExponent ε t) * n).re := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    (hasSum_oscillatingSmoothPower_div hε t).tsum_eq, cpowFloorSum, sub_re, Complex.re_sum]
  congr 1
  · refine sum_congr rfl fun d _ => ?_
    rw [oscillatingSmoothPower_eq_re hε, show ((n / d : ℕ) : ℂ) = (((n / d : ℕ) : ℝ) : ℂ) by
      push_cast; rfl, Complex.re_mul_ofReal]
  · rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal]

/-- **The prefix asymptotic of the oscillating smooth power.** For `0 < ε < 1` and `n ≥ 1`,
`|A(n) − Re(ζ(ρ) n^ρ/ρ)| ≤ K_ρ (√n)^{1−ε}`, `ρ = 1 − ε + it`. -/
theorem abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
      (riemannZeta (oscillationExponent ε t) * ((n : ℝ) : ℂ) ^ oscillationExponent ε t /
        oscillationExponent ε t).re| ≤
      floorSumRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) := by
  have h := norm_cpowFloorSum_sub_le (ρ := oscillationExponent ε t)
    (by rw [oscillationExponent_re]; linarith) (by rw [oscillationExponent_re]; linarith) hn
  rw [oscillationExponent_re] at h
  rw [weightCenteredPrefix_oscillatingSmoothPower_eq hε, ← sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-! ### Sufficiency: a zero pays the receiver -/

/-- `(√n^{1−ε})² ≤ n^{-(1+ε)} n(n+1)`. -/
theorem sq_sqrt_rpow_le {ε : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (Real.sqrt n ^ (1 - ε)) ^ 2 ≤ (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (Real.sqrt n ^ (1 - ε)) ^ 2 = (n : ℝ) ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  have h2 : (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) := by
    rw [← mul_assoc, ← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']; congr 1; ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.rpow_nonneg hn0.le _)

/-- A sequence of size `K (√n)^{1−ε}` has pronic energy at most `K²(1 + 1/ε)`. -/
theorem sum_sq_le_of_abs_le_sqrt_rpow {ε K : ℝ} (hε : 0 < ε) {f : ℕ → ℝ}
    (hf : ∀ n, 1 ≤ n → |f n| ≤ K * Real.sqrt n ^ (1 - ε)) (T : ℕ) :
    ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ K ^ 2 * (1 + 1 / ε) := by
  have hterm : ∀ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      K ^ 2 * (n : ℝ) ^ (-(1 + ε)) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have hsq : f n ^ 2 ≤ K ^ 2 * (Real.sqrt n ^ (1 - ε)) ^ 2 := by
      rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hf n hn1) 2
    rw [div_le_iff₀ hpr]
    calc f n ^ 2 ≤ K ^ 2 * (Real.sqrt n ^ (1 - ε)) ^ 2 := hsq
      _ ≤ K ^ 2 * ((n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (sq_sqrt_rpow_le hn1) (sq_nonneg K)
      _ = _ := by ring
  calc _ ≤ ∑ n ∈ Icc 1 T, K ^ 2 * (n : ℝ) ^ (-(1 + ε)) := sum_le_sum hterm
    _ = K ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(1 + ε)) := by rw [mul_sum]
    _ ≤ K ^ 2 * ((1 + 1 / ε) * ((1 : ℕ) : ℝ) ^ (-ε)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_one_sub_le hε le_rfl T) (sq_nonneg K)
    _ = K ^ 2 * (1 + 1 / ε) := by rw [Nat.cast_one, Real.one_rpow, mul_one]

/-- **A zero pays the oscillating smooth power.** For `0 < ε < 1`, if `ζ(1 − ε + it) = 0` then the
main term of the prefix vanishes and the receiver of `d^{-ε} cos(t log d)` is bounded. -/
theorem receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℝ) (hz : riemannZeta (oscillationExponent ε t) = 0) :
    ReceiverBounded (oscillatingSmoothPower ε t) := by
  refine ⟨floorSumRate (oscillationExponent ε t) ^ 2 * (1 + 1 / ε), fun T => ?_⟩
  rw [weightPronicEnergy]
  refine sum_sq_le_of_abs_le_sqrt_rpow hε (fun n hn => ?_) T
  have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hn
  rwa [hz, zero_mul, zero_div, zero_re, sub_zero] at h

/-! ### Necessity: a paid receiver forces a zero -/

/-- `Σ_{n ≤ T} 1/n ≥ log(T + 1)`. -/
theorem log_succ_le_sum_Icc_one_div (T : ℕ) :
    Real.log ((T : ℝ) + 1) ≤ ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
  have h := log_add_one_le_harmonic T
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  push_cast at h
  simpa only [one_div] using h

/-- The harmonic sums are unbounded. -/
theorem not_bddAbove_sum_Icc_one_div (L : ℝ) : ∃ T : ℕ, 1 ≤ T ∧ L < ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (Real.exp L)
  refine ⟨T + 1, by omega, ?_⟩
  have h1 := log_succ_le_sum_Icc_one_div (T + 1)
  have h2 : L < Real.log (((T + 1 : ℕ) : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    push_cast; linarith
  linarith

/-- **A paid oscillating smooth power forces a zero.** For `0 < ε ≤ 1/2`, if the receiver of
`d^{-ε} cos(t log d)` is bounded then `ζ(1 − ε + it) = 0`: otherwise the main term
`n^{1−ε} Re(a n^{it})`, `a = ζ(ρ)/ρ ≠ 0`, carries the logarithmic energy `(|a|²/4) H_T + O(1)`. -/
theorem zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) (hB : ReceiverBounded (oscillatingSmoothPower ε t)) :
    riemannZeta (oscillationExponent ε t) = 0 := by
  obtain ⟨E, hE⟩ := hB
  have hε1 : ε < 1 := by linarith
  set ρ := oscillationExponent ε t with hρ
  set a : ℂ := riemannZeta ρ / ρ with ha
  set K := floorSumRate ρ with hK
  set A := weightCenteredPrefix (oscillatingSmoothPower ε t)
    (∑' d : ℕ, oscillatingSmoothPower ε t d / d) with hA
  set M : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ρ).re with hM
  -- the remainder has bounded energy
  have hrem : ∀ n, 1 ≤ n → |A n - M n| ≤ K * Real.sqrt n ^ (1 - ε) := by
    intro n hn
    have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hn
    have hMeq : (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re = M n := by
      simp only [hM, ha]; congr 1; ring
    rw [← hρ, hMeq] at h
    exact h
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  set B := Real.sqrt E + |K| * Real.sqrt (1 + 1 / ε) with hBdef
  have hMnorm : ∀ T, pronicNorm M T ≤ B := by
    intro T
    have h1 : pronicNorm A T ≤ Real.sqrt E := by
      have h := hE T
      rw [weightPronicEnergy_eq_sq_pronicNorm] at h
      have h' := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (pronicNorm_nonneg _ _)] at h'
    have h2 : pronicNorm (fun n => A n - M n) T ≤ |K| * Real.sqrt (1 + 1 / ε) := by
      have h := sum_sq_le_of_abs_le_sqrt_rpow hε (f := fun n => A n - M n) hrem T
      rw [pronicNorm]
      calc Real.sqrt _ ≤ Real.sqrt (K ^ 2 * (1 + 1 / ε)) := Real.sqrt_le_sqrt h
        _ = |K| * Real.sqrt (1 + 1 / ε) := by
            rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs]
    have h3 := pronicNorm_add_le A (fun n => (-1) * (A n - M n)) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h3
    have h4 : pronicNorm M T = pronicNorm (fun n => A n + (-1) * (A n - M n)) T :=
      pronicNorm_congr fun n _ => by ring
    rw [h4, hBdef]
    linarith
  -- the main term carries the logarithmic energy of `u(n) = Re(a n^{it})`
  set u : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re with hu
  have hMu : ∀ n : ℕ, 1 ≤ n → M n = (n : ℝ) ^ (1 - ε) * u n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : ((n : ℝ) : ℂ) ^ ρ =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [hρ, oscillationExponent, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
        Complex.ofReal_cpow hn0.le]
    simp only [hM, hu]
    rw [hsplit, mul_left_comm, Complex.re_ofReal_mul]
  have hlow : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * B ^ 2 := by
    intro T
    have hMsq : ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ B ^ 2 := by
      have h := hMnorm T
      rw [pronicNorm] at h
      have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans h
      have hs0 : 0 ≤ ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        sum_nonneg fun n _ => by positivity
      calc _ = Real.sqrt (∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 :=
            (Real.sq_sqrt hs0).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    have hterm : ∀ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpow : (n : ℝ) ≤ ((n : ℝ) ^ (1 - ε)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ ((1 - ε) * ((2 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
      rw [hMu n hn1, mul_pow]
      rw [div_le_iff₀ hn0, mul_comm 2, mul_assoc]
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hpr]
      have hu2 : 0 ≤ u n ^ 2 := sq_nonneg _
      calc u n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ u n ^ 2 * (2 * (n : ℝ) * n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hu2
        _ = ((n : ℝ) * u n ^ 2) * (2 * n) := by ring
        _ ≤ (((n : ℝ) ^ (1 - ε)) ^ 2 * u n ^ 2) * (2 * n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hu2) (by positivity)
    calc _ ≤ ∑ n ∈ Icc 1 T, 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := sum_le_sum hterm
      _ = 2 * ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
      _ ≤ 2 * B ^ 2 := by linarith
  -- `u² = (|a|² + Re(a² n^{2it}))/2`
  have husq : ∀ n : ℕ, 1 ≤ n → u n ^ 2 =
      (‖a‖ ^ 2 + (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re) / 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set z := a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) with hz
    have hw : ‖((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
    have hz2 : z ^ 2 = a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) := by
      rw [hz, mul_pow, sq (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)),
        ← Complex.cpow_add _ _ (by exact_mod_cast hn0.ne')]
      push_cast; ring_nf
    have hnorm : ‖z‖ ^ 2 = ‖a‖ ^ 2 := by rw [hz, norm_mul, hw, mul_one]
    have hre : ∀ x : ℂ, x.re ^ 2 = (‖x‖ ^ 2 + (x ^ 2).re) / 2 := fun x => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq x, Complex.mul_re]; ring
    show z.re ^ 2 = _
    rw [hre z, hnorm, hz2]
  have hsum : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n =
      ‖a‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) +
        (a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re / 2 := by
    intro T
    rw [mul_sum, mul_sum, Complex.re_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hdiv : (a ^ 2 * (((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ))).re =
        (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re / n := by
      rw [← mul_div_assoc, Complex.div_ofReal_re]
    rw [husq n hn1, hdiv]
    ring
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- `t = 0`: the main term is `Re(a) n^{1−ε}` with `Re a < 0`
    exfalso
    have hu0 : ∀ n : ℕ, u n = a.re := fun n => by simp [hu, ht0]
    have hare : a.re < 0 := by
      have hρr : ρ = ((1 - ε : ℝ) : ℂ) := by rw [hρ, oscillationExponent, ht0]; simp
      have hz := riemannZeta_re_le_of_lt_one (σ := 1 - ε) (by linarith) (by linarith)
      rw [ha, hρr, Complex.div_ofReal_re]
      have : -(1 - ε) / (1 - (1 - ε)) < 0 := by
        apply div_neg_of_neg_of_pos <;> linarith
      exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    obtain ⟨T, -, hT⟩ := not_bddAbove_sum_Icc_one_div (2 * B ^ 2 / a.re ^ 2)
    have h := hlow T
    have heq : ∑ n ∈ Icc 1 T, u n ^ 2 / n = a.re ^ 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hu0]; ring
    rw [heq] at h
    have ha2 : 0 < a.re ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg hare hare
    rw [div_lt_iff₀ ha2] at hT
    linarith
  · -- `t ≠ 0`: the oscillating part is bounded
    by_contra hz0
    have ha0 : a ≠ 0 := by
      rw [ha]; exact div_ne_zero hz0 (fun h => by
        have := congrArg Complex.re h
        rw [oscillationExponent_re, zero_re] at this; linarith)
    set w : ℂ := 1 - ((2 * t : ℝ) : ℂ) * I with hw
    have hwre : 0 < w.re := by simp [hw]
    have hwne : w ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [hw] at this
      exact ht0 this
    set B₂ := 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w with hB₂
    have hS : ∀ T : ℕ, 1 ≤ T →
        ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)‖ ≤ B₂ := by
      intro T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hcp : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ) =
          cpowPartialSum w T := by
        rw [cpowPartialSum]
        refine sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
        rw [hw, show -(1 - ((2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I - 1 by ring,
          Complex.cpow_sub _ _ hnC, Complex.cpow_one]
      have h := norm_cpowPartialSum_sub_le hwre hwne hT le_rfl (by linarith)
      rw [show (1 : ℂ) - w = ((2 * t : ℝ) : ℂ) * I by rw [hw]; ring] at h
      have hT1 : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
      have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
      have hrate0 := partialSumRate_nonneg hwre
      rw [hcp]
      calc ‖cpowPartialSum w T‖ ≤ ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
            (((2 * t : ℝ) : ℂ) * I)‖ + ‖riemannZeta w‖ +
            ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
              (((2 * t : ℝ) : ℂ) * I) - riemannZeta w‖ := by
            have e : cpowPartialSum w T = ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                (((2 * t : ℝ) : ℂ) * I) + riemannZeta w +
                (cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                  (((2 * t : ℝ) : ℂ) * I) - riemannZeta w) := by ring
            exact (congrArg norm e).le.trans
              ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
        _ ≤ 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w * 1 := by
            rw [norm_div, hT1]
            gcongr
            exact h.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
        _ = B₂ := by rw [mul_one]
    have hna : 0 < ‖a‖ ^ 2 := by positivity
    obtain ⟨T, hT1, hT⟩ := not_bddAbove_sum_Icc_one_div ((4 * B ^ 2 + ‖a‖ ^ 2 * B₂) / ‖a‖ ^ 2)
    have h := hlow T
    rw [hsum T] at h
    have hre : |(a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re| ≤
        ‖a‖ ^ 2 * B₂ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hS T hT1) (by positivity)
    rw [div_lt_iff₀ hna] at hT
    have := (abs_le.mp hre).1
    nlinarith

/-! ### The detection law -/

/-- **The oscillating smooth power is paid exactly at the zeros of ζ.** For `0 < ε ≤ 1/2` and
`t ∈ ℝ`, the receiver of `d^{-ε} cos(t log d)` is bounded if and only if `ζ(1 − ε + it) = 0`. -/
theorem receiverBounded_oscillatingSmoothPower_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (t : ℝ) :
    ReceiverBounded (oscillatingSmoothPower ε t) ↔
      riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 :=
  ⟨zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t,
    receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t⟩

/-- **At half damping the paid frequencies are the ordinates of the critical zeros**:
`d^{-1/2} cos(t log d)` is paid iff `ζ(1/2 + it) = 0`. -/
theorem receiverBounded_oscillatingSmoothPower_half_iff (t : ℝ) :
    ReceiverBounded (oscillatingSmoothPower (1 / 2) t) ↔
      riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
  rw [receiverBounded_oscillatingSmoothPower_iff (by norm_num) le_rfl t]
  norm_num

/-- **The Riemann hypothesis in receiver form**: RH holds iff no oscillating smooth power
`d^{-ε} cos(t log d)` below half damping, `0 < ε < 1/2`, has a bounded receiver. -/
theorem riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ,
      ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro h ε hε hε2 t hB
    have hz := (receiverBounded_oscillatingSmoothPower_iff hε hε2.le t).1 hB
    exact h _ (by simp; linarith) (by simp; linarith) hz
  · intro h s hs1 hs2 hz
    have hε : 0 < 1 - s.re := by linarith
    have hε2 : 1 - s.re < 1 / 2 := by linarith
    apply h (1 - s.re) hε hε2 s.im
    rw [receiverBounded_oscillatingSmoothPower_iff hε hε2.le]
    have hs : ((1 - (1 - s.re) : ℝ) : ℂ) + (s.im : ℂ) * I = s := by
      apply Complex.ext <;> simp
    rw [hs]; exact hz

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
