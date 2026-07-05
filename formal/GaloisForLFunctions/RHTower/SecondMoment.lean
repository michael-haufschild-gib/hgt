/-
# SecondMoment — the Montgomery–Vaughan diagonal mean value for the AFE carrier

**The (a) brick of doc 55 §4/§6.** The covariance-profile input to the (CR-density)
open core of MID-central: the exact second-moment identity for the Dirichlet
polynomial `F(t) = ∑_{n∈s} a n · n^{-it}`. (The value-small-ball reduction this brick
was first written to feed is REFUTED — see the corrected role below and doc 55 §6.)

The content is the diagonal orthogonality of the characters `n^{-it}` on a finite
`t`-window: cross terms `m ≠ n` integrate to a bounded oscillatory remainder
(`cosInt`, `|·| ≤ 2/|log(n/m)|`), the diagonal `m = n` contributes the full window
length `U`. Hence

    ∫_T^{T+U} ‖F(t)‖² dt  =  U · ∑_{n∈s} (a n)²  +  Remainder,

with `Remainder` an explicit, absolutely-bounded off-diagonal double sum. For the
matched carrier `a n = 1/√n` on `s = Icc 1 N` (so `F(t) = F_N(½+it)`), the main
term is `U · ∑_{n≤N} 1/n ≥ U · log(N+1)`. More generally (`secondMoment_sigma`) the
`a n = n^{-σ}` carrier gives the covariance profile `K(σ) = ∑_{n≤N} n^{-2σ}`.

**Corrected role (doc 55 §6).** This σ-profile — NOT a value small-ball at the RMS
scale `√(log N)` — is the correct input to the near-line zero density. The
Gaussian-analytic zero intensity is `(1/4π)·(log K)″(σ)`; its integral over the
microscopic strip `0<σ−½≤c/log N` gives `ε(c)·U·log N` with `ε(c) ~ c/12π → 0`
(cross-checked: `1/12π ≈ 0.0265` matches the doc 55 §2 winding probe `κ ≈ 0.025–0.040`).
The earlier `√(log N)` value-small-ball reduction is REFUTED — Kronecker–Weyl
equidistribution of `{n^{-it}}` plus Harper's better-than-squareroot moments make
that ball asymptotically FULL, not empty.

This is the classical Montgomery–Vaughan diagonal main term made axiom-clean; it
consumes NO open input. The sharp `O(n)`-per-coefficient off-diagonal bound
(the full Montgomery–Vaughan inequality) is not needed here — the elementary
`2/|log(n/m)|` remainder suffices to isolate the profile.
-/
import Mathlib

namespace RHTower

open Complex Filter MeasureTheory Topology

/-- A single term of the Dirichlet polynomial: `a n · n^{-it} = a n · exp(-it·log n)`. -/
noncomputable def cterm (a : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  (a n : ℂ) * Complex.exp (-(t : ℂ) * Complex.I * (Real.log n : ℂ))

/-- The Dirichlet polynomial `F(t) = ∑_{n∈s} a n · n^{-it}`. -/
noncomputable def dpoly (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, cterm a t n

/-- Per-pair real part: `Re(cterm m · conj cterm n) = a m · a n · cos((log n − log m)·t)`.
This is the character orthogonality kernel before integration. -/
theorem cterm_mul_conj_re (a : ℕ → ℝ) (t : ℝ) (m n : ℕ) :
    (cterm a t m * (starRingEnd ℂ) (cterm a t n)).re
      = a m * a n * Real.cos ((Real.log n - Real.log m) * t) := by
  unfold cterm
  rw [map_mul, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (-(t : ℂ) * Complex.I * (Real.log n : ℂ))
      = (t : ℂ) * Complex.I * (Real.log n : ℂ) := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Complex.conj_ofReal, hconj]
  have harg : -(t : ℂ) * Complex.I * (Real.log m : ℂ)
        + (t : ℂ) * Complex.I * (Real.log n : ℂ)
      = (((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hprod : (a m : ℂ) * Complex.exp (-(t : ℂ) * Complex.I * (Real.log m : ℂ))
        * ((a n : ℂ) * Complex.exp ((t : ℂ) * Complex.I * (Real.log n : ℂ)))
      = ((a m * a n : ℝ) : ℂ)
        * Complex.exp ((((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I) := by
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]; push_cast; ring
  rw [hprod, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The integrand identity: `‖F(t)‖²` is the real double sum of oscillatory kernels. -/
theorem normSq_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    ‖dpoly a s t‖ ^ 2
      = ∑ m ∈ s, ∑ n ∈ s, a m * a n * Real.cos ((Real.log n - Real.log m) * t) := by
  rw [Complex.sq_norm]
  have key : (Complex.normSq (dpoly a s t) : ℂ)
      = ∑ m ∈ s, ∑ n ∈ s, cterm a t m * (starRingEnd ℂ) (cterm a t n) := by
    rw [← Complex.mul_conj]
    unfold dpoly
    rw [map_sum, Finset.sum_mul_sum]
  have hre := congrArg Complex.re key
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  apply Finset.sum_congr rfl
  intro m _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact cterm_mul_conj_re a t m n

/-- Positive interior sample plus continuity and nonnegativity gives positive interval
mass. This is the local bridge from visible covariance to an `L²`-mass statement. -/
theorem intervalIntegral_pos_of_continuous_nonneg_of_exists_pos {f : ℝ → ℝ} {A B : ℝ}
    (hf : Continuous f) (hnonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hpos : ∃ t ∈ Set.Ioo A B, 0 < f t) :
    0 < ∫ t in A..B, f t := by
  obtain ⟨t₀, ht₀, htpos⟩ := hpos
  have hAB : A < B := lt_trans ht₀.1 ht₀.2
  have hfi : IntervalIntegrable f MeasureTheory.volume A B := hf.intervalIntegrable A B
  have hnonneg_ae : 0 ≤ᶠ[ae (MeasureTheory.volume.restrict (Set.uIoc A B))] f := by
    rw [EventuallyLE, Set.uIoc_of_le hAB.le, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    exact hnonneg x ⟨le_of_lt hx.1, hx.2⟩
  have hsupp_pos : 0 < MeasureTheory.volume (Function.support f ∩ Set.Ioc A B) := by
    have hne_ev : ∀ᶠ x in 𝓝 t₀, f x ≠ 0 := hf.continuousAt.eventually_ne htpos.ne'
    have hIoo_ev : Set.Ioo A B ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀.1 ht₀.2
    have hnhds : Function.support f ∩ Set.Ioc A B ∈ 𝓝 t₀ := by
      filter_upwards [hne_ev, hIoo_ev] with x hxne hxIoo
      exact ⟨Function.mem_support.mpr hxne, Set.Ioo_subset_Ioc_self hxIoo⟩
    exact MeasureTheory.Measure.measure_pos_of_mem_nhds MeasureTheory.volume hnhds
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg_ae hfi]
  exact ⟨hAB, hsupp_pos⟩

/-- The single-frequency cosine integral over the window `[T, T+U]`:
`U` on the diagonal `L = 0`, else the bounded oscillatory `(sin − sin)/L`. -/
noncomputable def cosInt (L T U : ℝ) : ℝ :=
  if L = 0 then U else (Real.sin (L * (T + U)) - Real.sin (L * T)) / L

theorem cosInt_zero (T U : ℝ) : cosInt 0 T U = U := by
  rw [cosInt, if_pos rfl]

/-- `∫_T^{T+U} cos(L·t) dt = cosInt L T U`. -/
theorem integral_cos_lin_eq (L T U : ℝ) :
    ∫ t in T..(T + U), Real.cos (L * t) = cosInt L T U := by
  unfold cosInt
  by_cases hL : L = 0
  · subst hL
    rw [if_pos rfl]
    simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  · rw [if_neg hL, intervalIntegral.integral_comp_mul_left Real.cos hL,
      integral_cos, smul_eq_mul]
    field_simp

/-- Off-diagonal frequencies are nonzero: `log` is injective on the positives. -/
theorem log_diff_ne_zero (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≠ m) :
    Real.log n - Real.log m ≠ 0 := by
  have hlog : Real.log n ≠ Real.log m := by
    intro h; apply hnm
    have hmp : (0 : ℝ) < m := by exact_mod_cast hm
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hnp) (Set.mem_Ioi.mpr hmp) h
    exact_mod_cast this
  intro hc; apply hlog; linarith

/-- The oscillatory kernel is bounded by `2/|L|` off the diagonal. -/
theorem abs_cosInt_le (L T U : ℝ) (hL : L ≠ 0) : |cosInt L T U| ≤ 2 / |L| := by
  rw [cosInt, if_neg hL, abs_div]
  have hnum : |Real.sin (L * (T + U)) - Real.sin (L * T)| ≤ 2 := by
    have h1 := Real.abs_sin_le_one (L * (T + U))
    have h2 := Real.abs_sin_le_one (L * T)
    calc |Real.sin (L * (T + U)) - Real.sin (L * T)|
          ≤ |Real.sin (L * (T + U))| + |Real.sin (L * T)| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hLpos : 0 < |L| := abs_pos.mpr hL
  gcongr

/-- **The exact second moment.** `∫ ‖F(t)‖² = ∑_{m,n} a m a n · cosInt(log n − log m)`. -/
theorem secondMoment_eq (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly a s t‖ ^ 2)
      = ∑ m ∈ s, ∑ n ∈ s, a m * a n * cosInt (Real.log n - Real.log m) T U := by
  rw [intervalIntegral.integral_congr (fun t _ => normSq_dpoly a s t)]
  have hint_inner : ∀ m ∈ s, ∀ n ∈ s,
      IntervalIntegrable (fun t => a m * a n * Real.cos ((Real.log n - Real.log m) * t))
        MeasureTheory.volume T (T + U) := by
    intro m _ n _; apply Continuous.intervalIntegrable; fun_prop
  have hint_outer : ∀ m ∈ s,
      IntervalIntegrable
        (fun t => ∑ n ∈ s, a m * a n * Real.cos ((Real.log n - Real.log m) * t))
        MeasureTheory.volume T (T + U) := by
    intro m _; apply Continuous.intervalIntegrable
    apply continuous_finsetSum; intro n _; fun_prop
  rw [intervalIntegral.integral_finsetSum hint_outer]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_finsetSum (fun n hn => hint_inner m hm n hn)]
  apply Finset.sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_const_mul, integral_cos_lin_eq]

/-- **The mean value.** `∫ ‖F(t)‖² = U · ∑ (a n)² + off-diagonal remainder`. The
diagonal is the character orthogonality main term; the remainder is the explicit
off-diagonal double sum. -/
theorem secondMoment_meanValue (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly a s t‖ ^ 2)
      = U * (∑ m ∈ s, (a m) ^ 2)
        + ∑ m ∈ s, ∑ n ∈ s.erase m,
            a m * a n * cosInt (Real.log n - Real.log m) T U := by
  rw [secondMoment_eq]
  have hdiag : ∑ m ∈ s, a m * a m * cosInt (Real.log m - Real.log m) T U
      = U * ∑ m ∈ s, (a m) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [sub_self, cosInt_zero]; ring
  have hsplit : (∑ m ∈ s, ∑ n ∈ s, a m * a n * cosInt (Real.log n - Real.log m) T U)
      = (∑ m ∈ s, a m * a m * cosInt (Real.log m - Real.log m) T U)
        + ∑ m ∈ s, ∑ n ∈ s.erase m,
            a m * a n * cosInt (Real.log n - Real.log m) T U := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.add_sum_erase s
      (fun n => a m * a n * cosInt (Real.log n - Real.log m) T U) hm]
  rw [hsplit, hdiag]

/-- **The off-diagonal is absolutely bounded** by `∑ 2|a m a n|/|log(n/m)|`. Together
with `secondMoment_meanValue` this pins the mean value to its diagonal main term up
to a `U`-independent oscillatory error. -/
theorem offDiagonal_abs_le (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    |∑ m ∈ s, ∑ n ∈ s.erase m, a m * a n * cosInt (Real.log n - Real.log m) T U|
      ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m| := by
  calc |∑ m ∈ s, ∑ n ∈ s.erase m, a m * a n * cosInt (Real.log n - Real.log m) T U|
      ≤ ∑ m ∈ s, |∑ n ∈ s.erase m, a m * a n * cosInt (Real.log n - Real.log m) T U| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, |a m * a n * cosInt (Real.log n - Real.log m) T U| := by
        apply Finset.sum_le_sum; intro m _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m| := by
        apply Finset.sum_le_sum; intro m hm
        apply Finset.sum_le_sum; intro n hn
        rw [Finset.mem_erase] at hn
        obtain ⟨hnm, hns⟩ := hn
        have hL : Real.log n - Real.log m ≠ 0 :=
          log_diff_ne_zero m n (hs m hm) (hs n hns) hnm
        rw [abs_mul]
        have hcos := abs_cosInt_le (Real.log n - Real.log m) T U hL
        have hre : 2 * |a m * a n| / |Real.log n - Real.log m|
            = |a m * a n| * (2 / |Real.log n - Real.log m|) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)

/-- **Second-moment lower bound.** The exact diagonal main term minus the explicit
off-diagonal absolute bound is a certified lower bound for the interval mass. -/
theorem secondMoment_lower_bound (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    U * (∑ m ∈ s, (a m) ^ 2)
        - ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m|
      ≤ ∫ t in T..(T + U), ‖dpoly a s t‖ ^ 2 := by
  let R := ∑ m ∈ s, ∑ n ∈ s.erase m,
    a m * a n * cosInt (Real.log n - Real.log m) T U
  let B := ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m|
  have hR : -B ≤ R := (abs_le.mp (offDiagonal_abs_le a s T U hs)).1
  rw [secondMoment_meanValue]
  dsimp only [R, B] at hR ⊢
  linarith

/-- If the diagonal main term strictly dominates the explicit off-diagonal bound,
then the second moment on the interval is strictly positive. -/
theorem secondMoment_pos_of_offDiagonal_bound_lt_diagonal
    (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ) (hs : ∀ n ∈ s, 1 ≤ n)
    (hdom :
      (∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m|)
        < U * (∑ m ∈ s, (a m) ^ 2)) :
    0 < ∫ t in T..(T + U), ‖dpoly a s t‖ ^ 2 := by
  have hlow := secondMoment_lower_bound a s T U hs
  linarith

/-- Harmonic lower bound `log(N+1) ≤ ∑_{m=1}^N 1/m` (by telescoping `log`). -/
theorem harmonic_Icc_ge_log (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have h1 : (0 : ℝ) < ((N : ℝ) + 2) / ((N : ℝ) + 1) := by positivity
      have hlog := Real.log_le_sub_one_of_pos h1
      rw [Real.log_div (by positivity) (by positivity)] at hlog
      have hrw : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by
        field_simp; ring
      rw [hrw] at hlog; exact hlog
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast
    push_cast at ih
    have harg : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    rw [harg]
    linarith

/-- The matched-carrier coefficient `a n = 1/√n` gives diagonal `(a n)² = 1/n`. -/
theorem sq_sqrt_inv (n : ℕ) (hn : 1 ≤ n) : (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

/-- **The AFE carrier mean value.** For `F_N(½+it) = ∑_{n=1}^N n^{-1/2-it}`, the
second moment has diagonal main term `U · ∑_{n≤N} 1/n`. -/
theorem secondMoment_meanValue_sqrt (N : ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly (fun n => 1 / Real.sqrt n) (Finset.Icc 1 N) t‖ ^ 2)
      = U * (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ))
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (1 / Real.sqrt m) * (1 / Real.sqrt n)
              * cosInt (Real.log n - Real.log m) T U := by
  rw [secondMoment_meanValue]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  exact sq_sqrt_inv m hm.1

/-- **The scale.** The diagonal main term grows at least like `U · log(N+1)` —
the `√(log N)` RMS amplitude of `F_N(½+it)`. -/
theorem secondMoment_mainTerm_ge_log (N : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    U * Real.log ((N : ℝ) + 1) ≤ U * (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ)) :=
  mul_le_mul_of_nonneg_left (harmonic_Icc_ge_log N) hU

/-- The matched `1/√n` carrier has interval mass at least its logarithmic diagonal
scale minus the explicit off-diagonal bound. -/
theorem secondMoment_lower_bound_sqrt_log (N : ℕ) (T U : ℝ) (hU : 0 ≤ U) :
    U * Real.log ((N : ℝ) + 1)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(1 / Real.sqrt m) * (1 / Real.sqrt n)| / |Real.log n - Real.log m|
      ≤ ∫ t in T..(T + U),
          ‖dpoly (fun n => 1 / Real.sqrt n) (Finset.Icc 1 N) t‖ ^ 2 := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hsq : ∑ m ∈ Finset.Icc 1 N, (1 / Real.sqrt m) ^ 2
      = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact sq_sqrt_inv m (Finset.mem_Icc.mp hm).1
  have hmain : U * Real.log ((N : ℝ) + 1)
      ≤ U * (∑ m ∈ Finset.Icc 1 N, (1 / Real.sqrt m) ^ 2) := by
    rw [hsq]
    exact secondMoment_mainTerm_ge_log N U hU
  have hlow := secondMoment_lower_bound (fun n => 1 / Real.sqrt n) (Finset.Icc 1 N) T U hs
  linarith

/-- Positivity criterion for the matched `1/√n` carrier from the logarithmic
diagonal scale: if the explicit off-diagonal budget is below `U log(N+1)`, the
interval second moment is strictly positive. -/
theorem secondMoment_pos_sqrt_of_offDiagonal_bound_lt_log (N : ℕ) (T U : ℝ)
    (hU : 0 ≤ U)
    (hdom :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(1 / Real.sqrt m) * (1 / Real.sqrt n)| / |Real.log n - Real.log m|)
        < U * Real.log ((N : ℝ) + 1)) :
    0 < ∫ t in T..(T + U),
      ‖dpoly (fun n => 1 / Real.sqrt n) (Finset.Icc 1 N) t‖ ^ 2 := by
  have hlow := secondMoment_lower_bound_sqrt_log N T U hU
  linarith

/-- **The σ-profile.** For general `σ`, the carrier `a n = n^{-σ}` (so `F = F_N(σ+it)`)
has diagonal main term the covariance profile `K(σ) = ∑_{n≤N} n^{-2σ}`. This profile —
its log-second-derivative giving the Gaussian-analytic near-line zero intensity
`(1/4π)·(log K)″(σ)` (doc 55 §6) — is the corrected input to (CR-density), replacing
the refuted value-small-ball. At `σ = ½` it recovers `secondMoment_meanValue_sqrt`. -/
theorem secondMoment_sigma (N : ℕ) (σ T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly (fun n => (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) t‖ ^ 2)
      = U * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ))
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            ((m : ℝ) ^ (-σ)) * ((n : ℝ) ^ (-σ))
              * cosInt (Real.log n - Real.log m) T U := by
  have hmain : ∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-σ)) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [sq, ← Real.rpow_add hpos]; congr 1; ring
  rw [secondMoment_meanValue, hmain]

end RHTower

namespace RHTower

/-- **Threshold-form window positivity.**  A Dirichlet polynomial with one
nonzero coefficient has strictly positive `L²` mass on EVERY window longer
than the explicit threshold `B / ∑(a n)²`, where
`B = ∑∑ 2|aₘaₙ|/|log(n/m)|` is the `U`- and `T`-independent off-diagonal
constant: the per-window domination hypothesis of
`secondMoment_pos_of_offDiagonal_bound_lt_diagonal` is discharged by window
length alone, uniformly in the basepoint.  The carrier cannot be `L²`-silent
on any sufficiently long vertical window anywhere on the line. -/
theorem secondMoment_pos_of_large_window
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    {n₀ : ℕ} (hn₀ : n₀ ∈ s) (ha : a n₀ ≠ 0) (T U : ℝ)
    (hU : (∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |a m * a n| / |Real.log n - Real.log m|)
        / (∑ n ∈ s, (a n) ^ 2) < U) :
    0 < ∫ t in T..(T + U), ‖dpoly a s t‖ ^ 2 := by
  have hsum : 0 < ∑ n ∈ s, (a n) ^ 2 :=
    Finset.sum_pos' (fun n _ => sq_nonneg (a n))
      ⟨n₀, hn₀, (sq_nonneg (a n₀)).lt_of_ne (Ne.symm (pow_ne_zero 2 ha))⟩
  refine secondMoment_pos_of_offDiagonal_bound_lt_diagonal a s T U hs ?_
  rw [div_lt_iff₀ hsum] at hU
  linarith [hU]

end RHTower
