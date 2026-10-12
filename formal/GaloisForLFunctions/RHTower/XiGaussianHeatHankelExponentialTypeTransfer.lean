import GaloisForLFunctions.RHTower.XiGaussianHeatHankelWindowCeiling
import GaloisForLFunctions.HTGeometry.EvenEntireSquareLift

/-!
# Exponential-type zero-side witnesses reach the heat window at scale `1/N`

Let `Φ` be an even entire function of exponential type `B`, `|Φ(z)| ≤ C e^{B|z|}`, with
`|Φ(z)| ≤ D/(1 + |z|)` on the strip `|Im z| ≤ 1/2`, and with zero-side functional
`Z(Φ) = Σ_q Φ(z_q) \overline{Φ(\bar z_q)}` of negative real part.

**Theorem** (`eventually_re_heatHankel_evenTaylorPoly_neg`).  For every `K` with
`(eB + 1)² < 4K`, the even Taylor polynomials `T_nΦ(w) = Σ_{k ≤ n} Φ^{(2k)}(0)/(2k)! · w^k`
satisfy `Re H_{K/n}(T_nΦ, T_nΦ) < 0` for all large `n`.

Proof.
* `H_a(T_nΦ, T_nΦ) = Σ_q e^{-a w_q} T_nΦ(z_q²) \overline{T_nΦ(\bar z_q²)}`, and `T_nΦ(z²)` is the
  Taylor polynomial of `Φ` of degree `2n + 1`, since the odd coefficients vanish.
* Cauchy's estimate on the circle of radius `ρ = e(1 + |z|)` bounds the remainder by
  `2C e^{Bρ} e^{-(2n+2)}`.
* On the strip, `e^{-a Re z²/2} ≤ e^{1/8} e^{-a x²/2}` and `−a x²/2 + β|x| ≤ β²/(2a)` with
  `β = eB + 1`.  At `a = K/n` the weighted remainder is therefore `O(e^{n(β²/(2K) − 2)}) → 0`.
* Dominated convergence with the summable majorant `const/(1 + |w_q|)` gives
  `H_{K/n}(T_nΦ, T_nΦ) → Z(Φ)`.

**Corollary** (`eventually_exists_heatMomentDet_nonpos_of_exponentialType`).  For all large `n`,
some leading heat determinant `Δ_k(K/n)` with `k ≤ n + 1` is `≤ 0`.  An exponential-type witness of
type `B` therefore caps the heat window at `aN ≍ (eB + 1)²/4`, the same order `1/N` as the
unconditional window `aN ≤ κ`.
-/

open Complex Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix iteratedDeriv_odd_eq_zero_of_even)

namespace RHTower

noncomputable section

/-! ## The even Taylor polynomial -/

/-- The Taylor term `Φ^{(m)}(0)/m! · z^m`. -/
def entireTaylorTerm (Φ : ℂ → ℂ) (z : ℂ) (m : ℕ) : ℂ :=
  (m.factorial : ℂ)⁻¹ * iteratedDeriv m Φ 0 * z ^ m

/-- The even Taylor polynomial `Σ_{k ≤ n} Φ^{(2k)}(0)/(2k)! · X^k`. -/
def evenTaylorPoly (Φ : ℂ → ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) Φ 0) * X ^ k

theorem natDegree_evenTaylorPoly_le (Φ : ℂ → ℂ) (n : ℕ) : (evenTaylorPoly Φ n).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ k).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

theorem sum_range_two_mul_pairs (f : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- `T_nΦ(z²)` is the Taylor polynomial of the even function `Φ` of degree `2n + 1`. -/
theorem eval_evenTaylorPoly_sq {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z) (n : ℕ) (z : ℂ) :
    (evenTaylorPoly Φ n).eval (z ^ 2) =
      ∑ m ∈ Finset.range (2 * n + 2), entireTaylorTerm Φ z m := by
  rw [show 2 * n + 2 = 2 * (n + 1) by ring, sum_range_two_mul_pairs, evenTaylorPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [entireTaylorTerm, entireTaylorTerm, iteratedDeriv_odd_eq_zero_of_even heven k, eval_mul,
    eval_C, eval_pow, eval_X, ← pow_mul]
  ring

theorem hasSum_entireTaylorTerm {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (z : ℂ) :
    HasSum (entireTaylorTerm Φ z) (Φ z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hΦ 0 z
  have e : entireTaylorTerm Φ z =
      fun m => (m.factorial : ℂ)⁻¹ • (z - 0) ^ m • iteratedDeriv m Φ 0 := by
    funext m
    simp only [entireTaylorTerm, sub_zero, smul_eq_mul]
    ring
  rw [e]
  exact h

/-! ## Cauchy estimates and the remainder -/

theorem nonneg_of_growth {Φ : ℂ → ℂ} {C B : ℝ} (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖)) :
    0 ≤ C := by
  have h := hgrowth 0
  rw [norm_zero, mul_zero, Real.exp_zero, mul_one] at h
  exact (norm_nonneg _).trans h

/-- Cauchy's estimate: `|Φ^{(m)}(0)/m! · z^m| ≤ C e^{Bρ} (|z|/ρ)^m`. -/
theorem norm_entireTaylorTerm_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C B : ℝ}
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖)) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) (m : ℕ) :
    ‖entireTaylorTerm Φ z m‖ ≤ C * Real.exp (B * ρ) * (‖z‖ / ρ) ^ m := by
  have hD := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (f := Φ)
    (C := C * Real.exp (B * ρ)) m hρ hΦ.diffContOnCl fun w hw => by
      rw [mem_sphere_zero_iff_norm] at hw
      rw [← hw]
      exact hgrowth w
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [entireTaylorTerm, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
  calc (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m Φ 0‖ * ‖z‖ ^ m
      ≤ (m.factorial : ℝ)⁻¹ * (m.factorial * (C * Real.exp (B * ρ)) / ρ ^ m) * ‖z‖ ^ m := by
        gcongr
    _ = C * Real.exp (B * ρ) * (‖z‖ ^ m / ρ ^ m) := by
        field_simp

/-- The Taylor remainder: for `2|z| ≤ ρ`, `|Φ(z) − T_nΦ(z²)| ≤ 2C e^{Bρ} (|z|/ρ)^{2n+2}`. -/
theorem norm_sub_eval_evenTaylorPoly_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B : ℝ} (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) (hzρ : 2 * ‖z‖ ≤ ρ) (n : ℕ) :
    ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖ ≤
      2 * (C * Real.exp (B * ρ)) * (‖z‖ / ρ) ^ (2 * n + 2) := by
  set r := ‖z‖ / ρ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr : r ≤ 1 / 2 := by rw [hr_def, div_le_iff₀ hρ]; linarith
  have hC := nonneg_of_growth hgrowth
  have htail := (hasSum_nat_add_iff' (2 * n + 2)).2 (hasSum_entireTaylorTerm hΦ z)
  rw [← eval_evenTaylorPoly_sq heven] at htail
  have hgeom : HasSum (fun m => C * Real.exp (B * ρ) * r ^ (2 * n + 2) * r ^ m)
      (C * Real.exp (B * ρ) * r ^ (2 * n + 2) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have hle := htail.norm_le_of_bounded hgeom fun m => by
    calc ‖entireTaylorTerm Φ z (m + (2 * n + 2))‖
        ≤ C * Real.exp (B * ρ) * r ^ (m + (2 * n + 2)) :=
          norm_entireTaylorTerm_le hΦ hgrowth hρ z _
      _ = C * Real.exp (B * ρ) * r ^ (2 * n + 2) * r ^ m := by rw [pow_add]; ring
  have h1r : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    norm_num
    linarith
  calc ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖
      ≤ C * Real.exp (B * ρ) * r ^ (2 * n + 2) * (1 - r)⁻¹ := hle
    _ ≤ C * Real.exp (B * ρ) * r ^ (2 * n + 2) * 2 := by gcongr
    _ = 2 * (C * Real.exp (B * ρ)) * r ^ (2 * n + 2) := by ring

/-- **The heat-weighted remainder on the strip.**  For `0 < a ≤ 1` and `|Im z| ≤ 1/2`,
`e^{-a Re z²/2} (1 + |z|) |Φ(z) − T_nΦ(z²)| ≤ 2C exp(1/8 + 3β/2 + β²/(2a) − (2n + 2))`,
`β = eB + 1`. -/
theorem norm_heatWeighted_taylorRemainder_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) (n : ℕ) :
    Real.exp (-(a * (z ^ 2).re) / 2) * ((1 + ‖z‖) * ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖) ≤
      2 * C * Real.exp (1 / 8 + 3 / 2 * (B * Real.exp 1 + 1) +
        (B * Real.exp 1 + 1) ^ 2 / (2 * a) - (2 * n + 2)) := by
  set β := B * Real.exp 1 + 1 with hβ
  set ρ := Real.exp 1 * (1 + ‖z‖) with hρ_def
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hz0 := norm_nonneg z
  have hρ : 0 < ρ := by positivity
  have hzρ : 2 * ‖z‖ ≤ ρ := by rw [hρ_def]; nlinarith
  have hrem := norm_sub_eval_evenTaylorPoly_le hΦ heven hgrowth hρ z hzρ n
  have hC := nonneg_of_growth hgrowth
  have hr : ‖z‖ / ρ ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hρ, hρ_def, ← mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos 1).ne',
      one_mul]
    linarith
  have hpow : (‖z‖ / ρ) ^ (2 * n + 2) ≤ Real.exp (-(2 * n + 2 : ℝ)) := by
    calc (‖z‖ / ρ) ^ (2 * n + 2) ≤ Real.exp (-1) ^ (2 * n + 2) :=
          pow_le_pow_left₀ (by positivity) hr _
      _ = Real.exp (-(2 * n + 2 : ℝ)) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have hy2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hnorm : ‖z‖ ≤ |z.re| + 1 / 2 := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have h1z : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have hquad : -(a * z.re ^ 2) / 2 + β * |z.re| ≤ β ^ 2 / (2 * a) := by
    have h1 : (a * |z.re| - β) ^ 2 = a ^ 2 * z.re ^ 2 - 2 * a * β * |z.re| + β ^ 2 := by
      rw [sub_sq, mul_pow, sq_abs]; ring
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a * |z.re| - β)]
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hay : a * z.im ^ 2 ≤ 1 / 4 := by nlinarith
  have hβz : β * ‖z‖ ≤ β * (|z.re| + 1 / 2) := mul_le_mul_of_nonneg_left hnorm hβ0
  have hBρ : B * ρ = (β - 1) * (1 + ‖z‖) := by rw [hρ_def, hβ]; ring
  have hexp : -(a * (z ^ 2).re) / 2 + ‖z‖ + B * ρ - (2 * n + 2) ≤
      1 / 8 + 3 / 2 * β + β ^ 2 / (2 * a) - (2 * n + 2) := by
    rw [hre, hBρ]
    nlinarith
  calc Real.exp (-(a * (z ^ 2).re) / 2) *
        ((1 + ‖z‖) * ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖)
      ≤ Real.exp (-(a * (z ^ 2).re) / 2) *
          (Real.exp ‖z‖ * (2 * (C * Real.exp (B * ρ)) * Real.exp (-(2 * n + 2 : ℝ)))) := by
        gcongr
        exact hrem.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = 2 * C * Real.exp (-(a * (z ^ 2).re) / 2 + ‖z‖ + B * ρ - (2 * n + 2)) := by
        rw [sub_eq_add_neg _ (2 * (n : ℝ) + 2), Real.exp_add, Real.exp_add, Real.exp_add]
        ring
    _ ≤ 2 * C * Real.exp (1 / 8 + 3 / 2 * β + β ^ 2 / (2 * a) - (2 * n + 2)) := by
        gcongr

/-! ## The transfer -/

theorem abs_im_xiSpectralPoint_le_half (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  have h := xiSpectralPoint_im_sq_lt_quarter q
  have h2 := sq_abs (xiSpectralPoint q).im
  nlinarith [abs_nonneg (xiSpectralPoint q).im]

/-- On the strip, `e^{-a Re z²/2} |T_nΦ(z²)| ≤ (e^{1/8} D + ε)/(1 + |z|)` whenever the weighted
remainder is at most `ε`. -/
theorem heatWeighted_norm_eval_evenTaylorPoly_le {Φ : ℂ → ℂ} {D : ℝ}
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖)) {a ε : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) {n : ℕ} {z : ℂ} (hz : |z.im| ≤ 1 / 2)
    (hrem : Real.exp (-(a * (z ^ 2).re) / 2) *
      ((1 + ‖z‖) * ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖) ≤ ε) :
    Real.exp (-(a * (z ^ 2).re) / 2) * ‖(evenTaylorPoly Φ n).eval (z ^ 2)‖ ≤
      (Real.exp (1 / 8) * D + ε) / (1 + ‖z‖) := by
  have hz1 : 0 < 1 + ‖z‖ := by positivity
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have hy2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hw : Real.exp (-(a * (z ^ 2).re) / 2) ≤ Real.exp (1 / 8) := by
    refine Real.exp_le_exp.2 ?_
    rw [hre]
    nlinarith [sq_nonneg z.re]
  have hΦz := hdecay z hz
  have hD : 0 ≤ D := by
    have := (norm_nonneg _).trans hΦz
    rwa [le_div_iff₀ hz1, zero_mul] at this
  have htri : ‖(evenTaylorPoly Φ n).eval (z ^ 2)‖ ≤
      ‖Φ z‖ + ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖ := by
    have := norm_sub_le (Φ z) (Φ z - (evenTaylorPoly Φ n).eval (z ^ 2))
    rwa [sub_sub_cancel] at this
  rw [le_div_iff₀ hz1]
  have hE := Real.exp_pos (-(a * (z ^ 2).re) / 2)
  have h1 : Real.exp (-(a * (z ^ 2).re) / 2) * ‖Φ z‖ * (1 + ‖z‖) ≤ Real.exp (1 / 8) * D := by
    rw [le_div_iff₀ hz1] at hΦz
    calc Real.exp (-(a * (z ^ 2).re) / 2) * ‖Φ z‖ * (1 + ‖z‖)
        = Real.exp (-(a * (z ^ 2).re) / 2) * (‖Φ z‖ * (1 + ‖z‖)) := by ring
      _ ≤ Real.exp (1 / 8) * D := mul_le_mul hw hΦz (by positivity) (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left htri (mul_nonneg hE.le hz1.le)]

/-- **The heat-weighted Taylor remainder is eventually at most `1`** on the strip, at heat time
`K/n` with `(eB + 1)² < 4K`. -/
theorem eventually_heatWeighted_taylorRemainder_le_one {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖)) (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ K / n < 1 ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Real.exp (-((K / n) * (z ^ 2).re) / 2) *
        ((1 + ‖z‖) * ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖) ≤ 1 := by
  set β := B * Real.exp 1 + 1 with hβ
  have hK0 : 0 < K := by nlinarith [sq_nonneg β]
  have hC := nonneg_of_growth hgrowth
  set A := 2 * C * Real.exp (1 / 8 + 3 / 2 * β) with hA
  set ε : ℕ → ℝ := fun n => A * Real.exp ((β ^ 2 / (2 * K) - 2) * n - 2) with hε_def
  have hA0 : 0 ≤ A := by positivity
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hc : β ^ 2 / (2 * K) - 2 < 0 := by
      rw [sub_neg, div_lt_iff₀ (by positivity)]
      linarith
    have h1 : Tendsto (fun n : ℕ => (β ^ 2 / (2 * K) - 2) * (n : ℝ) - 2) atTop atBot :=
      tendsto_atBot_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul A
  have hkey : ∀ n : ℕ, 0 < n → K / n ≤ 1 → ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Real.exp (-((K / n) * (z ^ 2).re) / 2) *
        ((1 + ‖z‖) * ‖Φ z - (evenTaylorPoly Φ n).eval (z ^ 2)‖) ≤ ε n := by
    intro n hn hKn z hz
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
    have hK0' : K ≠ 0 := hK0.ne'
    refine (norm_heatWeighted_taylorRemainder_le hΦ heven hB hgrowth (div_pos hK0 hn') hKn hz
      n).trans (le_of_eq ?_)
    show _ = A * Real.exp ((β ^ 2 / (2 * K) - 2) * n - 2)
    rw [hA, hβ, mul_assoc (2 * C), ← Real.exp_add]
    congr 2
    field_simp
    ring
  have h1 : ∀ᶠ n : ℕ in atTop, K / n < 1 :=
    (tendsto_const_div_atTop_nhds_zero_nat K).eventually (gt_mem_nhds one_pos)
  have h2 : ∀ᶠ n : ℕ in atTop, ε n < 1 := hε.eventually (gt_mem_nhds one_pos)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hKn hεn hn
  exact ⟨hn, hKn, fun z hz => (hkey n hn hKn.le z hz).trans hεn.le⟩

/-- **Uniform heat-weighted bound for the Taylor polynomials** on the strip. -/
theorem eventually_heatWeighted_norm_evenTaylorPoly_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B D K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖))
    (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ K / n < 1 ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Real.exp (-((K / n) * (z ^ 2).re) / 2) * ‖(evenTaylorPoly Φ n).eval (z ^ 2)‖ ≤
        (Real.exp (1 / 8) * D + 1) / (1 + ‖z‖) := by
  have hK0 : 0 < K := by nlinarith [sq_nonneg (B * Real.exp 1 + 1)]
  filter_upwards [eventually_heatWeighted_taylorRemainder_le_one hΦ heven hB hgrowth hK]
    with n hn
  obtain ⟨hn0, hKn, h⟩ := hn
  exact ⟨hn0, hKn, fun z hz => heatWeighted_norm_eval_evenTaylorPoly_le hdecay
    (div_pos hK0 (by exact_mod_cast hn0)) hKn.le hz (h z hz)⟩

/-- **Exponential-type transfer, limit form.**  For an even entire `Φ` of exponential type `B`
with strip decay and `(eB + 1)² < 4K`, `H_{K/n}(T_nΦ, T_nΦ)` tends to the zero-side sum
`Σ_q Φ(z_q) \overline{Φ(\bar z_q)}`. -/
theorem tendsto_heatHankel_evenTaylorPoly {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B D K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖))
    (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    Tendsto (fun n : ℕ => heatHankel (K / n) (evenTaylorPoly Φ n) (evenTaylorPoly Φ n)) atTop
      (𝓝 (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
        (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q))))) := by
  have hK0 : 0 < K := by nlinarith [sq_nonneg (B * Real.exp 1 + 1)]
  have hD : 0 ≤ D := by
    have h := hdecay 0 (by simp)
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  -- pointwise convergence
  have hT : ∀ z : ℂ, Tendsto (fun n : ℕ => (evenTaylorPoly Φ n).eval (z ^ 2)) atTop (𝓝 (Φ z)) := by
    intro z
    have h2 : Tendsto (fun n : ℕ => 2 * n + 2) atTop atTop :=
      tendsto_atTop_mono (fun n => by show n ≤ 2 * n + 2; omega) tendsto_id
    have := (hasSum_entireTaylorTerm hΦ z).tendsto_sum_nat.comp h2
    refine this.congr fun n => ?_
    rw [Function.comp_apply, eval_evenTaylorPoly_sq heven]
  have hexp0 : Tendsto (fun n : ℕ => ((K / n : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat K)
    simpa [Function.comp_def] using this
  have hpt : ∀ q : XiZeroCopy, Tendsto
      (fun n : ℕ => heatHankelTermAt (K / n) (evenTaylorPoly Φ n) (evenTaylorPoly Φ n)
        (xiHeatFrequency q)) atTop
      (𝓝 (Φ (xiSpectralPoint q) * (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q))))) := by
    intro q
    set z := xiSpectralPoint q
    have hw : xiHeatFrequency q = z ^ 2 := rfl
    have hwc : (starRingEnd ℂ) (xiHeatFrequency q) = ((starRingEnd ℂ) z) ^ 2 := by
      rw [hw, map_pow]
    have he : Tendsto (fun n : ℕ => Complex.exp (-((K / n : ℝ) : ℂ) * xiHeatFrequency q)) atTop
        (𝓝 1) := by
      have := ((hexp0.neg.mul_const (xiHeatFrequency q))).cexp
      simpa using this
    have hc := ((Complex.continuous_conj.tendsto _).comp (hT ((starRingEnd ℂ) z)))
    have := (he.mul (hT z)).mul hc
    simp only [one_mul] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [heatHankelTermAt, hwc, hw]
  -- the dominating bound
  set M := (Real.exp (1 / 8) * D + 1) ^ 2 with hM
  have hev : ∀ᶠ n : ℕ in atTop, ∀ q : XiZeroCopy,
      ‖heatHankelTermAt (K / n) (evenTaylorPoly Φ n) (evenTaylorPoly Φ n) (xiHeatFrequency q)‖ ≤
        M * (1 / (1 + ‖xiHeatFrequency q‖)) := by
    filter_upwards [eventually_heatWeighted_norm_evenTaylorPoly_le hΦ heven hB hgrowth hdecay hK]
      with n hn q
    obtain ⟨hn, hKn, hbd⟩ := hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set a := K / (n : ℝ) with ha_def
    have ha : 0 < a := div_pos hK0 hn'
    set z := xiSpectralPoint q
    have hz := abs_im_xiSpectralPoint_le_half q
    have hzc : |((starRingEnd ℂ) z).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hz
    have hb1 := hbd z hz
    have hb2 := hbd _ hzc
    have hrec : ((starRingEnd ℂ) z ^ 2).re = (z ^ 2).re := by rw [← map_pow, Complex.conj_re]
    rw [hrec, Complex.norm_conj] at hb2
    have hw : xiHeatFrequency q = z ^ 2 := rfl
    have hnormw : ‖xiHeatFrequency q‖ = ‖z‖ ^ 2 := by rw [hw, norm_pow]
    have hz1 : 0 < 1 + ‖z‖ := by positivity
    have hnum : 0 ≤ Real.exp (1 / 8) * D + 1 := by positivity
    have hsplit : ‖heatHankelTermAt a (evenTaylorPoly Φ n) (evenTaylorPoly Φ n)
        (xiHeatFrequency q)‖ =
        (Real.exp (-(a * (z ^ 2).re) / 2) * ‖(evenTaylorPoly Φ n).eval (z ^ 2)‖) *
          (Real.exp (-(a * (z ^ 2).re) / 2) *
            ‖(evenTaylorPoly Φ n).eval ((starRingEnd ℂ) z ^ 2)‖) := by
      rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp, hw, map_pow]
      have hre : (-(a : ℂ) * z ^ 2).re = -(a * (z ^ 2).re) := by simp
      rw [hre]
      have : Real.exp (-(a * (z ^ 2).re)) =
          Real.exp (-(a * (z ^ 2).re) / 2) * Real.exp (-(a * (z ^ 2).re) / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      ring
    rw [hsplit]
    have hprod := mul_le_mul hb1 hb2 (by positivity) (by positivity)
    refine hprod.trans ?_
    rw [div_mul_div_comm, hnormw, mul_one_div]
    have hden : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
    calc (Real.exp (1 / 8) * D + 1) * (Real.exp (1 / 8) * D + 1) / ((1 + ‖z‖) * (1 + ‖z‖))
        ≤ M / ((1 + ‖z‖) * (1 + ‖z‖)) := by
          rw [hM, sq]
      _ ≤ M / (1 + ‖z‖ ^ 2) := by
          gcongr
  have hsum : Summable fun q : XiZeroCopy => M * (1 / (1 + ‖xiHeatFrequency q‖)) :=
    summable_inv_one_add_norm_xiHeatFrequency.mul_left M
  exact tendsto_tsum_of_dominated_convergence hsum hpt hev

/-- **Exponential-type transfer.**  An even entire zero-side witness of exponential type `B` gives
`Re H_{K/n}(T_nΦ, T_nΦ) < 0` for all large `n`, for every `K` with `(eB + 1)² < 4K`. -/
theorem eventually_re_heatHankel_evenTaylorPoly_neg {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B D K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖))
    (hneg : (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
      (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)))).re < 0)
    (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop,
      (heatHankel (K / n) (evenTaylorPoly Φ n) (evenTaylorPoly Φ n)).re < 0 := by
  have hre := (Complex.continuous_re.tendsto _).comp
    (tendsto_heatHankel_evenTaylorPoly hΦ heven hB hgrowth hdecay hK)
  filter_upwards [hre.eventually (gt_mem_nhds hneg)] with n hn
  exact hn


/-- **The window ceiling at scale `1/N`.**  Under the hypotheses of
`eventually_re_heatHankel_evenTaylorPoly_neg`, for all large `n` some leading heat determinant
`Δ_k(K/n)` with `k ≤ n + 1` is `≤ 0`. -/
theorem eventually_exists_heatMomentDet_nonpos_of_exponentialType {Φ : ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) (heven : ∀ z, Φ (-z) = Φ z) {C B D K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖))
    (hneg : (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
      (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)))).re < 0)
    (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n + 1, (leadingMatrix (heatMomentArray (K / n)) k).det ≤ 0 := by
  have hK0 : 0 < K := by nlinarith [sq_nonneg (B * Real.exp 1 + 1)]
  filter_upwards [eventually_re_heatHankel_evenTaylorPoly_neg hΦ heven hB hgrowth hdecay hneg hK,
    eventually_gt_atTop 0] with n hn hn0
  by_contra hcon
  push Not at hcon
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  exact hn.not_ge (heatHankel_re_nonneg_of_det_pos (div_pos hK0 hn') hcon
    (Nat.lt_succ_of_le (natDegree_evenTaylorPoly_le Φ n)))

end

end RHTower
