import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.Reflection

/-!
# de Bruijn's shift contraction of the zero strip

Let `f` be entire, even, real on the real axis (`f(z̄) = conj f(z)`), `f(0) ≠ 0`, with the order-one
envelope `‖f z‖ ≤ exp(C(1+‖z‖)log(2+‖z‖))`, and suppose every zero of `f` satisfies `|Im w| ≤ Δ`.
Then for `λ > 0` the function `f(z + iλ) + f(z − iλ)` has no zero with `Im z ≠ 0` and
`(Im z)² + λ² > Δ²` (`add_shift_ne_zero`): the zero strip shrinks from half-width `Δ` to
`√(Δ² − λ²)`, and to the real axis once `λ ≥ Δ`.

Mechanism. By Hadamard's factorization at order one, `f = f(0)·∏ E₁(z/ζ)` over the zeros with
multiplicity. For `Im z > 0` compare `‖f(z+iλ)‖` with `‖f(z−iλ)‖` factor by factor, after pairing
each zero `ζ` with its conjugate (an involution of the multiplicity index, since `f` is real):
* the exponential parts of `E₁` cancel inside a conjugate pair, because `Re(w/ζ + w/ζ̄)` depends
  on `w` only through `Re w`;
* for the linear parts, with `X = Re z − Re ζ`, `Y = Im z`, `b = Im ζ`,
  `|ζ − z − iλ|²|ζ̄ − z − iλ|² − |ζ − z + iλ|²|ζ̄ − z + iλ|² = 8Yλ(X² + Y² + λ² − b²) > 0`.
The logarithms of the factors are absolutely summable (`Σ 1/|ζ|² < ∞`), so the paired sum of
log-ratios is positive and `‖f(z−iλ)‖ < ‖f(z+iλ)‖`. Conjugation covers `Im z < 0`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower.DeBruijn

noncomputable section

variable {f : ℂ → ℂ}

/-! ## The pair inequality -/

/-- A conjugate pair `ζ, ζ̄` with `(Im ζ)² < (Im z)² + λ²`, `Im z > 0`, is strictly farther from
`z + iλ` than from `z − iλ`. -/
theorem pair_dist_lt {z ζ : ℂ} {lam : ℝ} (hlam : 0 < lam) (hz : 0 < z.im)
    (hb : ζ.im ^ 2 < z.im ^ 2 + lam ^ 2) :
    ‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ <
      ‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ := by
  set X := ζ.re - z.re
  set Y := z.im
  set b := ζ.im
  have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : ‖ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b - Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e2 : ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b + Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e3 : ‖ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b - Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e4 : ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b + Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have hdiff : (‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖) ^ 2 -
      (‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖) ^ 2 =
      8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    rw [mul_pow, mul_pow, e1, e2, e3, e4]
    ring
  have hpos : 0 < 8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    have : 0 < X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2 := by nlinarith [sq_nonneg X]
    positivity
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  linarith

/-! ## Zeros and their conjugates -/

theorem apply_zeroCopyPoint (hf : AnalyticOnNhd ℂ f univ) (q : ZeroCopy f) :
    f (zeroCopyPoint f q) = 0 := by
  by_contra h
  have hord : analyticOrderAt f (zeroCopyPoint f q) = 0 :=
    (hf _ (mem_univ _)).analyticOrderAt_eq_zero.mpr h
  apply q.1.2
  change (MeromorphicOn.divisor f univ) (zeroCopyPoint f q) = 0
  rw [divisor_univ_eq_analyticOrder hf, hord]
  rfl

theorem divisor_conj (hf : AnalyticOnNhd ℂ f univ)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (w : ℂ) :
    (MeromorphicOn.divisor f univ) ((starRingEnd ℂ) w) = (MeromorphicOn.divisor f univ) w := by
  rw [divisor_univ_eq_analyticOrder hf, divisor_univ_eq_analyticOrder hf,
    analyticOrderAt_conj_of_conjEquivariant hconj (hf w (mem_univ w)) (hf _ (mem_univ _))]

/-- Conjugation as an involution of the zero support of a real entire function. -/
def zeroSupportConj (hf : AnalyticOnNhd ℂ f univ)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ZeroSupport f ≃ ZeroSupport f where
  toFun w := ⟨(starRingEnd ℂ) (w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_conj hf hconj]
    exact Function.mem_support.mp w.2⟩
  invFun w := ⟨(starRingEnd ℂ) (w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_conj hf hconj]
    exact Function.mem_support.mp w.2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- Conjugation lifted to the multiplicity-copy index. -/
def zeroCopyConj (hf : AnalyticOnNhd ℂ f univ)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ZeroCopy f ≃ ZeroCopy f :=
  Equiv.sigmaCongr (zeroSupportConj hf hconj) (fun w => Equiv.cast (by
    change Fin ((MeromorphicOn.divisor f univ) ((w : ZeroSupport f) : ℂ)).toNat =
      Fin ((MeromorphicOn.divisor f univ) ((starRingEnd ℂ) ((w : ZeroSupport f) : ℂ))).toNat
    rw [divisor_conj hf hconj]))

theorem zeroCopyPoint_conj (hf : AnalyticOnNhd ℂ f univ)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (q : ZeroCopy f) :
    zeroCopyPoint f (zeroCopyConj hf hconj q) = (starRingEnd ℂ) (zeroCopyPoint f q) := rfl

/-! ## Logarithms of the genus-one factors -/

theorem weierstrassE1_ne_zero {u : ℂ} (hu : u ≠ 1) : weierstrassE1 u ≠ 0 := by
  unfold weierstrassE1
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu)) (Complex.exp_ne_zero _)

/-- `|log ‖E₁(u)‖| ≤ ‖u‖²` when `‖u‖ ≤ 1/2`. -/
theorem abs_log_norm_weierstrassE1_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    |Real.log ‖weierstrassE1 u‖| ≤ ‖u‖ ^ 2 := by
  have hu1 : u ≠ 1 := by
    intro h; rw [h, norm_one] at hu; norm_num at hu
  have h1u : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  unfold weierstrassE1
  rw [norm_mul, Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.mpr h1u) (Real.exp_pos _).ne',
    Real.log_exp, ← Complex.log_re]
  have hlt : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have hlog := Complex.norm_log_one_add_sub_self_le hlt
  rw [norm_neg] at hlog
  have hre : (Complex.log (1 - u)).re + u.re = (Complex.log (1 + -u) - -u).re := by
    rw [← sub_eq_add_neg]; simp
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hlog.trans ?_)
  have h2 : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [sq_nonneg ‖u‖]

/-- The logarithms of the genus-one factors at a point are absolutely summable. -/
theorem summable_log_norm_weierstrassE1 {ι : Type*} {a : ι → ℂ}
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (w : ℂ) :
    Summable (fun i => Real.log ‖weierstrassE1 (w / a i)‖) := by
  refine Summable.of_norm_bounded_eventually (g := fun i => ‖w‖ ^ 2 * (1 / ‖a i‖ ^ (2 : ℕ)))
    (hsum.mul_left _) ?_
  have ht := hsum.tendsto_cofinite_zero
  have hc : (0 : ℝ) < 1 / (4 * ‖w‖ ^ 2 + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with i hi
  rw [Real.norm_eq_abs]
  by_cases hai : a i = 0
  · simp [hai]
  have hapos : 0 < ‖a i‖ := norm_pos_iff.mpr hai
  have hinv : 1 / ‖a i‖ ^ 2 < 1 / (4 * ‖w‖ ^ 2 + 1) := hi
  have hbig : 4 * ‖w‖ ^ 2 + 1 < ‖a i‖ ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hinv
    linarith
  have hu : ‖w / a i‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hapos]
    nlinarith [norm_nonneg w]
  refine (abs_log_norm_weierstrassE1_le hu).trans (le_of_eq ?_)
  rw [norm_div, div_pow]
  ring

/-! ## The paired comparison -/

/-- For a conjugate pair the product of the two genus-one factors is the product of distances
times an exponential depending on `w` only through `Re w`. -/
theorem norm_weierstrassE1_pair {ζ : ℂ} (hζ : ζ ≠ 0) (w : ℂ) :
    ‖weierstrassE1 (w / ζ)‖ * ‖weierstrassE1 (w / (starRingEnd ℂ) ζ)‖ =
      ‖ζ - w‖ * ‖(starRingEnd ℂ) ζ - w‖ / ‖ζ‖ ^ 2 *
        Real.exp (2 * ζ.re * w.re / Complex.normSq ζ) := by
  have hζc : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).mpr hζ
  unfold weierstrassE1
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : ‖1 - w / ζ‖ = ‖ζ - w‖ / ‖ζ‖ := by
    rw [show (1 : ℂ) - w / ζ = (ζ - w) / ζ by field_simp, norm_div]
  have h2 : ‖1 - w / (starRingEnd ℂ) ζ‖ = ‖(starRingEnd ℂ) ζ - w‖ / ‖ζ‖ := by
    rw [show (1 : ℂ) - w / (starRingEnd ℂ) ζ = ((starRingEnd ℂ) ζ - w) / (starRingEnd ℂ) ζ by
      field_simp, norm_div, Complex.norm_conj]
  have hre : (w / ζ).re + (w / (starRingEnd ℂ) ζ).re = 2 * ζ.re * w.re / Complex.normSq ζ := by
    have hn : Complex.normSq ζ ≠ 0 := (Complex.normSq_pos.mpr hζ).ne'
    rw [Complex.div_re, Complex.div_re, Complex.normSq_conj]
    simp only [Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  rw [h1, h2]
  calc ‖ζ - w‖ / ‖ζ‖ * Real.exp (w / ζ).re * (‖(starRingEnd ℂ) ζ - w‖ / ‖ζ‖ *
        Real.exp (w / (starRingEnd ℂ) ζ).re)
      = ‖ζ - w‖ * ‖(starRingEnd ℂ) ζ - w‖ / ‖ζ‖ ^ 2 *
          (Real.exp (w / ζ).re * Real.exp (w / (starRingEnd ℂ) ζ).re) := by ring
    _ = _ := by rw [← Real.exp_add, hre]

/-- **Paired factor comparison.** -/
theorem norm_weierstrassE1_pair_lt {ζ z : ℂ} (hζ : ζ ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hz : 0 < z.im) (hb : ζ.im ^ 2 < z.im ^ 2 + lam ^ 2) :
    ‖weierstrassE1 ((z - lam * I) / ζ)‖ * ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖ <
      ‖weierstrassE1 ((z + lam * I) / ζ)‖ *
        ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖ := by
  rw [norm_weierstrassE1_pair hζ, norm_weierstrassE1_pair hζ]
  have hre : (z - lam * I).re = (z + lam * I).re := by simp
  rw [hre]
  have hζn : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.mpr hζ; positivity
  exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (pair_dist_lt hlam hz hb) hζn)
    (Real.exp_pos _)

/-! ## The contraction -/

theorem analyticOrderAt_ne_top_of_ne_zero (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  have h0 : analyticOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]
    exact ENat.zero_ne_top
  exact hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z) h0

/-- The modulus of `f` at a non-zero point as the exponential of the summed factor logarithms. -/
theorem norm_eq_exp_tsum {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {w : ℂ} (hw : f w ≠ 0) :
    ‖f w‖ = ‖f 0‖ * Real.exp (∑' q : ZeroCopy f,
      Real.log ‖weierstrassE1 (w / zeroCopyPoint f q)‖) := by
  have hford := analyticOrderAt_ne_top_of_ne_zero hf hf0
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
  have hmul := multipliable_canonicalProductE1Indexed hane hsum w
  have hpos : ∀ q : ZeroCopy f, 0 < ‖weierstrassE1 (w / zeroCopyPoint f q)‖ := by
    intro q
    refine norm_pos_iff.mpr (weierstrassE1_ne_zero ?_)
    intro h1
    have : w = zeroCopyPoint f q := by
      rw [div_eq_one_iff_eq (hane q)] at h1; exact h1
    exact hw (this ▸ apply_zeroCopyPoint hf q)
  have hP : ‖OrderOneHadamard.hadamardProduct f w‖ =
      Real.exp (∑' q : ZeroCopy f, Real.log ‖weierstrassE1 (w / zeroCopyPoint f q)‖) := by
    rw [Real.rexp_tsum_eq_tprod hpos (summable_log_norm_weierstrassE1 hsum w), ← hmul.norm_tprod]
    rfl
  rw [hfac w, norm_mul, hP]

/-- A summable real family whose sums over the orbits of an involution are positive has positive
sum. -/
theorem tsum_pos_of_involution {ι : Type*} [Nonempty ι] {φ : ι → ℝ} (hφ : Summable φ)
    (σ : ι ≃ ι) (hpair : ∀ q, 0 < φ q + φ (σ q)) : 0 < ∑' q, φ q := by
  have hφσ : Summable (fun q => φ (σ q)) := σ.summable_iff.mpr hφ
  have hsplit : ∑' q, (φ q + φ (σ q)) = (∑' q, φ q) + ∑' q, φ (σ q) := hφ.tsum_add hφσ
  have hσeq : ∑' q, φ (σ q) = ∑' q, φ q := σ.tsum_eq φ
  obtain ⟨q₀⟩ := ‹Nonempty ι›
  have hpos : 0 < ∑' q, (φ q + φ (σ q)) :=
    (hφ.add hφσ).tsum_pos (fun q => (hpair q).le) q₀ (hpair q₀)
  linarith

/-- The paired log-ratio of genus-one factors is positive. -/
theorem log_ratio_pair_pos
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {Δ : ℝ} (hΔ : ∀ w, f w = 0 → |w.im| ≤ Δ) {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : 0 < z.im) (hzΔ : Δ ^ 2 < z.im ^ 2 + lam ^ 2)
    (hu : f (z - lam * I) ≠ 0) (hv : f (z + lam * I) ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 0) (hζz : f ζ = 0) :
    0 < (Real.log ‖weierstrassE1 ((z + lam * I) / ζ)‖ -
        Real.log ‖weierstrassE1 ((z - lam * I) / ζ)‖) +
      (Real.log ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖ -
        Real.log ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖) := by
  have hb : ζ.im ^ 2 < z.im ^ 2 + lam ^ 2 := by
    have h1 := hΔ ζ hζz
    have h2 : ζ.im ^ 2 ≤ Δ ^ 2 := by
      have := abs_nonneg ζ.im
      nlinarith [sq_abs ζ.im]
    linarith
  have hne : ∀ w : ℂ, f w ≠ 0 → ∀ ξ : ℂ, f ξ = 0 → ξ ≠ 0 → 0 < ‖weierstrassE1 (w / ξ)‖ := by
    intro w hw ξ hξ hξ0
    refine norm_pos_iff.mpr (weierstrassE1_ne_zero ?_)
    intro h1
    rw [div_eq_one_iff_eq hξ0] at h1
    exact hw (h1 ▸ hξ)
  have hζcz : f ((starRingEnd ℂ) ζ) = 0 := by rw [hconj, hζz, map_zero]
  have hζc0 : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).mpr hζ
  have key := norm_weierstrassE1_pair_lt hζ hlam hz hb
  have p1 := hne _ hu ζ hζz hζ
  have p2 := hne _ hu _ hζcz hζc0
  have p3 := hne _ hv ζ hζz hζ
  have p4 := hne _ hv _ hζcz hζc0
  have hlog := Real.log_lt_log (mul_pos p1 p2) key
  rw [Real.log_mul p1.ne' p2.ne', Real.log_mul p3.ne' p4.ne'] at hlog
  linarith

/-- **Strict modulus increase across the shift.** For `Im z > 0` with `(Im z)² + λ² > Δ²`, if `f`
has a zero, `‖f(z − iλ)‖ < ‖f(z + iλ)‖`. -/
theorem norm_sub_shift_lt {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {Δ : ℝ} (hΔ : ∀ w, f w = 0 → |w.im| ≤ Δ) {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : 0 < z.im) (hzΔ : Δ ^ 2 < z.im ^ 2 + lam ^ 2) (hne : Nonempty (ZeroCopy f))
    (hu : f (z - lam * I) ≠ 0) (hv : f (z + lam * I) ≠ 0) :
    ‖f (z - lam * I)‖ < ‖f (z + lam * I)‖ := by
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  rw [norm_eq_exp_tsum hC hf hf0 heven hbound hu, norm_eq_exp_tsum hC hf hf0 heven hbound hv]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) (norm_pos_iff.mpr hf0)
  have hsu := summable_log_norm_weierstrassE1 hsum (z - lam * I)
  have hsv := summable_log_norm_weierstrassE1 hsum (z + lam * I)
  rw [← sub_pos, ← hsv.tsum_sub hsu]
  refine tsum_pos_of_involution (hsv.sub hsu) (zeroCopyConj hf hconj) (fun q => ?_)
  rw [zeroCopyPoint_conj hf hconj q]
  exact log_ratio_pair_pos hconj hΔ hlam hz hzΔ hu hv (hane q) (apply_zeroCopyPoint hf q)

/-- **de Bruijn's shift contraction.** Under the standing hypotheses, `f(z+iλ) + f(z−iλ) ≠ 0`
whenever `Im z ≠ 0` and `(Im z)² + λ² > Δ²`. -/
theorem add_shift_ne_zero {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {Δ : ℝ} (hΔ : ∀ w, f w = 0 → |w.im| ≤ Δ) {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z.im ≠ 0) (hzΔ : Δ ^ 2 < z.im ^ 2 + lam ^ 2) :
    f (z + lam * I) + f (z - lam * I) ≠ 0 := by
  -- the upper case
  have upper : ∀ z : ℂ, 0 < z.im → Δ ^ 2 < z.im ^ 2 + lam ^ 2 →
      f (z + lam * I) + f (z - lam * I) ≠ 0 := by
    intro z hz hzΔ
    have hv : f (z + lam * I) ≠ 0 := by
      intro h0
      have h1 := hΔ _ h0
      have him : (z + lam * I).im = z.im + lam := by simp
      rw [him, abs_of_pos (by linarith)] at h1
      nlinarith
    by_cases hu : f (z - lam * I) = 0
    · rw [hu, add_zero]; exact hv
    rcases isEmpty_or_nonempty (ZeroCopy f) with hempty | hne
    · -- no zeros: `f` is constant
      have hford := analyticOrderAt_ne_top_of_ne_zero hf hf0
      have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven
        hbound
      have hconst : ∀ w, f w = f 0 := by
        intro w
        rw [hfac w]
        change f 0 * ∏' q : ZeroCopy f, weierstrassE1 (w / zeroCopyPoint f q) = f 0
        rw [tprod_empty, mul_one]
      rw [hconst (z + lam * I), hconst (z - lam * I)]
      intro h
      exact hf0 (by linear_combination h / 2)
    · intro hsum0
      have hlt := norm_sub_shift_lt hC hf hf0 heven hconj hbound hΔ hlam hz hzΔ hne hu hv
      have : f (z + lam * I) = -f (z - lam * I) := by linear_combination hsum0
      rw [this, norm_neg] at hlt
      exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h := upper ((starRingEnd ℂ) z) (by simpa using hneg) (by simpa using hzΔ)
    intro hsum0
    apply h
    have e1 : (starRingEnd ℂ) z + lam * I = (starRingEnd ℂ) (z - lam * I) := by
      rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have e2 : (starRingEnd ℂ) z - lam * I = (starRingEnd ℂ) (z + lam * I) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [e1, e2, hconj, hconj, ← map_add, add_comm, hsum0, map_zero]
  · exact upper z hpos hzΔ

end

end RHTower.DeBruijn
