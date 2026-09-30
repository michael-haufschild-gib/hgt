import GaloisForLFunctions.RHTower.DeBruijnZeroMotion

/-!
# The top zero of `H_t` descends strictly faster than de Bruijn's rate

Let `z*` be a simple zero of `H_t` whose imaginary part `y* > 0` is maximal, and let `x_r` be a real
zero. Then

`Im (H_t''(z*)/H_t'(z*)) ≤ −1/y* − 2y*/((x_r − Re z*)² + y*²)`   (`im_ratio_le_of_top_zero`).

Since `z*` moves with velocity `H''/H'`, `d/dt (Im z)² ≤ −2 − 4y*²/((x_r − Re z*)² + y*²)`: the de
Bruijn rate `−2` is exceeded by a definite amount coming from the real zero.

**Proof.** Two estimates of `D(λ) = log|H(z* + iλ)| − log|H(z* − iλ)|` for small `λ > 0`:
* from the Hadamard product and the local pair law, every conjugate pair of zeros contributes
  nonnegatively; the pair `z*, z̄*` contributes exactly `log((2y*+λ)/(2y*−λ)) ≥ λ/y*` and the real
  zero `½ log((X² + (y*+λ)²)/(X² + (y*−λ)²)) ≥ 2y*λ/(X² + (y*+λ)²)`;
* from the third-order Taylor expansion `H(z* + w) = Aw + Bw² + O(|w|³)`, `A = H'(z*)`,
  `B = H''(z*)/2`: `D(λ) ≤ −2λ Im(B/A) + Cλ²`.
Dividing by `2λ` and letting `λ → 0` gives the claim.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Elementary inequalities -/

theorem rexp_sub_taylor_two_le {r : ℝ} (hr : 0 ≤ r) :
    Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 * Real.exp r := by
  set h : ℝ → ℝ := fun s => s ^ 3 * Real.exp s - (Real.exp s - 1 - s - s ^ 2 / 2) with hh
  have hd : ∀ s, HasDerivAt h ((3 * s ^ 2 + s ^ 3) * Real.exp s - (Real.exp s - 1 - s)) s := by
    intro s
    have h1 := ((hasDerivAt_pow 3 s).mul (Real.hasDerivAt_exp s))
    have h2 := ((((Real.hasDerivAt_exp s).sub_const 1).sub (hasDerivAt_id s)).sub
      ((hasDerivAt_pow 2 s).div_const 2))
    refine (h1.sub h2).congr_deriv ?_
    simp; ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hd s).deriv]
    have hs0 : 0 ≤ s := le_of_lt hs
    have := rexp_sub_one_sub_le hs0
    have he := Real.exp_pos s
    nlinarith [sq_nonneg s, mul_nonneg (pow_nonneg hs0 3) he.le]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr) hr
  simp only [hh] at this
  norm_num at this
  linarith

theorem norm_cexp_sub_taylor_two_le (w : ℂ) :
    ‖Complex.exp w - 1 - w - w ^ 2 / 2‖ ≤ ‖w‖ ^ 3 * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial,
    Nat.cast_one, div_one, zero_add, Nat.succ_eq_add_one] at h
  norm_num at h
  refine (le_of_eq_of_le (by ring_nf) h).trans ?_
  have := rexp_sub_taylor_two_le (norm_nonneg w)
  linarith

/-- `log((1+s)/(1−s)) ≥ 2s` for `0 ≤ s < 1`. -/
theorem two_mul_le_log_div {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * s ≤ Real.log ((1 + s) / (1 - s)) := by
  set f : ℝ → ℝ := fun u => Real.log ((1 + u) / (1 - u)) - 2 * u with hf
  have hd : ∀ u ∈ Ico (0 : ℝ) 1, HasDerivAt f (2 / (1 - u ^ 2) - 2) u := by
    intro u hu
    have h1 : 0 < 1 + u := by linarith [hu.1]
    have h2 : 0 < 1 - u := by linarith [hu.2]
    have hlog : HasDerivAt (fun u : ℝ => Real.log ((1 + u) / (1 - u)))
        (1 / (1 + u) + 1 / (1 - u)) u := by
      have e : (fun u : ℝ => Real.log ((1 + u) / (1 - u))) =ᶠ[𝓝 u]
          fun u => Real.log (1 + u) - Real.log (1 - u) := by
        filter_upwards [Ioo_mem_nhds (by linarith : -1 < u) hu.2] with v hv
        rw [Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
      refine HasDerivAt.congr_of_eventuallyEq ?_ e
      have a1 := ((hasDerivAt_id u).const_add 1).log h1.ne'
      have a2 := ((hasDerivAt_id u).const_sub 1).log h2.ne'
      refine (a1.sub a2).congr_deriv ?_
      simp; ring
    refine (hlog.sub ((hasDerivAt_id u).const_mul 2)).congr_deriv ?_
    have h3 : (1 : ℝ) - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
    have e : 1 / (1 + u) + 1 / (1 - u) = 2 / (1 - u ^ 2) := by
      field_simp
      ring
    rw [e]
    ring
  have hmono : MonotoneOn f (Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt)
      fun u hu => ?_
    rw [(hd u (interior_subset hu)).deriv]
    rw [interior_Ico] at hu
    have h0 : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    rw [sub_nonneg, le_div_iff₀ h0]
    nlinarith [hu.1]
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨hs0, hs1⟩ hs0
  simp only [hf] at this
  norm_num at this
  linarith

/-- `log(1 + u) ≥ u/(1 + u)` for `u ≥ 0`. -/
theorem div_one_add_le_log {u : ℝ} (hu : 0 ≤ u) : u / (1 + u) ≤ Real.log (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  have := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
  linarith

/-! ## Third-order Taylor bound -/

theorem norm_riemannHeat_taylor_three_le {t : ℝ} (ht : 0 ≤ t) {z₀ z : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    ‖riemannHeat t z - riemannHeat t z₀ - deriv (riemannHeat t) z₀ * (z - z₀) -
        deriv (deriv (riemannHeat t)) z₀ / 2 * (z - z₀) ^ 2‖ ≤
      (∫ x, |x| ^ 3 * ‖heatWeight t x‖ * Real.exp ((|z₀.im| + 1) * |x|)) * ‖z - z₀‖ ^ 3 := by
  set G := heatWeight t
  have hGc := continuous_heatWeight t
  have hself : ∀ x, ‖G x‖ ≤ ‖heatWeight t x‖ * (|x| ^ 1 + 1) := fun x =>
    le_mul_of_one_le_right (norm_nonneg _) (by have := abs_nonneg x; rw [pow_one]; linarith)
  have hA := integrable_heat_exp_mul ht G hGc hself z
  have hB := integrable_heat_exp_mul ht G hGc hself z₀
  have hC := integrable_heat_exp_mul ht (fun x => G x * (I * x)) (hGc.mul (by fun_prop))
    (fun x => by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        pow_one]
      nlinarith [norm_nonneg (G x), abs_nonneg x]) z₀
  have hD : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z₀ * x)) := by
    refine ((integrable_pow_mul_heatWeight ht 2 |z₀.im|)).mono'
      ((((by fun_prop : Continuous fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))).mul hGc).mul
        (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
      ← sq_abs x]
    gcongr
    exact norm_exp_I_mul_le z₀ x
  rw [(hasDerivAt_deriv_riemannHeat ht z₀).deriv, deriv_riemannHeat ht]
  simp only [riemannHeat_eq_expTransform, expTransform]
  rw [← integral_mul_const, ← integral_sub hA hB, ← integral_sub ?_ (hC.mul_const _),
    show ∀ c : ℂ, -c / 2 * (z - z₀) ^ 2 = c * (-(z - z₀) ^ 2 / 2) by intro c; ring,
    ← integral_mul_const, ← integral_sub ?_ (hD.mul_const _)]
  rotate_left
  · exact (hA.sub hB).sub (hC.mul_const _)
  · exact hA.sub hB
  refine (norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight ht 3 (|z₀.im| + 1)).mul_const (‖z - z₀‖ ^ 3))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_mul_const _ _))
  set w : ℂ := I * (z - z₀) * x with hw
  have hsplit : G x * Complex.exp (I * z * x) - G x * Complex.exp (I * z₀ * x) -
      G x * (I * x) * Complex.exp (I * z₀ * x) * (z - z₀) -
      ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z₀ * x) * (-(z - z₀) ^ 2 / 2) =
      G x * Complex.exp (I * z₀ * x) * (Complex.exp w - 1 - w - w ^ 2 / 2) := by
    have : Complex.exp (I * z * x) = Complex.exp (I * z₀ * x) * Complex.exp w := by
      rw [← Complex.exp_add]; congr 1; rw [hw]; ring
    rw [this, hw]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hsplit, norm_mul, norm_mul]
  have hwn : ‖w‖ = ‖z - z₀‖ * |x| := by
    rw [hw, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hwle : ‖w‖ ≤ |x| := by rw [hwn]; nlinarith [abs_nonneg x, norm_nonneg (z - z₀)]
  have h1 := norm_cexp_sub_taylor_two_le w
  have h2 := norm_exp_I_mul_le z₀ x
  calc ‖G x‖ * ‖Complex.exp (I * z₀ * x)‖ * ‖Complex.exp w - 1 - w - w ^ 2 / 2‖
      ≤ ‖G x‖ * Real.exp (|z₀.im| * |x|) * (‖w‖ ^ 3 * Real.exp |x|) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = |x| ^ 3 * ‖G x‖ * Real.exp ((|z₀.im| + 1) * |x|) * ‖z - z₀‖ ^ 3 := by
        rw [hwn, show (|z₀.im| + 1) * |x| = |z₀.im| * |x| + |x| by ring, Real.exp_add]; ring

/-! ## The Hadamard lower bound -/

section Hadamard

open GaloisForLFunctions.EntireZeroDivisor

variable {f : ℂ → ℂ}

/-- Every zero of an entire function that does not vanish at `0` carries a multiplicity copy. -/
theorem exists_zeroCopy_of_eq_zero (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) {ζ : ℂ}
    (hζ : f ζ = 0) : ∃ q : ZeroCopy f, zeroCopyPoint f q = ζ := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ne_zero hf hf0 ζ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ((hf ζ (mem_univ _)).analyticOrderAt_eq_zero.mp (by rw [← hn]; rfl)) hζ
  have hdiv : (MeromorphicOn.divisor f univ) ζ = n := by
    rw [divisor_univ_eq_analyticOrder hf, ← hn]; rfl
  have hmem : ζ ∈ (MeromorphicOn.divisor f univ).support := by
    rw [Function.mem_support, hdiv]; exact_mod_cast hn0
  refine ⟨⟨⟨ζ, hmem⟩, ⟨0, ?_⟩⟩, rfl⟩
  change 0 < ((MeromorphicOn.divisor f univ) ζ).toNat
  rw [hdiv]
  simp only [Int.toNat_natCast]
  omega

/-- The contribution of a conjugate pair `ζ, ζ̄` to `log|f(z + iλ)| − log|f(z − iλ)|`, doubled, in
terms of the four squared distances. -/
theorem two_mul_log_pair_sub_eq {ζ z : ℂ} (hζ : ζ ≠ 0) (lam : ℝ)
    (hu : z - lam * I ≠ ζ) (hu' : z - lam * I ≠ (starRingEnd ℂ) ζ)
    (hv : z + lam * I ≠ ζ) (hv' : z + lam * I ≠ (starRingEnd ℂ) ζ) :
    2 * ((Real.log ‖weierstrassE1 ((z + lam * I) / ζ)‖ +
        Real.log ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖) -
      (Real.log ‖weierstrassE1 ((z - lam * I) / ζ)‖ +
        Real.log ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖)) =
      Real.log (((ζ.re - z.re) ^ 2 + (ζ.im - z.im - lam) ^ 2) *
          ((ζ.re - z.re) ^ 2 + (ζ.im + z.im + lam) ^ 2)) -
        Real.log (((ζ.re - z.re) ^ 2 + (ζ.im - z.im + lam) ^ 2) *
          ((ζ.re - z.re) ^ 2 + (ζ.im + z.im - lam) ^ 2)) := by
  have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hζn : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.mpr hζ; positivity
  -- the log of a pair product
  have hpair : ∀ w : ℂ, w ≠ ζ → w ≠ (starRingEnd ℂ) ζ →
      2 * (Real.log ‖weierstrassE1 (w / ζ)‖ + Real.log ‖weierstrassE1 (w / (starRingEnd ℂ) ζ)‖) =
        Real.log (‖ζ - w‖ ^ 2 * ‖(starRingEnd ℂ) ζ - w‖ ^ 2) - 2 * Real.log (‖ζ‖ ^ 2) +
          2 * (2 * ζ.re * w.re / Complex.normSq ζ) := by
    intro w hw hw'
    have h1 : 0 < ‖ζ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw))
    have h2 : 0 < ‖(starRingEnd ℂ) ζ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw'))
    have hE : ∀ ξ : ℂ, ξ ≠ 0 → w ≠ ξ → ‖weierstrassE1 (w / ξ)‖ ≠ 0 := by
      intro ξ hξ hwξ
      refine norm_ne_zero_iff.mpr (weierstrassE1_ne_zero ?_)
      rw [Ne, div_eq_one_iff_eq hξ]; exact hwξ
    rw [← Real.log_mul (hE ζ hζ hw) (hE _ ((map_ne_zero _).mpr hζ) hw'),
      norm_weierstrassE1_pair hζ, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_div (by positivity) hζn.ne',
      show ‖ζ - w‖ ^ 2 * ‖(starRingEnd ℂ) ζ - w‖ ^ 2 = (‖ζ - w‖ * ‖(starRingEnd ℂ) ζ - w‖) ^ 2 by
        ring, Real.log_pow (‖ζ - w‖ * ‖(starRingEnd ℂ) ζ - w‖) 2]
    push_cast
    ring
  have e1 : ‖ζ - (z - lam * I)‖ ^ 2 = (ζ.re - z.re) ^ 2 + (ζ.im - z.im + lam) ^ 2 := by
    rw [hsq]; simp; ring
  have e2 : ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ ^ 2 =
      (ζ.re - z.re) ^ 2 + (ζ.im + z.im - lam) ^ 2 := by
    rw [hsq]; simp; ring
  have e3 : ‖ζ - (z + lam * I)‖ ^ 2 = (ζ.re - z.re) ^ 2 + (ζ.im - z.im - lam) ^ 2 := by
    rw [hsq]; simp; ring
  have e4 : ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ ^ 2 =
      (ζ.re - z.re) ^ 2 + (ζ.im + z.im + lam) ^ 2 := by
    rw [hsq]; simp; ring
  have hre : (z - lam * I).re = (z + lam * I).re := by simp
  have A := hpair _ hv hv'
  have B := hpair _ hu hu'
  rw [e3, e4] at A
  rw [e1, e2, hre] at B
  linarith

/-- Three distinct points `q₁, σq₁, q₂` of a summable family whose sums over the orbits of the
involution `σ` are nonnegative bound twice the total sum from below. -/
theorem le_two_mul_tsum_of_involution {ι : Type*} {φ : ι → ℝ} (hφ : Summable φ) (σ : ι ≃ ι)
    (hpair : ∀ q, 0 ≤ φ q + φ (σ q)) {q₁ q₂ : ι} (h1 : q₁ ≠ σ q₁) (h2 : q₂ ≠ q₁)
    (h3 : q₂ ≠ σ q₁) :
    (φ q₁ + φ (σ q₁)) + (φ (σ q₁) + φ (σ (σ q₁))) + (φ q₂ + φ (σ q₂)) ≤ 2 * ∑' q, φ q := by
  classical
  have hφσ : Summable (fun q => φ (σ q)) := σ.summable_iff.mpr hφ
  have hψ : Summable (fun q => φ q + φ (σ q)) := hφ.add hφσ
  have htwo : ∑' q, (φ q + φ (σ q)) = 2 * ∑' q, φ q := by
    rw [hφ.tsum_add hφσ, σ.tsum_eq φ]; ring
  have := hψ.sum_le_tsum {q₁, σ q₁, q₂} (fun q _ => hpair q)
  rw [Finset.sum_insert (by simp [h1, Ne.symm h2]), Finset.sum_insert (by simp [Ne.symm h3]),
    Finset.sum_singleton] at this
  linarith

/-- The doubled pair contribution at the zero `z` itself (`ζ = z` or `ζ = z̄`, `Im z = y`):
`log((λ(2y+λ))²) − log((λ(2y−λ))²) = 2 log((2y+λ)/(2y−λ))`. -/
theorem log_pair_self_eq {y lam : ℝ} (hlam : 0 < lam) (hlam2 : lam < 2 * y) (b : ℝ)
    (hb : b = y ∨ b = -y) :
    Real.log ((0 + (b - y - lam) ^ 2) * (0 + (b + y + lam) ^ 2)) -
        Real.log ((0 + (b - y + lam) ^ 2) * (0 + (b + y - lam) ^ 2)) =
      2 * Real.log ((2 * y + lam) / (2 * y - lam)) := by
  have hx : 0 < 2 * y - lam := by linarith
  have hx' : 0 < 2 * y + lam := by linarith
  have e : (0 + (b - y - lam) ^ 2) * (0 + (b + y + lam) ^ 2) = (lam * (2 * y + lam)) ^ 2 ∧
      (0 + (b - y + lam) ^ 2) * (0 + (b + y - lam) ^ 2) = (lam * (2 * y - lam)) ^ 2 := by
    rcases hb with rfl | rfl <;> constructor <;> ring
  rw [e.1, e.2, Real.log_pow, Real.log_pow, Real.log_mul hlam.ne' hx'.ne',
    Real.log_mul hlam.ne' hx.ne', Real.log_div hx'.ne' hx.ne']
  push_cast
  ring

/-- **The Hadamard lower bound at a top zero.** Let `z*` be a zero of a real even entire `f` of
order one with `y* = Im z* > 0` maximal among the imaginary parts of the zeros, and `x_r` a real
zero. For `0 < λ < 2y*` with `f(z* ± iλ) ≠ 0`,
`λ/y* + 2y*λ/((x_r − Re z*)² + (y* + λ)²) ≤ log|f(z* + iλ)| − log|f(z* − iλ)|`.
Every conjugate pair of zeros contributes nonnegatively (local pair law); the pair `z*, z̄*`
contributes `log((2y* + λ)/(2y* − λ))` and the real zero `½ log` of the ratio of its squared
distances. -/
theorem le_log_sub_of_top_zero_of_hadamard {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {zs : ℂ} (hzs : f zs = 0)
    (hys : 0 < zs.im) (htop : ∀ ζ, f ζ = 0 → ζ.im ^ 2 ≤ zs.im ^ 2) {xr : ℝ}
    (hxr : f xr = 0) {lam : ℝ} (hlam : 0 < lam) (hlam2 : lam < 2 * zs.im)
    (hu : f (zs - lam * I) ≠ 0) (hv : f (zs + lam * I) ≠ 0) :
    lam / zs.im + 2 * zs.im * lam / ((xr - zs.re) ^ 2 + (zs.im + lam) ^ 2) ≤
      Real.log ‖f (zs + lam * I)‖ - Real.log ‖f (zs - lam * I)‖ := by
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  rw [norm_eq_exp_tsum hC hf hf0 heven hbound hu, norm_eq_exp_tsum hC hf hf0 heven hbound hv,
    Real.log_mul (norm_ne_zero_iff.mpr hf0) (Real.exp_pos _).ne',
    Real.log_mul (norm_ne_zero_iff.mpr hf0) (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  have hsu := summable_log_norm_weierstrassE1 hsum (zs - lam * I)
  have hsv := summable_log_norm_weierstrassE1 hsum (zs + lam * I)
  rw [add_sub_add_left_eq_sub, ← hsv.tsum_sub hsu]
  have hne : ∀ w : ℂ, f w ≠ 0 → ∀ ξ : ℂ, f ξ = 0 → w ≠ ξ := fun w hw ξ hξ h => hw (h ▸ hξ)
  -- the doubled orbit sums in terms of squared distances
  have hpairval : ∀ q : ZeroCopy f,
      2 * ((Real.log ‖weierstrassE1 ((zs + lam * I) / zeroCopyPoint f q)‖ -
          Real.log ‖weierstrassE1 ((zs - lam * I) / zeroCopyPoint f q)‖) +
        (Real.log ‖weierstrassE1 ((zs + lam * I) / zeroCopyPoint f (zeroCopyConj hf hconj q))‖ -
          Real.log ‖weierstrassE1 ((zs - lam * I) / zeroCopyPoint f (zeroCopyConj hf hconj q))‖)) =
      Real.log ((((zeroCopyPoint f q).re - zs.re) ^ 2 +
            ((zeroCopyPoint f q).im - zs.im - lam) ^ 2) *
          (((zeroCopyPoint f q).re - zs.re) ^ 2 + ((zeroCopyPoint f q).im + zs.im + lam) ^ 2)) -
        Real.log ((((zeroCopyPoint f q).re - zs.re) ^ 2 +
            ((zeroCopyPoint f q).im - zs.im + lam) ^ 2) *
          (((zeroCopyPoint f q).re - zs.re) ^ 2 + ((zeroCopyPoint f q).im + zs.im - lam) ^ 2)) := by
    intro q
    have hζz : f (zeroCopyPoint f q) = 0 := apply_zeroCopyPoint hf q
    have hζcz : f ((starRingEnd ℂ) (zeroCopyPoint f q)) = 0 := by rw [hconj, hζz, map_zero]
    rw [← two_mul_log_pair_sub_eq (hane q) lam (hne _ hu _ hζz) (hne _ hu _ hζcz)
      (hne _ hv _ hζz) (hne _ hv _ hζcz), zeroCopyPoint_conj hf hconj q]
    ring
  -- positivity of the squared distances from `z* − iλ`
  have hdist : ∀ ζ : ℂ, f ζ = 0 →
      0 < (ζ.re - zs.re) ^ 2 + (ζ.im - zs.im + lam) ^ 2 := by
    intro ζ hζ
    have := hne _ hu _ hζ
    by_contra h0
    have ha : ζ.re - zs.re = 0 := by nlinarith [sq_nonneg (ζ.re - zs.re), sq_nonneg (ζ.im - zs.im + lam)]
    have hb : ζ.im - zs.im + lam = 0 := by
      nlinarith [sq_nonneg (ζ.re - zs.re), sq_nonneg (ζ.im - zs.im + lam)]
    exact this (Complex.ext (by simp; linarith) (by simp; linarith))
  have hpairnn : ∀ q : ZeroCopy f,
      0 ≤ (Real.log ‖weierstrassE1 ((zs + lam * I) / zeroCopyPoint f q)‖ -
          Real.log ‖weierstrassE1 ((zs - lam * I) / zeroCopyPoint f q)‖) +
        (Real.log ‖weierstrassE1 ((zs + lam * I) / zeroCopyPoint f (zeroCopyConj hf hconj q))‖ -
          Real.log ‖weierstrassE1 ((zs - lam * I) / zeroCopyPoint f (zeroCopyConj hf hconj q))‖) := by
    intro q
    have hζz : f (zeroCopyPoint f q) = 0 := apply_zeroCopyPoint hf q
    have hζcz : f ((starRingEnd ℂ) (zeroCopyPoint f q)) = 0 := by rw [hconj, hζz, map_zero]
    have hb := htop _ hζz
    have h1 := hdist _ hζz
    have h2 := hdist _ hζcz
    simp only [Complex.conj_re, Complex.conj_im] at h2
    set a := (zeroCopyPoint f q).re - zs.re
    set b := (zeroCopyPoint f q).im
    set y := zs.im
    have hle : (a ^ 2 + (b - y + lam) ^ 2) * (a ^ 2 + (b + y - lam) ^ 2) ≤
        (a ^ 2 + (b - y - lam) ^ 2) * (a ^ 2 + (b + y + lam) ^ 2) := by
      have : 0 ≤ 8 * y * lam * (a ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by
        have : 0 ≤ a ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg lam]
        positivity
      nlinarith
    have hlog := Real.log_le_log (mul_pos h1 (by nlinarith [h2])) hle
    have := hpairval q
    linarith
  -- the three distinguished copies
  obtain ⟨q₁, hq₁⟩ := exists_zeroCopy_of_eq_zero hf hf0 hzs
  obtain ⟨q₂, hq₂⟩ := exists_zeroCopy_of_eq_zero hf hf0 hxr
  have hσq₁ : zeroCopyPoint f (zeroCopyConj hf hconj q₁) = (starRingEnd ℂ) zs := by
    rw [zeroCopyPoint_conj hf hconj q₁, hq₁]
  have hne1 : q₁ ≠ zeroCopyConj hf hconj q₁ := by
    intro h
    have := congrArg (fun q => (zeroCopyPoint f q).im) h
    simp only [hσq₁, hq₁, Complex.conj_im] at this
    linarith
  have hne2 : q₂ ≠ q₁ := by
    intro h
    have := congrArg (fun q => (zeroCopyPoint f q).im) h
    simp only [hq₁, hq₂, Complex.ofReal_im] at this
    linarith
  have hne3 : q₂ ≠ zeroCopyConj hf hconj q₁ := by
    intro h
    have := congrArg (fun q => (zeroCopyPoint f q).im) h
    simp only [hσq₁, hq₂, Complex.ofReal_im, Complex.conj_im] at this
    linarith
  have hfin := le_two_mul_tsum_of_involution (hsv.sub hsu) (zeroCopyConj hf hconj)
    hpairnn hne1 hne2 hne3
  -- evaluate the three orbit sums
  have hden : 0 < (xr - zs.re) ^ 2 + (zs.im - lam) ^ 2 := by
    have := hdist _ hxr
    simp only [Complex.ofReal_re, Complex.ofReal_im] at this
    nlinarith [this]
  have hden' : 0 < (xr - zs.re) ^ 2 + (zs.im + lam) ^ 2 := by positivity
  have hv1 := (hpairval q₁).trans (show _ = 2 * Real.log ((2 * zs.im + lam) / (2 * zs.im - lam)) by
    rw [hq₁, sub_self, zero_pow two_ne_zero]
    exact log_pair_self_eq hlam hlam2 zs.im (Or.inl rfl))
  have hv2 := (hpairval (zeroCopyConj hf hconj q₁)).trans
    (show _ = 2 * Real.log ((2 * zs.im + lam) / (2 * zs.im - lam)) by
      rw [hσq₁, Complex.conj_re, Complex.conj_im, sub_self, zero_pow two_ne_zero]
      exact log_pair_self_eq hlam hlam2 (-zs.im) (Or.inr rfl))
  have hv3 := (hpairval q₂).trans (show _ = 2 * Real.log ((xr - zs.re) ^ 2 + (zs.im + lam) ^ 2) -
      2 * Real.log ((xr - zs.re) ^ 2 + (zs.im - lam) ^ 2) by
    rw [hq₂, Complex.ofReal_re, Complex.ofReal_im,
      show ((xr - zs.re) ^ 2 + (0 - zs.im - lam) ^ 2) *
          ((xr - zs.re) ^ 2 + (0 + zs.im + lam) ^ 2) =
        ((xr - zs.re) ^ 2 + (zs.im + lam) ^ 2) ^ 2 by ring,
      show ((xr - zs.re) ^ 2 + (0 - zs.im + lam) ^ 2) *
          ((xr - zs.re) ^ 2 + (0 + zs.im - lam) ^ 2) =
        ((xr - zs.re) ^ 2 + (zs.im - lam) ^ 2) ^ 2 by ring,
      Real.log_pow, Real.log_pow]
    push_cast
    ring)
  -- the elementary lower bounds
  set y := zs.im
  set X2 := (xr - zs.re) ^ 2
  have hL1 : lam / y ≤ Real.log ((2 * y + lam) / (2 * y - lam)) := by
    have h := two_mul_le_log_div (s := lam / (2 * y)) (by positivity)
      (by rw [div_lt_one (by positivity)]; exact hlam2)
    rw [show (1 + lam / (2 * y)) / (1 - lam / (2 * y)) = (2 * y + lam) / (2 * y - lam) by
      field_simp] at h
    calc lam / y = 2 * (lam / (2 * y)) := by field_simp
      _ ≤ _ := h
  have hL2 : 4 * y * lam / (X2 + (y + lam) ^ 2) ≤
      Real.log (X2 + (y + lam) ^ 2) - Real.log (X2 + (y - lam) ^ 2) := by
    set w := 4 * y * lam / (X2 + (y - lam) ^ 2)
    have hw0 : 0 ≤ w := by positivity
    have h := div_one_add_le_log hw0
    have e1 : 1 + w = (X2 + (y + lam) ^ 2) / (X2 + (y - lam) ^ 2) := by
      simp only [w]; field_simp; ring
    have e2 : w / (1 + w) = 4 * y * lam / (X2 + (y + lam) ^ 2) := by
      rw [e1]; simp only [w]; field_simp
    rw [e2, e1, Real.log_div hden'.ne' hden.ne'] at h
    exact h
  have e3 : 2 * y * lam / (X2 + (y + lam) ^ 2) = (1 / 2) * (4 * y * lam / (X2 + (y + lam) ^ 2)) := by
    ring
  linarith

theorem le_log_sub_of_top_zero {t : ℝ} (ht : 0 ≤ t) {zs : ℂ} (hzs : riemannHeat t zs = 0)
    (hys : 0 < zs.im) (htop : ∀ ζ, riemannHeat t ζ = 0 → ζ.im ^ 2 ≤ zs.im ^ 2) {xr : ℝ}
    (hxr : riemannHeat t xr = 0) {lam : ℝ} (hlam : 0 < lam) (hlam2 : lam < 2 * zs.im)
    (hu : riemannHeat t (zs - lam * I) ≠ 0) (hv : riemannHeat t (zs + lam * I) ≠ 0) :
    lam / zs.im + 2 * zs.im * lam / ((xr - zs.re) ^ 2 + (zs.im + lam) ^ 2) ≤
      Real.log ‖riemannHeat t (zs + lam * I)‖ - Real.log ‖riemannHeat t (zs - lam * I)‖ := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht).exists_envelope
  exact le_log_sub_of_top_zero_of_hadamard hC (riemannHeat_analytic ht) (riemannHeat_zero_ne ht)
    (riemannHeat_neg ht) (riemannHeat_conj ht) hbound hzs hys htop hxr hlam hlam2 hu hv

end Hadamard

/-! ## The Taylor upper bound -/

/-- **Logarithmic modulus near a simple zero.** If `‖g(z* + w) − Aw − Bw²‖ ≤ M‖w‖³`, `A ≠ 0`,
`0 < ‖w‖ ≤ 1` and `2(‖B‖ + M)‖w‖ ≤ ‖A‖`, then `g(z* + w) ≠ 0` and
`|log|g(z* + w)| − log|A| − log|w| − Re(Bw/A)| ≤ (M/|A| + (‖B‖ + M)²/|A|²)|w|²`. -/
theorem abs_log_norm_sub_le_of_taylor {g : ℂ → ℂ} {zs A B : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hA : A ≠ 0) {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ ≤ 1)
    (hT : ‖g (zs + w) - A * w - B * w ^ 2‖ ≤ M * ‖w‖ ^ 3)
    (hsmall : 2 * (‖B‖ + M) * ‖w‖ ≤ ‖A‖) :
    g (zs + w) ≠ 0 ∧
      |Real.log ‖g (zs + w)‖ - (Real.log ‖A‖ + Real.log ‖w‖ + (B / A * w).re)| ≤
        (M / ‖A‖ + (‖B‖ + M) ^ 2 / ‖A‖ ^ 2) * ‖w‖ ^ 2 := by
  set l := ‖w‖ with hl
  set a := ‖A‖ with ha
  have hl0 : 0 < l := norm_pos_iff.mpr hw0
  have ha0 : 0 < a := norm_pos_iff.mpr hA
  have hAw : A * w ≠ 0 := mul_ne_zero hA hw0
  set R := g (zs + w) - A * w - B * w ^ 2 with hR
  set e := R / (A * w) with he
  set u := B / A * w + e with hu
  have hg : g (zs + w) = A * w * (1 + u) := by
    rw [hu, he, mul_add, mul_add, mul_div_cancel₀ _ hAw, hR]
    field_simp
    ring
  have hen : ‖e‖ ≤ M * l ^ 2 / a := by
    rw [he, norm_div, norm_mul, div_le_div_iff₀ (by positivity) ha0]
    calc ‖R‖ * a ≤ M * l ^ 3 * a := by gcongr
      _ = M * l ^ 2 * (a * l) := by ring
  have hBn : ‖B / A * w‖ = ‖B‖ * l / a := by rw [norm_mul, norm_div]; ring
  have hun : ‖u‖ ≤ (‖B‖ + M) * l / a := by
    calc ‖u‖ ≤ ‖B / A * w‖ + ‖e‖ := norm_add_le _ _
      _ ≤ ‖B‖ * l / a + M * l ^ 2 / a := by rw [hBn]; gcongr
      _ ≤ (‖B‖ + M) * l / a := by
        rw [← add_div]
        gcongr
        have : M * l ^ 2 ≤ M * l := mul_le_mul_of_nonneg_left (by nlinarith) hM
        nlinarith [norm_nonneg B]
  have hhalf : (‖B‖ + M) * l / a ≤ 1 / 2 := by
    rw [div_le_iff₀ ha0]; linarith
  have hu1 : ‖u‖ < 1 := by linarith
  have h1u : 0 < ‖1 + u‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-u)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  refine ⟨by rw [hg]; exact mul_ne_zero hAw (norm_pos_iff.mp h1u), ?_⟩
  rw [hg, norm_mul, norm_mul, Real.log_mul (by positivity) h1u.ne',
    Real.log_mul ha0.ne' hl0.ne']
  have hlog : |Real.log ‖1 + u‖ - u.re| ≤ ‖u‖ ^ 2 := by
    rw [← Complex.log_re, ← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ((Complex.norm_log_one_add_sub_self_le hu1).trans ?_)
    have h2 : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hre : u.re = (B / A * w).re + e.re := by rw [hu, Complex.add_re]
  have here : |e.re| ≤ M * l ^ 2 / a := (Complex.abs_re_le_norm e).trans hen
  have hu2 : ‖u‖ ^ 2 ≤ (‖B‖ + M) ^ 2 / a ^ 2 * l ^ 2 := by
    calc ‖u‖ ^ 2 ≤ ((‖B‖ + M) * l / a) ^ 2 := by gcongr
      _ = _ := by ring
  have e1 : Real.log a + Real.log l + Real.log ‖1 + u‖ -
      (Real.log a + Real.log l + (B / A * w).re) = (Real.log ‖1 + u‖ - u.re) + e.re := by
    rw [hre]; ring
  rw [e1]
  calc |(Real.log ‖1 + u‖ - u.re) + e.re| ≤ |Real.log ‖1 + u‖ - u.re| + |e.re| := abs_add_le _ _
    _ ≤ (‖B‖ + M) ^ 2 / a ^ 2 * l ^ 2 + M * l ^ 2 / a := by linarith
    _ = (M / a + (‖B‖ + M) ^ 2 / a ^ 2) * l ^ 2 := by ring

/-- **The vertical log-ratio at a simple zero.** Near a simple zero `z*` of `H_t` (`t ≥ 0`),
`log|H_t(z* + iλ)| − log|H_t(z* − iλ)| ≤ −λ Im(H_t''(z*)/H_t'(z*)) + Cλ²` for small `λ > 0`. -/
theorem log_sub_le_of_simple_zero {t : ℝ} (ht : 0 ≤ t) {zs : ℂ}
    (hzs : riemannHeat t zs = 0) (hd : deriv (riemannHeat t) zs ≠ 0) :
    ∃ l₀ > 0, ∃ C, ∀ lam : ℝ, 0 < lam → lam ≤ l₀ →
      riemannHeat t (zs - lam * I) ≠ 0 ∧ riemannHeat t (zs + lam * I) ≠ 0 ∧
        Real.log ‖riemannHeat t (zs + lam * I)‖ - Real.log ‖riemannHeat t (zs - lam * I)‖ ≤
          -lam * (deriv (deriv (riemannHeat t)) zs / deriv (riemannHeat t) zs).im +
            C * lam ^ 2 := by
  set A := deriv (riemannHeat t) zs
  set B := deriv (deriv (riemannHeat t)) zs / 2
  set M := ∫ x, |x| ^ 3 * ‖heatWeight t x‖ * Real.exp ((|zs.im| + 1) * |x|)
  have hM : 0 ≤ M := integral_nonneg fun x => by positivity
  have ha0 : 0 < ‖A‖ := norm_pos_iff.mpr hd
  set l₀ := min 1 (‖A‖ / (2 * (‖B‖ + M) + 1))
  have hl₀ : 0 < l₀ := lt_min one_pos (by positivity)
  refine ⟨l₀, hl₀, 2 * (M / ‖A‖ + (‖B‖ + M) ^ 2 / ‖A‖ ^ 2), fun lam hlam hle => ?_⟩
  have key : ∀ w : ℂ, ‖w‖ = lam → riemannHeat t (zs + w) ≠ 0 ∧
      |Real.log ‖riemannHeat t (zs + w)‖ - (Real.log ‖A‖ + Real.log lam + (B / A * w).re)| ≤
        (M / ‖A‖ + (‖B‖ + M) ^ 2 / ‖A‖ ^ 2) * lam ^ 2 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hw; linarith
    have hw1 : ‖w‖ ≤ 1 := by rw [hw]; exact hle.trans (min_le_left _ _)
    have hT := norm_riemannHeat_taylor_three_le ht (z₀ := zs) (z := zs + w)
      (by rw [add_sub_cancel_left]; exact hw1)
    rw [add_sub_cancel_left, hzs, sub_zero] at hT
    have hsmall : 2 * (‖B‖ + M) * ‖w‖ ≤ ‖A‖ := by
      have h2 : lam ≤ ‖A‖ / (2 * (‖B‖ + M) + 1) := hle.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h2
      rw [hw]
      nlinarith
    have := abs_log_norm_sub_le_of_taylor (g := riemannHeat t) (zs := zs) hM hd hw0 hw1
      hT hsmall
    rw [hw] at this
    exact this
  have hp := key (lam * I) (by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlam])
  have hm := key (-(lam * I)) (by rw [norm_neg, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam])
  rw [← sub_eq_add_neg] at hm
  refine ⟨hm.1, hp.1, ?_⟩
  have hre : (B / A * (lam * I)).re - (B / A * -(lam * I)).re =
      -lam * (deriv (deriv (riemannHeat t)) zs / A).im := by
    have e : B / A = (deriv (deriv (riemannHeat t)) zs / A) / 2 := by simp only [B]; ring
    rw [e]
    simp only [mul_neg, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im]
    ring
  have h1 := (abs_le.mp hp.2).2
  have h2 := (abs_le.mp hm.2).1
  linarith

/-! ## The velocity of the top zero -/

/-- **The top zero descends strictly faster than de Bruijn's rate.** Let `z*` be a simple zero of
`H_t` (`t ≥ 0`) with `y* = Im z* > 0` maximal among the imaginary parts of the zeros, and `x_r` a
real zero of `H_t`. Then
`Im(H_t''(z*)/H_t'(z*)) ≤ −1/y* − 2y*/((x_r − Re z*)² + y*²)`. -/
theorem im_ratio_le_of_top_zero {t : ℝ} (ht : 0 ≤ t) {zs : ℂ} (hzs : riemannHeat t zs = 0)
    (hd : deriv (riemannHeat t) zs ≠ 0) (hys : 0 < zs.im)
    (htop : ∀ ζ, riemannHeat t ζ = 0 → ζ.im ^ 2 ≤ zs.im ^ 2) {xr : ℝ}
    (hxr : riemannHeat t xr = 0) :
    (deriv (deriv (riemannHeat t)) zs / deriv (riemannHeat t) zs).im ≤
      -1 / zs.im - 2 * zs.im / ((xr - zs.re) ^ 2 + zs.im ^ 2) := by
  obtain ⟨l₀, hl₀, C, hC⟩ := log_sub_le_of_simple_zero ht hzs hd
  set y := zs.im
  set X2 := (xr - zs.re) ^ 2
  set m := (deriv (deriv (riemannHeat t)) zs / deriv (riemannHeat t) zs).im
  have hF : Tendsto (fun l : ℝ => -1 / y - 2 * y / (X2 + (y + l) ^ 2) + C * l) (𝓝[>] 0)
      (𝓝 (-1 / y - 2 * y / (X2 + y ^ 2))) := by
    have hc : ContinuousAt (fun l : ℝ => -1 / y - 2 * y / (X2 + (y + l) ^ 2) + C * l) 0 := by
      refine ContinuousAt.add (continuousAt_const.sub (continuousAt_const.div (by fun_prop) ?_))
        (by fun_prop)
      positivity
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine ge_of_tendsto hF ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hl₀ hys)] with lam hlam
  have hl0 : 0 < lam := hlam.1
  have hly : lam < y := hlam.2.trans_le (min_le_right _ _)
  obtain ⟨hu, hv, hup⟩ := hC lam hl0 (hlam.2.le.trans (min_le_left _ _))
  have hlow := le_log_sub_of_top_zero ht hzs hys htop hxr hl0 (by linarith) hu hv
  have hden : 0 < X2 + (y + lam) ^ 2 := by positivity
  have e1 : lam / y = lam * (1 / y) := by ring
  have e2 : 2 * y * lam / (X2 + (y + lam) ^ 2) = lam * (2 * y / (X2 + (y + lam) ^ 2)) := by ring
  have hmain : lam * (1 / y + 2 * y / (X2 + (y + lam) ^ 2)) ≤ lam * (-m + C * lam) := by
    nlinarith
  have := le_of_mul_le_mul_left hmain hl0
  have e3 : -1 / y = -(1 / y) := by ring
  linarith


end

end RHTower.DeBruijn
