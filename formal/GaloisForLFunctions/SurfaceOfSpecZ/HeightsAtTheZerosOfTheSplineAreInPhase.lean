import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEverySamplingSet

/-!
# Heights at the zeros of the spline are in phase

The zero `½ + x + iγ` enters the spline traces with the coefficient `sinc(γ − ix)⁸` (`B̂ = sinc⁴`,
`k̂ = B̂²`), whose phase is uncontrolled in general. At the zeros `γ = 2πM` of `B̂` it is not:
`sin(2πM − ix) = −i sinh x`, so

  `sinc(2πM − ix)⁸ = sinh⁸ x / (2πM − ix)⁸`

has phase `O(x/M)` (`re_sincPow_mul_exp_ge`), modulus between `x⁸/(7M)⁸` and `1/M⁸`
(`norm_sincPow_le`, `le_norm_sincPow`). Together with simultaneous Dirichlet approximation above a
prescribed height (`exists_resonant_ge`), this places zeros in phase with every degree
`a log p + b log q` of a window, with explicitly bounded heights.

The dominance lemma (`neg_five_le_tsum_of_window`) is the positivity step of a Wolff-type tower:
weights `w_k`, depths `x_k ↑`, windows `[U_k, U_{k+1}]`; if the `k`-th term is in phase on its window,
the earlier ones are dominated there and the later ones are negligible, the sum is `≥ −5`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### Simultaneous Dirichlet approximation above a given height -/

/-- **Dirichlet above a height.** For `A, Q ≥ 1` some `M ∈ [A, 2A + (2AQ)^m]` has `‖M αᵢ‖ ≤ 1/Q`:
either the Dirichlet denominator `d` for precision `1/(2AQ)` is `≥ A`, or its multiple `⌈A/d⌉d`
works. -/
theorem exists_resonant_ge {m : ℕ} (α : Fin m → ℝ) {A Q : ℕ} (hA : 1 ≤ A) (hQ : 1 ≤ Q) :
    ∃ M : ℕ, A ≤ M ∧ M ≤ 2 * A + (2 * A * Q) ^ m ∧
      ∀ i, ∃ r : ℤ, |(M : ℝ) * α i - r| ≤ 1 / Q := by
  obtain ⟨d, hd1, hdle, hd⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet α
    (Q := 2 * A * Q) (by positivity)
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hden : ((2 * A * Q : ℕ) : ℝ) = 2 * A * Q := by push_cast; ring
  by_cases hdA : A ≤ d
  · refine ⟨d, hdA, by omega, fun i => ?_⟩
    obtain ⟨r, hr⟩ := hd i
    refine ⟨r, hr.le.trans ?_⟩
    rw [hden, div_le_div_iff₀ (by positivity) hQ']
    nlinarith
  · push Not at hdA
    have hd0 : 0 < d := hd1
    have h1 : A / d * d ≤ A := Nat.div_mul_le_self A d
    have h2 : A < A / d * d + d := Nat.lt_div_mul_add hd0
    have hjA : A / d + 1 ≤ 2 * A := by have := Nat.div_le_self A d; omega
    refine ⟨(A / d + 1) * d, ?_, ?_, fun i => ?_⟩
    · rw [add_mul, one_mul]; generalize A / d * d = t at *; omega
    · rw [add_mul, one_mul]; generalize A / d * d = t at *; omega
    · obtain ⟨r, hr⟩ := hd i
      refine ⟨((A / d + 1 : ℕ) : ℤ) * r, ?_⟩
      have hjle : ((A / d + 1 : ℕ) : ℝ) ≤ 2 * A := by exact_mod_cast hjA
      rw [show (((A / d + 1) * d : ℕ) : ℝ) * α i - (((A / d + 1 : ℕ) : ℤ) * r : ℤ) =
          ((A / d + 1 : ℕ) : ℝ) * ((d : ℝ) * α i - r) by push_cast; ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((A / d + 1 : ℕ) : ℝ))]
      calc ((A / d + 1 : ℕ) : ℝ) * |(d : ℝ) * α i - r|
          ≤ 2 * A * (1 / ((2 * A * Q : ℕ) : ℝ)) :=
            mul_le_mul hjle hr.le (abs_nonneg _) (by positivity)
        _ = 1 / Q := by rw [hden]; field_simp

/-! ### The spline coefficient at the zeros of `B̂` -/

/-- `sin(2πM − ix) = −i sinh x`. -/
theorem sin_two_pi_nat_sub (M : ℕ) (x : ℝ) :
    Complex.sin (((2 * Real.pi * M : ℝ) : ℂ) - x * I) = -(I * (Real.sinh x : ℂ)) := by
  have h1 : Complex.sin ((2 * Real.pi * M : ℝ) : ℂ) = 0 := by
    have := Complex.sin_nat_mul_pi (2 * M)
    rw [← this]; push_cast; ring_nf
  have h2 : Complex.cos ((2 * Real.pi * M : ℝ) : ℂ) = 1 := by
    have := Complex.cos_nat_mul_two_pi M
    rw [← this]; push_cast; ring_nf
  rw [Complex.sin_sub, Complex.sin_mul_I, Complex.cos_mul_I, h1, h2, ← Complex.ofReal_sinh]
  ring

/-- The spectral point `2πM − ix`. -/
def splinePoint (M : ℕ) (x : ℝ) : ℂ := ((2 * Real.pi * M : ℝ) : ℂ) - x * I

theorem splinePoint_re (M : ℕ) (x : ℝ) : (splinePoint M x).re = 2 * Real.pi * M := by
  simp [splinePoint]

theorem splinePoint_im (M : ℕ) (x : ℝ) : (splinePoint M x).im = -x := by
  simp [splinePoint]

theorem splinePoint_ne_zero {M : ℕ} (hM : 1 ≤ M) (x : ℝ) : splinePoint M x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [splinePoint_re, Complex.zero_re] at this
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [Real.pi_pos]

/-- **At the zeros of `B̂`:** `sinc(2πM − ix)⁸ = sinh⁸ x / (2πM − ix)⁸`. -/
theorem sincC_splinePoint_pow {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    sincC (splinePoint M x) ^ 8 = ((Real.sinh x ^ 8 : ℝ) : ℂ) / splinePoint M x ^ 8 := by
  rw [sincC, if_neg (splinePoint_ne_zero hM x), splinePoint, sin_two_pi_nat_sub, div_pow,
    ← splinePoint]
  congr 1
  have hI : (-(I * (Real.sinh x : ℂ))) ^ 8 = (I ^ 2) ^ 4 * (Real.sinh x : ℂ) ^ 8 := by ring
  rw [hI, Complex.I_sq]; push_cast; ring

theorem norm_splinePoint_ge (M : ℕ) (x : ℝ) : 2 * Real.pi * M ≤ ‖splinePoint M x‖ := by
  have h := Complex.abs_re_le_norm (splinePoint M x)
  rw [splinePoint_re] at h
  exact (le_abs_self _).trans h

theorem norm_splinePoint_le (M : ℕ) (x : ℝ) : ‖splinePoint M x‖ ≤ 2 * Real.pi * M + |x| := by
  have h := Complex.norm_le_abs_re_add_abs_im (splinePoint M x)
  rw [splinePoint_re, splinePoint_im, abs_neg] at h
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * M)] at h

theorem norm_sincPow_eq {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    ‖sincC (splinePoint M x) ^ 8‖ = Real.sinh x ^ 8 / ‖splinePoint M x‖ ^ 8 := by
  rw [sincC_splinePoint_pow hM, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sinh x ^ 8)]

theorem sinh_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : Real.sinh x ≤ 1 := by
  rw [Real.sinh_eq]
  have h1 : Real.exp x ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hx1
  have h2 : Real.exp (1 / 2) < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr (by linarith [Real.log_two_gt_d9])
  have h3 : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

/-- **Modulus from above:** `‖sinc(2πM − ix)⁸‖ ≤ 1/M⁸` for `0 ≤ x ≤ ½`. -/
theorem norm_sincPow_le {M : ℕ} (hM : 1 ≤ M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖sincC (splinePoint M x) ^ 8‖ ≤ 1 / (M : ℝ) ^ 8 := by
  rw [norm_sincPow_eq hM]
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hw : (M : ℝ) ≤ ‖splinePoint M x‖ :=
    le_trans (by nlinarith [Real.pi_gt_three]) (norm_splinePoint_ge M x)
  have hs0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  have hs : Real.sinh x ^ 8 ≤ 1 := pow_le_one₀ hs0 (sinh_le_one hx0 hx1)
  calc Real.sinh x ^ 8 / ‖splinePoint M x‖ ^ 8 ≤ 1 / ‖splinePoint M x‖ ^ 8 :=
        div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ 1 / (M : ℝ) ^ 8 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hw 8)

/-- **Modulus from below:** `‖sinc(2πM − ix)⁸‖ ≥ x⁸/(7M)⁸` for `0 ≤ x ≤ ½`. -/
theorem le_norm_sincPow {M : ℕ} (hM : 1 ≤ M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    x ^ 8 / (7 * M : ℝ) ^ 8 ≤ ‖sincC (splinePoint M x) ^ 8‖ := by
  rw [norm_sincPow_eq hM]
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hw0 : 0 < ‖splinePoint M x‖ := norm_pos_iff.mpr (splinePoint_ne_zero hM x)
  have hw : ‖splinePoint M x‖ ≤ 7 * M := by
    have := norm_splinePoint_le M x
    rw [abs_of_nonneg hx0] at this
    nlinarith [Real.pi_lt_d2]
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0
  calc x ^ 8 / (7 * M : ℝ) ^ 8 ≤ Real.sinh x ^ 8 / (7 * M : ℝ) ^ 8 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hs 8) (by positivity)
    _ ≤ Real.sinh x ^ 8 / ‖splinePoint M x‖ ^ 8 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hw0.le hw 8)

/-- `‖vⁿ − 1‖ ≤ n‖v − 1‖` on the unit circle. -/
theorem norm_pow_sub_one_le {v : ℂ} (hv : ‖v‖ = 1) (n : ℕ) : ‖v ^ n - 1‖ ≤ n * ‖v - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range n, v ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖v ^ i‖ := norm_sum_le _ _
    _ = n := by simp [norm_pow, hv]

/-- **In phase.** If `M ≥ 6`, `0 ≤ x ≤ ½` and `‖e^{iθ} − 1‖ ≤ ¼`, then
`Re(sinc(2πM − ix)⁸ e^{iθ}) ≥ ½ ‖sinc(2πM − ix)⁸‖`. -/
theorem re_sincPow_mul_exp_ge {M : ℕ} (hM : 6 ≤ M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    {θ : ℝ} (hθ : ‖cexp (θ * I) - 1‖ ≤ 1 / 4) :
    ‖sincC (splinePoint M x) ^ 8‖ / 2 ≤ (sincC (splinePoint M x) ^ 8 * cexp (θ * I)).re := by
  have hM1 : 1 ≤ M := by omega
  set w := splinePoint M x with hwdef
  have hw0 : w ≠ 0 := splinePoint_ne_zero hM1 x
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set s : ℝ := Real.sinh x ^ 8 / ‖w‖ ^ 8 with hs
  set v : ℂ := (‖w‖ : ℂ) / w with hv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn, div_self hwn.ne']
  have hc : sincC w ^ 8 = (s : ℂ) * v ^ 8 := by
    rw [hwdef, sincC_splinePoint_pow hM1, ← hwdef, hs, hv, div_pow]
    push_cast
    field_simp
  have hnc : ‖sincC w ^ 8‖ = s := by
    rw [hc, norm_mul, norm_pow, hvn, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  -- `‖v − 1‖ ≤ 2x/‖w‖ ≤ 1/37`
  have hM' : (6 : ℝ) ≤ M := by exact_mod_cast hM
  have hwge : 2 * Real.pi * M ≤ ‖w‖ := norm_splinePoint_ge M x
  have hnum : ‖(‖w‖ : ℂ) - w‖ ≤ 2 * x := by
    have hre : ((‖w‖ : ℂ) - w).re = ‖w‖ - 2 * Real.pi * M := by
      rw [Complex.sub_re, Complex.ofReal_re, hwdef, splinePoint_re]
    have him : ((‖w‖ : ℂ) - w).im = x := by
      rw [Complex.sub_im, Complex.ofReal_im, hwdef, splinePoint_im]; ring
    have hle := Complex.norm_le_abs_re_add_abs_im ((‖w‖ : ℂ) - w)
    rw [hre, him, abs_of_nonneg hx0, abs_of_nonneg (by linarith)] at hle
    have hup := norm_splinePoint_le M x
    rw [abs_of_nonneg hx0, ← hwdef] at hup
    linarith
  have hv1 : ‖v - 1‖ ≤ 1 / 37 := by
    have : v - 1 = ((‖w‖ : ℂ) - w) / w := by rw [hv]; field_simp
    rw [this, norm_div, div_le_iff₀ hwn]
    nlinarith [Real.pi_gt_three]
  have hv8 : ‖v ^ 8 - 1‖ ≤ 8 / 37 := by
    have := norm_pow_sub_one_le hvn 8
    push_cast at this
    linarith
  -- `Re(v⁸ e^{iθ}) ≥ ½`
  have he : ‖cexp (θ * I)‖ = 1 := by rw [Complex.norm_exp_ofReal_mul_I]
  have hre : 1 / 2 ≤ (v ^ 8 * cexp (θ * I)).re := by
    have hsplit : v ^ 8 * cexp (θ * I) - 1 = (v ^ 8 - 1) * cexp (θ * I) + (cexp (θ * I) - 1) := by
      ring
    have hn : ‖v ^ 8 * cexp (θ * I) - 1‖ ≤ 8 / 37 + 1 / 4 := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, he, mul_one]
      linarith
    have h1 := Complex.abs_re_le_norm (v ^ 8 * cexp (θ * I) - 1)
    rw [Complex.sub_re, Complex.one_re] at h1
    have := neg_abs_le ((v ^ 8 * cexp (θ * I)).re - 1)
    linarith
  rw [hnc, hc, mul_assoc, Complex.re_ofReal_mul]
  have hs0 : 0 ≤ s := by positivity
  nlinarith

/-! ### Dominance windows -/

/-- **The dominance lemma.** Let `0 ≤ x_j ≤ Θ` increase, `w_j ≥ 0` with `w_0 ≤ 1` and
`w_j ≤ 2^{−j} e^{−Θ U_{j−1}}`, `U` increase from `U_0 ≥ 0`, and `|a_j|, |b_j| ≤ w_j`. On the window
`U_k ≤ λ ≤ U_{k+1}`, if `a_k ≥ w_k/2`, `a_{k+1} ≥ 0` and `w_k e^{(x_k − x_{k−1})U_k} ≥ 8`, then
`Σ_j (e^{x_jλ} a_j + e^{−x_jλ} b_j) ≥ −5`: the earlier terms are dominated by the `k`-th, the later
ones are negligible, the reflected ones sum to at most `Σ w ≤ 4`. -/
theorem neg_five_le_tsum_of_window {Θ : ℝ} (hΘ : 0 < Θ) {x w U a b : ℕ → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hxΘ : ∀ j, x j ≤ Θ) (hxm : Monotone x) (hw : ∀ j, 0 ≤ w j)
    (hw0 : w 0 ≤ 1) (hwhi : ∀ j, w (j + 1) ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * U j)))
    (hUm : Monotone U) (hU0 : 0 ≤ U 0) (ha : ∀ j, |a j| ≤ w j) (hb : ∀ j, |b j| ≤ w j)
    {lam : ℝ} (hlam : 0 ≤ lam) {k : ℕ} (hkl : U k ≤ lam) (hku : lam ≤ U (k + 1))
    (hak : w k / 2 ≤ a k) (hak1 : 0 ≤ a (k + 1))
    (hlo : ∀ n, k = n + 1 → 8 ≤ w (n + 1) * Real.exp ((x (n + 1) - x n) * U (n + 1))) :
    -5 ≤ ∑' j, (Real.exp (x j * lam) * a j + Real.exp (-(x j * lam)) * b j) := by
  -- the weights are dominated by `2 · 2^{−j}`
  have hwg : ∀ j, w j ≤ 2 * (1 / 2) ^ j := by
    intro j
    rcases j with _ | j
    · simp; linarith
    · have h1 := hwhi j
      have h2 : Real.exp (-(Θ * U j)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := hUm (Nat.zero_le j); nlinarith)
      have h3 : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
      nlinarith
  have hgeo : Summable fun j : ℕ => 2 * (1 / 2 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  have hwsum : Summable w := Summable.of_nonneg_of_le hw hwg hgeo
  have hwtot : ∑' j, w j ≤ 4 := by
    calc ∑' j, w j ≤ ∑' j : ℕ, 2 * (1 / 2 : ℝ) ^ j := Summable.tsum_le_tsum hwg hwsum hgeo
      _ = 4 := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hexpx : ∀ j, Real.exp (x j * lam) ≤ Real.exp (Θ * lam) := fun j =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxΘ j) hlam)
  have hmain : Summable fun j => Real.exp (x j * lam) * a j := by
    refine Summable.of_norm_bounded (hwsum.mul_left (Real.exp (Θ * lam))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexpx j) (ha j) (abs_nonneg _) (Real.exp_pos _).le
  have hrefl : Summable fun j => Real.exp (-(x j * lam)) * b j := by
    refine Summable.of_norm_bounded hwsum fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-(x j * lam)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := mul_nonneg (hx0 j) hlam; linarith)
    nlinarith [abs_nonneg (b j), hb j]
  rw [hmain.tsum_add hrefl]
  -- the reflected terms
  have hR : -4 ≤ ∑' j, Real.exp (-(x j * lam)) * b j := by
    have : ∑' j, -w j ≤ ∑' j, Real.exp (-(x j * lam)) * b j := by
      refine Summable.tsum_le_tsum (fun j => ?_) hwsum.neg hrefl
      have h1 : Real.exp (-(x j * lam)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := mul_nonneg (hx0 j) hlam; linarith)
      have h2 := neg_abs_le (b j)
      have h3 := hb j
      have h4 : 0 < Real.exp (-(x j * lam)) := Real.exp_pos _
      nlinarith
    rw [tsum_neg] at this
    linarith
  -- the main terms: head, the `k`-th, the `(k+1)`-st, tail
  rw [← hmain.sum_add_tsum_nat_add (k + 2), Finset.sum_range_succ, Finset.sum_range_succ]
  have htail : -1 ≤ ∑' i, Real.exp (x (i + (k + 2)) * lam) * a (i + (k + 2)) := by
    have hle : ∀ i, -((1 / 2 : ℝ) ^ (i + (k + 2))) ≤
        Real.exp (x (i + (k + 2)) * lam) * a (i + (k + 2)) := by
      intro i
      have h1 := hwhi (i + (k + 1))
      rw [show i + (k + 1) + 1 = i + (k + 2) by ring] at h1
      have hU : lam ≤ U (i + (k + 1)) := hku.trans (hUm (by omega))
      have h2 : Real.exp (x (i + (k + 2)) * lam) * Real.exp (-(Θ * U (i + (k + 1)))) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]
        have := mul_le_mul_of_nonneg_right (hxΘ (i + (k + 2))) hlam
        nlinarith
      have h3 := neg_abs_le (a (i + (k + 2)))
      have h4 := ha (i + (k + 2))
      have h5 : 0 < Real.exp (x (i + (k + 2)) * lam) := Real.exp_pos _
      have h6 : (0 : ℝ) ≤ (1 / 2) ^ (i + (k + 2)) := by positivity
      have h7 : Real.exp (x (i + (k + 2)) * lam) * w (i + (k + 2)) ≤ (1 / 2) ^ (i + (k + 2)) := by
        calc Real.exp (x (i + (k + 2)) * lam) * w (i + (k + 2))
            ≤ Real.exp (x (i + (k + 2)) * lam) *
                ((1 / 2) ^ (i + (k + 2)) * Real.exp (-(Θ * U (i + (k + 1))))) :=
              mul_le_mul_of_nonneg_left h1 h5.le
          _ = (1 / 2) ^ (i + (k + 2)) *
                (Real.exp (x (i + (k + 2)) * lam) * Real.exp (-(Θ * U (i + (k + 1))))) := by ring
          _ ≤ (1 / 2) ^ (i + (k + 2)) * 1 := mul_le_mul_of_nonneg_left h2 h6
          _ = _ := mul_one _
      nlinarith
    have hgs : Summable fun i : ℕ => (1 / 2 : ℝ) ^ (i + (k + 2)) :=
      (summable_nat_add_iff (k + 2)).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have hsum : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (k + 2)) ≤ 1 := by
      have : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (k + 2)) = (1 / 2) ^ (k + 2) * 2 := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num; ring
      rw [this]
      have : (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ (k + 2) ≤ (1 / 2) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 2 := by norm_num
      linarith
    have := Summable.tsum_le_tsum hle hgs.neg ((summable_nat_add_iff (k + 2)).mpr hmain)
    rw [tsum_neg] at this
    linarith
  -- head plus the `k`-th term is nonnegative
  have hhead : 0 ≤ ∑ j ∈ Finset.range k, Real.exp (x j * lam) * a j +
      Real.exp (x k * lam) * a k := by
    rcases k with _ | n
    · simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      have := hw 0
      have : 0 ≤ a 0 := le_trans (by linarith) hak
      positivity
    · have hlo' := hlo n rfl
      -- the head is at least `−4 e^{x_n λ}`
      have hh : -(4 * Real.exp (x n * lam)) ≤
          ∑ j ∈ Finset.range (n + 1), Real.exp (x j * lam) * a j := by
        have h1 : ∀ j ∈ Finset.range (n + 1), -(Real.exp (x n * lam) * w j) ≤
            Real.exp (x j * lam) * a j := by
          intro j hj
          have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hx : Real.exp (x j * lam) ≤ Real.exp (x n * lam) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxm hjn) hlam)
          have h2 := neg_abs_le (a j)
          have h3 := ha j
          have h4 : 0 < Real.exp (x j * lam) := Real.exp_pos _
          have h5 := hw j
          nlinarith
        have h2 := Finset.sum_le_sum h1
        have h3 : ∑ j ∈ Finset.range (n + 1), w j ≤ 4 :=
          (sum_le_tsum _ (fun j _ => hw j) hwsum).trans hwtot
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h2
        have h4 : 0 < Real.exp (x n * lam) := Real.exp_pos _
        nlinarith
      -- the `(n+1)`-st term is at least `4 e^{x_n λ}`
      have hk : 4 * Real.exp (x n * lam) ≤ Real.exp (x (n + 1) * lam) * a (n + 1) := by
        have h1 : 8 ≤ w (n + 1) * Real.exp ((x (n + 1) - x n) * lam) := by
          refine hlo'.trans (mul_le_mul_of_nonneg_left ?_ (hw _))
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkl
            (by linarith [hxm (Nat.le_succ n)]))
        have h2 : Real.exp (x (n + 1) * lam) =
            Real.exp (x n * lam) * Real.exp ((x (n + 1) - x n) * lam) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]
        have h4 : 0 < Real.exp (x n * lam) := Real.exp_pos _
        have h5 : 0 < Real.exp ((x (n + 1) - x n) * lam) := Real.exp_pos _
        nlinarith
      linarith
  have hk1 : 0 ≤ Real.exp (x (k + 1) * lam) * a (k + 1) := mul_nonneg (Real.exp_pos _).le hak1
  linarith

/-- **Every point lies in a window** of an increasing sequence from `U_0 ≤ λ` that exceeds `λ`. -/
theorem exists_window {U : ℕ → ℝ} {lam : ℝ} (hU0 : U 0 ≤ lam) (hUt : ∃ n, lam ≤ U n) :
    ∃ k, U k ≤ lam ∧ lam ≤ U (k + 1) := by
  classical
  have hex : ∃ n, lam ≤ U (n + 1) := by
    obtain ⟨n, hn⟩ := hUt
    rcases n with _ | n
    · exact ⟨0, by linarith [hU0, hn, le_antisymm hn hU0 ▸ le_refl lam] |>.trans (le_refl _)⟩
    · exact ⟨n, hn⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | m
  · exact hU0
  · have := Nat.find_min hex (show m < Nat.find hex by omega)
    push Not at this
    exact this.le

end GaloisForLFunctions.SurfaceOfSpecZ
