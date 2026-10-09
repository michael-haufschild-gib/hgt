import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount

/-!
# A gap between zeros forces a large prime polynomial

Under RH the window explicit formula for `Φ_ℓ e^{−iTu}` and `Φ_ℓ′ e^{−iTu}` reads
`S_k = ∫ψ_k(τ − T)(μ + Π_X + P_X)(τ)dτ` with `ψ_k = |(Φ_ℓ^{(k)})^|²`, `X = e^{2ℓ}` and
`S_k = Σ_γ ψ_k(γ − T)`.  The prime part is an explicit cosine polynomial
(`integral_psi_shift_mul_PX`):

  `∫ψ_k(τ − T)P_X(τ)dτ = −(1/π) Σ_{n ≤ X} Λ(n)n^{−½} ŵ_k(log n) cos(T log n)`,
  `ŵ_k(v) = ∫ψ_k(x)cos(xv)dx`,  `|ŵ_k| ≤ ∫ψ_k`,

because `ψ_k` is even (`psi_neg`).  The polar part is `O(√X/T)` against the window
(`abs_PiX_le_div`, `integral_psi_shift_mul_abs_PiX_le`).

If no zero lies within `δ = D/ℓ` of `T`, then `ψ₀(γ − T) ≤ ψ₁(γ − T)/δ²` for every zero, so
`S₀ ≤ S₁/δ²` (`tsum_psi_zero_le_of_gap`).  Comparing with the archimedean main terms
`S₀ ≈ ℓE log T`, `S₁/δ² ≤ ½ℓE log T` gives (`gap_primePoly_large`)

  `(E/2)ℓ log T − Kℓ ≤ −(1/π) Σ_{n ≤ X} Λ(n)n^{−½}(ŵ₁(log n)/δ² − ŵ₀(log n)) cos(T log n)`,

whenever `1 ≤ ℓ`, `e^{2ℓ} ≤ T` and `T ≥ 2`.  A zero-free stretch is thus a large value of a
prime polynomial of length `X`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ArithmeticFunction.vonMangoldt
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-! ## Symmetry of the window spectra -/

theorem paperFT_cb_neg (ℓ : ℝ) (k : ℕ) (y : ℝ) :
    paperFT (cb ℓ k) ((-y : ℝ) : ℂ) = starRingEnd ℂ (paperFT (cb ℓ k) (y : ℂ)) := by
  unfold paperFT
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [cb, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem psi_neg (ℓ : ℝ) (k : ℕ) (y : ℝ) : psi ℓ k (-y) = psi ℓ k y := by
  simp only [psi]
  rw [paperFT_cb_neg, Complex.norm_conj]

theorem integrable_psi_mul_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) : Integrable (fun x => psi ℓ k x * g x) :=
  (integrable_psi hℓ k).mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

/-- `ψ_k` is even, so its sine transform vanishes. -/
theorem integral_psi_mul_sin {ℓ : ℝ} (k : ℕ) (v : ℝ) :
    ∫ x, psi ℓ k x * Real.sin (x * v) = 0 := by
  have h := integral_neg_eq_self (fun x => psi ℓ k x * Real.sin (x * v)) volume
  simp only [psi_neg, neg_mul, Real.sin_neg, mul_neg, integral_neg] at h
  linarith

/-- The cosine transform `ŵ_k(v) = ∫ψ_k(x)cos(xv)dx`. -/
def wcos (ℓ : ℝ) (k : ℕ) (v : ℝ) : ℝ := ∫ x, psi ℓ k x * Real.cos (x * v)

theorem abs_wcos_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (v : ℝ) :
    |wcos ℓ k v| ≤ ∫ x, psi ℓ k x := by
  unfold wcos
  refine (abs_integral_le_integral_abs).trans (integral_mono
    (integrable_psi_mul_bdd hℓ k (by fun_prop) (fun x => Real.abs_cos_le_one _)).abs
    (integrable_psi hℓ k) (fun x => ?_))
  simp only
  rw [abs_mul, abs_of_nonneg (psi_nonneg ℓ k x)]
  exact mul_le_of_le_one_right (psi_nonneg ℓ k x) (Real.abs_cos_le_one _)

/-- `∫ψ_k(τ − T)cos(τL)dτ = ŵ_k(L)cos(TL)`. -/
theorem integral_psi_shift_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (T L : ℝ) :
    ∫ τ, psi ℓ k (τ - T) * Real.cos (τ * L) = wcos ℓ k L * Real.cos (T * L) := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun τ => psi ℓ k τ * Real.cos ((τ + T) * L)) T
  simp only [sub_add_cancel] at h
  rw [h]
  have e : ∀ τ, psi ℓ k τ * Real.cos ((τ + T) * L) =
      Real.cos (T * L) * (psi ℓ k τ * Real.cos (τ * L)) -
        Real.sin (T * L) * (psi ℓ k τ * Real.sin (τ * L)) := by
    intro τ; rw [add_mul, Real.cos_add]; ring
  simp_rw [e]
  rw [integral_sub ((integrable_psi_mul_bdd hℓ k (by fun_prop)
      (fun x => Real.abs_cos_le_one _)).const_mul _)
      ((integrable_psi_mul_bdd hℓ k (by fun_prop) (fun x => Real.abs_sin_le_one _)).const_mul _),
    integral_const_mul, integral_const_mul, integral_psi_mul_sin, mul_zero, sub_zero]
  unfold wcos
  ring

/-! ## The prime part -/

theorem continuous_PX (X : ℝ) : Continuous (PX X) := by
  unfold PX
  exact continuous_const.mul (continuous_finsetSum _ fun n _ => by fun_prop)

theorem abs_PX_le_of_nonneg {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) : |PX X τ| ≤ X ^ 2 / Real.pi :=
  abs_PX_le hX τ

/-- **The prime part of the window explicit formula is a cosine polynomial.** -/
theorem integral_psi_shift_mul_PX {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (T : ℝ) {X : ℝ} :
    ∫ τ, psi ℓ k (τ - T) * PX X τ =
      -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        Λ n / Real.sqrt n * (wcos ℓ k (Real.log n) * Real.cos (T * Real.log n)) := by
  have hint : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, Integrable (fun τ =>
      Λ n / Real.sqrt n * (psi ℓ k (τ - T) * Real.cos (τ * Real.log n))) := by
    intro n _
    refine Integrable.const_mul ?_ _
    have := (integrable_psi_mul_bdd hℓ k (g := fun x => Real.cos ((x + T) * Real.log n))
      (by fun_prop) (fun x => Real.abs_cos_le_one _)).comp_sub_right T
    simpa only [sub_add_cancel] using this
  have e : (fun τ => psi ℓ k (τ - T) * PX X τ) = fun τ =>
      -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        Λ n / Real.sqrt n * (psi ℓ k (τ - T) * Real.cos (τ * Real.log n)) := by
    funext τ
    unfold PX
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e, integral_const_mul, integral_finsetSum _ hint]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_psi_shift_mul_cos hℓ]

/-! ## The polar part -/

/-- `|Π_X(τ)| ≤ (√X + 3)/(1 + |τ|)` for `X ≥ 1`. -/
theorem abs_PiX_le_div {X : ℝ} (hX : 1 ≤ X) (τ : ℝ) :
    |PiX X τ| ≤ (Real.sqrt X + 3) / (1 + |τ|) := by
  have hπ := Real.pi_gt_three
  have hτ := abs_nonneg τ
  have hsq : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  set s : ℂ := 1 / 2 + I * (τ : ℂ) with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = τ := by simp [hs]
  have hn2 : ‖s‖ ^ 2 = 1 / 4 + τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]; ring
  have hsn : (1 + |τ|) / 3 ≤ ‖s‖ := by
    have h := Real.le_sqrt_of_sq_le (x := (1 + |τ|) / 3) (y := ‖s‖ ^ 2) (by rw [hn2]; nlinarith)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hsn0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) hsn
  have hXs : ‖(X : ℂ) ^ s‖ = Real.sqrt X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hsre, Real.sqrt_eq_rpow]
  have hq : ‖((X : ℂ) ^ s - 1) / s‖ ≤ 3 * (Real.sqrt X + 1) / (1 + |τ|) := by
    rw [norm_div, div_le_div_iff₀ hsn0 (by positivity)]
    have h := norm_sub_le ((X : ℂ) ^ s) 1
    rw [norm_one, hXs] at h
    have hsx : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    nlinarith
  have h3 := (Complex.abs_re_le_norm _).trans hq
  have h1 : 0 < 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) := by positivity
  have h2 : 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) ≤ 3 / 2 / (1 + |τ|) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : (1 + |τ|) ≤ 9 * (1 / 4 + τ ^ 2) := by nlinarith [sq_nonneg (3 * |τ| - 1 / 6)]
    have hB : 9 * (1 / 4 + τ ^ 2) ≤ 3 * Real.pi * (1 / 4 + τ ^ 2) := by nlinarith [sq_nonneg τ]
    linarith
  have e : PiX X τ = 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) *
      (((X : ℂ) ^ s - 1) / s).re := rfl
  rw [e]
  have hπi : 0 < 1 / Real.pi := by positivity
  have h4 : |(1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re| ≤ (Real.sqrt X + 1) / (1 + |τ|) := by
    rw [abs_mul, abs_of_pos hπi]
    calc 1 / Real.pi * |(((X : ℂ) ^ s - 1) / s).re|
        ≤ 1 / Real.pi * (3 * (Real.sqrt X + 1) / (1 + |τ|)) :=
          mul_le_mul_of_nonneg_left h3 hπi.le
      _ ≤ (Real.sqrt X + 1) / (1 + |τ|) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have hsx : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
          have : 0 ≤ (Real.sqrt X + 1) * (1 + |τ|) := by positivity
          rw [one_div, inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  calc |1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + 1 / Real.pi * (((X : ℂ) ^ s - 1) / s).re|
      ≤ |1 / (2 * Real.pi * (1 / 4 + τ ^ 2))| + |1 / Real.pi * (((X : ℂ) ^ s - 1) / s).re| :=
        abs_add_le _ _
    _ ≤ 3 / 2 / (1 + |τ|) + (Real.sqrt X + 1) / (1 + |τ|) := by
        rw [abs_of_pos h1]; exact add_le_add h2 h4
    _ ≤ (Real.sqrt X + 3) / (1 + |τ|) := by
        rw [← add_div]; apply div_le_div_of_nonneg_right _ (by positivity); linarith

theorem continuous_PiX {X : ℝ} (hX : 0 < X) : Continuous (PiX X) := by
  have hslit : ∀ τ : ℝ, (X : ℂ) ∈ Complex.slitPlane := fun _ => by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hX
  have hs0 : ∀ τ : ℝ, (1 / 2 + I * (τ : ℂ)) ≠ 0 := fun τ h => by
    have := congrArg Complex.re h; simp at this
  unfold PiX
  refine Continuous.add (by
    refine continuous_const.div (by fun_prop) fun τ => ?_
    have : 0 < 2 * Real.pi * (1 / 4 + τ ^ 2) := by positivity
    exact this.ne') ?_
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  refine Continuous.div ?_ (by fun_prop) hs0
  exact ((continuous_const.cpow (by fun_prop) (fun τ => hslit τ))).sub continuous_const

/-- `ψ_k(x)/(1 + |x + T|) ≤ 2ψ_k(x)/T + 4ψ_{k+1}(x)/T²`. -/
theorem psi_div_one_add_abs_le {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T) (k : ℕ) (x : ℝ) :
    psi ℓ k x / (1 + |x + T|) ≤ 2 * psi ℓ k x / T + 4 * psi ℓ (k + 1) x / T ^ 2 := by
  rw [psi_succ_eq hℓ]
  have hp := psi_nonneg ℓ k x
  have hden : 0 < 1 + |x + T| := by positivity
  by_cases hx : |x| ≤ T / 2
  · have hxT : T / 2 ≤ |x + T| := by
      have := neg_abs_le x
      rw [abs_of_pos (by linarith : (0 : ℝ) < x + T)]
      linarith
    have h1 : psi ℓ k x / (1 + |x + T|) ≤ 2 * psi ℓ k x / T := by
      rw [div_le_div_iff₀ hden hT]; nlinarith
    have h2 : 0 ≤ 4 * (x ^ 2 * psi ℓ k x) / T ^ 2 := by positivity
    linarith
  · push Not at hx
    have hx2 : T ^ 2 ≤ 4 * x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    have h1 : psi ℓ k x / (1 + |x + T|) ≤ psi ℓ k x := div_le_self hp (by linarith [abs_nonneg (x + T)])
    have h2 : psi ℓ k x ≤ 4 * (x ^ 2 * psi ℓ k x) / T ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : 0 ≤ 2 * psi ℓ k x / T := by positivity
    linarith

/-- The polar part against the window: `∫ψ_k(τ − T)|Π_X(τ)| ≤ (√X + 3)(2I_k/T + 4I_{k+1}/T²)`. -/
theorem integral_psi_shift_mul_abs_PiX_le {ℓ T X : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T) (hX : 1 ≤ X)
    (k : ℕ) :
    ∫ τ, psi ℓ k (τ - T) * |PiX X τ| ≤
      (Real.sqrt X + 3) * (2 * (∫ x, psi ℓ k x) / T + 4 * (∫ x, psi ℓ (k + 1) x) / T ^ 2) := by
  have hPc := continuous_PiX (by linarith : (0 : ℝ) < X)
  have hb : ∀ τ, |(fun τ => |PiX X τ|) τ| ≤ Real.sqrt X + 3 := by
    intro τ
    simp only [abs_abs]
    refine (abs_PiX_le_div hX τ).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ Real.sqrt X + 3 := by positivity
    nlinarith [abs_nonneg τ]
  have hiL : Integrable (fun τ => psi ℓ k (τ - T) * |PiX X τ|) := by
    have := (integrable_psi_mul_bdd hℓ k (g := fun x => |PiX X (x + T)|)
      (hPc.comp (continuous_id.add continuous_const)).abs (fun x => by
        simpa using hb (x + T))).comp_sub_right T
    simpa only [sub_add_cancel] using this
  have hi0 := (integrable_psi hℓ k).comp_sub_right T
  have hi1 := (integrable_psi hℓ (k + 1)).comp_sub_right T
  have hiR : Integrable (fun τ => (Real.sqrt X + 3) *
      (2 * psi ℓ k (τ - T) / T + 4 * psi ℓ (k + 1) (τ - T) / T ^ 2)) :=
    (((hi0.const_mul 2).div_const T).add ((hi1.const_mul 4).div_const (T ^ 2))).const_mul _
  refine (integral_mono hiL hiR (fun τ => ?_)).trans (le_of_eq ?_)
  · simp only
    have h1 := abs_PiX_le_div hX τ
    have h2 := psi_div_one_add_abs_le hℓ hT k (τ - T)
    rw [sub_add_cancel] at h2
    have hp := psi_nonneg ℓ k (τ - T)
    have hsx : 0 ≤ Real.sqrt X + 3 := by positivity
    calc psi ℓ k (τ - T) * |PiX X τ| ≤ psi ℓ k (τ - T) * ((Real.sqrt X + 3) / (1 + |τ|)) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ = (Real.sqrt X + 3) * (psi ℓ k (τ - T) / (1 + |τ|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hsx
  · rw [integral_const_mul, integral_add ((hi0.const_mul 2).div_const T)
      ((hi1.const_mul 4).div_const (T ^ 2)), integral_div, integral_div, integral_const_mul,
      integral_const_mul, integral_sub_right_eq_self (psi ℓ k) T,
      integral_sub_right_eq_self (psi ℓ (k + 1)) T]

/-! ## The gap inequality -/

/-- **A gap forces `S₀ ≤ S₁/δ²`.**  Under RH, if every zero has ordinate at distance `≥ δ` from `T`,
then `Σ m ψ₀(γ − T) ≤ δ⁻² Σ m ψ₁(γ − T)`. -/
theorem tsum_psi_zero_le_of_gap (hRH : RiemannHypothesis) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (T : ℝ) (hgap : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - T|) :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) ≤
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T)) / δ ^ 2 := by
  obtain ⟨hs0, -, -⟩ := explicitFormula_window hRH hℓ T 0
  obtain ⟨hs1, -, -⟩ := explicitFormula_window hRH hℓ T 1
  rw [← tsum_div_const]
  refine Summable.tsum_le_tsum (fun ρ => ?_) hs0 (hs1.div_const _)
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hg := hgap ρ ρ.2
  have hx2 : δ ^ 2 ≤ ((ρ : ℂ).im - T) ^ 2 := by
    rw [← sq_abs ((ρ : ℂ).im - T)]; exact pow_le_pow_left₀ hδ.le hg 2
  rw [psi_one_eq hℓ, le_div_iff₀ (by positivity)]
  have hp := psi_nonneg ℓ 0 ((ρ : ℂ).im - T)
  have := mul_le_mul_of_nonneg_left hx2 (mul_nonneg hm hp)
  nlinarith

/-! ## A gap forces a large prime polynomial -/

/-- `(√X + 3)·a/T ≤ 4a` and `(√X + 3)·a/T² ≤ 4a` when `√X ≤ √T`, `T ≥ 1`, `a ≥ 0`. -/
theorem sqrt_add_three_mul_div_le {X T a : ℝ} (hT : 1 ≤ T) (hX : Real.sqrt X ≤ Real.sqrt T)
    (ha : 0 ≤ a) : (Real.sqrt X + 3) * (a / T) ≤ 4 * a ∧ (Real.sqrt X + 3) * (a / T ^ 2) ≤ 4 * a := by
  have hsT : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
  have hsTT : Real.sqrt T ≤ T := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hT0 : 0 < T := by linarith
  have h1 : (Real.sqrt X + 3) * (a / T) ≤ 4 * a := by
    rw [mul_div_assoc', div_le_iff₀ hT0]
    have : Real.sqrt X + 3 ≤ 4 * T := by linarith
    nlinarith
  refine ⟨h1, le_trans ?_ h1⟩
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left ha hT0 (by nlinarith)) (by positivity)

/-- Decomposition `∫ψ_k ν_X = ∫ψ_k μ + ∫ψ_k Π_X + ∫ψ_k P_X` of the archimedean side. -/
theorem integral_psi_shift_nuX_decomp {ℓ T X : ℝ} (hℓ : 0 < ℓ) (hX : 1 ≤ X) (k : ℕ)
    (hik : Integrable (fun τ => psi ℓ k (τ - T) * nuX X τ)) :
    Integrable (fun τ => psi ℓ k (τ - T) * mu τ) ∧
      ∫ τ, psi ℓ k (τ - T) * nuX X τ = (∫ τ, psi ℓ k (τ - T) * mu τ) +
        (∫ τ, psi ℓ k (τ - T) * PiX X τ) + ∫ τ, psi ℓ k (τ - T) * PX X τ := by
  have hPc := continuous_PiX (by linarith : (0 : ℝ) < X)
  have hiPol : Integrable (fun τ => psi ℓ k (τ - T) * PiX X τ) := by
    have := (integrable_psi_mul_bdd hℓ k (g := fun x => PiX X (x + T)) (B := Real.sqrt X + 3)
      (hPc.comp (continuous_id.add continuous_const)) (fun x => by
        refine (abs_PiX_le_div hX (x + T)).trans (div_le_self (by positivity) ?_)
        linarith [abs_nonneg (x + T)])).comp_sub_right T
    simpa only [sub_add_cancel] using this
  have hiP : Integrable (fun τ => psi ℓ k (τ - T) * PX X τ) := by
    have := (integrable_psi_mul_bdd hℓ k (g := fun x => PX X (x + T)) (B := X ^ 2 / Real.pi)
      ((continuous_PX X).comp (continuous_id.add continuous_const))
      (fun x => abs_PX_le (by linarith) (x + T))).comp_sub_right T
    simpa only [sub_add_cancel] using this
  have hiμ : Integrable (fun τ => psi ℓ k (τ - T) * mu τ) := by
    have h := (hik.sub hiPol).sub hiP
    refine h.congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply, nuX]
    ring
  refine ⟨hiμ, ?_⟩
  have h12 : Integrable (fun τ => psi ℓ k (τ - T) * mu τ + psi ℓ k (τ - T) * PiX X τ) :=
    hiμ.add hiPol
  calc ∫ τ, psi ℓ k (τ - T) * nuX X τ
      = ∫ τ, ((psi ℓ k (τ - T) * mu τ + psi ℓ k (τ - T) * PiX X τ) +
          psi ℓ k (τ - T) * PX X τ) :=
        integral_congr_ae (Eventually.of_forall fun τ => by simp only [nuX]; ring)
    _ = (∫ τ, (psi ℓ k (τ - T) * mu τ + psi ℓ k (τ - T) * PiX X τ)) +
          ∫ τ, psi ℓ k (τ - T) * PX X τ := integral_add h12 hiP
    _ = _ := by rw [integral_add hiμ hiPol]

/-- The polar part is at most `8I_k + 16I_{k+1}` when `X ≤ T`. -/
theorem abs_integral_psi_shift_mul_PiX_le {ℓ T X : ℝ} (hℓ : 0 < ℓ) (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXT : X ≤ T) (k : ℕ) :
    |∫ τ, psi ℓ k (τ - T) * PiX X τ| ≤ 8 * (∫ x, psi ℓ k x) + 16 * (∫ x, psi ℓ (k + 1) x) := by
  have hI0 : 0 ≤ ∫ x, psi ℓ k x := integral_nonneg fun x => psi_nonneg ℓ k x
  have hI1 : 0 ≤ ∫ x, psi ℓ (k + 1) x := integral_nonneg fun x => psi_nonneg ℓ (k + 1) x
  have hsX : Real.sqrt X ≤ Real.sqrt T := Real.sqrt_le_sqrt hXT
  have h := integral_psi_shift_mul_abs_PiX_le (T := T) hℓ (by linarith) hX k
  obtain ⟨b1, -⟩ := sqrt_add_three_mul_div_le hT hsX (by positivity : 0 ≤ 2 * ∫ x, psi ℓ k x)
  obtain ⟨-, b2⟩ := sqrt_add_three_mul_div_le hT hsX (by positivity : 0 ≤ 4 * ∫ x, psi ℓ (k + 1) x)
  have habs : |∫ τ, psi ℓ k (τ - T) * PiX X τ| ≤ ∫ τ, psi ℓ k (τ - T) * |PiX X τ| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun τ => ?_)))
    simp only [abs_mul, abs_of_nonneg (psi_nonneg ℓ k (τ - T))]
  have hsplit : (Real.sqrt X + 3) * (2 * (∫ x, psi ℓ k x) / T + 4 * (∫ x, psi ℓ (k + 1) x) / T ^ 2) =
      (Real.sqrt X + 3) * (2 * (∫ x, psi ℓ k x) / T) +
        (Real.sqrt X + 3) * (4 * (∫ x, psi ℓ (k + 1) x) / T ^ 2) := by ring
  linarith

/-- Lower bound for `∫ψ₀(τ − T)μ(τ)`. -/
theorem integral_psi_zero_shift_mul_mu_ge {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T)
    (hi : Integrable (fun τ => psi ℓ 0 (τ - T) * mu τ)) :
    mu (T / 2) * (2 * Real.pi * ℓ * energy 0) -
      (mu (T / 2) + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) ≤
        ∫ τ, psi ℓ 0 (τ - T) * mu τ := by
  have hi0' := (integrable_psi hℓ 0).comp_sub_right T
  have hi1' := (integrable_psi hℓ 1).comp_sub_right T
  have hR : ∫ τ, (mu (T / 2) * psi ℓ 0 (τ - T) - (mu (T / 2) + 1) * (4 / T ^ 2) *
      psi ℓ 1 (τ - T)) = mu (T / 2) * (2 * Real.pi * ℓ * energy 0) -
      (mu (T / 2) + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) := by
    rw [integral_sub (hi0'.const_mul _) (hi1'.const_mul _), integral_const_mul,
      integral_const_mul, integral_sub_right_eq_self (psi ℓ 0) T,
      integral_sub_right_eq_self (psi ℓ 1) T, integral_psi_zero hℓ, integral_psi_one hℓ]
  rw [← hR]
  refine integral_mono ((hi0'.const_mul _).sub (hi1'.const_mul _)) hi (fun τ => ?_)
  have h := psi_zero_mul_mu_ge hℓ hT (τ - T)
  rw [sub_add_cancel] at h
  simpa only using h

/-- Upper bound for `∫ψ₁(τ − T)μ(τ)`. -/
theorem integral_psi_one_shift_mul_mu_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 1 ≤ T) (hi : Integrable (fun τ => psi ℓ 1 (τ - T) * mu τ)) :
    ∫ τ, psi ℓ 1 (τ - T) * mu τ ≤ mu (3 * T / 2) * (2 * Real.pi * energy 1 / ℓ) +
      (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3) := by
  have hi1' := (integrable_psi hℓ 1).comp_sub_right T
  have hi2' := (integrable_psi hℓ 2).comp_sub_right T
  have hR : ∫ τ, (mu (3 * T / 2) * psi ℓ 1 (τ - T) +
      (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * psi ℓ 2 (τ - T)) =
      mu (3 * T / 2) * (2 * Real.pi * energy 1 / ℓ) +
        (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3) := by
    rw [integral_add (hi1'.const_mul _) (hi2'.const_mul _), integral_const_mul,
      integral_const_mul, integral_sub_right_eq_self (psi ℓ 1) T,
      integral_sub_right_eq_self (psi ℓ 2) T, integral_psi_one hℓ, integral_psi_two hℓ]
  rw [← hR]
  refine integral_mono hi ((hi1'.const_mul _).add (hi2'.const_mul _)) (fun τ => ?_)
  have hmu := mu_add_le hC0 hC hT (τ - T)
  rw [sub_add_cancel] at hmu
  have hp := psi_nonneg ℓ 1 (τ - T)
  have h2 : psi ℓ 2 (τ - T) = (τ - T) ^ 2 * psi ℓ 1 (τ - T) := psi_succ_eq hℓ 1 (τ - T)
  simp only
  rw [h2]
  have := mul_le_mul_of_nonneg_left hmu hp
  nlinarith

/-- The combination `−(1/π)Σ c_n((a_n/d − b_n)e_n) = P_a/d − P_b`. -/
theorem neg_inv_pi_sum_sub_div {s : Finset ℕ} (c a b e : ℕ → ℝ) (d : ℝ) :
    -(1 / Real.pi) * ∑ n ∈ s, c n * ((a n / d - b n) * e n) =
      (-(1 / Real.pi) * ∑ n ∈ s, c n * (a n * e n)) / d -
        -(1 / Real.pi) * ∑ n ∈ s, c n * (b n * e n) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem ga_A {μ₃ E₀ E₁ ℓ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 < D) (hμ : -1 < μ₃) (hE1 : 0 ≤ E₁)
    (hE1D : E₁ / D ^ 2 ≤ E₀ / 2) :
    μ₃ * (2 * Real.pi * E₁ / ℓ) * (ℓ ^ 2 / D ^ 2) ≤ (μ₃ + 1) * (Real.pi * E₀ * ℓ) := by
  have hπ := Real.pi_pos
  have e : μ₃ * (2 * Real.pi * E₁ / ℓ) * (ℓ ^ 2 / D ^ 2) =
      (μ₃ + 1) * (2 * Real.pi * ℓ * (E₁ / D ^ 2)) - 2 * Real.pi * ℓ * (E₁ / D ^ 2) := by
    field_simp; ring
  have h1 : 2 * Real.pi * ℓ * (E₁ / D ^ 2) ≤ Real.pi * E₀ * ℓ := by
    have := mul_le_mul_of_nonneg_left hE1D (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ℓ)
    linarith
  have h2 : 0 ≤ 2 * Real.pi * ℓ * (E₁ / D ^ 2) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ μ₃ + 1)
  linarith

theorem ga_B {c E₂ ℓ T D : ℝ} (hc : 0 ≤ c) (hE2 : 0 ≤ E₂) (hℓ : 1 ≤ ℓ) (hT : 1 ≤ T)
    (hD : 1 ≤ D) :
    c * (4 / T ^ 2) * (2 * Real.pi * E₂ / ℓ ^ 3) * (ℓ ^ 2 / D ^ 2) ≤
      8 * Real.pi * c * E₂ * ℓ := by
  have hπ := Real.pi_pos
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hD0 : 0 < D := by linarith
  have e : c * (4 / T ^ 2) * (2 * Real.pi * E₂ / ℓ ^ 3) * (ℓ ^ 2 / D ^ 2) =
      8 * Real.pi * c * E₂ * (1 / (T ^ 2 * ℓ * D ^ 2)) := by field_simp; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have h1 : 1 ≤ T ^ 2 * D ^ 2 := one_le_mul_of_one_le_of_one_le hT2 hD2
  have h2 : 1 ≤ ℓ * ℓ := by nlinarith
  nlinarith

theorem ga_Q1 {E₁ E₂ ℓ D : ℝ} (hE1 : 0 ≤ E₁) (hE2 : 0 ≤ E₂) (hℓ : 1 ≤ ℓ) (hD : 1 ≤ D) :
    (8 * (2 * Real.pi * E₁ / ℓ) + 16 * (2 * Real.pi * E₂ / ℓ ^ 3)) * (ℓ ^ 2 / D ^ 2) ≤
      (16 * Real.pi * E₁ + 32 * Real.pi * E₂) * ℓ := by
  have hπ := Real.pi_pos
  have hℓ0 : 0 < ℓ := by linarith
  have hD0 : 0 < D := by linarith
  have e : (8 * (2 * Real.pi * E₁ / ℓ) + 16 * (2 * Real.pi * E₂ / ℓ ^ 3)) * (ℓ ^ 2 / D ^ 2) =
      (16 * Real.pi * E₁ * ℓ + 32 * Real.pi * E₂ / ℓ) / D ^ 2 := by field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have hℓℓ : 1 ≤ ℓ * ℓ := by nlinarith
  have h3 : 32 * Real.pi * E₂ / ℓ ≤ 32 * Real.pi * E₂ * ℓ := by
    rw [div_le_iff₀ hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left hℓℓ (by positivity : (0 : ℝ) ≤ 32 * Real.pi * E₂)]
  have h4 : 0 ≤ (16 * Real.pi * E₁ + 32 * Real.pi * E₂) * ℓ := by positivity
  have h5 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD : (1 : ℝ) ≤ D ^ 2) h4
  linarith

theorem ga_Q0 {E₀ E₁ ℓ : ℝ} (hE1 : 0 ≤ E₁) (hℓ : 1 ≤ ℓ) :
    8 * (2 * Real.pi * ℓ * E₀) + 16 * (2 * Real.pi * E₁ / ℓ) ≤
      (16 * Real.pi * E₀ + 32 * Real.pi * E₁) * ℓ := by
  have hπ := Real.pi_pos
  have hℓ0 : 0 < ℓ := by linarith
  have hℓℓ : 1 ≤ ℓ * ℓ := by nlinarith
  have h3 : 16 * (2 * Real.pi * E₁ / ℓ) ≤ 32 * Real.pi * E₁ * ℓ := by
    rw [mul_div_assoc', div_le_iff₀ hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left hℓℓ (by positivity : (0 : ℝ) ≤ 32 * Real.pi * E₁)]
  nlinarith

theorem ga_M0 {μ₁ E₁ ℓ T C : ℝ} (hμ : μ₁ ≤ T + C) (hT : 2 ≤ T) (hℓ : 1 ≤ ℓ) (hC : 0 ≤ C)
    (hE1 : 0 ≤ E₁) :
    (μ₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * E₁ / ℓ) ≤ 8 * Real.pi * E₁ * (C + 2) * ℓ := by
  have hπ := Real.pi_pos
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
  rcases le_or_gt (μ₁ + 1) 0 with hneg | hpos
  · have : (μ₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * E₁ / ℓ) ≤ 0 := by
      have h1 : 0 ≤ (4 / T ^ 2) * (2 * Real.pi * E₁ / ℓ) := by positivity
      nlinarith
    have : 0 ≤ 8 * Real.pi * E₁ * (C + 2) * ℓ := by positivity
    linarith
  have hmT : μ₁ + 1 ≤ (C + 2) * T ^ 2 := by
    have hTT : T ≤ T ^ 2 := by nlinarith
    have h4 : C + 1 ≤ (C + 1) * T ^ 2 := le_mul_of_one_le_right (by linarith) hT2
    nlinarith
  have e : (μ₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * E₁ / ℓ) =
      8 * Real.pi * E₁ * ((μ₁ + 1) / (T ^ 2 * ℓ)) := by field_simp; ring
  rw [e, show 8 * Real.pi * E₁ * (C + 2) * ℓ = 8 * Real.pi * E₁ * ((C + 2) * ℓ) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have hℓℓ : 1 ≤ ℓ * ℓ := by nlinarith
  have h5 : 0 ≤ (C + 2) * T ^ 2 := by positivity
  have h1 : (C + 2) * T ^ 2 ≤ (C + 2) * ℓ * (T ^ 2 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓℓ h5
    nlinarith
  linarith

theorem ga_st {E₀ ℓ C L₁ L₂ μ₁ μ₃ : ℝ} (hE0 : 0 < E₀) (hℓ : 0 < ℓ)
    (hst : (L₁ - L₂) / (4 * Real.pi) - 2 * C ≤ μ₁ - μ₃ / 2) :
    E₀ / 2 * ℓ * L₁ - (E₀ / 2 * L₂ + 4 * Real.pi * E₀ * C) * ℓ ≤
      2 * Real.pi * ℓ * E₀ * (μ₁ - μ₃ / 2) := by
  have hπ := Real.pi_pos
  have h := mul_le_mul_of_nonneg_left hst (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ℓ * E₀)
  have e : 2 * Real.pi * ℓ * E₀ * ((L₁ - L₂) / (4 * Real.pi) - 2 * C) =
      E₀ / 2 * ℓ * L₁ - (E₀ / 2 * L₂ + 4 * Real.pi * E₀ * C) * ℓ := by
    field_simp; ring
  linarith

/-- The arithmetic of the gap inequality. -/
theorem gap_arith {ℓ T D E₀ E₁ E₂ C μ₁ μ₃ M₀ M₁ Q₀ Q₁ P₀ P₁ : ℝ} (hℓ : 1 ≤ ℓ) (hT : 2 ≤ T)
    (hD : 1 ≤ D) (hE0 : 0 < E₀) (hE1 : 0 ≤ E₁) (hE2 : 0 ≤ E₂) (hC0 : 0 ≤ C)
    (hE1D : E₁ / D ^ 2 ≤ E₀ / 2)
    (hgap : M₀ + Q₀ + P₀ ≤ (M₁ + Q₁ + P₁) * (ℓ ^ 2 / D ^ 2))
    (hM0 : μ₁ * (2 * Real.pi * ℓ * E₀) - (μ₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * E₁ / ℓ) ≤ M₀)
    (hM1 : M₁ ≤ μ₃ * (2 * Real.pi * E₁ / ℓ) +
      (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * (2 * Real.pi * E₂ / ℓ ^ 3))
    (hQ0 : |Q₀| ≤ 8 * (2 * Real.pi * ℓ * E₀) + 16 * (2 * Real.pi * E₁ / ℓ))
    (hQ1 : |Q₁| ≤ 8 * (2 * Real.pi * E₁ / ℓ) + 16 * (2 * Real.pi * E₂ / ℓ ^ 3))
    (hst : (Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) - 2 * C ≤ μ₁ - μ₃ / 2)
    (hμ₁ : μ₁ ≤ T + C) (hμ₃ : -1 < μ₃) :
    E₀ / 2 * ℓ * Real.log T - (E₀ / 2 * Real.log (12 * Real.pi) + 4 * Real.pi * E₀ * C +
      Real.pi * E₀ + 8 * Real.pi * E₁ * (C + 2) + 8 * Real.pi * (1 / (2 * Real.pi) + C) * E₂ +
      (16 * Real.pi * E₀ + 32 * Real.pi * E₁) + (16 * Real.pi * E₁ + 32 * Real.pi * E₂)) * ℓ ≤
        P₁ * (ℓ ^ 2 / D ^ 2) - P₀ := by
  have hπ := Real.pi_pos
  have hℓ0 : 0 < ℓ := by linarith
  have hD0 : 0 < D := by linarith
  have hc0 : 0 ≤ 1 / (2 * Real.pi) + C := by positivity
  have hw : 0 ≤ ℓ ^ 2 / D ^ 2 := by positivity
  have hA := ga_A hℓ0 hD0 hμ₃ hE1 hE1D (E₀ := E₀)
  have hB := ga_B hc0 hE2 hℓ (by linarith : (1 : ℝ) ≤ T) hD
  have hM1d : M₁ * (ℓ ^ 2 / D ^ 2) ≤ (μ₃ + 1) * (Real.pi * E₀ * ℓ) +
      8 * Real.pi * (1 / (2 * Real.pi) + C) * E₂ * ℓ := by
    have h1 := mul_le_mul_of_nonneg_right hM1 hw
    rw [add_mul] at h1
    linarith
  have hQ1d : Q₁ * (ℓ ^ 2 / D ^ 2) ≤ (16 * Real.pi * E₁ + 32 * Real.pi * E₂) * ℓ :=
    (mul_le_mul_of_nonneg_right ((le_abs_self Q₁).trans hQ1) hw).trans (ga_Q1 hE1 hE2 hℓ hD)
  have hQ0d : -((16 * Real.pi * E₀ + 32 * Real.pi * E₁) * ℓ) ≤ Q₀ := by
    have h1 := ga_Q0 (E₀ := E₀) hE1 hℓ
    have h2 := neg_abs_le Q₀
    linarith
  have hM0d := ga_M0 hμ₁ hT hℓ hC0 hE1
  have hstm := ga_st (L₁ := Real.log T) (L₂ := Real.log (12 * Real.pi)) hE0 hℓ0 hst
  have hexpand : 2 * Real.pi * ℓ * E₀ * (μ₁ - μ₃ / 2) =
      μ₁ * (2 * Real.pi * ℓ * E₀) - (μ₃ + 1) * (Real.pi * E₀ * ℓ) + Real.pi * E₀ * ℓ := by ring
  have hsplit : (M₁ + Q₁ + P₁) * (ℓ ^ 2 / D ^ 2) =
      M₁ * (ℓ ^ 2 / D ^ 2) + Q₁ * (ℓ ^ 2 / D ^ 2) + P₁ * (ℓ ^ 2 / D ^ 2) := by ring
  linarith

/-- **A gap between zeros forces a large prime polynomial.**  Under RH there is `K` such that for
`ℓ ≥ 1`, `T ≥ 2`, `e^{2ℓ} ≤ T`, if every zero has ordinate at distance `≥ D/ℓ` from `T`, then
`(E/2)ℓ log T − Kℓ ≤ −(1/π) Σ_{n ≤ e^{2ℓ}} Λ(n)n^{−½}(ŵ₁(log n)/(D/ℓ)² − ŵ₀(log n))cos(T log n)`. -/
theorem gap_primePoly_large (hRH : RiemannHypothesis) :
    ∃ K : ℝ, ∀ ℓ T : ℝ, 1 ≤ ℓ → 2 ≤ T → Real.exp (2 * ℓ) ≤ T →
      (∀ ρ ∈ zetaZeroConfig.carrier, windowD / ℓ ≤ |ρ.im - T|) →
      energy 0 / 2 * ℓ * Real.log T - K * ℓ ≤
        -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (2 * ℓ)⌋₊,
          Λ n / Real.sqrt n * ((wcos ℓ 1 (Real.log n) / (windowD / ℓ) ^ 2 -
            wcos ℓ 0 (Real.log n)) * Real.cos (T * Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_stirling
  refine ⟨energy 0 / 2 * Real.log (12 * Real.pi) + 4 * Real.pi * energy 0 * C +
    Real.pi * energy 0 + 8 * Real.pi * energy 1 * (C + 2) +
    8 * Real.pi * (1 / (2 * Real.pi) + C) * energy 2 +
    (16 * Real.pi * energy 0 + 32 * Real.pi * energy 1) +
    (16 * Real.pi * energy 1 + 32 * Real.pi * energy 2), fun ℓ T hℓ hT hXT hgap => ?_⟩
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hD := one_le_windowD
  have hDpos : 0 < windowD := by linarith
  have hX1 : 1 ≤ Real.exp (2 * ℓ) := Real.one_le_exp (by positivity)
  have hδ0 : 0 < windowD / ℓ := by positivity
  have hδ2 : 1 / (windowD / ℓ) ^ 2 = ℓ ^ 2 / windowD ^ 2 := by field_simp
  obtain ⟨-, hi0, he0⟩ := explicitFormula_window hRH hℓ0 T 0
  obtain ⟨-, hi1, he1⟩ := explicitFormula_window hRH hℓ0 T 1
  have hg := tsum_psi_zero_le_of_gap hRH hℓ0 hδ0 T hgap
  rw [he0, he1] at hg
  obtain ⟨iμ0, hS0⟩ := integral_psi_shift_nuX_decomp hℓ0 hX1 0 hi0
  obtain ⟨iμ1, hS1⟩ := integral_psi_shift_nuX_decomp hℓ0 hX1 1 hi1
  rw [hS0, hS1, integral_psi_shift_mul_PX hℓ0 0 T, integral_psi_shift_mul_PX hℓ0 1 T,
    div_eq_mul_one_div _ ((windowD / ℓ) ^ 2), hδ2] at hg
  have hE1D : energy 1 / windowD ^ 2 ≤ energy 0 / 2 := by
    have hE0 := energy_zero_pos
    rw [div_le_iff₀ (by positivity), windowD_sq]
    have e : energy 0 / 2 * (2 * energy 1 / energy 0 + 1) = energy 1 + energy 0 / 2 := by
      field_simp
    rw [e]; linarith
  have key := gap_arith hℓ hT hD energy_zero_pos (energy_nonneg 1) (energy_nonneg 2) hC0 hE1D hg
    (integral_psi_zero_shift_mul_mu_ge hℓ0 hT0 iμ0)
    (integral_psi_one_shift_mul_mu_le hC0 hC hℓ0 hT1 iμ1)
    (by simpa [integral_psi_zero hℓ0, integral_psi_one hℓ0] using
      abs_integral_psi_shift_mul_PiX_le hℓ0 hT1 hX1 hXT 0)
    (by simpa [integral_psi_one hℓ0, integral_psi_two hℓ0] using
      abs_integral_psi_shift_mul_PiX_le hℓ0 hT1 hX1 hXT 1)
    (mu_half_sub_ge hC0 hC hT) (mu_half_le hC0 hC hT) (neg_one_lt_mu _)
  rw [neg_inv_pi_sum_sub_div, div_eq_mul_one_div _ ((windowD / ℓ) ^ 2), hδ2]
  exact key

end

end RHTower.Littlewood
