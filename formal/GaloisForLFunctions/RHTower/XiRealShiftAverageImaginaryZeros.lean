import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.ZetaFarRightDecay
import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass

/-!
# Real-shift averages of `Ξ` have purely imaginary zeros

For real `h ≠ 0` put `G_h(z) = (Ξ(z+h) + Ξ(z−h))/2`, i.e. `G_h = cosh(hD)Ξ`. On the imaginary axis,
`G_h((½−σ)i) = Re ξ(σ + ih)`. Along the horizontal line `Im s = h` the phase of `ξ` grows without
bound as `σ → ∞`, so `Re ξ(σ + ih)` vanishes for arbitrarily large `σ`. Each such vanishing is a
purely imaginary zero of `G_h`, so `G_h` is not Laguerre–Pólya, unconditionally.

Proof. On `Re s > 1`, `ξ = M·ζ` with `M(s) = s(s−1)/2 · Γ_ℝ(s)`. Moreover `M(s+2) = M(s)·q(s)` with
`q(s) = (s+2)(s+1)/(2π(s−1))`. For `s = σ + ih`, `h > 0`, `σ ≥ 6 + h`, the ratio `q` lies in the
closed first quadrant with `arg q ≥ Im q/‖q‖ ≥ h/(16σ)`. Along `σ_k = σ₀ + 2k` the phases of `M`
therefore increase by steps in `[0, π/2]` with divergent sum, and enter every arc of length `π/2`.
Since `‖ζ − 1‖ ≤ 3/8 < √2/2` there, `Re ξ` takes both signs, and the intermediate value theorem
gives the zero.

Contrast: imaginary shifts `(Ξ(z+ih) + Ξ(z−ih))/2` are Laguerre–Pólya for `h ≥ ½`.
-/

open Complex Filter Topology Finset

namespace RHTower.RealShiftAverage

noncomputable section

/-- The archimedean factor `M(s) = s(s−1)/2 · Γ_ℝ(s)`, so that `ξ = M·ζ` on `Re s > 1`. -/
def archPart (s : ℂ) : ℂ := s * (s - 1) / 2 * Complex.Gammaℝ s

/-- The two-step ratio `q(s) = (s+2)(s+1)/(2π(s−1))` of the archimedean factor. -/
def stepRatio (s : ℂ) : ℂ := (s + 2) * (s + 1) / (2 * (Real.pi : ℂ) * (s - 1))

theorem xi_eq_archPart_mul_zeta {s : ℂ} (hs : 1 < s.re) : xi s = archPart s * riemannZeta s := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have h1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; linarith
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0, archPart]
  field_simp

theorem archPart_add_two {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    archPart (s + 2) = archPart s * stepRatio s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [archPart, archPart, stepRatio, Complex.Gammaℝ_add_two h0]
  field_simp
  ring

/-- The numerator `N = (s+2)(s+1)·conj(s−1)`, with `q = N/(2π‖s−1‖²)`. -/
theorem stepRatio_eq (s : ℂ) (h1 : s ≠ 1) :
    stepRatio s = ((s + 2) * (s + 1) * (starRingEnd ℂ) (s - 1)) /
      ((2 * Real.pi * Complex.normSq (s - 1) : ℝ) : ℂ) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : (Complex.normSq (s - 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hs1).ne'
  rw [stepRatio, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    ← Complex.mul_conj (s - 1)]
  have hc : (starRingEnd ℂ) (s - 1) ≠ 0 := (map_ne_zero _).mpr hs1
  field_simp

private theorem numerator_re (σ h : ℝ) :
    (((σ + h * I) + 2) * ((σ + h * I) + 1) * (starRingEnd ℂ) ((σ + h * I) - 1)).re =
      σ ^ 3 + 2 * σ ^ 2 - σ - 2 + h ^ 2 * (σ + 4) := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem numerator_im (σ h : ℝ) :
    (((σ + h * I) + 2) * ((σ + h * I) + 1) * (starRingEnd ℂ) ((σ + h * I) - 1)).im =
      h * (σ ^ 2 - 2 * σ - 5 + h ^ 2) := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem norm_shift_le {σ h c : ℝ} (hh : 0 ≤ h) (hc : |c| ≤ 2) (hσ : 2 + h ≤ σ) :
    ‖(σ + h * I) + c‖ ≤ 2 * σ := by
  have he : (σ + h * I) + (c : ℂ) = ((σ + c : ℝ) : ℂ) + (h : ℂ) * I := by push_cast; ring
  have hab : |σ + c| ≤ σ + 2 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hc).1, (abs_le.mp hc).2]
  rw [he]
  calc ‖((σ + c : ℝ) : ℂ) + (h : ℂ) * I‖ ≤ ‖((σ + c : ℝ) : ℂ)‖ + ‖(h : ℂ) * I‖ := norm_add_le _ _
    _ = |σ + c| + h := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ 2 * σ := by linarith

/-- On `σ ≥ 6 + h`, `h > 0`, the step ratio lies in the open first quadrant and turns the phase
by at least `h/(16σ)`. -/
theorem stepRatio_bounds {σ h : ℝ} (hh : 0 < h) (hσ : 6 + h ≤ σ) :
    0 < (stepRatio (σ + h * I)).re ∧ 0 < (stepRatio (σ + h * I)).im ∧
      h / (16 * σ) ≤ (stepRatio (σ + h * I)).im / ‖stepRatio (σ + h * I)‖ := by
  set s : ℂ := σ + h * I with hs
  have h1 : s ≠ 1 := by
    intro e
    have := congrArg Complex.im e
    simp [hs] at this
    linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  set N : ℂ := (s + 2) * (s + 1) * (starRingEnd ℂ) (s - 1) with hN
  set r : ℝ := 2 * Real.pi * Complex.normSq (s - 1) with hr
  have hrpos : 0 < r := by
    have := Complex.normSq_pos.mpr hs1
    positivity
  have hq : stepRatio s = N / (r : ℂ) := stepRatio_eq s h1
  have hNre : N.re = σ ^ 3 + 2 * σ ^ 2 - σ - 2 + h ^ 2 * (σ + 4) := numerator_re σ h
  have hNim : N.im = h * (σ ^ 2 - 2 * σ - 5 + h ^ 2) := numerator_im σ h
  have hσ6 : 6 ≤ σ := by linarith
  have hNre_pos : 0 < N.re := by rw [hNre]; nlinarith
  have hNim_ge : h * (σ ^ 2 / 2) ≤ N.im := by
    have key : σ ^ 2 / 2 ≤ σ ^ 2 - 2 * σ - 5 + h ^ 2 := by nlinarith
    rw [hNim]; exact mul_le_mul_of_nonneg_left key hh.le
  have hNnorm : ‖N‖ ≤ 8 * σ ^ 3 := by
    have e2 : ‖s + 2‖ ≤ 2 * σ := by
      have := norm_shift_le (c := 2) hh.le (by norm_num) (by linarith : 2 + h ≤ σ)
      simpa [hs] using this
    have e1 : ‖s + 1‖ ≤ 2 * σ := by
      have := norm_shift_le (c := 1) hh.le (by norm_num) (by linarith : 2 + h ≤ σ)
      simpa [hs] using this
    have em : ‖s - 1‖ ≤ 2 * σ := by
      have := norm_shift_le (c := -1) hh.le (by norm_num) (by linarith : 2 + h ≤ σ)
      simpa [hs, sub_eq_add_neg] using this
    rw [hN, norm_mul, norm_mul, Complex.norm_conj]
    calc ‖s + 2‖ * ‖s + 1‖ * ‖s - 1‖ ≤ (2 * σ) * (2 * σ) * (2 * σ) := by
          gcongr
      _ = 8 * σ ^ 3 := by ring
  have hqre : (stepRatio s).re = N.re / r := by rw [hq, Complex.div_ofReal_re]
  have hqim : (stepRatio s).im = N.im / r := by rw [hq, Complex.div_ofReal_im]
  have hqnorm : ‖stepRatio s‖ = ‖N‖ / r := by
    rw [hq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hNpos : 0 < ‖N‖ := lt_of_lt_of_le hNre_pos (Complex.re_le_norm N)
  have hNim_pos : 0 < N.im := lt_of_lt_of_le (by positivity) hNim_ge
  refine ⟨by rw [hqre]; positivity, by rw [hqim]; positivity, ?_⟩
  rw [hqim, hqnorm, div_div_div_cancel_right₀ hrpos.ne']
  rw [div_le_div_iff₀ (by positivity) hNpos]
  calc h * ‖N‖ ≤ h * (8 * σ ^ 3) := by gcongr
    _ = 16 * σ * (h * (σ ^ 2 / 2)) := by ring
    _ ≤ 16 * σ * N.im := by gcongr
    _ = N.im * (16 * σ) := by ring

/-- The phase increment of one step lies in `[h/(16σ), π/2]`. -/
theorem arg_stepRatio_bounds {σ h : ℝ} (hh : 0 < h) (hσ : 6 + h ≤ σ) :
    h / (16 * σ) ≤ (stepRatio (σ + h * I)).arg ∧ (stepRatio (σ + h * I)).arg ≤ Real.pi / 2 := by
  obtain ⟨hre, him, hratio⟩ := stepRatio_bounds hh hσ
  refine ⟨?_, Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre.le)⟩
  have harg0 : 0 ≤ (stepRatio (σ + h * I)).arg := Complex.arg_nonneg_iff.mpr him.le
  calc h / (16 * σ) ≤ (stepRatio (σ + h * I)).im / ‖stepRatio (σ + h * I)‖ := hratio
    _ = Real.sin (stepRatio (σ + h * I)).arg := (Complex.sin_arg _).symm
    _ ≤ (stepRatio (σ + h * I)).arg := Real.sin_le harg0

/-- **Discrete intermediate values.** A nondecreasing unbounded sequence with steps at most `δ`
meets every interval `[a, a + δ]` above any of its terms. -/
theorem exists_mem_Icc_of_steps {S : ℕ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hmono : ∀ k, S k ≤ S (k + 1)) (hstep : ∀ k, S (k + 1) ≤ S k + δ)
    (hunb : ∀ B, ∃ k, B ≤ S k) (K : ℕ) {a : ℝ} (ha : S K ≤ a) :
    ∃ k, K ≤ k ∧ a ≤ S k ∧ S k ≤ a + δ := by
  have hmono' : Monotone S := monotone_nat_of_le_succ hmono
  have hex : ∃ n, a ≤ S (K + n) := by
    obtain ⟨k₀, hk₀⟩ := hunb a
    exact ⟨k₀, hk₀.trans (hmono' (by omega))⟩
  classical
  set n := Nat.find hex with hn
  have hP : a ≤ S (K + n) := Nat.find_spec hex
  refine ⟨K + n, by omega, hP, ?_⟩
  rcases Nat.eq_zero_or_eq_succ_pred n with h0 | hsucc
  · rw [h0, add_zero] at hP ⊢; linarith
  · have hlt : ¬ a ≤ S (K + (n - 1)) := Nat.find_min hex (by omega)
    have e : K + n = K + (n - 1) + 1 := by omega
    rw [e]
    have := hstep (K + (n - 1))
    linarith [not_le.mp hlt]

/-! ### The phase rotation along `Im s = h` -/

/-- The points `s_k = σ₀ + 2k + ih`. -/
def pt (σ₀ h : ℝ) (k : ℕ) : ℂ := ((σ₀ + 2 * k : ℝ) : ℂ) + h * I

theorem pt_succ (σ₀ h : ℝ) (k : ℕ) : pt σ₀ h (k + 1) = pt σ₀ h k + 2 := by
  simp only [pt]; push_cast; ring

theorem pt_re (σ₀ h : ℝ) (k : ℕ) : (pt σ₀ h k).re = σ₀ + 2 * k := by simp [pt]

/-- Cumulative phase `arg M(s₀) + Σ_{j<k} arg q(s_j)`. -/
def phase (σ₀ h : ℝ) (k : ℕ) : ℝ :=
  (archPart (pt σ₀ h 0)).arg + ∑ j ∈ range k, (stepRatio (pt σ₀ h j)).arg

/-- Cumulative modulus `‖M(s₀)‖ · Π_{j<k} ‖q(s_j)‖`. -/
def modulus (σ₀ h : ℝ) (k : ℕ) : ℝ :=
  ‖archPart (pt σ₀ h 0)‖ * ∏ j ∈ range k, ‖stepRatio (pt σ₀ h j)‖

theorem modulus_nonneg (σ₀ h : ℝ) (k : ℕ) : 0 ≤ modulus σ₀ h k := by
  unfold modulus; positivity

/-- Polar form of `M(s_k)` with the cumulative phase. -/
theorem archPart_pt_eq {σ₀ : ℝ} (hσ₀ : 2 ≤ σ₀) (h : ℝ) (k : ℕ) :
    archPart (pt σ₀ h k) = (modulus σ₀ h k : ℂ) * cexp (phase σ₀ h k * I) := by
  induction k with
  | zero =>
    simp only [modulus, phase, range_zero, prod_empty, sum_empty, mul_one, add_zero]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  | succ k ih =>
    have hre : 2 ≤ (pt σ₀ h k).re := by rw [pt_re]; have := k.cast_nonneg (α := ℝ); linarith
    have h0 : pt σ₀ h k ≠ 0 := fun e => by rw [e, zero_re] at hre; linarith
    have h1 : pt σ₀ h k ≠ 1 := fun e => by rw [e, one_re] at hre; linarith
    rw [pt_succ, archPart_add_two h0 h1, ih]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (stepRatio (pt σ₀ h k))]
    simp only [modulus, phase, prod_range_succ, sum_range_succ]
    push_cast
    rw [show ((‖archPart (pt σ₀ h 0)‖ : ℂ) * ∏ j ∈ range k, (‖stepRatio (pt σ₀ h j)‖ : ℂ)) *
        cexp ((((archPart (pt σ₀ h 0)).arg : ℂ) + ∑ j ∈ range k, ((stepRatio (pt σ₀ h j)).arg : ℂ)) * I) *
        ((‖stepRatio (pt σ₀ h k)‖ : ℂ) * cexp (((stepRatio (pt σ₀ h k)).arg : ℂ) * I)) =
        (‖archPart (pt σ₀ h 0)‖ : ℂ) * ((∏ j ∈ range k, (‖stepRatio (pt σ₀ h j)‖ : ℂ)) *
          (‖stepRatio (pt σ₀ h k)‖ : ℂ)) *
        (cexp ((((archPart (pt σ₀ h 0)).arg : ℂ) + ∑ j ∈ range k, ((stepRatio (pt σ₀ h j)).arg : ℂ)) * I) *
          cexp (((stepRatio (pt σ₀ h k)).arg : ℂ) * I)) by ring, ← Complex.exp_add]
    congr 2
    ring

theorem norm_archPart_pt {σ₀ : ℝ} (hσ₀ : 2 ≤ σ₀) (h : ℝ) (k : ℕ) :
    ‖archPart (pt σ₀ h k)‖ = modulus σ₀ h k := by
  rw [archPart_pt_eq hσ₀, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (modulus_nonneg σ₀ h k)]

theorem re_archPart_pt {σ₀ : ℝ} (hσ₀ : 2 ≤ σ₀) (h : ℝ) (k : ℕ) :
    (archPart (pt σ₀ h k)).re = modulus σ₀ h k * Real.cos (phase σ₀ h k) := by
  rw [archPart_pt_eq hσ₀, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem phase_succ (σ₀ h : ℝ) (k : ℕ) :
    phase σ₀ h (k + 1) = phase σ₀ h k + (stepRatio (pt σ₀ h k)).arg := by
  simp only [phase, sum_range_succ]; ring

theorem pt_eq (σ₀ h : ℝ) (k : ℕ) : pt σ₀ h k = ((σ₀ + 2 * k : ℝ) : ℂ) + h * I := rfl

theorem phase_step_bounds {σ₀ h : ℝ} (hh : 0 < h) (hσ₀ : 6 + h ≤ σ₀) (k : ℕ) :
    h / (16 * (σ₀ + 2 * k)) ≤ phase σ₀ h (k + 1) - phase σ₀ h k ∧
      phase σ₀ h (k + 1) - phase σ₀ h k ≤ Real.pi / 2 := by
  rw [phase_succ, add_sub_cancel_left, pt_eq]
  exact arg_stepRatio_bounds hh (by have := k.cast_nonneg (α := ℝ); linarith)

theorem phase_unbounded {σ₀ h : ℝ} (hh : 0 < h) (hσ₀ : 6 + h ≤ σ₀) (B : ℝ) :
    ∃ k, B ≤ phase σ₀ h k := by
  have hσpos : 0 < σ₀ := by linarith
  set c : ℝ := h / (16 * (σ₀ + 2)) with hc
  have hcpos : 0 < c := by positivity
  have hlow : ∀ k : ℕ, phase σ₀ h 0 + c * ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ≤ phase σ₀ h k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, mul_add]
      have hstep := (phase_step_bounds hh hσ₀ k).1
      have hk : c * (1 / ((k : ℝ) + 1)) ≤ h / (16 * (σ₀ + 2 * k)) := by
        rw [hc, div_mul_div_comm, mul_one]
        apply div_le_div_of_nonneg_left hh.le (by positivity)
        have := k.cast_nonneg (α := ℝ)
        nlinarith
      linarith
  have ht := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨k, hk⟩ := (ht.eventually_ge_atTop ((B - phase σ₀ h 0) / c)).exists
  refine ⟨k, le_trans ?_ (hlow k)⟩
  have := (div_le_iff₀ hcpos).mp hk
  linarith

/-! ### Sign changes of `Re ξ` along `Im s = h` -/

private theorem three_eighths_lt : (3 : ℝ) / 8 < √2 / 2 := by
  have : (3 / 4 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

private theorem cos_ge_of_near {θ : ℝ} {m : ℕ}
    (h1 : m * (2 * Real.pi) - Real.pi / 4 ≤ θ) (h2 : θ ≤ m * (2 * Real.pi) + Real.pi / 4) :
    √2 / 2 ≤ Real.cos θ := by
  rw [← Real.cos_sub_nat_mul_two_pi θ m, ← Real.cos_abs, ← Real.cos_pi_div_four]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_le]; constructor <;> linarith

private theorem cos_le_of_near {θ : ℝ} {m : ℕ}
    (h1 : m * (2 * Real.pi) + 3 * Real.pi / 4 ≤ θ) (h2 : θ ≤ m * (2 * Real.pi) + 5 * Real.pi / 4) :
    Real.cos θ ≤ -(√2 / 2) := by
  have e : θ = (θ - Real.pi - m * (2 * Real.pi)) + Real.pi + m * (2 * Real.pi) := by ring
  rw [e, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, neg_le_neg_iff, ← Real.cos_abs,
    ← Real.cos_pi_div_four]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_le]; constructor <;> linarith

/-- On `Re s ≥ 3`, the sign of `Re ξ` follows the phase of `M` once `cos` of it is `≥ √2/2`. -/
private theorem re_xi_bounds {σ₀ h : ℝ} (hσ₀ : 3 ≤ σ₀) (k : ℕ) :
    modulus σ₀ h k * (Real.cos (phase σ₀ h k) - 3 / 8) ≤ (xi (pt σ₀ h k)).re ∧
      (xi (pt σ₀ h k)).re ≤ modulus σ₀ h k * (Real.cos (phase σ₀ h k) + 3 / 8) := by
  have hre : 3 ≤ (pt σ₀ h k).re := by rw [pt_re]; have := k.cast_nonneg (α := ℝ); linarith
  have hz := norm_riemannZeta_sub_one_le_of_three_le hre
  have hxi : xi (pt σ₀ h k) =
      archPart (pt σ₀ h k) + archPart (pt σ₀ h k) * (riemannZeta (pt σ₀ h k) - 1) := by
    rw [xi_eq_archPart_mul_zeta (by linarith)]; ring
  have herr : |(archPart (pt σ₀ h k) * (riemannZeta (pt σ₀ h k) - 1)).re| ≤
      modulus σ₀ h k * (3 / 8) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_archPart_pt (by linarith)]
    exact mul_le_mul_of_nonneg_left hz (modulus_nonneg _ _ _)
  rw [hxi, Complex.add_re, re_archPart_pt (by linarith)]
  constructor <;> nlinarith [abs_le.mp herr]

theorem modulus_pos {σ₀ h : ℝ} (hh : 0 < h) (hσ₀ : 6 + h ≤ σ₀) (k : ℕ) : 0 < modulus σ₀ h k := by
  unfold modulus
  apply mul_pos
  · rw [norm_pos_iff]
    have hre : 1 < (pt σ₀ h 0).re := by rw [pt_re]; simp; linarith
    have h0 : pt σ₀ h 0 ≠ 0 := fun e => by rw [e, zero_re] at hre; linarith
    have h1 : pt σ₀ h 0 - 1 ≠ 0 := fun e => by
      rw [sub_eq_zero] at e; rw [e, one_re] at hre; linarith
    unfold archPart
    exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
  · apply prod_pos
    intro j _
    rw [norm_pos_iff]
    intro e
    have := (stepRatio_bounds hh (σ := σ₀ + 2 * j) (by have := j.cast_nonneg (α := ℝ); linarith)).1
    rw [← pt_eq, e, zero_re] at this
    exact lt_irrefl 0 this

/-- **Sign changes.** For `h > 0`, `Re ξ(σ + ih)` vanishes at points `σ ≥ R` for every `R`, and it is
positive somewhere on `σ ≥ R`. -/
theorem exists_re_xi_eq_zero {h : ℝ} (hh : 0 < h) (R : ℝ) :
    (∃ σ, R ≤ σ ∧ (xi ((σ : ℂ) + h * I)).re = 0) ∧
      ∃ σ, R ≤ σ ∧ 0 < (xi ((σ : ℂ) + h * I)).re := by
  set σ₀ : ℝ := max (6 + h) R with hσ₀def
  have hσ₀ : 6 + h ≤ σ₀ := le_max_left _ _
  have hσR : R ≤ σ₀ := le_max_right _ _
  have hmono : ∀ k, phase σ₀ h k ≤ phase σ₀ h (k + 1) := fun k => by
    have := (phase_step_bounds hh hσ₀ k).1
    have : 0 ≤ h / (16 * (σ₀ + 2 * k)) := by
      have := k.cast_nonneg (α := ℝ); apply div_nonneg hh.le; nlinarith
    linarith
  have hstep : ∀ k, phase σ₀ h (k + 1) ≤ phase σ₀ h k + Real.pi / 2 := fun k => by
    have := (phase_step_bounds hh hσ₀ k).2; linarith
  have hunb := phase_unbounded hh hσ₀
  set m : ℕ := ⌈(|phase σ₀ h 0| + 1) / (2 * Real.pi)⌉₊ with hm
  have hm2 : |phase σ₀ h 0| + 1 ≤ m * (2 * Real.pi) := by
    have := Nat.le_ceil ((|phase σ₀ h 0| + 1) / (2 * Real.pi))
    rw [← hm, div_le_iff₀ (by positivity)] at this
    exact this
  have hpi4 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
  have hph0 := le_abs_self (phase σ₀ h 0)
  obtain ⟨k₁, -, hk₁a, hk₁b⟩ := exists_mem_Icc_of_steps (by positivity) hmono hstep hunb 0
    (a := m * (2 * Real.pi) - Real.pi / 4) (by linarith)
  obtain ⟨k₂, -, hk₂a, hk₂b⟩ := exists_mem_Icc_of_steps (by positivity) hmono hstep hunb 0
    (a := m * (2 * Real.pi) + 3 * Real.pi / 4) (by linarith [Real.pi_pos])
  have hc₁ : √2 / 2 ≤ Real.cos (phase σ₀ h k₁) := cos_ge_of_near hk₁a (by linarith)
  have hc₂ : Real.cos (phase σ₀ h k₂) ≤ -(√2 / 2) := cos_le_of_near hk₂a (by linarith)
  have h38 := three_eighths_lt
  have hσ3 : 3 ≤ σ₀ := by linarith
  have hpos₁ : 0 < (xi (pt σ₀ h k₁)).re := by
    have := (re_xi_bounds (h := h) hσ3 k₁).1
    have := modulus_pos hh hσ₀ k₁
    nlinarith
  have hneg₂ : (xi (pt σ₀ h k₂)).re < 0 := by
    have := (re_xi_bounds (h := h) hσ3 k₂).2
    have := modulus_pos hh hσ₀ k₂
    nlinarith
  set f : ℝ → ℝ := fun σ => (xi ((σ : ℂ) + h * I)).re with hf
  have hfc : Continuous f :=
    Complex.continuous_re.comp (xi_differentiable.continuous.comp
      (Complex.continuous_ofReal.add continuous_const))
  have hf₁ : 0 < f (σ₀ + 2 * k₁) := hpos₁
  have hf₂ : f (σ₀ + 2 * k₂) < 0 := hneg₂
  refine ⟨?_, ⟨σ₀ + 2 * k₁, by have := k₁.cast_nonneg (α := ℝ); linarith, hpos₁⟩⟩
  rcases le_total (σ₀ + 2 * (k₁ : ℝ)) (σ₀ + 2 * k₂) with hle | hle
  · obtain ⟨σ, hσ, hz⟩ := intermediate_value_Icc' hle hfc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f (σ₀ + 2 * k₂)) (f (σ₀ + 2 * k₁)) from ⟨hf₂.le, hf₁.le⟩)
    exact ⟨σ, by have := k₁.cast_nonneg (α := ℝ); linarith [hσ.1], hz⟩
  · obtain ⟨σ, hσ, hz⟩ := intermediate_value_Icc hle hfc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f (σ₀ + 2 * k₂)) (f (σ₀ + 2 * k₁)) from ⟨hf₂.le, hf₁.le⟩)
    exact ⟨σ, by have := k₂.cast_nonneg (α := ℝ); linarith [hσ.1], hz⟩

/-! ### Imaginary zeros of `cosh(hD)Ξ` -/

/-- The real-shift average `G_h(z) = (Ξ(z+h) + Ξ(z−h))/2 = cosh(hD)Ξ`. -/
def realShiftAverage (h : ℝ) (z : ℂ) : ℂ := (XiC (z + h) + XiC (z - h)) / 2

theorem realShiftAverage_neg (h : ℝ) : realShiftAverage (-h) = realShiftAverage h := by
  funext z
  simp only [realShiftAverage, Complex.ofReal_neg, sub_neg_eq_add, ← sub_eq_add_neg, add_comm]

/-- On the imaginary axis, `G_h((½ − σ)i) = Re ξ(σ + ih)`. -/
theorem realShiftAverage_imag (h σ : ℝ) :
    realShiftAverage h (((1 / 2 - σ : ℝ) : ℂ) * I) = (((xi ((σ : ℂ) + h * I)).re : ℝ) : ℂ) := by
  have e₁ : 1 / 2 + ((((1 / 2 - σ : ℝ) : ℂ) * I) + h) * I = (σ : ℂ) + h * I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e₂ : 1 / 2 + ((((1 / 2 - σ : ℝ) : ℂ) * I) - h) * I = (starRingEnd ℂ) ((σ : ℂ) + h * I) := by
    apply Complex.ext <;> simp
  rw [realShiftAverage, XiC, XiC, e₁, e₂, xi_conj, Complex.add_conj]
  push_cast
  ring

/-- **`cosh(hD)Ξ` has purely imaginary zeros of arbitrarily large modulus**, for every real
`h ≠ 0`. -/
theorem exists_imag_zero_realShiftAverage {h : ℝ} (hh : h ≠ 0) (R : ℝ) :
    ∃ y : ℝ, R ≤ |y| ∧ realShiftAverage h ((y : ℂ) * I) = 0 := by
  wlog hpos : 0 < h generalizing h
  · have hneg : 0 < -h := by
      rcases lt_or_gt_of_ne hh with h' | h'
      · linarith
      · exact absurd h' hpos
    obtain ⟨y, hy, hz⟩ := this (neg_ne_zero.mpr hh) hneg
    exact ⟨y, hy, by rwa [realShiftAverage_neg] at hz⟩
  obtain ⟨⟨σ, hσ, hz⟩, -⟩ := exists_re_xi_eq_zero hpos (|R| + 1)
  refine ⟨1 / 2 - σ, ?_, ?_⟩
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [abs_nonneg R])]
    linarith [le_abs_self R]
  · rw [realShiftAverage_imag, hz, Complex.ofReal_zero]

/-- **`cosh(hD)Ξ` is never Laguerre–Pólya.** For every real `h ≠ 0`,
`(Ξ(z+h) + Ξ(z−h))/2` has non-real zeros. No hypothesis on the zeros of `ζ` is used. -/
theorem not_laguerrePolya_realShiftAverage {h : ℝ} (hh : h ≠ 0) :
    ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya (realShiftAverage h) := by
  intro hLP
  wlog hpos : 0 < h generalizing h
  · have hneg : 0 < -h := by
      rcases lt_or_gt_of_ne hh with h' | h'
      · linarith
      · exact absurd h' hpos
    exact this (neg_ne_zero.mpr hh) (by rwa [realShiftAverage_neg]) hneg
  obtain ⟨⟨σ, hσ, hz⟩, ⟨σ₁, hσ₁, hpos₁⟩⟩ := exists_re_xi_eq_zero hpos 1
  have ha : realShiftAverage h (((1 / 2 - σ₁ : ℝ) : ℂ) * I) ≠ 0 := by
    rw [realShiftAverage_imag]
    exact_mod_cast hpos₁.ne'
  have hzero : realShiftAverage h (((1 / 2 - σ : ℝ) : ℂ) * I) = 0 := by
    rw [realShiftAverage_imag, hz, Complex.ofReal_zero]
  have him := GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya hLP ha hzero
  simp at him
  linarith

end

end RHTower.RealShiftAverage
