import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Spectral mass at poles of arbitrary order

Rescaling a vertical window by its distance from a pole of order `m` produces
the integrable density `(1+x²)⁻ᵐ`. Continuity of the numerator and test weight
suffices for the atom law; no derivative bound on either is needed.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The vertical square-mass kernel of a pole of order `m`. -/
def poleMassKernel (m : ℕ) (x : ℝ) : ℝ := ((1 + x ^ 2) ^ m)⁻¹

theorem poleMassKernel_pos (m : ℕ) (x : ℝ) : 0 < poleMassKernel m x := by
  unfold poleMassKernel
  positivity

theorem poleMassKernel_le {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    poleMassKernel m x ≤ (1 + x ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  simpa only [pow_one] using pow_le_pow_right₀ (by nlinarith [sq_nonneg x] : 1 ≤ 1 + x ^ 2) hm

theorem integrable_poleMassKernel {m : ℕ} (hm : 1 ≤ m) :
    Integrable (poleMassKernel m) := by
  refine integrable_inv_one_add_sq.mono' ?_ ?_
  · exact (Continuous.inv₀ (by fun_prop)
      (fun x => by positivity)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (poleMassKernel_pos m x)]
    exact poleMassKernel_le hm x

/-- The positive mass of the order-`m` atom. -/
def poleMassConstant (m : ℕ) : ℝ := ∫ x, poleMassKernel m x

theorem poleMassConstant_pos {m : ℕ} (hm : 1 ≤ m) : 0 < poleMassConstant m := by
  unfold poleMassConstant
  apply (integral_pos_iff_support_of_nonneg
    (fun x => (poleMassKernel_pos m x).le) (integrable_poleMassKernel hm)).mpr
  have hs : Function.support (poleMassKernel m) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (poleMassKernel_pos m x).ne'
  rw [hs]
  simp

/-- Normalizing the squared pole removes exactly `2m` powers of the line distance. -/
theorem scaled_norm_pole_eq {e : ℝ} (he : 0 < e) (x : ℝ) (m : ℕ) (a : ℂ) :
    e ^ (2 * m) * ‖a / ((e : ℂ) + ((e * x : ℝ) : ℂ) * I) ^ m‖ ^ 2 =
      ‖a‖ ^ 2 * poleMassKernel m x := by
  have hn : ‖(e : ℂ) + ((e * x : ℝ) : ℂ) * I‖ ^ 2 = e ^ 2 * (1 + x ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hd : (‖(e : ℂ) + ((e * x : ℝ) : ℂ) * I‖ ^ m) ^ 2 =
      e ^ (2 * m) * (1 + x ^ 2) ^ m := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, hn, mul_pow, ← pow_mul]
  rw [norm_div, div_pow, norm_pow, hd]
  unfold poleMassKernel
  field_simp [he.ne']

/-- The affine rescaling of a window includes its Jacobian. -/
theorem integral_rescaled_window (f : ℝ → ℝ) (y₀ δ : ℝ) {e : ℝ} (he : 0 < e) :
    (∫ x, (Icc (y₀ - δ) (y₀ + δ)).indicator f (y₀ + e * x)) =
      e⁻¹ * ∫ y in Icc (y₀ - δ) (y₀ + δ), f y := by
  have h := Measure.integral_comp_mul_left
    (fun t => (Icc (y₀ - δ) (y₀ + δ)).indicator f (t + y₀)) e
  rw [integral_add_right_eq_self, integral_indicator measurableSet_Icc,
    abs_of_pos (inv_pos.mpr he), smul_eq_mul] at h
  simpa only [add_comm y₀] using h

/-- An order-`m` pole carries a spectral atom at scale `e^(2m−1)`.
The numerator is only required to be bounded on the box and continuous at its center. -/
theorem tendsto_window_atom_of_pole_order {S : ℝ → ℝ → ℂ} {H : ℂ → ℂ}
    {m : ℕ} {y₀ δ M W : ℝ} {w : ℝ → ℝ}
    (hm : 1 ≤ m) (hδ : 0 < δ) (_hM : 0 ≤ M)
    (hcont : ∀ e ∈ Ioo 0 δ, Continuous (S e))
    (hH : ContinuousAt H 0)
    (hbound : ∀ e ∈ Ioo 0 δ, ∀ y ∈ Icc (y₀ - δ) (y₀ + δ),
      ‖H ((e : ℂ) + ((y - y₀ : ℝ) : ℂ) * I)‖ ≤ M)
    (hpole : ∀ e ∈ Ioo 0 δ, ∀ y ∈ Icc (y₀ - δ) (y₀ + δ),
      S e y = H ((e : ℂ) + ((y - y₀ : ℝ) : ℂ) * I) /
        ((e : ℂ) + ((y - y₀ : ℝ) : ℂ) * I) ^ m)
    (hw : Continuous w) (hwW : ∀ y, |w y| ≤ W) :
    Tendsto (fun e : ℝ => e ^ (2 * m - 1) *
      ∫ y in Icc (y₀ - δ) (y₀ + δ), ‖S e y‖ ^ 2 * w y)
      (𝓝[>] 0) (𝓝 (poleMassConstant m * ‖H 0‖ ^ 2 * w y₀)) := by
  let J : ℝ → ℝ → ℝ := fun e y => e ^ (2 * m) * (‖S e y‖ ^ 2 * w y)
  let F : ℝ → ℝ → ℝ := fun e x =>
    (Icc (y₀ - δ) (y₀ + δ)).indicator (J e) (y₀ + e * x)
  have hW : 0 ≤ W := (abs_nonneg (w y₀)).trans (hwW y₀)
  have hlocal : ∀ e ∈ Ioo 0 δ, ∀ x, y₀ + e * x ∈ Icc (y₀ - δ) (y₀ + δ) →
      F e x = ‖H ((e : ℂ) + ((e * x : ℝ) : ℂ) * I)‖ ^ 2 *
        poleMassKernel m x * w (y₀ + e * x) := by
    intro e he x hx
    dsimp only [F]
    rw [indicator_of_mem hx]
    dsimp only [J]
    rw [hpole e he _ hx,
      show y₀ + e * x - y₀ = e * x by ring, ← mul_assoc, scaled_norm_pole_eq he.1]
  have hlim : Tendsto (fun e => ∫ x, F e x) (𝓝[>] 0)
      (𝓝 (∫ x, ‖H 0‖ ^ 2 * poleMassKernel m x * w y₀)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (M ^ 2 * W) * (1 + x ^ 2)⁻¹) ?_ ?_
      (integrable_inv_one_add_sq.const_mul (M ^ 2 * W)) ?_
    · filter_upwards [Ioo_mem_nhdsGT hδ] with e he
      have hJ : Measurable (J e) :=
        (continuous_const.mul (((hcont e he).norm.pow 2).mul hw)).measurable
      exact ((hJ.indicator measurableSet_Icc).comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hδ] with e he
      filter_upwards [] with x
      by_cases hx : y₀ + e * x ∈ Icc (y₀ - δ) (y₀ + δ)
      · rw [hlocal e he x hx, norm_mul, norm_mul, norm_pow, norm_norm,
          Real.norm_eq_abs, abs_of_pos (poleMassKernel_pos m x), Real.norm_eq_abs]
        have hHM : ‖H ((e : ℂ) + ((e * x : ℝ) : ℂ) * I)‖ ≤ M := by
          simpa only [add_sub_cancel_left] using hbound e he _ hx
        calc ‖H ((e : ℂ) + ((e * x : ℝ) : ℂ) * I)‖ ^ 2 * poleMassKernel m x * |w (y₀ + e * x)|
            ≤ M ^ 2 * poleMassKernel m x * W :=
              mul_le_mul (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg _) hHM 2) (poleMassKernel_pos m x).le)
                (hwW _) (abs_nonneg _) (mul_nonneg (sq_nonneg M) (poleMassKernel_pos m x).le)
          _ ≤ (M ^ 2 * W) * (1 + x ^ 2)⁻¹ := by
            nlinarith [mul_le_mul_of_nonneg_left (poleMassKernel_le hm x)
              (mul_nonneg (sq_nonneg M) hW)]
      · dsimp only [F]
        rw [indicator_of_notMem hx, norm_zero]
        positivity
    · filter_upwards [] with x
      have hz : Tendsto (fun e : ℝ => (e : ℂ) + ((e * x : ℝ) : ℂ) * I)
          (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous (fun e : ℝ => (e : ℂ) + ((e * x : ℝ) : ℂ) * I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have hy : Tendsto (fun e : ℝ => y₀ + e * x) (𝓝[>] 0) (𝓝 y₀) := by
        have hc : Continuous (fun e : ℝ => y₀ + e * x) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have hwin : ∀ᶠ e : ℝ in 𝓝[>] 0, y₀ + e * x ∈ Icc (y₀ - δ) (y₀ + δ) :=
        hy.eventually (Icc_mem_nhds (by linarith) (by linarith))
      have h := (((hH.tendsto.comp hz).norm.pow 2).mul_const (poleMassKernel m x)).mul
        ((hw.tendsto y₀).comp hy)
      refine h.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hδ, hwin] with e he hwin
      exact (hlocal e he x hwin).symm
  have hvalue : (∫ x, ‖H 0‖ ^ 2 * poleMassKernel m x * w y₀) =
      poleMassConstant m * ‖H 0‖ ^ 2 * w y₀ := by
    rw [integral_mul_const, integral_const_mul]
    unfold poleMassConstant
    ring
  rw [hvalue] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : 0 < e := he
  dsimp only [F]
  rw [integral_rescaled_window _ _ _ he0]
  change e⁻¹ * (∫ y in Icc (y₀ - δ) (y₀ + δ),
    e ^ (2 * m) * (‖S e y‖ ^ 2 * w y)) = _
  have hp : e ^ (2 * m) = e ^ (2 * m - 1) * e := by
    conv_lhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ]
  rw [integral_const_mul, hp]
  field_simp [he0.ne']

/-- A positive mass at one pole scale forces divergence at every lower scale. -/
theorem tendsto_lower_scale_mass_atTop {W T : ℝ → ℝ} {k N : ℕ} {A : ℝ}
    (hNk : N < k) (hA : 0 < A)
    (hW : Tendsto (fun e => e ^ k * W e) (𝓝[>] 0) (𝓝 A))
    (hle : ∀ᶠ e : ℝ in 𝓝[>] 0, W e ≤ T e) :
    Tendsto (fun e => e ^ N * T e) (𝓝[>] 0) atTop := by
  have hi : Tendsto (fun e : ℝ => (e⁻¹) ^ (k - N)) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (by omega : k - N ≠ 0)).comp tendsto_inv_nhdsGT_zero
  have hsmall : Tendsto (fun e => e ^ N * W e) (𝓝[>] 0) atTop := by
    refine (hi.atTop_mul_pos hA hW).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    have he0 : e ≠ 0 := (show 0 < e from he).ne'
    have hp : e ^ k = e ^ N * e ^ (k - N) := by
      rw [← pow_add, Nat.add_sub_of_le hNk.le]
    rw [inv_pow, hp]
    field_simp [he0]
  refine tendsto_atTop_mono' _ ?_ hsmall
  filter_upwards [hle, self_mem_nhdsWithin] with e he he0
  exact mul_le_mul_of_nonneg_left he (pow_nonneg (show 0 ≤ e from le_of_lt he0) _)

/-- A finite local mass disappears at every strictly higher pole scale. -/
theorem tendsto_higher_scale_mass_zero {W : ℝ → ℝ} {k N : ℕ} {A : ℝ}
    (hkN : k < N) (hW : Tendsto (fun e => e ^ k * W e) (𝓝[>] 0) (𝓝 A)) :
    Tendsto (fun e => e ^ N * W e) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun e : ℝ => e ^ (N - k)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun e : ℝ => e ^ (N - k)) := by fun_prop
    simpa only [zero_pow (by omega : N - k ≠ 0)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := hp.mul hW
  rw [zero_mul] at h
  convert h using 1
  funext e
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkN.le]

/-- A polynomially bounded nonnegative window has zero share when the total
mass diverges faster than its polynomial scale. -/
theorem tendsto_mass_share_zero_of_scaled_mass_atTop {W T : ℝ → ℝ} {N : ℕ} {C : ℝ}
    (hW0 : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 ≤ W e)
    (hW : ∀ᶠ e : ℝ in 𝓝[>] 0, e ^ N * W e ≤ C)
    (hT : Tendsto (fun e => e ^ N * T e) (𝓝[>] 0) atTop) :
    Tendsto (fun e => W e / T e) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e ^ N * T e :=
    ((tendsto_atTop.mp hT) 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  have hratio : ∀ e : ℝ, 0 < e → W e / T e = (e ^ N * W e) / (e ^ N * T e) := by
    intro e he
    exact (mul_div_mul_left _ _ (pow_ne_zero _ he.ne')).symm
  refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds (x := C)).div_atTop hT)
  · filter_upwards [hW0, hpos, self_mem_nhdsWithin] with e he hp he0
    rw [hratio e he0]
    exact div_nonneg (mul_nonneg (pow_nonneg (show 0 ≤ e from le_of_lt he0) _) he) hp.le
  · filter_upwards [hW, hpos, self_mem_nhdsWithin] with e he hp he0
    rw [hratio e he0]
    exact div_le_div_of_nonneg_right he hp.le

#print axioms tendsto_window_atom_of_pole_order

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
