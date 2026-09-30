import GaloisForLFunctions.RHTower.WeilFullConeNearNullPositiveDefinite
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# Translation bounds for the deficit of a Weil-positive system with summable excess

Let `lam` be full-cone Weil-positive with summable excess. Write `a = e − v`, where
`a(n) = (lam(n) − Λ(n))/√n`, `e = a⁺` and `v = a⁻`.
- The potential `ψ = K⋆W_a` has `−ψ` positive definite, so `|ψ(y)| ≤ −ψ(0)`.
- The excess potential `K⋆W_e` is bounded by `2‖e‖₁ K(0)`.
- Hence the deficit potential `K⋆W_v = K⋆W_e − ψ` is bounded:
  `kernelPotential v y ≤ B` for every `y` (`exists_kernelPotential_deficit_le`).

**Kernel domination** (`tsum_mul_kernelSmooth_le`). For every nonnegative integrable profile `P`,
`Σ_n v(n)((K⋆P)(log n) + (K⋆P)(−log n)) = ∫ (K⋆W_v)(y) P(y) dy ≤ B ∫P`.

**Cauchy profiles** (`exists_tsum_deficit_cauchyProfile_le`). The profile
`P_{δ,s}(u) = δ/(1 + δ²(u − s)²)`, `0 < δ ≤ 1`, is at most `3/(2κ)` times its `K`-smoothing,
where `κ = min_{[−1,1]} K > 0`. Its integral is `π`. So `Σ_n v(n)(P_{δ,s}(log n) + P_{δ,s}(−log n))`
is bounded uniformly in `δ` and `s`. This is the form in which the deficit is a translation-bounded
measure.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal

namespace RHTower.WeilExcess

noncomputable section

/-- The Riemann-kernel potential of a weight sequence. -/
def kernelPotential (w : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, w n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))

/-- The `K`-smoothing `(K⋆P)(u) = ∫ K(u − y) P(y) dy`. -/
def kernelSmooth (P : ℝ → ℝ) (u : ℝ) : ℝ := ∫ y, riemannAutocorr (u - y) * P y

/-- The excess `a⁺` and the deficit `a⁻` of the normalized deviation. -/
def deviationExcess (lam : ℕ → ℝ) (n : ℕ) : ℝ := max (weilDeviation lam n) 0

def deviationDeficit (lam : ℕ → ℝ) (n : ℕ) : ℝ := max (-weilDeviation lam n) 0

theorem deviationExcess_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ deviationExcess lam n :=
  le_max_right _ _

theorem deviationDeficit_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ deviationDeficit lam n :=
  le_max_right _ _

theorem weilDeviation_eq_sub (lam : ℕ → ℝ) (n : ℕ) :
    weilDeviation lam n = deviationExcess lam n - deviationDeficit lam n :=
  (max_zero_sub_max_neg_zero_eq_self _).symm

theorem riemannAutocorr_le_zero (y : ℝ) : riemannAutocorr y ≤ riemannAutocorr 0 := by
  unfold riemannAutocorr
  have hsq : Integrable fun t => riemannKernelReal t * riemannKernelReal t := by
    simpa using integrable_riemannKernelReal_mul 0
  have hsq' : Integrable fun t => riemannKernelReal (t - y) * riemannKernelReal (t - y) :=
    hsq.comp_sub_right y
  have hshift : (∫ t, riemannKernelReal (t - y) * riemannKernelReal (t - y)) =
      ∫ t, riemannKernelReal t * riemannKernelReal t :=
    integral_sub_right_eq_self (fun t => riemannKernelReal t * riemannKernelReal t) y
  have hmono : (∫ t, riemannKernelReal t * riemannKernelReal (t - y)) ≤
      ∫ t, (riemannKernelReal t * riemannKernelReal t +
        riemannKernelReal (t - y) * riemannKernelReal (t - y)) / 2 := by
    refine integral_mono (integrable_riemannKernelReal_mul y) ((hsq.add hsq').div_const 2)
      fun t => ?_
    nlinarith [sq_nonneg (riemannKernelReal t - riemannKernelReal (t - y))]
  rw [integral_div, integral_add hsq hsq', hshift] at hmono
  simp only [sub_zero]
  linarith

theorem riemannAutocorr_pos (y : ℝ) : 0 < riemannAutocorr y := by
  have hint := integrable_riemannKernelReal_mul y
  unfold riemannAutocorr
  rw [integral_pos_iff_support_of_nonneg (fun t => (mul_pos (riemannKernelReal_pos t)
    (riemannKernelReal_pos _)).le) hint]
  have hsupp : Function.support (fun t => riemannKernelReal t * riemannKernelReal (t - y)) =
      Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (mul_pos (riemannKernelReal_pos t) (riemannKernelReal_pos _)).ne'
  rw [hsupp, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-! ## Kernel domination -/

theorem integrable_riemannAutocorr_mul {P : ℝ → ℝ} (hPc : Continuous P) (hPi : Integrable P)
    (u : ℝ) : Integrable fun y => riemannAutocorr (u - y) * P y := by
  refine Integrable.mono' (hPi.norm.const_mul (riemannAutocorr 0))
    ((continuous_riemannAutocorr.comp (continuous_const.sub continuous_id)).mul
      hPc).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg _)]
  exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (norm_nonneg _)

/-- **Kernel domination.** If the potential of a nonnegative weight is bounded by `B`, its pairing
with every `K`-smoothed nonnegative integrable profile is at most `B ∫ P`. -/
theorem tsum_mul_kernelSmooth_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {B : ℝ}
    (hsum : ∀ y, Summable fun n : ℕ => w n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)))
    (hB : ∀ y, kernelPotential w y ≤ B) {P : ℝ → ℝ} (hP0 : ∀ y, 0 ≤ P y) (hPc : Continuous P)
    (hPi : Integrable P) :
    Summable (fun n : ℕ => w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n))) ∧
      ∑' n : ℕ, w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n)) ≤
        B * ∫ y, P y := by
  set f : ℕ → ℝ → ℝ := fun n y => w n *
    (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) * P y with hf
  have hf0 : ∀ n y, 0 ≤ f n y := fun n y =>
    mul_nonneg (mul_nonneg (hw n) (add_nonneg (riemannAutocorr_nonneg _)
      (riemannAutocorr_nonneg _))) (hP0 y)
  have hfc : ∀ n, Continuous (f n) := fun n =>
    (continuous_const.mul ((continuous_riemannAutocorr.comp (continuous_id.add continuous_const)).add
      (continuous_riemannAutocorr.comp (continuous_id.sub continuous_const)))).mul hPc
  have hfi : ∀ n, Integrable (f n) := by
    intro n
    have h1 := integrable_riemannAutocorr_mul hPc hPi (-Real.log n)
    have h2 := integrable_riemannAutocorr_mul hPc hPi (Real.log n)
    refine ((h1.add h2).const_mul (w n)).congr (Eventually.of_forall fun y => ?_)
    show w n * (riemannAutocorr (-Real.log n - y) * P y + riemannAutocorr (Real.log n - y) * P y)
      = _
    simp only [hf]
    rw [show -Real.log n - y = -(y + Real.log n) by ring, riemannAutocorr_neg,
      show Real.log n - y = -(y - Real.log n) by ring, riemannAutocorr_neg]
    ring
  have hint : ∀ n, ∫ y, f n y =
      w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n)) := by
    intro n
    have h1 := integrable_riemannAutocorr_mul hPc hPi (Real.log n)
    have h2 := integrable_riemannAutocorr_mul hPc hPi (-Real.log n)
    unfold kernelSmooth
    rw [← integral_add h1 h2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf]
    rw [show Real.log n - y = -(y - Real.log n) by ring, riemannAutocorr_neg,
      show -Real.log n - y = -(y + Real.log n) by ring, riemannAutocorr_neg]
    ring
  set g : ℕ → ℝ := fun n => w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n))
    with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    show 0 ≤ w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n))
    rw [← hint n]; exact integral_nonneg (hf0 n)
  -- the pairing in `ℝ≥0∞`
  have hlin : ∑' n, ENNReal.ofReal (g n) = ∫⁻ y, ENNReal.ofReal (kernelPotential w y * P y) := by
    have e1 : ∀ n, ENNReal.ofReal (g n) = ∫⁻ y, ENNReal.ofReal (f n y) := fun n => by
      show ENNReal.ofReal (w n * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n))) = _
      rw [← hint n]
      exact ofReal_integral_eq_lintegral_ofReal (hfi n) (Eventually.of_forall (hf0 n))
    simp only [e1]
    rw [← lintegral_tsum fun n => (hfc n).measurable.ennreal_ofReal.aemeasurable]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hf0 n y) ((hsum y).mul_right (P y))]
    congr 1
    unfold kernelPotential
    rw [tsum_mul_right]
  have hle : ∫⁻ y, ENNReal.ofReal (kernelPotential w y * P y) ≤ ENNReal.ofReal (B * ∫ y, P y) := by
    have hB0 : ∀ y, kernelPotential w y * P y ≤ B * P y := fun y =>
      mul_le_mul_of_nonneg_right (hB y) (hP0 y)
    calc ∫⁻ y, ENNReal.ofReal (kernelPotential w y * P y)
        ≤ ∫⁻ y, ENNReal.ofReal (B * P y) := lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hB0 y)
      _ = ENNReal.ofReal (∫ y, B * P y) := by
          by_cases hB' : 0 ≤ B
          · rw [ofReal_integral_eq_lintegral_ofReal (hPi.const_mul B)
              (Eventually.of_forall fun y => mul_nonneg hB' (hP0 y))]
          · push Not at hB'
            have h0 : ∀ y, ENNReal.ofReal (B * P y) = 0 := fun y =>
              ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg hB'.le (hP0 y))
            simp only [h0, lintegral_zero]
            exact (ENNReal.ofReal_eq_zero.mpr (by
              rw [integral_const_mul]
              exact mul_nonpos_of_nonpos_of_nonneg hB'.le (integral_nonneg hP0))).symm
      _ = ENNReal.ofReal (B * ∫ y, P y) := by rw [integral_const_mul]
  have htot : ∑' n, ENNReal.ofReal (g n) ≤ ENNReal.ofReal (B * ∫ y, P y) := hlin ▸ hle
  have hne : ∑' n, ENNReal.ofReal (g n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot
  have hsg : Summable g := by
    have := ENNReal.summable_toReal hne
    exact this.congr fun n => ENNReal.toReal_ofReal (hg0 n)
  refine ⟨hsg, ?_⟩
  have e := ENNReal.ofReal_tsum_of_nonneg hg0 hsg
  have h1 : ENNReal.ofReal (∑' n, g n) ≤ ENNReal.ofReal (B * ∫ y, P y) := e ▸ htot
  by_cases hB' : 0 ≤ B * ∫ y, P y
  · exact (ENNReal.ofReal_le_ofReal_iff hB').mp h1
  · push Not at hB'
    have := ENNReal.ofReal_eq_zero.mpr hB'.le
    rw [this, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    have h2 : 0 ≤ ∑' n, g n := tsum_nonneg hg0
    have h3 : ∑' n, g n = 0 := le_antisymm h1 h2
    have h4 : (0 : ℝ) ≤ ∫ y, P y := integral_nonneg hP0
    exfalso
    rcases le_or_gt 0 B with hb | hb
    · exact absurd (mul_nonneg hb h4) (not_le.mpr hB')
    · have := hB (0 : ℝ)
      have hk : 0 ≤ kernelPotential w 0 := tsum_nonneg fun n => mul_nonneg (hw n)
        (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))
      linarith

/-! ## The deficit potential is bounded -/

theorem abs_deviationExcess_le (lam : ℕ → ℝ) (n : ℕ) :
    |deviationExcess lam n| ≤ |weilDeviation lam n| := by
  rw [abs_of_nonneg (deviationExcess_nonneg lam n)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem abs_deviationDeficit_le (lam : ℕ → ℝ) (n : ℕ) :
    |deviationDeficit lam n| ≤ |weilDeviation lam n| := by
  rw [abs_of_nonneg (deviationDeficit_nonneg lam n)]
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem deviationExcess_zero (lam : ℕ → ℝ) : deviationExcess lam 0 = 0 := by
  simp [deviationExcess, weilDeviation_zero]

theorem deviationDeficit_zero (lam : ℕ → ℝ) : deviationDeficit lam 0 = 0 := by
  simp [deviationDeficit, weilDeviation_zero]

theorem summable_excess_term {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Summable fun n : ℕ => deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
  exact summable_potential_term riemannAutocorr_nonneg hC₁
    (fun n => (abs_deviationExcess_le lam n).trans (hC n)) (deviationExcess_zero lam) hC0 y

theorem summable_deficit_term {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Summable fun n : ℕ => deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
  exact summable_potential_term riemannAutocorr_nonneg hC₁
    (fun n => (abs_deviationDeficit_le lam n).trans (hC n)) (deviationDeficit_zero lam) hC0 y

theorem deviationPotential_eq_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    deviationPotential lam y =
      kernelPotential (deviationExcess lam) y - kernelPotential (deviationDeficit lam) y := by
  unfold deviationPotential kernelPotential
  rw [← Summable.tsum_sub (summable_excess_term hW y) (summable_deficit_term hW y)]
  refine tsum_congr fun n => ?_
  rw [weilDeviation_eq_sub]; ring

/-- **The deficit potential is bounded** when the excess is summable. -/
theorem exists_kernelPotential_deficit_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hexc : Summable (deviationExcess lam)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, kernelPotential (deviationDeficit lam) y ≤ B := by
  have hpd := positiveDefiniteOnReal_neg_deviationPotential hW
  set E := ∑' n, deviationExcess lam n with hE
  have hE0 : 0 ≤ E := tsum_nonneg (deviationExcess_nonneg lam)
  refine ⟨2 * riemannAutocorr 0 * E + (-deviationPotential lam 0), ?_, fun y => ?_⟩
  · have h := GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal.norm_le hpd 0
    have h0 : 0 ≤ -deviationPotential lam 0 := by
      have := (norm_nonneg _).trans h
      simpa using this
    have := riemannAutocorr_nonneg 0
    positivity
  · have hnorm := GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal.norm_le hpd y
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at hnorm
    have hexcle : kernelPotential (deviationExcess lam) y ≤ 2 * riemannAutocorr 0 * E := by
      unfold kernelPotential
      calc ∑' n, deviationExcess lam n *
            (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))
          ≤ ∑' n, deviationExcess lam n * (2 * riemannAutocorr 0) :=
            (summable_excess_term hW y).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
              (by linarith [riemannAutocorr_le_zero (y + Real.log n),
                riemannAutocorr_le_zero (y - Real.log n)]) (deviationExcess_nonneg lam n))
              (hexc.mul_right _)
        _ = 2 * riemannAutocorr 0 * E := by rw [tsum_mul_right, hE]; ring
    have heq := deviationPotential_eq_sub hW y
    have h1 : -deviationPotential lam y ≤ -deviationPotential lam 0 := (le_abs_self _).trans hnorm
    linarith

/-! ## Cauchy profiles -/

/-- The Cauchy profile `δ/(1 + (δ(u − s))²)`. -/
def cauchyProfile (δ s u : ℝ) : ℝ := δ / (1 + (δ * (u - s)) ^ 2)

theorem cauchyProfile_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (s u : ℝ) : 0 ≤ cauchyProfile δ s u := by
  unfold cauchyProfile; positivity

theorem continuous_cauchyProfile (δ s : ℝ) : Continuous (cauchyProfile δ s) := by
  unfold cauchyProfile
  exact continuous_const.div (by fun_prop) fun u => by positivity

theorem integral_cauchyProfile {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ∫ u, cauchyProfile δ s u = π := by
  have h1 : (∫ u, cauchyProfile δ s u) = ∫ u, δ * (1 + (δ * u) ^ 2)⁻¹ := by
    have := integral_sub_right_eq_self (μ := volume) (fun u => δ * (1 + (δ * u) ^ 2)⁻¹) s
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [cauchyProfile, div_eq_mul_inv]
  rw [h1, integral_const_mul,
    Measure.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) δ, integral_univ_inv_one_add_sq,
    abs_inv, abs_of_pos hδ, smul_eq_mul]
  field_simp

theorem integrable_cauchyProfile {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Integrable (cauchyProfile δ s) := by
  by_contra h
  have := integral_undef h
  rw [integral_cauchyProfile hδ s] at this
  exact Real.pi_pos.ne' this

theorem exists_riemannAutocorr_ge :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ Icc (-1 : ℝ) 1, κ ≤ riemannAutocorr z := by
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num, by norm_num⟩ continuous_riemannAutocorr.continuousOn
  exact ⟨riemannAutocorr z₀, riemannAutocorr_pos z₀, fun z hz => hmin hz⟩

/-- A Cauchy profile of scale `δ ≤ 1` is dominated by its `K`-smoothing. -/
theorem cauchyProfile_le_kernelSmooth {κ : ℝ} (hκ : 0 < κ)
    (hκK : ∀ z ∈ Icc (-1 : ℝ) 1, κ ≤ riemannAutocorr z) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s u : ℝ) : cauchyProfile δ s u ≤ (3 / (2 * κ)) * kernelSmooth (cauchyProfile δ s) u := by
  set P := cauchyProfile δ s with hP
  have hPu : 0 < P u := by simp only [hP, cauchyProfile]; positivity
  have hlow : ∀ y ∈ Icc (u - 1) (u + 1), κ * (P u / 3) ≤ riemannAutocorr (u - y) * P y := by
    intro y hy
    have hK : κ ≤ riemannAutocorr (u - y) := hκK _ ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hPy : P u / 3 ≤ P y := by
      simp only [hP, cauchyProfile]
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hd : |y - s| ≤ |u - s| + 1 := by
        have := abs_sub_le y u s
        have : |y - u| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
        linarith
      have hsq : (δ * (y - s)) ^ 2 ≤ 2 * (δ * (u - s)) ^ 2 + 2 := by
        have h1 : (y - s) ^ 2 ≤ (|u - s| + 1) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        have h2 : (|u - s| + 1) ^ 2 ≤ 2 * (u - s) ^ 2 + 2 := by
          nlinarith [sq_abs (u - s), sq_nonneg (|u - s| - 1)]
        have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
        calc (δ * (y - s)) ^ 2 = δ ^ 2 * (y - s) ^ 2 := by ring
          _ ≤ δ ^ 2 * (2 * (u - s) ^ 2 + 2) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
          _ ≤ 2 * (δ * (u - s)) ^ 2 + 2 := by nlinarith [sq_nonneg (u - s)]
      nlinarith
    exact mul_le_mul hK hPy (by positivity) (riemannAutocorr_nonneg _)
  have hint := integrable_riemannAutocorr_mul (continuous_cauchyProfile δ s)
    (integrable_cauchyProfile hδ0 s) u
  have hset : (volume.real (Icc (u - 1) (u + 1))) • (κ * (P u / 3)) ≤
      ∫ y in Icc (u - 1) (u + 1), riemannAutocorr (u - y) * P y :=
    setIntegral_ge_of_const_le measurableSet_Icc (by simp) hlow hint.integrableOn
  have hvol : volume.real (Icc (u - 1) (u + 1)) = 2 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [hvol, smul_eq_mul] at hset
  have hfull := setIntegral_le_integral (s := Icc (u - 1) (u + 1)) hint
    (Eventually.of_forall fun y => mul_nonneg (riemannAutocorr_nonneg _)
      (cauchyProfile_nonneg hδ0.le s y))
  have hI : 2 * (κ * (P u / 3)) ≤ ∫ y, riemannAutocorr (u - y) * P y := hset.trans hfull
  show P u ≤ 3 / (2 * κ) * ∫ y, riemannAutocorr (u - y) * P y
  calc P u = 3 / (2 * κ) * (2 * (κ * (P u / 3))) := by field_simp
    _ ≤ 3 / (2 * κ) * ∫ y, riemannAutocorr (u - y) * P y :=
        mul_le_mul_of_nonneg_left hI (by positivity)

/-- **Translation bound for the deficit.** Its pairing with every Cauchy profile of scale at
most one is bounded, uniformly in the scale and the centre. -/
theorem exists_tsum_deficit_cauchyProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hexc : Summable (deviationExcess lam)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ s : ℝ,
      Summable (fun n : ℕ => deviationDeficit lam n *
        (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n))) ∧
      ∑' n : ℕ, deviationDeficit lam n *
        (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n)) ≤ D := by
  obtain ⟨B, hB0, hB⟩ := exists_kernelPotential_deficit_le hW hexc
  obtain ⟨κ, hκ, hκK⟩ := exists_riemannAutocorr_ge
  refine ⟨3 / (2 * κ) * (B * π), by positivity, fun δ hδ0 hδ1 s => ?_⟩
  obtain ⟨hsum, hle⟩ := tsum_mul_kernelSmooth_le (deviationDeficit_nonneg lam)
    (summable_deficit_term hW) hB (cauchyProfile_nonneg hδ0.le s) (continuous_cauchyProfile δ s)
    (integrable_cauchyProfile hδ0 s)
  rw [integral_cauchyProfile hδ0 s] at hle
  have hdom : ∀ n : ℕ, deviationDeficit lam n *
      (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n)) ≤
      3 / (2 * κ) * (deviationDeficit lam n * (kernelSmooth (cauchyProfile δ s) (Real.log n) +
        kernelSmooth (cauchyProfile δ s) (-Real.log n))) := by
    intro n
    have h1 := cauchyProfile_le_kernelSmooth hκ hκK hδ0 hδ1 s (Real.log n)
    have h2 := cauchyProfile_le_kernelSmooth hκ hκK hδ0 hδ1 s (-Real.log n)
    have hv := deviationDeficit_nonneg lam n
    nlinarith
  have hsum' : Summable (fun n : ℕ => deviationDeficit lam n *
      (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n))) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (deviationDeficit_nonneg lam n)
      (add_nonneg (cauchyProfile_nonneg hδ0.le s _) (cauchyProfile_nonneg hδ0.le s _)))
      hdom (hsum.mul_left _)
  refine ⟨hsum', ?_⟩
  calc _ ≤ ∑' n : ℕ, 3 / (2 * κ) * (deviationDeficit lam n *
        (kernelSmooth (cauchyProfile δ s) (Real.log n) +
          kernelSmooth (cauchyProfile δ s) (-Real.log n))) :=
        hsum'.tsum_le_tsum hdom (hsum.mul_left _)
    _ = 3 / (2 * κ) * ∑' n : ℕ, deviationDeficit lam n *
        (kernelSmooth (cauchyProfile δ s) (Real.log n) +
          kernelSmooth (cauchyProfile δ s) (-Real.log n)) := tsum_mul_left
    _ ≤ 3 / (2 * κ) * (B * π) := mul_le_mul_of_nonneg_left hle (by positivity)

end

end RHTower.WeilExcess
