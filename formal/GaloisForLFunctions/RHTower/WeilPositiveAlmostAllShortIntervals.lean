import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport
import GaloisForLFunctions.HTGeometry.PlancherelInequalityReal

/-!
# Almost all short windows meet the support of a Weil-positive system

Let `lam` be Weil-positive in Herglotz form for an archimedean datum of logarithmic growth
(`HerglotzWeilPositive`), for example ζ's datum.  For every `0 < ε ≤ 1`, the windows
`(y, y + y X^{ε-1})` with `y = e^u`, `u ∈ [log X, log 2X]`, that miss the support of `lam` have
starting points of total logarithmic measure `O(X^{-ε/2})`
(`volume_gapStarts_le_of_herglotzWeilPositive`).

* On a window missing the support, the smoothed sum `Σ lam(n) φ_δ(n/y)` vanishes, so the
  contour-shifted integral `(1/2π) y^c 𝓕F(log y)` has size at least `y δ/4`
  (`smoothedSum_sub_eq_shifted_integral`, `integral_shortBump_ge`).
* Plancherel (`lintegral_norm_sq_angularFourier_le`) bounds `∫ |𝓕F|²` by `2π ∫ |F|²`.
* The Harnack bound on `E = D − 1/(s−1)` and the Lorentzian decay of `𝓜φ_δ` give
  `∫ |F|² ≪ δ^{1-2κ}` (`integral_sq_lorentz_rpow_le`); Markov's inequality concludes.

A Weil-positive system supported on the primes therefore forces primes in almost all windows of
length `X^ε`, for every `ε > 0` (`volume_primeGapStarts_le_of_zetaWeilPositive`).
-/

open Complex Metric Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- `x^{c+it} = x^c e^{i t log x}` for `x > 0`. -/
theorem ofReal_cpow_add_mul_I {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    (x : ℂ) ^ ((c : ℂ) + t * I) = ((x ^ c : ℝ) : ℂ) * Complex.exp (I * (Real.log x : ℝ) * t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Squared Lorentzian against a small power.**  For `0 < δ ≤ 1` and `0 < κ ≤ 1/4`,
`∫ (δ/(1 + δ²y²))² (|y| + 3)^{2κ} dy ≤ δ^{1-2κ} · lorentzHalfConst`. -/
theorem integral_sq_lorentz_rpow_le {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (hκ4 : κ ≤ 1 / 4) :
    Integrable (fun y : ℝ => (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ)) ∧
      ∫ y : ℝ, (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ) ≤
        δ ^ (1 - 2 * κ) * lorentzHalfConst := by
  obtain ⟨hI, hb⟩ := integral_lorentz_rpow_le hδ hδ1 (κ := 2 * κ) (by linarith) (by linarith)
  have hpt : ∀ y : ℝ, (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ) ≤
      δ * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (2 * κ)) := by
    intro y
    have hden : 1 ≤ 1 + δ ^ 2 * y ^ 2 := by nlinarith [sq_nonneg (δ * y)]
    have hq : δ / (1 + δ ^ 2 * y ^ 2) ≤ δ := div_le_self hδ.le hden
    have hq0 : 0 ≤ δ / (1 + δ ^ 2 * y ^ 2) := by positivity
    have hp : 0 ≤ (|y| + 3) ^ (2 * κ) := by positivity
    calc (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ)
        = (δ / (1 + δ ^ 2 * y ^ 2)) * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (2 * κ)) := by ring
      _ ≤ δ * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (2 * κ)) := by gcongr
  have hcont : Continuous fun y : ℝ => (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ) := by
    have h1 : Continuous fun y : ℝ => δ / (1 + δ ^ 2 * y ^ 2) :=
      continuous_const.div (by fun_prop) (fun y => by positivity)
    exact (h1.pow 2).mul ((continuous_abs.add continuous_const).rpow_const
      (fun _ => Or.inr (by linarith)))
  have hint : Integrable fun y : ℝ => (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ) :=
    (hI.const_mul δ).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt y)
  refine ⟨hint, ?_⟩
  calc ∫ y : ℝ, (δ / (1 + δ ^ 2 * y ^ 2)) ^ 2 * (|y| + 3) ^ (2 * κ)
      ≤ ∫ y : ℝ, δ * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (2 * κ)) :=
        integral_mono hint (hI.const_mul δ) hpt
    _ = δ * ∫ y : ℝ, δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (2 * κ) := integral_const_mul _ _
    _ ≤ δ * (δ ^ (-(2 * κ)) * lorentzHalfConst) := by gcongr
    _ = δ ^ (1 - 2 * κ) * lorentzHalfConst := by
        rw [← mul_assoc, show (1 - 2 * κ) = 1 + -(2 * κ) by ring, Real.rpow_add hδ,
          Real.rpow_one]


/-- **Almost all short intervals meet the support of a Weil-positive system.**  Let `lam` be
Weil-positive in Herglotz form for an archimedean datum `A` of logarithmic growth, and `0 < ε ≤ 1`.
For `X ≥ 1`, the logarithmic starting points `u ∈ [log X, log 2X]` whose window
`(e^u, e^u + e^u X^{ε-1})` (of length between `X^ε` and `2X^ε`) misses the support of `lam` form a
set of measure `O(X^{-ε/2})`.

Proof: on such a window the smoothed sum vanishes, so the contour-shifted integral
`(1/2π) e^{uc} 𝓕F(u)` has size `≥ e^u δ/4`; Plancherel bounds `∫ |𝓕F|²` by `2π ∫ |F|²`, and the
Harnack/Lorentzian bound gives `∫ |F|² ≪ δ^{1-2κ}`.  Markov's inequality finishes. -/
theorem volume_gapStarts_le_of_herglotzWeilPositive {lam : ℕ → ℝ} {A : ℂ → ℂ} {K : ℝ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) (hK : 0 ≤ K)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hW : HerglotzWeilPositive lam A) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ n : ℕ, Real.exp u < n → (n : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) → lam n = 0}
        ≤ ENNReal.ofReal (C * X ^ (-(ε / 2))) := by
  obtain ⟨Φ, hΦ, hre, hid⟩ := hW.herglotz
  have hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ) := hW.summable 2 (by norm_num)
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_deriv_shortBumpProfile
  set L : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hL : 0 ≤ L := tsum_nonneg fun n => by positivity
  set CE : ℝ := 6 * (K + 1 + L)
  have hCE : 0 ≤ CE := by positivity
  have hid2 : ∀ t : ℝ, Φ (2 + t * I) =
      A (2 + t * I) + 1 / (2 + t * I - 1) - LSeries (fun n => (lam n : ℂ)) (2 + t * I) :=
    fun t => hid _ (by simp)
  set E : ℂ → ℂ := fun s => A s - Φ s
  have hE : ∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 2 →
      ‖E (σ + t * I)‖ ≤ CE * Real.log (|t| + 3) / (σ - 1 / 2) :=
    fun σ t hσ hσ2 => norm_regularPart_le hK hsum hΦ hre hAK hid2 hσ hσ2
  set η : ℝ := ε / 8
  have hη : 0 < η := by positivity
  set c : ℝ := 1 / 2 + η
  have hc : 1 / 2 < c := by simp only [c]; linarith
  have hc2 : c ≤ 2 := by simp only [c, η]; linarith
  have hcη : c - 1 / 2 = η := by simp only [c]; ring
  set B : ℝ := (4 + 16 * M) * CE / (η * η)
  have hB : 0 ≤ B := by positivity
  have hJ : 0 ≤ lorentzHalfConst := integral_nonneg fun v => by positivity
  refine ⟨8 * B ^ 2 * lorentzHalfConst / Real.pi, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set δ : ℝ := X ^ (ε - 1)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hX0 _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  set Mf : ℂ → ℂ := mellin (fun u => (shortBump δ u : ℂ))
  have hMd : Differentiable ℂ Mf := differentiable_mellin_shortBump hδ
  set F : ℝ → ℂ := fun t => Mf ((c : ℂ) + t * I) * E ((c : ℂ) + t * I)
  -- pointwise bound
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ B * (δ / (1 + δ ^ 2 * t ^ 2) * (|t| + 3) ^ η) := by
    intro t
    have h1 := norm_mellin_shortBump_le_lorentz hδ hδ1 hM (σ := c) (t := t) (by linarith) hc2
    have h2 := hE c t hc hc2
    rw [hcη] at h2
    have hlog := log_abs_add_three_le_rpow hη t
    have hden : 0 < 1 + δ ^ 2 * t ^ 2 := by positivity
    calc ‖F t‖ = ‖Mf ((c : ℂ) + t * I)‖ * ‖E ((c : ℂ) + t * I)‖ := norm_mul _ _
      _ ≤ ((4 + 16 * M) * δ / (1 + δ ^ 2 * t ^ 2)) * (CE * Real.log (|t| + 3) / η) := by
          gcongr
      _ ≤ ((4 + 16 * M) * δ / (1 + δ ^ 2 * t ^ 2)) * (CE * ((|t| + 3) ^ η / η) / η) := by
          gcongr
      _ = B * (δ / (1 + δ ^ 2 * t ^ 2) * (|t| + 3) ^ η) := by
          simp only [B]; field_simp
  have hFc : Continuous F := by
    have hmem : ∀ t : ℝ, ((c : ℂ) + t * I) ∈ {s : ℂ | 1 / 2 < s.re} := fun t => by simpa using hc
    have hEc : Continuous fun t : ℝ => E ((c : ℂ) + t * I) :=
      (hA.sub hΦ).continuousOn.comp_continuous (by fun_prop) hmem
    exact (hMd.continuous.comp (by fun_prop)).mul hEc
  obtain ⟨hI1, -⟩ := integral_lorentz_rpow_le hδ hδ1 hη (by simp only [η]; linarith)
  have hFi : Integrable F :=
    (hI1.const_mul B).mono' hFc.aestronglyMeasurable (Eventually.of_forall hFb)
  obtain ⟨hI2, hI2b⟩ := integral_sq_lorentz_rpow_le hδ hδ1 hη (by simp only [η]; linarith)
  have hF2b : ∀ t : ℝ, ‖F t‖ ^ 2 ≤ B ^ 2 * ((δ / (1 + δ ^ 2 * t ^ 2)) ^ 2 * (|t| + 3) ^ (2 * η)) := by
    intro t
    have h := hFb t
    have hpow : (|t| + 3) ^ (2 * η) = ((|t| + 3) ^ η) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
    rw [hpow]
    calc ‖F t‖ ^ 2 ≤ (B * (δ / (1 + δ ^ 2 * t ^ 2) * (|t| + 3) ^ η)) ^ 2 := by
          gcongr
      _ = B ^ 2 * ((δ / (1 + δ ^ 2 * t ^ 2)) ^ 2 * ((|t| + 3) ^ η) ^ 2) := by ring
  have hF2i : Integrable fun t => ‖F t‖ ^ 2 :=
    (hI2.const_mul (B ^ 2)).mono' (hFc.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hF2b t)
  have hF2int : ∫ t, ‖F t‖ ^ 2 ≤ B ^ 2 * (δ ^ (1 - 2 * η) * lorentzHalfConst) := by
    calc ∫ t, ‖F t‖ ^ 2
        ≤ ∫ t, B ^ 2 * ((δ / (1 + δ ^ 2 * t ^ 2)) ^ 2 * (|t| + 3) ^ (2 * η)) :=
          integral_mono hF2i (hI2.const_mul _) hF2b
      _ = B ^ 2 * ∫ t, (δ / (1 + δ ^ 2 * t ^ 2)) ^ 2 * (|t| + 3) ^ (2 * η) :=
          integral_const_mul _ _
      _ ≤ B ^ 2 * (δ ^ (1 - 2 * η) * lorentzHalfConst) := by gcongr
  have hPl := lintegral_norm_sq_angularFourier_le hFc hFi hF2i
  -- lower bound on the gap set
  set τ₀ : ℝ := (Real.pi * X ^ (1 - c) * δ / 2) ^ 2
  have hτ₀ : 0 < τ₀ := by positivity
  have hsub : {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
      ∀ n : ℕ, Real.exp u < n → (n : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) → lam n = 0} ⊆
      {u : ℝ | ENNReal.ofReal τ₀ ≤ ENNReal.ofReal (‖angularFourier F u‖ ^ 2)} := by
    rintro u ⟨hu, hgap⟩
    simp only [mem_setOf_eq]
    apply ENNReal.ofReal_le_ofReal
    set x : ℝ := Real.exp u
    have hx0 : 0 < x := Real.exp_pos u
    have hXx : X ≤ x := by
      have := Real.exp_le_exp.mpr hu.1; rwa [Real.exp_log hX0] at this
    have hx1 : 1 ≤ x := le_trans hX hXx
    have hzero : ∑' n : ℕ, lam n * shortBump δ (n / x) = 0 := by
      have hterm : ∀ n : ℕ, lam n * shortBump δ (n / x) = 0 := by
        intro n
        by_cases hb : shortBump δ (n / x) = 0
        · simp [hb]
        · have hmem : (n : ℝ) / x ∈ Ioo 1 (1 + δ) := by
            by_contra h; exact hb (shortBump_eq_zero hδ h)
          have h1 : x < n := by
            have := hmem.1; rwa [lt_div_iff₀ hx0, one_mul] at this
          have h2 : (n : ℝ) < x + x * X ^ (ε - 1) := by
            have := hmem.2; rw [div_lt_iff₀ hx0] at this; simp only [δ] at this; linarith
          simp [hgap n h1 h2]
      simp [hterm]
    have hident := smoothedSum_sub_eq_shifted_integral hK hA hAK hsum hΦ hre hid2 hδ hδ1 hx1 hc hc2
    rw [hzero] at hident
    have hrewrite : ∫ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) *
        mellin (fun u => (shortBump δ u : ℂ)) ((c : ℂ) + y * I) *
          (A ((c : ℂ) + y * I) - Φ ((c : ℂ) + y * I)) =
        ((x ^ c : ℝ) : ℂ) * angularFourier F u := by
      rw [angularFourier, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [F, E, Mf]
      rw [ofReal_cpow_add_mul_I hx0, show Real.log x = u from Real.log_exp u]
      ring
    rw [hrewrite] at hident
    have hnorm := congrArg norm hident
    rw [Complex.ofReal_zero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      norm_mul, norm_mul] at hnorm
    have hπn : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; norm_num
    rw [hπn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 c)] at hnorm
    have hint := integral_shortBump_ge hδ
    have hlow : x * δ / 4 ≤ |x * ∫ u, shortBump δ u| := by
      calc x * δ / 4 = x * (δ / 4) := by ring
        _ ≤ x * ∫ u, shortBump δ u := by gcongr
        _ ≤ |x * ∫ u, shortBump δ u| := le_abs_self _
    rw [hnorm] at hlow
    -- `‖𝓕F(u)‖ ≥ (π/2) x^{1-c} δ ≥ (π/2) X^{1-c} δ`
    have hxc : x ^ (1 - c) * x ^ c = x := by
      rw [← Real.rpow_add hx0]; simp
    have hkey : Real.pi * x ^ (1 - c) * δ / 2 ≤ ‖angularFourier F u‖ := by
      have hxcpos : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
      have this : x ^ (1 - c) * x ^ c * δ / 4 ≤
          1 / (2 * Real.pi) * (x ^ c * ‖angularFourier F u‖) := by rw [hxc]; exact hlow
      have hπ := Real.pi_pos
      have h' : x ^ c * (x ^ (1 - c) * δ / 4) ≤ x ^ c * (‖angularFourier F u‖ / (2 * Real.pi)) := by
        calc x ^ c * (x ^ (1 - c) * δ / 4) = x ^ (1 - c) * x ^ c * δ / 4 := by ring
          _ ≤ 1 / (2 * Real.pi) * (x ^ c * ‖angularFourier F u‖) := this
          _ = x ^ c * (‖angularFourier F u‖ / (2 * Real.pi)) := by ring
      have h'' := le_of_mul_le_mul_left h' hxcpos
      rw [le_div_iff₀ (by positivity)] at h''
      nlinarith
    have hXc : X ^ (1 - c) ≤ x ^ (1 - c) :=
      Real.rpow_le_rpow hX0.le hXx (by simp only [c, η]; linarith)
    have hlow2 : Real.pi * X ^ (1 - c) * δ / 2 ≤ ‖angularFourier F u‖ := by
      refine le_trans ?_ hkey
      have := Real.pi_pos
      gcongr
    have h0 : 0 ≤ Real.pi * X ^ (1 - c) * δ / 2 := by positivity
    simp only [τ₀]
    exact pow_le_pow_left₀ h0 hlow2 2
  have hmeas : AEMeasurable (fun u => ENNReal.ofReal (‖angularFourier F u‖ ^ 2)) :=
    ((continuous_angularFourier hFc hFi).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  calc volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ n : ℕ, Real.exp u < n → (n : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) → lam n = 0}
      ≤ volume {u : ℝ | ENNReal.ofReal τ₀ ≤ ENNReal.ofReal (‖angularFourier F u‖ ^ 2)} :=
        measure_mono hsub
    _ ≤ (∫⁻ u, ENNReal.ofReal (‖angularFourier F u‖ ^ 2)) / ENNReal.ofReal τ₀ :=
        meas_ge_le_lintegral_div hmeas (by simpa using hτ₀) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * Real.pi * ∫ x, ‖F x‖ ^ 2) / ENNReal.ofReal τ₀ := by gcongr
    _ = ENNReal.ofReal (2 * Real.pi * (∫ x, ‖F x‖ ^ 2) / τ₀) := by
        rw [ENNReal.ofReal_div_of_pos hτ₀]
    _ ≤ ENNReal.ofReal (8 * B ^ 2 * lorentzHalfConst / Real.pi * X ^ (-(ε / 2))) := by
        apply ENNReal.ofReal_le_ofReal
        have hπ := Real.pi_pos
        -- exponent bookkeeping
        have hδpow : δ ^ (1 - 2 * η) / δ ^ 2 = X ^ ((ε - 1) * (-1 - 2 * η)) := by
          rw [show δ ^ 2 = δ ^ (2 : ℝ) by norm_num, ← Real.rpow_sub hδ, ← Real.rpow_mul hX0.le]
          congr 1; ring
        have hXpow : X ^ ((ε - 1) * (-1 - 2 * η)) / (X ^ (1 - c)) ^ 2 ≤ X ^ (-(ε / 2)) := by
          rw [show (X ^ (1 - c)) ^ 2 = X ^ (2 * (1 - c)) by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; ring_nf,
            ← Real.rpow_sub hX0]
          apply Real.rpow_le_rpow_of_exponent_le hX
          simp only [c, η]; nlinarith
        have hbound : 2 * Real.pi * (∫ x, ‖F x‖ ^ 2) / τ₀ ≤
            2 * Real.pi * (B ^ 2 * (δ ^ (1 - 2 * η) * lorentzHalfConst)) / τ₀ := by gcongr
        calc 2 * Real.pi * (∫ x, ‖F x‖ ^ 2) / τ₀
            ≤ 2 * Real.pi * (B ^ 2 * (δ ^ (1 - 2 * η) * lorentzHalfConst)) / τ₀ := hbound
          _ = 8 * B ^ 2 * lorentzHalfConst / Real.pi *
                (X ^ ((ε - 1) * (-1 - 2 * η)) / (X ^ (1 - c)) ^ 2) := by
              simp only [τ₀]
              rw [← hδpow]
              field_simp
              ring
          _ ≤ 8 * B ^ 2 * lorentzHalfConst / Real.pi * X ^ (-(ε / 2)) := by gcongr


/-- **A Weil-positive system supported on the primes forces primes in almost all windows of length
`X^ε`.**  The logarithmic starting points `u ∈ [log X, log 2X]` whose window
`(e^u, e^u + e^u X^{ε-1})` contains no prime form a set of measure `O(X^{-ε/2})`. -/
theorem volume_primeGapStarts_le_of_herglotzWeilPositive {lam : ℕ → ℝ} {A : ℂ → ℂ} {K : ℝ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) (hK : 0 ≤ K)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hW : HerglotzWeilPositive lam A) (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ p : ℕ, p.Prime → Real.exp u < p → (p : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) →
          False}
        ≤ ENNReal.ofReal (C * X ^ (-(ε / 2))) := by
  obtain ⟨C, hC⟩ := volume_gapStarts_le_of_herglotzWeilPositive hA hK hAK hW hε hε1
  refine ⟨C, fun X hX => le_trans (measure_mono ?_) (hC X hX)⟩
  rintro u ⟨hu, hno⟩
  refine ⟨hu, fun n h1 h2 => ?_⟩
  by_contra hn
  exact hno n (hsupp n hn) h1 h2

/-- **ζ's Weil cone: almost all windows of length `X^ε` meet the support.** -/
theorem volume_gapStarts_le_of_zetaWeilPositive {lam : ℕ → ℝ}
    (hW : HerglotzWeilPositive lam zetaArchimedeanDatum) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ n : ℕ, Real.exp u < n → (n : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) → lam n = 0}
        ≤ ENNReal.ofReal (C * X ^ (-(ε / 2))) := by
  obtain ⟨K, hK, hKb⟩ := exists_log_bound_zetaArchimedeanDatum
  exact volume_gapStarts_le_of_herglotzWeilPositive
    (differentiableOn_zetaArchimedeanDatum.mono fun s hs => by
      show 0 < s.re; have : 1 / 2 < s.re := hs; linarith) hK hKb hW hε hε1

/-- **ζ's Weil cone: a prime-supported producer forces primes in almost all windows of length
`X^ε`**, for every `ε > 0`. -/
theorem volume_primeGapStarts_le_of_zetaWeilPositive {lam : ℕ → ℝ}
    (hW : HerglotzWeilPositive lam zetaArchimedeanDatum) (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ p : ℕ, p.Prime → Real.exp u < p → (p : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) →
          False}
        ≤ ENNReal.ofReal (C * X ^ (-(ε / 2))) := by
  obtain ⟨K, hK, hKb⟩ := exists_log_bound_zetaArchimedeanDatum
  exact volume_primeGapStarts_le_of_herglotzWeilPositive
    (differentiableOn_zetaArchimedeanDatum.mono fun s hs => by
      show 0 < s.re; have : 1 / 2 < s.re := hs; linarith) hK hKb hW hsupp hε hε1

end RHTower
