import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsForPerturbedLattices
import GaloisForLFunctions.HTGeometry.JensenIntegratedCountBound
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity
import GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# Blindness costs the density aperture

A window `f` of aperture `A` is **blind** to a configuration `Λ ⊆ ℂ` when its transform vanishes on
`Λ`. The constructions of this programme give blind windows at every aperture above `πD` for
lattices, finite unions of lattices and bounded perturbations of lattices of density `D`. Here the
aperture `πD` is shown to be necessary for every configuration of lower density `D`, with no
structure assumed.

* **Jensen's inequality for a window** (`log_norm_add_density_le`). The transform `F = f̂` is entire
  with `‖F(z)‖ ≤ C e^{A|Im z|}`, and the angular mean of `|Im z|` on the circle of radius `R` about
  a real point is `≤ (2/π)R`. If the closed ball of radius `ρ` about `c` contains at least
  `2Dρ − K` points of `Λ` for `ρ₀ ≤ ρ ≤ R`, Jensen's formula with the integrated lower count gives
  `log|F(c)| + 2D(R − ρ₀) − K log(R/ρ₀) ≤ log C + (2/π)A R`.
* **The density aperture is necessary** (`pi_mul_le_of_blind`). Letting `R → ∞`: a window blind to a
  configuration whose balls about `c` hold `≥ 2Dρ − K` points for all large `ρ`, and whose
  transform does not vanish at `c`, has aperture `A ≥ πD`.
* **Nonzero windows** (`pi_mul_le_aperture_of_blind`). A nonzero window has a real point with
  `f̂(c) ≠ 0`; if `Λ` has lower density `≥ D` about every real point, every nonzero window blind to
  `Λ` has aperture `≥ πD`. For the lattice `hℤ` (`D = 1/h`) this is the threshold `π/h` of
  `exists_window_blind_to_lattice_iff`.
* **Unbounded density** (`eq_zero_of_blind_of_unbounded_density`). No nonzero window of any aperture
  is blind to a configuration of unbounded lower density. The zeros of `ζ` have density
  `(1/2π)log(T/2π)` at height `T`; for them the corpus proves the stronger statement that no
  nonzero window is blind to the real zeros of `Ξ` (`eq_zero_of_blind_to_real_zeros_of_xi`).

The price of blindness is width, measured by density: πD is the exact cost, attained by the
constructions for lattices and their perturbations and necessary for every configuration.
-/

open MeasureTheory Complex Set Metric Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- The growth constant `max(2AM, 1)` of a window bounded by `M` on `[−A, A]`. -/
def windowGrowthConstant (A M : ℝ) : ℝ := max (M * (2 * A)) 1

theorem one_le_windowGrowthConstant (A M : ℝ) : 1 ≤ windowGrowthConstant A M := le_max_right _ _

/-- Pointwise Jensen majorant: `log‖f̂(z)‖ ≤ log C + A|Im z|`. -/
theorem log_norm_paperFT_le {g : ℝ → ℂ} {A M : ℝ} (hA : 0 ≤ A) (hgs : tsupport g ⊆ Icc (-A) A)
    (hM : ∀ u, ‖g u‖ ≤ M) (z : ℂ) :
    Real.log ‖paperFT g z‖ ≤ Real.log (windowGrowthConstant A M) + A * |z.im| := by
  have hC := one_le_windowGrowthConstant A M
  have hlogC : 0 ≤ Real.log (windowGrowthConstant A M) := Real.log_nonneg hC
  by_cases h0 : paperFT g z = 0
  · rw [h0, norm_zero, Real.log_zero]; positivity
  · have hb := norm_paperFT_le_of_tsupport hA hgs hM z
    have hb' : ‖paperFT g z‖ ≤ windowGrowthConstant A M * Real.exp (A * |z.im|) := by
      calc ‖paperFT g z‖ ≤ M * Real.exp (A * |z.im|) * (2 * A) := hb
        _ = (M * (2 * A)) * Real.exp (A * |z.im|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    calc Real.log ‖paperFT g z‖
        ≤ Real.log (windowGrowthConstant A M * Real.exp (A * |z.im|)) :=
          Real.log_le_log (norm_pos_iff.mpr h0) hb'
      _ = _ := by
          rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]

/-- `∫_{ρ₀}^R (2Dρ − K)/ρ dρ = 2D(R − ρ₀) − K log(R/ρ₀)`. -/
theorem integral_linear_count_div {D K ρ₀ R : ℝ} (hρ₀ : 0 < ρ₀) (hR : ρ₀ ≤ R) :
    ∫ ρ in ρ₀..R, (2 * D * ρ - K) / ρ = 2 * D * (R - ρ₀) - K * Real.log (R / ρ₀) := by
  have h0 : (0 : ℝ) ∉ uIcc ρ₀ R := by
    rw [uIcc_of_le hR]; exact fun h => by linarith [h.1]
  have hcongr : EqOn (fun ρ => (2 * D * ρ - K) / ρ) (fun ρ => 2 * D - K * ρ⁻¹) (uIcc ρ₀ R) :=
    fun ρ hρ => by
      have : ρ ≠ 0 := fun h => h0 (h ▸ hρ)
      field_simp
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_inv (fun x hx => fun h => h0 (h ▸ hx))
      continuousOn_id).const_mul K), intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_inv h0, smul_eq_mul]
  ring

/-- **Jensen's inequality for a window blind to a configuration.** -/
theorem log_norm_add_density_le {g : ℝ → ℂ} {A M : ℝ} (hA : 0 ≤ A) (hg : Continuous g)
    (hgs : tsupport g ⊆ Icc (-A) A) (hM : ∀ u, ‖g u‖ ≤ M) {c : ℝ} (hc : paperFT g c ≠ 0)
    {Λ : Set ℂ} (hΛ : ∀ z ∈ Λ, paperFT g z = 0) {D K ρ₀ R : ℝ} (hρ₀ : 0 < ρ₀) (hR : ρ₀ ≤ R)
    (hcount : ∀ ρ ∈ Icc ρ₀ R, ∃ T : Finset ℂ, (∀ z ∈ T, z ∈ Λ ∧ z ∈ closedBall (c : ℂ) ρ) ∧
      2 * D * ρ - K ≤ T.card) :
    Real.log ‖paperFT g c‖ + (2 * D * (R - ρ₀) - K * Real.log (R / ρ₀)) ≤
      Real.log (windowGrowthConstant A M) + A * (2 / π * R) := by
  classical
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  have hFd : Differentiable ℂ (paperFT g) := WeilEF.differentiable_paperFT hg hgc
  have hFa : AnalyticOnNhd ℂ (paperFT g) univ := fun z _ => hFd.analyticAt z
  have hint : IntervalIntegrable (fun ρ => (2 * D * ρ - K) / ρ) volume ρ₀ R := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hR]
    exact (by fun_prop : Continuous fun ρ : ℝ => 2 * D * ρ - K).continuousOn.div continuousOn_id
      fun x hx => (hρ₀.trans_le hx.1).ne'
  have hφ : ∀ ρ ∈ Icc ρ₀ R, 2 * D * ρ - K ≤
      ∑ᶠ u, (MeromorphicOn.divisor (paperFT g) (closedBall (c : ℂ) ρ) u : ℝ) := by
    intro ρ hρ
    obtain ⟨T, hT, hcard⟩ := hcount ρ hρ
    have hle := _root_.RHTower.card_le_sum_divisor_of_finite_zeros hFd hc T id (injOn_id _)
      (fun i hi => (hT i hi).2) (fun i hi => hΛ _ (hT i hi).1)
    rw [← _root_.RHTower.cast_finsum_divisor]
    exact hcard.trans (by exact_mod_cast hle)
  have hJ := HTGeometry.log_norm_add_integral_le_circleAverage hFa hc hρ₀ hR hint hφ
  rw [integral_linear_count_div hρ₀ hR] at hJ
  have hR0 : 0 ≤ R := hρ₀.le.trans hR
  have hcont : Continuous fun z : ℂ => Real.log (windowGrowthConstant A M) + A * |z.im| := by
    fun_prop
  have hmono := Real.circleAverage_mono
    (MeromorphicOn.circleIntegrable_log_norm (fun z _ => (hFd.analyticAt z).meromorphicAt))
    (hcont.continuousOn.circleIntegrable') fun z _ => log_norm_paperFT_le hA hgs hM z
  have hsplit : Real.circleAverage (fun z : ℂ => Real.log (windowGrowthConstant A M) + A * |z.im|)
      (c : ℂ) R = Real.log (windowGrowthConstant A M) +
        A * Real.circleAverage (fun z : ℂ => |z.im|) (c : ℂ) R := by
    rw [show (fun z : ℂ => Real.log (windowGrowthConstant A M) + A * |z.im|) =
        (fun _ => Real.log (windowGrowthConstant A M)) + fun z => A • |z.im| by
          funext z; simp [smul_eq_mul],
      Real.circleAverage_add (continuous_const.continuousOn.circleIntegrable')
        ((by fun_prop : Continuous fun z : ℂ => A • |z.im|).continuousOn.circleIntegrable'),
      Real.circleAverage_const, Real.circleAverage_fun_smul, smul_eq_mul]
  have him := HTGeometry.circleAverage_abs_im_le (c : ℂ) hR0
  rw [Complex.ofReal_im, abs_zero, zero_add] at him
  have := mul_le_mul_of_nonneg_left him hA
  linarith

/-- An affine lower count `2Dρ − K` against a subexponential remainder forces `2D ≤ a`. -/
theorem le_of_forall_linear_le {D K ρ₀ a B : ℝ} (hρ₀ : 0 < ρ₀) (hK : 0 ≤ K)
    (h : ∀ R, ρ₀ ≤ R → 2 * D * R - K * Real.log (R / ρ₀) ≤ a * R + B) : 2 * D ≤ a := by
  by_contra hlt
  push Not at hlt
  set ε := 2 * D - a with hε
  have hε0 : 0 < ε := by linarith
  -- `log(R/ρ₀) ≤ R/(ρ₀ t) + log t` with `K/(ρ₀ t) ≤ ε/2`
  set t := 2 * (K + 1) / (ε * ρ₀) with ht
  have ht0 : 0 < t := by positivity
  set R := max ρ₀ (2 * (|B| + K * |Real.log t|) / ε + 1) with hRdef
  have hR : ρ₀ ≤ R := le_max_left _ _
  have hR0 : 0 < R := hρ₀.trans_le hR
  have hlog : Real.log (R / ρ₀) ≤ R / (ρ₀ * t) + |Real.log t| := by
    have e : R / ρ₀ = R / (ρ₀ * t) * t := by field_simp
    rw [e, Real.log_mul (by positivity) ht0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < R / (ρ₀ * t) by positivity)
    linarith [le_abs_self (Real.log t)]
  have hKt : K * (R / (ρ₀ * t)) ≤ ε / 2 * R := by
    have e : K * (R / (ρ₀ * t)) = K * ε / (2 * (K + 1)) * R := by
      rw [ht]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hR0.le
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmain := h R hR
  have hKlog : K * Real.log (R / ρ₀) ≤ ε / 2 * R + K * |Real.log t| := by
    have := mul_le_mul_of_nonneg_left hlog hK
    rw [mul_add] at this; linarith
  have hRbig : 2 * (|B| + K * |Real.log t|) / ε + 1 ≤ R := le_max_right _ _
  have h2 : 2 * (|B| + K * |Real.log t|) < ε * R := by
    have := (div_lt_iff₀ hε0).mp (by linarith : 2 * (|B| + K * |Real.log t|) / ε < R)
    linarith
  have hB := le_abs_self B
  have : ε * R ≤ ε / 2 * R + K * |Real.log t| + B := by rw [hε] at *; linarith
  nlinarith [abs_nonneg (Real.log t)]

/-- **The density aperture is necessary.** A window of aperture `A` whose transform does not vanish
at the real point `c` and is blind to a configuration holding `≥ 2Dρ − K` points in every ball of
radius `ρ ≥ ρ₀` about `c` has `πD ≤ A`. -/
theorem pi_mul_le_of_blind {g : ℝ → ℂ} {A M : ℝ} (hA : 0 ≤ A) (hg : Continuous g)
    (hgs : tsupport g ⊆ Icc (-A) A) (hM : ∀ u, ‖g u‖ ≤ M) {c : ℝ} (hc : paperFT g c ≠ 0)
    {Λ : Set ℂ} (hΛ : ∀ z ∈ Λ, paperFT g z = 0) {D K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hcount : ∀ ρ, ρ₀ ≤ ρ → ∃ T : Finset ℂ, (∀ z ∈ T, z ∈ Λ ∧ z ∈ closedBall (c : ℂ) ρ) ∧
      2 * D * ρ - K ≤ T.card) :
    π * D ≤ A := by
  set K' := max K 0
  have hcount' : ∀ ρ, ρ₀ ≤ ρ → ∃ T : Finset ℂ, (∀ z ∈ T, z ∈ Λ ∧ z ∈ closedBall (c : ℂ) ρ) ∧
      2 * D * ρ - K' ≤ T.card := fun ρ hρ => by
    obtain ⟨T, hT, hcard⟩ := hcount ρ hρ
    exact ⟨T, hT, le_trans (by linarith [le_max_left K 0]) hcard⟩
  have key := le_of_forall_linear_le (D := D) (K := K') (a := 2 / π * A)
    (B := Real.log (windowGrowthConstant A M) - Real.log ‖paperFT g c‖ + 2 * D * ρ₀) hρ₀
    (le_max_right K 0) fun R hR => by
      have := log_norm_add_density_le hA hg hgs hM hc hΛ hρ₀ hR fun ρ hρ => hcount' ρ hρ.1
      linarith
  have hπ := Real.pi_pos
  have : 2 * D * π ≤ 2 / π * A * π := mul_le_mul_of_nonneg_right key hπ.le
  rw [show 2 / π * A * π = 2 * A by field_simp] at this
  linarith

/-- A nonzero window has a real point where its transform does not vanish. -/
theorem exists_paperFT_real_ne_zero {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hne : f ≠ 0) : ∃ c : ℝ, paperFT f c ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (_root_.RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_real_eq_zero hf
    (hf.integrable_of_hasCompactSupport hfc) h)

/-- `Λ` holds at least `2Dρ − K` points in the large balls about every real point. -/
def HasLowerDensityAtLeast (Λ : Set ℂ) (D : ℝ) : Prop :=
  ∀ c : ℝ, ∃ K ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ, ρ₀ ≤ ρ → ∃ T : Finset ℂ,
    (∀ z ∈ T, z ∈ Λ ∧ z ∈ closedBall (c : ℂ) ρ) ∧ 2 * D * ρ - K ≤ T.card

/-- **Blindness costs the density aperture.** Every nonzero window of aperture `A` blind to a
configuration of lower density `≥ D` has `πD ≤ A`. -/
theorem pi_mul_le_aperture_of_blind {f : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hf : ApertureWindow A f)
    (hne : f ≠ 0) {Λ : Set ℂ} {D : ℝ} (hΛD : HasLowerDensityAtLeast Λ D)
    (hΛ : ∀ z ∈ Λ, paperFT f z = 0) : π * D ≤ A := by
  have hfc := hf.hasCompactSupport
  obtain ⟨c, hc⟩ := exists_paperFT_real_ne_zero hf.1.continuous hfc hne
  obtain ⟨M, hM⟩ := hf.1.continuous.bounded_above_of_compact_support hfc
  obtain ⟨K, ρ₀, hρ₀, hcount⟩ := hΛD c
  exact pi_mul_le_of_blind hA hf.1.continuous hf.2 hM hc hΛ hρ₀ hcount

/-- **No window is blind to unbounded density.** A window blind to a configuration of lower density
`≥ D` for every `D` is zero. -/
theorem eq_zero_of_blind_of_unbounded_density {f : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ApertureWindow A f) {Λ : Set ℂ} (hΛD : ∀ D, HasLowerDensityAtLeast Λ D)
    (hΛ : ∀ z ∈ Λ, paperFT f z = 0) : f = 0 := by
  by_contra hne
  have h := pi_mul_le_aperture_of_blind hA hf hne (hΛD (A / π + 1)) hΛ
  have hπ := Real.pi_pos
  have : π * (A / π + 1) = A + π := by field_simp
  linarith

/-- **No window is blind to the zeros of `ζ`** (corpus: `eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero`).
A window whose transform vanishes at every real zero of `Ξ`, i.e. at every critical zero of `ζ` in
the camera coordinate, is zero. -/
theorem eq_zero_of_blind_to_real_zeros_of_xi {f : ℝ → ℂ} {A : ℝ} (hf : ApertureWindow A f)
    (hvan : ∀ t : ℝ, _root_.RHTower.XiC (t : ℂ) = 0 → paperFT f t = 0) : f = 0 :=
  _root_.RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero
    hf.1.continuous hf.hasCompactSupport hvan

end GaloisForLFunctions.ZeroConfigurationGeometry
