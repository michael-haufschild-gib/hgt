import GaloisForLFunctions.RHTower.WeilConeNullEnergyBlindTestCarrier

/-!
# A null prime-blind test makes every Weil-positive spectrum purely atomic

Let `F` be a real test with `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}` (`ExpDecayTest`).

* **Analyticity** (`exists_analyticOnNhd_paperFT`).  `F̂(z) = ∫ F(u) e^{izu} du` is analytic on the
  open strip `|Im z| < 1/2 + δ`.
* **Isolated real zeros** (`countable_setOf_paperFT_eq_zero`).  If `F̂` does not vanish identically
  on the real line, its real zeros form a countable set: each is isolated by the identity theorem.

**Theorem** (`exists_countable_carrier_of_null`).  If `F` is moreover prime-blind with zero pole
and archimedean energy (a NULL test, MUST-1334/1336), then for every full-cone Weil-positive system
`lam` the boundary measure `μ_lam` is carried by a countable set, namely the real zeros of `F̂`.

So, given a NULL test, every point of the Weil cone has a purely atomic spectrum, like the zero
counting measure of an `L`-function.  RH then follows exactly when some cone point has integer
atoms (corpus `vonMangoldt_and_riemannHypothesis_of_integer_counting`), and rational atoms produce
real-rooted twins (corpus `exists_realRooted_twin_of_fractional_counting`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- `|e^{izu}| ≤ e^{|Im z| |u|}`. -/
private theorem norm_cexp_I_mul_le_exp_abs (z : ℂ) (u : ℝ) :
    ‖Complex.exp (I * z * u)‖ ≤ Real.exp (|z.im| * |u|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [hre]
  have := neg_abs_le (z.im * u)
  rw [abs_mul] at this
  linarith

/-- **The transform of a decay-class test is analytic on a strip wider than the critical one.** -/
theorem exists_analyticOnNhd_paperFT {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    ∃ ε : ℝ, 1 / 2 < ε ∧
      AnalyticOnNhd ℂ (paperFT (fun u => (F u : ℂ))) {z : ℂ | |z.im| < ε} := by
  obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
  refine ⟨1 / 2 + δ, by linarith, ?_⟩
  have hopen : IsOpen {z : ℂ | |z.im| < 1 / 2 + δ} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => ?_) hopen
  have hz₀' : |z₀.im| < 1 / 2 + δ := hz₀
  set m : ℝ := 1 / 2 + δ - |z₀.im| with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set g : ℝ → ℂ := fun u => (F u : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp hF2.continuous
  set Fz : ℂ → ℝ → ℂ := fun z u => g u * Complex.exp (I * z * u) with hFz
  set Fz' : ℂ → ℝ → ℂ := fun z u => g u * (I * u * Complex.exp (I * z * u)) with hFz'
  set bound : ℝ → ℝ := fun u => (4 * C / m) * Real.exp (-(m / 4 * |u|)) with hbound
  have hball : Metric.ball z₀ (m / 2) ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by positivity)
  have hmeas : ∀ z, AEStronglyMeasurable (Fz z) volume := fun z =>
    (hgc.mul (by fun_prop)).aestronglyMeasurable
  have hexpint : ∀ c : ℝ, 0 < c → Integrable (fun u : ℝ => Real.exp (-(c * |u|))) := fun c hc =>
    ((RHTower.integrable_exp_neg_abs).comp_mul_left' hc.ne').congr
      (Eventually.of_forall fun u => by simp only [abs_mul, abs_of_pos hc])
  have hint₀ : Integrable (Fz z₀) := by
    refine ((hexpint m hm0).const_mul C).mono' (hmeas z₀) (Eventually.of_forall fun u => ?_)
    simp only [hFz, hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |F u| * ‖Complex.exp (I * z₀ * u)‖
        ≤ (C * Real.exp (-((1 / 2 + δ) * |u|))) * Real.exp (|z₀.im| * |u|) :=
          mul_le_mul (hb u).1 (norm_cexp_I_mul_le_exp_abs z₀ u) (norm_nonneg _) (by positivity)
      _ = C * Real.exp (-(m * |u|)) := by
          rw [mul_assoc, ← Real.exp_add, hm]; congr 2; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := Fz) (F' := Fz')
    (x₀ := z₀) (bound := bound) hball (Eventually.of_forall hmeas) hint₀
    ((hgc.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u z hz => ?_) ((hexpint (m / 4) (by positivity)).const_mul _)
    (Eventually.of_forall fun u z _ => ?_)
  · exact h.2.differentiableAt.differentiableWithinAt
  · -- the bound on the derivative
    have hzim : |z.im| ≤ |z₀.im| + m / 2 := by
      have := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at this
      have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at h1
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    simp only [hFz', hg, hbound]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have he : ‖Complex.exp (I * z * u)‖ ≤ Real.exp ((|z₀.im| + m / 2) * |u|) :=
      (norm_cexp_I_mul_le_exp_abs z u).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzim (abs_nonneg u)))
    have hu : |u| ≤ (4 / m) * Real.exp (m / 4 * |u|) := by
      have h1 := Real.add_one_le_exp (m / 4 * |u|)
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
      nlinarith [abs_nonneg u]
    have hFu := (hb u).1
    calc |F u| * (|u| * ‖Complex.exp (I * z * u)‖)
        ≤ (C * Real.exp (-((1 / 2 + δ) * |u|))) *
            ((4 / m) * Real.exp (m / 4 * |u|) * Real.exp ((|z₀.im| + m / 2) * |u|)) := by
          gcongr
      _ = (4 * C / m) * Real.exp (-((1 / 2 + δ) * |u|) + m / 4 * |u| +
            (|z₀.im| + m / 2) * |u|) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ = (4 * C / m) * Real.exp (-(m / 4 * |u|)) := by
          congr 2; rw [hm]; ring
  · -- the derivative
    have h1 : HasDerivAt (fun z : ℂ => I * z * (u : ℂ)) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    have h2 := (h1.cexp).const_mul (g u)
    simp only [hFz, hFz']
    exact h2.congr_deriv (by ring)

/-- **The real zeros of a nonvanishing decay-class transform form a countable set.** -/
theorem countable_setOf_paperFT_eq_zero {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hne : ∃ r : ℝ, paperFT (fun u => (F u : ℂ)) r ≠ 0) :
    {r : ℝ | paperFT (fun u => (F u : ℂ)) r = 0}.Countable := by
  obtain ⟨ε, hε, ha⟩ := exists_analyticOnNhd_paperFT hF
  set f := paperFT (fun u => (F u : ℂ)) with hf
  set S : Set ℂ := {z : ℂ | |z.im| < ε} with hS
  have hSconv : Convex ℝ S := by
    have : S = Complex.im ⁻¹' Set.Ioo (-ε) ε := by
      ext z; simp [hS, abs_lt]
    rw [this]
    exact (convex_Ioo _ _).linear_preimage Complex.imLm
  have hreal : ∀ r : ℝ, (r : ℂ) ∈ S := fun r => by
    show |((r : ℂ)).im| < ε
    simp; linarith
  -- every real zero is isolated
  have hiso : ∀ r₀ : ℝ, f r₀ = 0 → ∀ᶠ r : ℝ in 𝓝[≠] r₀, f (r : ℂ) ≠ 0 := by
    intro r₀ _
    rcases (ha _ (hreal r₀)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨r₁, hr₁⟩ := hne
      exact hr₁ (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hSconv.isPreconnected
        (hreal r₀) h (hreal r₁))
    · have hc : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] r₀) (𝓝[≠] (r₀ : ℂ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun r hr => by
            simpa using hr)
      exact hc.eventually h
  set Z : Set ℝ := {r : ℝ | f r = 0} with hZ
  have hdisc : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    have h := hiso x hx
    rw [Filter.eventually_iff_exists_mem] at h
    obtain ⟨U, hU, hUne⟩ := h
    rw [← Filter.empty_mem_iff_bot]
    refine Filter.mem_of_superset (Filter.inter_mem_inf hU (Filter.mem_principal_self Z)) ?_
    rintro y ⟨hyU, hyZ⟩
    exact hUne y hyU hyZ
  have : Countable Z := (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
  exact Set.countable_coe_iff.mp this

/-- **A NULL test confines every Weil-positive spectrum to a countable set.** -/
theorem exists_countable_carrier_of_null {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) (hnull : archPoleEnergy F = 0)
    (hne : ∃ r : ℝ, paperFT (fun u => (F u : ℂ)) r ≠ 0) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ S : Set ℝ, S.Countable ∧ boundaryMeasure hW Sᶜ = 0 := by
  refine ⟨{r : ℝ | paperFT (fun u => (F u : ℂ)) r = 0}, countable_setOf_paperFT_eq_zero hF hne,
    ?_⟩
  have h := boundaryMeasure_paperFT_ne_zero_of_null hF hblind hnull hW
  refine measure_mono_null (fun r hr => ?_) h
  simpa using hr

end RHTower.WeilSpectral
