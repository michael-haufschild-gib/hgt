import GaloisForLFunctions.RHTower.ModularArcAnnihilatingMeasure
import GaloisForLFunctions.HTGeometry.SymmetricCoshKernelPositiveDefinite

/-!
# A positive, self-dual, Whittaker-blind measure on the modular bottom arc

Parametrize the bottom arc `{u² + y² = 1, |u| ≤ ½}` of the standard fundamental domain of `SL₂(ℤ)` by
`u ∈ [−½, ½]`, `y = √(1 − u²)`.  For a finite measure `ν` on the arc, its log-scale Poisson profile is

`B_ν(v) = ∫ (y/2)^{1/2} (cosh v − u)^{−1/2} dν(u)`  (`arcPoissonProfile`),

which is `e^{v/2} h(e^v)` for the superposition `h(x) = ∫ (y/|x − z|²)^{1/2} dν` of the `s = ½` Poisson
vectors attached to the points `z = u + iy` of the arc.

**Theorem** (`exists_arcWitness`).  There is a nonzero finite measure `ν` on the arc such that:
1. `ν` is invariant under `u ↦ −u`.  On the arc this is `z ↦ −z̄`, and also the inversion
   `S: z ↦ −1/z`, so `h` is even and `S`-invariant.
2. Every decaying Whittaker function at the spectral parameter `s = ½` integrates to zero:
   `∫ √y K₀(2π(n+1)y) cos(2π(n+1)u) dν = ∫ √y K₀(2π(n+1)y) sin(2π(n+1)u) dν = 0` for every `n`.
3. `B_ν` is strictly positive definite: `∫ cos(τv) B_ν(v) dv > 0` for every real `τ`.

Proof.  Start from the annihilating probability measure of `exists_probabilityMeasure_arc_annihilating`,
reweight by `y^{−1/2}` (this turns `K₀(c y)` into `√y K₀(c y)`), and symmetrize under `u ↦ −u`; the cosine
modes are even and the sine modes odd.  By symmetry `B_ν(v) = ½ ∫ (y/2)^{1/2} 𝒦_u(v) dν` with
`𝒦_u(v) = (cosh v + u)^{−1/2} + (cosh v − u)^{−1/2}`.  Fubini and
`integral_cos_mul_symCoshKernel_pos` give 3.

Via the Fourier transform `∫ (y/|x − z|²)^{1/2} e^{−2πiξx} dx = 2√y K₀(2π|ξ|y) e^{−2πiξu}`, property 2
says that `h` has no nonzero Fourier mode at the nonzero integers, so its periodization is constant.
Property 3 is positive definiteness of `h` in the logarithmic variable.  `h` decays only like
`(∫√y dν)/|x|`.  In the multiplier language of the (N1) problem this witness is blind at every `log n`
and positive on the critical line, and its only defect is the ζ-pole at `s = 1`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The reflection `u ↦ −u` of the arc parameter. -/
def arcNeg (u : ArcParam) : ArcParam :=
  ⟨-u.1, ⟨by linarith [u.2.2], by linarith [u.2.1]⟩⟩

theorem continuous_arcNeg : Continuous arcNeg :=
  continuous_subtype_val.neg.subtype_mk _

theorem measurable_arcNeg : Measurable arcNeg := continuous_arcNeg.measurable

theorem arcNeg_arcNeg (u : ArcParam) : arcNeg (arcNeg u) = u := by
  ext; simp [arcNeg]

theorem modularArcHeight_neg (u : ℝ) : modularArcHeight (-u) = modularArcHeight u := by
  simp [modularArcHeight]

/-- The weight `y^{−1/2}` on the arc. -/
def arcWeight (u : ArcParam) : ℝ≥0 :=
  ⟨modularArcHeight u ^ (-1 / 2 : ℝ), Real.rpow_nonneg (Real.sqrt_nonneg _) _⟩

theorem coe_arcWeight (u : ArcParam) :
    (arcWeight u : ℝ) = modularArcHeight u ^ (-1 / 2 : ℝ) := rfl

theorem continuous_arcWeight : Continuous arcWeight := by
  refine Continuous.subtype_mk ?_ _
  have hpos : ∀ u : ArcParam, modularArcHeight u ≠ 0 := fun u => (modularArcHeight_pos u.2).ne'
  exact (by unfold modularArcHeight; fun_prop : Continuous fun u : ArcParam =>
    modularArcHeight u).rpow_const fun u => Or.inl (hpos u)

/-- The Whittaker cosine mode `√y K₀(c_n y) cos(c_n u)` on the arc. -/
def arcWhittakerCos (n : ℕ) (u : ArcParam) : ℝ :=
  Real.sqrt (modularArcHeight u) * arcCosMode n u

/-- The Whittaker sine mode `√y K₀(c_n y) sin(c_n u)` on the arc. -/
def arcWhittakerSin (n : ℕ) (u : ArcParam) : ℝ :=
  Real.sqrt (modularArcHeight u) * arcSinMode n u

/-- The log-scale Poisson profile `B_ν(v) = ∫ (y/2)^{1/2} (cosh v − u)^{−1/2} dν`. -/
def arcPoissonProfile (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  ∫ u, Real.sqrt (modularArcHeight u / 2) * (Real.cosh v - u) ^ (-1 / 2 : ℝ) ∂ν

theorem arcWeight_mul_sqrt (u : ArcParam) :
    (arcWeight u : ℝ) * Real.sqrt (modularArcHeight u) = 1 := by
  have hy := modularArcHeight_pos u.2
  rw [coe_arcWeight, Real.sqrt_eq_rpow, ← Real.rpow_add hy]
  norm_num

theorem continuous_arcWhittakerCos (n : ℕ) : Continuous (arcWhittakerCos n) := by
  unfold arcWhittakerCos modularArcHeight
  exact (by fun_prop : Continuous fun u : ArcParam => Real.sqrt (Real.sqrt (1 - (u : ℝ) ^ 2))).mul
    (arcCosMode n).continuous

theorem continuous_arcWhittakerSin (n : ℕ) : Continuous (arcWhittakerSin n) := by
  unfold arcWhittakerSin modularArcHeight
  exact (by fun_prop : Continuous fun u : ArcParam => Real.sqrt (Real.sqrt (1 - (u : ℝ) ^ 2))).mul
    (arcSinMode n).continuous

theorem arcWhittakerCos_neg (n : ℕ) (u : ArcParam) :
    arcWhittakerCos n (arcNeg u) = arcWhittakerCos n u := by
  simp [arcWhittakerCos, arcCosMode_apply, arcNeg, modularArcHeight_neg, Real.cos_neg]

theorem arcWhittakerSin_neg (n : ℕ) (u : ArcParam) :
    arcWhittakerSin n (arcNeg u) = -arcWhittakerSin n u := by
  simp [arcWhittakerSin, arcSinMode_apply, arcNeg, modularArcHeight_neg, Real.sin_neg]

theorem one_le_arcWeight (u : ArcParam) : (1 : ℝ) ≤ arcWeight u := by
  have hy := modularArcHeight_pos u.2
  have hy1 : modularArcHeight u ≤ 1 := by
    unfold modularArcHeight
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
  rw [coe_arcWeight]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num)

theorem arcWeight_le_two (u : ArcParam) : (arcWeight u : ℝ) ≤ 2 := by
  have hy := modularArcHeight_pos u.2
  have hy2 : (1 / 4 : ℝ) ≤ modularArcHeight u := by
    unfold modularArcHeight
    rw [Real.le_sqrt (by norm_num) (by nlinarith [u.2.1, u.2.2])]
    nlinarith [u.2.1, u.2.2]
  rw [coe_arcWeight]
  calc modularArcHeight u ^ (-1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hy2 (by norm_num)
    _ = 2 := by
        rw [show (1 / 4 : ℝ) = 2 ^ (-2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num

/-- The pointwise kernel `(y/2)^{1/2} (cosh v − u)^{−1/2}`. -/
def arcPoissonKernel (u : ArcParam) (v : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u / 2) * (Real.cosh v - u) ^ (-1 / 2 : ℝ)

theorem arcPoissonKernel_add_neg (u : ArcParam) (v : ℝ) :
    arcPoissonKernel u v + arcPoissonKernel (arcNeg u) v =
      Real.sqrt (modularArcHeight u / 2) * symCoshKernel u v := by
  simp only [arcPoissonKernel, arcNeg, modularArcHeight_neg, symCoshKernel, sub_neg_eq_add]
  ring

theorem cosh_sub_arc_pos (u : ArcParam) (v : ℝ) : 0 < Real.cosh v - u := by
  have := Real.one_le_cosh v; linarith [u.2.2]

theorem arcPoissonKernel_le (u : ArcParam) (v : ℝ) :
    |arcPoissonKernel u v| ≤ 2 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have hc := Real.cosh_pos v
  have h1 := Real.one_le_cosh v
  have hp := cosh_sub_arc_pos u v
  have hsq : Real.sqrt (modularArcHeight u / 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have : modularArcHeight u ≤ 1 := by
      unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
    linarith
  have hhalf : Real.cosh v / 2 ≤ Real.cosh v - u := by linarith [u.2.2]
  unfold arcPoissonKernel
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hp.le _))]
  calc Real.sqrt (modularArcHeight u / 2) * (Real.cosh v - u) ^ (-1 / 2 : ℝ)
      ≤ 1 * (Real.cosh v / 2) ^ (-1 / 2 : ℝ) :=
        mul_le_mul hsq (Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by norm_num))
          (Real.rpow_nonneg hp.le _) zero_le_one
    _ = Real.sqrt 2 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
        rw [one_mul, Real.div_rpow hc.le (by norm_num), div_eq_mul_inv, mul_comm,
          ← Real.rpow_neg (by norm_num), show -(-1 / 2 : ℝ) = 1 / 2 by norm_num,
          ← Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
    _ ≤ 2 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
        gcongr
        rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem continuous_arcPoissonKernel :
    Continuous fun p : ℝ × ArcParam => arcPoissonKernel p.2 p.1 := by
  unfold arcPoissonKernel modularArcHeight
  refine Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow_const (by fun_prop) fun p => Or.inl (cosh_sub_arc_pos p.2 p.1).ne'

theorem integrable_of_continuous_arc {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ}
    (hg : Continuous g) : Integrable g ν :=
  (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).integrable ν

/-- **A positive, self-dual, Whittaker-blind measure on the modular arc.** -/
theorem exists_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ n : ℕ, ∫ u, arcWhittakerCos n u ∂ν = 0 ∧ ∫ u, arcWhittakerSin n u ∂ν = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_arc_annihilating
  set μ₀ : Measure ArcParam := (μ : Measure ArcParam).withDensity fun u => (arcWeight u : ℝ≥0∞)
    with hμ₀
  have hwm : Measurable arcWeight := continuous_arcWeight.measurable
  have hfin0 : IsFiniteMeasure μ₀ := by
    refine isFiniteMeasure_withDensity ?_
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (2 : ℝ≥0∞) ∂(μ : Measure ArcParam)) ?_ ?_
    · simp [lintegral_const]
    · refine lintegral_mono fun u => ?_
      have h : arcWeight u ≤ 2 := by
        rw [← NNReal.coe_le_coe]; simpa using arcWeight_le_two u
      calc (arcWeight u : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h
        _ = 2 := by norm_num
  have hint0 : ∀ g : ArcParam → ℝ, ∫ u, g u ∂μ₀ =
      ∫ u, (arcWeight u : ℝ) * g u ∂(μ : Measure ArcParam) := fun g => by
    rw [hμ₀, integral_withDensity_eq_integral_smul hwm]
    rfl
  set ν : Measure ArcParam := μ₀ + μ₀.map arcNeg with hν
  have hfinmap : IsFiniteMeasure (μ₀.map arcNeg) := Measure.isFiniteMeasure_map μ₀ arcNeg
  have hfin : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hintν : ∀ g : ArcParam → ℝ, Continuous g →
      ∫ u, g u ∂ν = ∫ u, g u ∂μ₀ + ∫ u, g (arcNeg u) ∂μ₀ := by
    intro g hg
    rw [hν, integral_add_measure (integrable_of_continuous_arc hg)
      (integrable_of_continuous_arc hg), integral_map measurable_arcNeg.aemeasurable
      hg.aestronglyMeasurable]
  -- annihilation by `μ₀`
  have hcos0 : ∀ n, ∫ u, arcWhittakerCos n u ∂μ₀ = 0 := by
    intro n
    rw [hint0]
    have e : (fun u => (arcWeight u : ℝ) * arcWhittakerCos n u) = fun u => arcCosMode n u := by
      funext u; unfold arcWhittakerCos; rw [← mul_assoc, arcWeight_mul_sqrt, one_mul]
    rw [e]; exact (hμ n).1
  have hsin0 : ∀ n, ∫ u, arcWhittakerSin n u ∂μ₀ = 0 := by
    intro n
    rw [hint0]
    have e : (fun u => (arcWeight u : ℝ) * arcWhittakerSin n u) = fun u => arcSinMode n u := by
      funext u; unfold arcWhittakerSin; rw [← mul_assoc, arcWeight_mul_sqrt, one_mul]
    rw [e]; exact (hμ n).2
  -- `μ₀ ≠ 0`
  have hμ₀pos : 0 < μ₀ univ := by
    rw [hμ₀, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc (0 : ℝ≥0∞) < ∫⁻ _, (1 : ℝ≥0∞) ∂(μ : Measure ArcParam) := by simp
      _ ≤ ∫⁻ u, (arcWeight u : ℝ≥0∞) ∂(μ : Measure ArcParam) := lintegral_mono fun u => by
          have h : 1 ≤ arcWeight u := by
            rw [← NNReal.coe_le_coe]; simpa using one_le_arcWeight u
          calc (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) := by norm_num
            _ ≤ (arcWeight u : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h
  refine ⟨ν, hfin, ?_, ?_, fun n => ⟨?_, ?_⟩, fun τ => ?_⟩
  · intro h0
    have : ν univ = 0 := by rw [h0]; rfl
    rw [hν, Measure.add_apply] at this
    have := (add_eq_zero.mp this).1
    exact hμ₀pos.ne' this
  · rw [hν, Measure.map_add _ _ measurable_arcNeg, Measure.map_map measurable_arcNeg
      measurable_arcNeg]
    have hid : arcNeg ∘ arcNeg = id := funext arcNeg_arcNeg
    rw [hid, Measure.map_id, add_comm]
  · rw [hintν _ (continuous_arcWhittakerCos n)]
    simp only [arcWhittakerCos_neg]
    rw [hcos0, add_zero]
  · rw [hintν _ (continuous_arcWhittakerSin n)]
    simp only [arcWhittakerSin_neg]
    rw [integral_neg, hsin0, neg_zero, add_zero]
  · -- positive definiteness
    have hprof : ∀ v, arcPoissonProfile ν v =
        ∫ u, Real.sqrt (modularArcHeight u / 2) * symCoshKernel u v ∂μ₀ := by
      intro v
      change ∫ u, arcPoissonKernel u v ∂ν = _
      have c1 : Continuous fun u : ArcParam => arcPoissonKernel u v :=
        continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)
      have c2 : Continuous fun u : ArcParam => arcPoissonKernel (arcNeg u) v :=
        continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_arcNeg)
      rw [hintν (fun u => arcPoissonKernel u v) c1,
        ← integral_add (integrable_of_continuous_arc c1) (integrable_of_continuous_arc c2)]
      exact integral_congr_ae (Eventually.of_forall fun u => arcPoissonKernel_add_neg u v)
    set F : ℝ → ArcParam → ℝ := fun v u =>
      Real.cos (τ * v) * (Real.sqrt (modularArcHeight u / 2) * symCoshKernel u v) with hF
    have hFcont : Continuous fun p : ℝ × ArcParam => F p.1 p.2 := by
      have e : (fun p : ℝ × ArcParam => F p.1 p.2) = fun p => Real.cos (τ * p.1) *
          (arcPoissonKernel p.2 p.1 + arcPoissonKernel (arcNeg p.2) p.1) := by
        funext p; simp only [hF, arcPoissonKernel_add_neg]
      rw [e]
      have h1 : Continuous fun p : ℝ × ArcParam => arcPoissonKernel p.2 p.1 :=
        continuous_arcPoissonKernel
      have h2 : Continuous fun p : ℝ × ArcParam => arcPoissonKernel (arcNeg p.2) p.1 :=
        continuous_arcPoissonKernel.comp (continuous_fst.prodMk (continuous_arcNeg.comp continuous_snd))
      have h0 : Continuous fun p : ℝ × ArcParam => Real.cos (τ * p.1) :=
        Real.continuous_cos.comp (continuous_const.mul continuous_fst)
      exact h0.mul (h1.add h2)
    have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
    have hFint : Integrable (Function.uncurry F) (volume.prod μ₀) := by
      have hbound : Integrable (fun p : ℝ × ArcParam =>
          4 * Real.cosh p.1 ^ (-(1 / 2) : ℝ) * (1 : ℝ)) (volume.prod μ₀) :=
        (hI.const_mul 4).mul_prod (integrable_const (1 : ℝ))
      refine hbound.mono' hFcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, hF, mul_one]
      have hk := arcPoissonKernel_add_neg p.2 p.1
      rw [← hk, Real.norm_eq_abs, abs_mul]
      calc |Real.cos (τ * p.1)| * |arcPoissonKernel p.2 p.1 + arcPoissonKernel (arcNeg p.2) p.1|
          ≤ 1 * (2 * Real.cosh p.1 ^ (-(1 / 2) : ℝ) + 2 * Real.cosh p.1 ^ (-(1 / 2) : ℝ)) :=
            mul_le_mul (Real.abs_cos_le_one _) ((abs_add_le _ _).trans
              (add_le_add (arcPoissonKernel_le _ _) (arcPoissonKernel_le _ _)))
              (abs_nonneg _) zero_le_one
        _ = 4 * Real.cosh p.1 ^ (-(1 / 2) : ℝ) := by ring
    have hswap := integral_integral_swap hFint
    have hlhs : ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v = ∫ v, ∫ u, F v u ∂μ₀ := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hF]
      rw [hprof, ← integral_const_mul]
    rw [hlhs, hswap]
    have hinner : ∀ u : ArcParam, ∫ v, F v u =
        Real.sqrt (modularArcHeight u / 2) * ∫ v, Real.cos (τ * v) * symCoshKernel u v := by
      intro u
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hF]; ring
    have hpos : ∀ u : ArcParam, 0 < ∫ v, F v u := by
      intro u
      rw [hinner]
      have hc : |(u : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith [u.2.1, u.2.2]
      exact mul_pos (Real.sqrt_pos.mpr (by have := modularArcHeight_pos u.2; positivity))
        (integral_cos_mul_symCoshKernel_pos hc τ)
    have hintU : Integrable (fun u => ∫ v, F v u) μ₀ := hFint.integral_prod_right
    rw [integral_pos_iff_support_of_nonneg (fun u => (hpos u).le) hintU]
    have hsupp : Function.support (fun u => ∫ v, F v u) = univ := by
      ext u; simp [(hpos u).ne']
    rw [hsupp]
    exact hμ₀pos

end

end RHTower
