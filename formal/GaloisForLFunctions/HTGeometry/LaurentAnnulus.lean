import GaloisForLFunctions.HTGeometry.AnnulusCauchy
import GaloisForLFunctions.HTGeometry.PolydiscApproximation

/-!
# The Laurent decomposition on an annulus

The Cauchy formula on an annulus splits a function holomorphic there into an outer part, the Cauchy
transform of the outer circle, and an inner part, minus the Cauchy transform of the inner circle.
The outer part is analytic on the whole disc bounded by the outer circle — this is mathlib's power
series for a Cauchy transform — so it is approximated uniformly on every smaller closed disc by
polynomials, which are entire.

* `GaloisForLFunctions.HTGeometry.laurentOuter`, `GaloisForLFunctions.HTGeometry.laurentInner` : the
  two parts.
* `GaloisForLFunctions.HTGeometry.laurent_decomposition` : their sum is the function.
* `GaloisForLFunctions.HTGeometry.laurentOuter_hasFPowerSeriesOnBall` : the outer part is analytic
  on the disc.
* `GaloisForLFunctions.HTGeometry.exists_entire_approx_laurentOuter` : uniform approximation of the
  outer part by entire functions.
-/

open Complex Metric Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section Laurent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The outer part of the Laurent decomposition: the Cauchy transform of the outer circle. -/
noncomputable def laurentOuter (f : ℂ → E) (c : ℂ) (R : ℝ) (z : ℂ) : E :=
  ((2 * Real.pi * Complex.I : ℂ))⁻¹ • ∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ

/-- The inner part of the Laurent decomposition: minus the Cauchy transform of the inner circle. -/
noncomputable def laurentInner (f : ℂ → E) (c : ℂ) (r : ℝ) (z : ℂ) : E :=
  -(((2 * Real.pi * Complex.I : ℂ))⁻¹ • ∮ ζ in C(c, r), (ζ - z)⁻¹ • f ζ)

theorem annulusTwoPiI_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- **The Laurent decomposition.**  On the annulus a holomorphic function is the sum of the Cauchy
transforms of the two boundary circles. -/
theorem laurent_decomposition {f : ℂ → E} {c : ℂ} {a b r R : ℝ}
    (ha : 0 < a) (har : a < r) (hrR : r < R) (hRb : R < b)
    (hf : DifferentiableOn ℂ f (annulusAt c a b))
    {z : ℂ} (hz1 : r < ‖z - c‖) (hz2 : ‖z - c‖ < R) :
    f z = laurentOuter f c R z + laurentInner f c r z := by
  have h := annulusCauchyFormula ha har hrR hRb hf hz1 hz2
  have hsc := congrArg (fun x : E => ((2 * Real.pi * Complex.I : ℂ))⁻¹ • x) h
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ annulusTwoPiI_ne_zero, one_smul] at hsc
  rw [laurentOuter, laurentInner, ← hsc]
  abel

/-- **The outer part is analytic on the disc bounded by the outer circle.** -/
theorem laurentOuter_hasFPowerSeriesOnBall {f : ℂ → E} {c : ℂ} {R : NNReal}
    (hR : 0 < R) (hint : CircleIntegrable f c (R : ℝ)) :
    HasFPowerSeriesOnBall (laurentOuter f c (R : ℝ)) (cauchyPowerSeries f c (R : ℝ)) c (R : ENNReal) :=
  hasFPowerSeriesOn_cauchy_integral hint hR

/-- **Uniform approximation of the outer part by entire functions.**  The partial sums of its power
series are polynomials, and they converge uniformly on every smaller closed disc. -/
theorem exists_entire_approx_laurentOuter {f : ℂ → E} {c : ℂ} {R : NNReal} {ρ ε : ℝ}
    (hR : 0 < R) (hint : CircleIntegrable f c (R : ℝ)) (hρ : 0 ≤ ρ) (hρR : ρ < (R : ℝ))
    (hε : 0 < ε) :
    ∃ P : ℂ → E, Differentiable ℂ P ∧
      ∀ z ∈ Metric.ball c ρ, ‖laurentOuter f c (R : ℝ) z - P z‖ < ε := by
  have hball := laurentOuter_hasFPowerSeriesOnBall hR hint
  have hcoe : ((ρ.toNNReal : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ hρ
  have hlt : ((ρ.toNNReal : NNReal) : ENNReal) < (R : ENNReal) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hcoe]
    exact hρR
  have huniform := hball.tendstoUniformlyOn hlt
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 huniform) ε hε)
  refine ⟨fun z => (cauchyPowerSeries f c (R : ℝ)).partialSum N (z - c),
    (differentiable_partialSum _ N).comp (differentiable_id.sub_const c), fun z hz => ?_⟩
  have hzball : z - c ∈ Metric.ball (0 : ℂ) ((ρ.toNNReal : NNReal) : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right, hcoe]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hz
  have hkey := hN N le_rfl (z - c) hzball
  rw [dist_eq_norm] at hkey
  have hzc : c + (z - c) = z := by ring
  rw [hzc] at hkey
  exact hkey

end Laurent

section InnerSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Laurent coefficients of the inner part. -/
noncomputable def annulusLaurentCoeff (f : ℂ → E) (c : ℂ) (r : ℝ) (k : ℕ) : E :=
  ((2 * Real.pi * Complex.I : ℂ))⁻¹ • ∮ ζ in C(c, r), ((ζ - c) ^ k) • f ζ

/-- **The Laurent coefficients are bounded by the maximum on the circle.** -/
theorem norm_annulusLaurentCoeff_le {f : ℂ → E} {c : ℂ} {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hf : ∀ ζ ∈ Metric.sphere c r, ‖f ζ‖ ≤ M) (k : ℕ) :
    ‖annulusLaurentCoeff f c r k‖ ≤ r ^ k * M * r := by
  have hbound : ∀ ζ ∈ Metric.sphere c r, ‖((ζ - c) ^ k) • f ζ‖ ≤ r ^ k * M := by
    intro ζ hζ
    rw [norm_smul, norm_pow]
    have hnorm : ‖ζ - c‖ = r := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp hζ
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hf ζ hζ) (by positivity)
  have h := circleIntegral.norm_integral_le_of_norm_le_const hr hbound
  rw [annulusLaurentCoeff, norm_smul, norm_inv]
  have hnorm2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm2pi]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ hpi]
  calc ‖∮ ζ in C(c, r), ((ζ - c) ^ k) • f ζ‖ ≤ 2 * Real.pi * r * (r ^ k * M) := h
    _ = r ^ k * M * r * (2 * Real.pi) := by ring

/-- **The inner part is the sum of its Laurent series** outside the circle. -/
theorem hasSum_laurentInner {f : ℂ → E} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hfc : ContinuousOn f (Metric.sphere c r)) (hfb : ∀ ζ ∈ Metric.sphere c r, ‖f ζ‖ ≤ M)
    {z : ℂ} (hz : r < ‖z - c‖) :
    HasSum (fun k => ((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k) (laurentInner f c r z) := by
  have hzc : z - c ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hz
    linarith
  set cc : Fin 1 → ℂ := fun _ => c with hcc
  set rr : Fin 1 → ℝ := fun _ => r with hrr
  have hmap : ∀ θ : Fin 1 → ℝ, torusMap cc rr θ 0 = circleMap c r (θ 0) := fun θ => rfl
  have hsphere : ∀ θ : Fin 1 → ℝ, torusMap cc rr θ 0 ∈ Metric.sphere c r := by
    intro θ
    rw [hmap θ]
    exact circleMap_mem_sphere c hr.le (θ 0)
  set F : ℕ → (Fin 1 → ℂ) → E := fun k x =>
    (((x 0 - c) ^ k * ((z - c) ^ (k + 1))⁻¹ : ℂ)) • f (x 0) with hF
  set G : (Fin 1 → ℂ) → E := fun x => -((x 0 - z)⁻¹ • f (x 0)) with hG
  have hFθ : ∀ (k : ℕ) (θ : Fin 1 → ℝ), F k (torusMap cc rr θ)
      = (((circleMap c r (θ 0) - c) ^ k * ((z - c) ^ (k + 1))⁻¹ : ℂ)) • f (circleMap c r (θ 0)) :=
    fun k θ => rfl
  have hcircle : Continuous fun θ : Fin 1 → ℝ => circleMap c r (θ 0) :=
    (continuous_circleMap c r).comp (continuous_apply 0)
  have hcontF : ∀ k, Continuous fun θ : Fin 1 → ℝ => F k (torusMap cc rr θ) := by
    intro k
    simp only [hFθ k]
    refine Continuous.smul ?_ (hfc.comp_continuous hcircle fun θ => hsphere θ)
    exact (((hcircle.sub continuous_const).pow k).mul continuous_const)
  have hptsum : ∀ θ : Fin 1 → ℝ,
      HasSum (fun k => F k (torusMap cc rr θ)) (G (torusMap cc rr θ)) := by
    intro θ
    set ζ : ℂ := torusMap cc rr θ 0 with hζ
    have hζn : ‖ζ - c‖ = r := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp (hsphere θ)
    have hq : ‖(ζ - c) / (z - c)‖ < 1 := by
      rw [norm_div, hζn, div_lt_one (lt_trans hr hz)]
      exact hz
    have hgeo := hasSum_geometric_of_norm_lt_one hq
    have hscaled := (hgeo.smul_const (f ζ)).const_smul ((z - c)⁻¹)
    have hterms : ∀ k : ℕ,
        ((z - c)⁻¹ : ℂ) • (((ζ - c) / (z - c)) ^ k • f ζ)
          = (((ζ - c) ^ k * ((z - c) ^ (k + 1))⁻¹ : ℂ)) • f ζ := by
      intro k
      rw [smul_smul]
      congr 1
      rw [div_pow, pow_succ]
      field_simp
    have hzζ : z - ζ ≠ 0 := by
      intro hcon
      rw [sub_eq_zero] at hcon
      rw [← hcon] at hζn
      exact absurd hζn (ne_of_gt hz)
    have hden : (1 : ℂ) - (ζ - c) / (z - c) = (z - ζ) / (z - c) := by
      rw [eq_div_iff hzc, sub_mul, one_mul, div_mul_cancel₀ _ hzc]
      ring
    have hscal : ((z - c)⁻¹ : ℂ) * (1 - (ζ - c) / (z - c))⁻¹ = -(ζ - z)⁻¹ := by
      rw [hden]
      rw [show ζ - z = -(z - ζ) by ring]
      field_simp
    have hlimit : ((z - c)⁻¹ : ℂ) • ((1 - (ζ - c) / (z - c))⁻¹ • f ζ) = -((ζ - z)⁻¹ • f ζ) := by
      rw [smul_smul, hscal, neg_smul]
    show HasSum (fun k => F k (torusMap cc rr θ)) (-((ζ - z)⁻¹ • f ζ))
    rw [← hlimit]
    exact HasSum.congr_fun hscaled fun k => (hterms k).symm
  set b : ℕ → ℝ := fun k => M * (r ^ k / ‖z - c‖ ^ (k + 1)) with hbdef
  have hzn : (0 : ℝ) < ‖z - c‖ := lt_trans hr hz
  have hb : ∀ (k : ℕ) (θ : Fin 1 → ℝ), ‖F k (torusMap cc rr θ)‖ ≤ b k := by
    intro k θ
    have hζn : ‖circleMap c r (θ 0) - c‖ = r := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp (circleMap_mem_sphere c hr.le (θ 0))
    rw [hFθ k θ, norm_smul, norm_mul, norm_pow, norm_inv, norm_pow, hζn, hbdef]
    have hfb' := hfb _ (circleMap_mem_sphere c hr.le (θ 0))
    have hpos : (0 : ℝ) < ‖z - c‖ ^ (k + 1) := pow_pos hzn (k + 1)
    calc r ^ k * (‖z - c‖ ^ (k + 1))⁻¹ * ‖f (circleMap c r (θ 0))‖
        ≤ r ^ k * (‖z - c‖ ^ (k + 1))⁻¹ * M := by
          refine mul_le_mul_of_nonneg_left hfb' ?_
          positivity
      _ = M * (r ^ k / ‖z - c‖ ^ (k + 1)) := by
          field_simp
  have hbsum : Summable b := by
    have hgeo : Summable fun k : ℕ => (r / ‖z - c‖) ^ k :=
      summable_geometric_of_lt_one (by positivity) ((div_lt_one hzn).2 hz)
    have heq : b = fun k => (M / ‖z - c‖) * (r / ‖z - c‖) ^ k := by
      funext k
      simp only [hbdef, div_pow, pow_succ]
      field_simp
    rw [heq]
    exact hgeo.mul_left _
  have hmain := hasSum_torusIntegral hcontF hptsum hb hbsum
  -- convert the torus integrals back to circle integrals
  have hFint : ∀ k : ℕ, (∯ ζ in T(cc, rr), F k ζ)
      = (2 * Real.pi * Complex.I : ℂ) • (((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k) := by
    intro k
    rw [torusIntegral_dim1]
    show (∮ ζ in C(c, r), (((ζ - c) ^ k * ((z - c) ^ (k + 1))⁻¹ : ℂ)) • f ζ) = _
    have hsplit : ∀ ζ : ℂ, (((ζ - c) ^ k * ((z - c) ^ (k + 1))⁻¹ : ℂ)) • f ζ
        = (((z - c) ^ (k + 1))⁻¹ : ℂ) • (((ζ - c) ^ k : ℂ) • f ζ) := by
      intro ζ
      rw [smul_smul]
      congr 1
      ring
    simp only [hsplit]
    rw [circleIntegral.integral_smul]
    refine Eq.symm ?_
    rw [annulusLaurentCoeff, smul_comm ((z - c) ^ (k + 1))⁻¹ ((2 * Real.pi * Complex.I : ℂ)⁻¹),
      smul_smul, mul_inv_cancel₀ annulusTwoPiI_ne_zero, one_smul]
  have hGint : (∯ ζ in T(cc, rr), G ζ)
      = (2 * Real.pi * Complex.I : ℂ) • laurentInner f c r z := by
    rw [torusIntegral_dim1]
    show (∮ ζ in C(c, r), -((ζ - z)⁻¹ • f ζ)) = _
    have hneg : ∀ ζ : ℂ, -((ζ - z)⁻¹ • f ζ) = ((-1 : ℂ)) • ((ζ - z)⁻¹ • f ζ) := fun ζ => by
      rw [neg_smul, one_smul]
    simp only [hneg]
    rw [circleIntegral.integral_smul]
    refine Eq.symm ?_
    rw [laurentInner, smul_neg, smul_smul, mul_inv_cancel₀ annulusTwoPiI_ne_zero, one_smul,
      ← neg_one_smul ℂ]
  rw [hGint] at hmain
  simp only [hFint] at hmain
  have hcancel := hmain.const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  simpa only [smul_smul, inv_mul_cancel_left₀ annulusTwoPiI_ne_zero,
    inv_mul_cancel₀ annulusTwoPiI_ne_zero, one_smul] using hcancel

end InnerSeries

section InnerApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The partial sums of the inner Laurent series: polynomials in `(z − c)⁻¹`. -/
noncomputable def laurentInnerPartial (f : ℂ → E) (c : ℂ) (r : ℝ) (N : ℕ) (z : ℂ) : E :=
  ∑ k ∈ Finset.range N, ((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k

/-- **The partial sums of the inner Laurent series are holomorphic away from the centre.** -/
theorem differentiableOn_laurentInnerPartial (f : ℂ → E) (c : ℂ) (r : ℝ) (N : ℕ) :
    DifferentiableOn ℂ (laurentInnerPartial f c r N) {z : ℂ | z ≠ c} := by
  have hterm : ∀ k : ℕ, DifferentiableOn ℂ
      (fun z : ℂ => ((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k) {z : ℂ | z ≠ c} := by
    intro k z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
    exact (((differentiableAt_id.sub_const c).pow _).inv (pow_ne_zero _ hzc)).smul_const _
  have heq : laurentInnerPartial f c r N
      = ∑ k ∈ Finset.range N, fun z : ℂ => ((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k := by
    funext z
    simp [laurentInnerPartial, Finset.sum_apply]
  rw [heq]
  exact DifferentiableOn.sum fun k _ => hterm k

/-- **Uniform approximation of the inner part by a partial sum**, outside a circle of radius larger
than the one the coefficients are taken on. -/
theorem exists_approx_laurentInner {f : ℂ → E} {c : ℂ} {r M ρ ε : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hfc : ContinuousOn f (Metric.sphere c r)) (hfb : ∀ ζ ∈ Metric.sphere c r, ‖f ζ‖ ≤ M)
    (hrρ : r < ρ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : ℂ, ρ ≤ ‖z - c‖ →
      ‖laurentInner f c r z - laurentInnerPartial f c r N z‖ ≤ ε := by
  classical
  have hρ : 0 < ρ := lt_trans hr hrρ
  set a : ℕ → ℝ := fun k => (M * r / ρ) * (r / ρ) ^ k with hadef
  have hasum : Summable a := by
    refine Summable.mul_left _ ?_
    exact summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hrρ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' i, a (i + N) ≤ ε := by
    obtain ⟨N, hNall⟩ := (Metric.tendsto_atTop.1 (tendsto_sum_nat_add a)) ε hε
    refine ⟨N, ?_⟩
    have h := hNall N le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
  refine ⟨N, fun z hz => ?_⟩
  have hzn : r < ‖z - c‖ := lt_of_lt_of_le hrρ hz
  have hsum := hasSum_laurentInner hr hM hfc hfb hzn
  set tm : ℕ → E := fun k => ((z - c) ^ (k + 1))⁻¹ • annulusLaurentCoeff f c r k with htm
  have hzcn : (0 : ℝ) < ‖z - c‖ := lt_trans hr hzn
  have hbound : ∀ k, ‖tm k‖ ≤ a k := by
    intro k
    rw [htm, norm_smul, norm_inv, norm_pow]
    have h1 : ‖annulusLaurentCoeff f c r k‖ ≤ r ^ k * M * r := norm_annulusLaurentCoeff_le hr.le hM hfb k
    have h2 : (0 : ℝ) < ‖z - c‖ ^ (k + 1) := pow_pos hzcn (k + 1)
    have h3 : ρ ^ (k + 1) ≤ ‖z - c‖ ^ (k + 1) := pow_le_pow_left₀ hρ.le hz (k + 1)
    have h4 : (‖z - c‖ ^ (k + 1))⁻¹ ≤ (ρ ^ (k + 1))⁻¹ :=
      inv_anti₀ (pow_pos hρ (k + 1)) h3
    calc (‖z - c‖ ^ (k + 1))⁻¹ * ‖annulusLaurentCoeff f c r k‖
        ≤ (ρ ^ (k + 1))⁻¹ * (r ^ k * M * r) := by
          refine mul_le_mul h4 h1 (norm_nonneg _) (by positivity)
      _ = a k := by
          simp only [hadef, div_pow, pow_succ]
          field_simp
  have hnormsum : Summable fun k => ‖tm k‖ :=
    hasum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have hpart : laurentInnerPartial f c r N z = ∑ i ∈ Finset.range N, tm i := rfl
  have hdiff : laurentInner f c r z - laurentInnerPartial f c r N z = ∑' i, tm (i + N) := by
    rw [hpart, ← hsum.tsum_eq, ← hsplit]
    abel
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm (hnormsum.comp_injective (add_left_injective N))) ?_
  refine le_trans (Summable.tsum_le_tsum (fun i => hbound (i + N))
    (hnormsum.comp_injective (add_left_injective N))
    (hasum.comp_injective (add_left_injective N))) hN

end InnerApprox

section RungeAnnulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A circle inside an annulus. -/
theorem sphere_subset_annulusAt {c : ℂ} {a b t : ℝ} (hat : a < t) (htb : t < b) :
    Metric.sphere c t ⊆ annulusAt c a b := by
  intro ζ hζ
  have h : ‖ζ - c‖ = t := by
    rw [← Complex.dist_eq]
    exact Metric.mem_sphere.mp hζ
  exact ⟨by rw [h]; exact hat, by rw [h]; exact htb⟩

/-- A continuous function is bounded on a circle. -/
theorem exists_bound_on_sphere {f : ℂ → E} {c : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Metric.sphere c t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ Metric.sphere c t, ‖f ζ‖ ≤ M := by
  rcases Set.eq_empty_or_nonempty (Metric.sphere c t) with hemp | hne
  · exact ⟨0, le_rfl, fun ζ hζ => absurd hζ (by rw [hemp]; exact fun h => h)⟩
  · obtain ⟨p, hp, hmax⟩ := (isCompact_sphere c t).exists_isMaxOn hne
      (continuous_norm.comp_continuousOn hf)
    exact ⟨‖f p‖, norm_nonneg _, fun ζ hζ => hmax hζ⟩

/-- **The Runge step on an annulus.**  A function holomorphic on the annulus of radii `(a, b)` is
approximated uniformly on every closed sub-annulus, to any accuracy, by a function holomorphic on
the punctured plane: the outer part of its Laurent decomposition by a polynomial, the inner part by
a polynomial in `(z − c)⁻¹`. -/
theorem exists_punctured_approx_annulus {f : ℂ → E} {c : ℂ} {a b ρ σ ε : ℝ}
    (ha : 0 < a) (haρ : a < ρ) (hρσ : ρ ≤ σ) (hσb : σ < b)
    (hf : DifferentiableOn ℂ f (annulusAt c a b)) (hε : 0 < ε) :
    ∃ P : ℂ → E, DifferentiableOn ℂ P {z : ℂ | z ≠ c} ∧
      ∀ z : ℂ, ρ ≤ ‖z - c‖ → ‖z - c‖ ≤ σ → ‖f z - P z‖ ≤ ε := by
  classical
  set r : ℝ := (a + ρ) / 2 with hrdef
  set R : ℝ := (σ + b) / 2 with hRdef
  set ρ' : ℝ := (σ + R) / 2 with hρ'def
  have har : a < r := by rw [hrdef]; linarith
  have hrρ : r < ρ := by rw [hrdef]; linarith
  have hrpos : 0 < r := lt_trans ha har
  have hσR : σ < R := by rw [hRdef]; linarith
  have hRb : R < b := by rw [hRdef]; linarith
  have hσρ' : σ < ρ' := by rw [hρ'def]; linarith
  have hρ'R : ρ' < R := by rw [hρ'def]; linarith
  have hrR : r < R := by linarith
  have hRpos : 0 < R := by linarith
  have hρ'nn : 0 ≤ ρ' := by linarith [lt_trans (lt_trans ha haρ) (lt_of_le_of_lt hρσ hσρ')]
  -- data on the two circles
  have hsphR : ContinuousOn f (Metric.sphere c R) :=
    hf.continuousOn.mono (sphere_subset_annulusAt (by linarith) hRb)
  have hsphr : ContinuousOn f (Metric.sphere c r) :=
    hf.continuousOn.mono (sphere_subset_annulusAt har (by linarith))
  obtain ⟨M, hMnn, hM⟩ := exists_bound_on_sphere hrpos.le hsphr
  have hRcoe : ((R.toNNReal : NNReal) : ℝ) = R := Real.coe_toNNReal R hRpos.le
  have hRnn : 0 < R.toNNReal := by
    rw [← NNReal.coe_pos, hRcoe]
    exact hRpos
  have hint : CircleIntegrable f c ((R.toNNReal : NNReal) : ℝ) := by
    rw [hRcoe]
    exact hsphR.circleIntegrable hRpos.le
  obtain ⟨P₁, hP₁diff, hP₁⟩ :=
    exists_entire_approx_laurentOuter (f := f) (c := c) (R := R.toNNReal) (ρ := ρ') (ε := ε / 2)
      hRnn hint hρ'nn (by rw [hRcoe]; exact hρ'R) (by linarith)
  obtain ⟨N, hN⟩ :=
    exists_approx_laurentInner (f := f) (c := c) (r := r) (M := M) (ρ := ρ) (ε := ε / 2)
      hrpos hMnn hsphr hM hrρ (by linarith)
  refine ⟨fun z => P₁ z + laurentInnerPartial f c r N z, ?_, ?_⟩
  · exact (hP₁diff.differentiableOn).add (differentiableOn_laurentInnerPartial f c r N)
  · intro z hz1 hz2
    have hzr : r < ‖z - c‖ := lt_of_lt_of_le hrρ hz1
    have hzR : ‖z - c‖ < R := lt_of_le_of_lt hz2 hσR
    have hdec := laurent_decomposition ha har hrR hRb hf hzr hzR
    have hzball : z ∈ Metric.ball c ρ' := by
      rw [Metric.mem_ball, Complex.dist_eq]
      linarith
    have h1 : ‖laurentOuter f c ((R.toNNReal : NNReal) : ℝ) z - P₁ z‖ < ε / 2 := hP₁ z hzball
    have h2 : ‖laurentInner f c r z - laurentInnerPartial f c r N z‖ ≤ ε / 2 := hN z hz1
    have hRR : ((R.toNNReal : NNReal) : ℝ) = R := hRcoe
    rw [hRR] at h1
    have hsplit : f z - (P₁ z + laurentInnerPartial f c r N z)
        = (laurentOuter f c R z - P₁ z) + (laurentInner f c r z - laurentInnerPartial f c r N z) := by
      rw [hdec]
      abel
    rw [hsplit]
    calc ‖(laurentOuter f c R z - P₁ z) + (laurentInner f c r z - laurentInnerPartial f c r N z)‖
        ≤ ‖laurentOuter f c R z - P₁ z‖ + ‖laurentInner f c r z - laurentInnerPartial f c r N z‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1.le h2
      _ = ε := by ring

end RungeAnnulus

end GaloisForLFunctions.HTGeometry
