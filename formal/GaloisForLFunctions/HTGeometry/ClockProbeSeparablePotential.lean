import GaloisForLFunctions.HTGeometry.ClockRescaledProbeTransfer

/-!
# Separable potentials: probes that vary in two directions at once

Every determination result so far uses probes constant on the leaves of one foliation. Products
break that restriction. On a chart of constant signature the carré du champ of two factors with
transverse supports vanishes, so the d'Alembertian is additive on the product:

`□(f g) = g □f + f □g`  when `f` varies only along `i₀` and `g` not at all along `i₀`.

Hence a solution of `□f + V₁ f = 0` times a solution of `□g + V₂ g = 0` solves the equation with the
**sum** potential. Taking both factors from Picard–Lindelöf produces probes for
`V(x) = V₁(⟪n₁,x⟫) + V₂(⟪n₂,x⟫)` with arbitrary `C¹` profiles — a potential genuinely varying in two
independent directions.

The chart calculus of the corpus is stated at `ContDiff ℝ ∞`, which the Picard–Lindelöf probes do not
satisfy. The first section therefore rebuilds the flat d'Alembertian at the regularity those probes
actually have: pointwise differentiability of the first partial derivatives.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The flat d'Alembertian at low regularity -/

theorem coordPartial_congr {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (h : f =ᶠ[nhds x] g) (i : Fin d) : coordPartial i f x = coordPartial i g x := by
  rw [coordPartial, coordPartial, h.fderiv_eq]

theorem ofSignature_flux_eq (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (u : (Fin d → ℝ) → ℝ) (i : Fin d) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.flux u i
      = fun y => Real.sqrt |∏ k, eps k| * ((eps i)⁻¹ * coordPartial i u y) := by
  funext y
  simp only [SmoothMetricChart.flux, SmoothPseudoMetric.ofSignature_density,
    SmoothPseudoMetric.ofSignature_inverseMetric, Matrix.diagonal_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The flat d'Alembertian needs only differentiable first partials.** -/
theorem ofSignature_dalembert_of_differentiableAt (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hdiff : ∀ i, DifferentiableAt ℝ (coordPartial i u) x) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert u x
      = ∑ i, (eps i)⁻¹ * coordPartial i (coordPartial i u) x := by
  have hrhopos : (0 : ℝ) < Real.sqrt |∏ k, eps k| := by
    rw [← SmoothPseudoMetric.ofSignature_density eps heps x]
    exact (SmoothPseudoMetric.ofSignature eps heps).chart.density_pos x
  have hcp : ∀ i : Fin d,
      coordPartial i ((SmoothPseudoMetric.ofSignature eps heps).chart.flux u i) x
        = Real.sqrt |∏ k, eps k| * ((eps i)⁻¹ * coordPartial i (coordPartial i u) x) := by
    intro i
    rw [ofSignature_flux_eq eps heps u i,
      coordPartial_const_mul ((hdiff i).const_mul ((eps i)⁻¹)) _ i,
      coordPartial_const_mul (hdiff i) _ i]
  rw [SmoothMetricChart.dalembert, SmoothPseudoMetric.ofSignature_density,
    Finset.sum_congr rfl fun i _ => hcp i, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hrhopos), one_mul]

/-! ## Covector lifts at low regularity -/

/-- **Transverse constancy of a covector lift**, with no differentiability hypothesis. -/
theorem coordPartial_covectorLift_of_zero (n : Fin (d + 1) → ℝ) (w : ℝ → ℝ)
    {i : Fin (d + 1)} (hni : n i = 0) (x : Fin (d + 1) → ℝ) :
    coordPartial i (covectorLift n w) x = 0 := by
  have hphase : ∀ t : ℝ,
      covectorPhase n (x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
        = covectorPhase n x := by
    intro t
    have h1 : covectorCLM n (x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
        = covectorCLM n x + t • covectorCLM n (Pi.single i (1 : ℝ)) := by
      rw [map_add, map_smul]
    rw [← covectorCLM_apply, h1, covectorCLM_apply, covectorCLM_apply, covectorPhase_single,
      hni]
    simp
  by_cases hd : DifferentiableAt ℝ (covectorLift (d := d) n w) x
  · have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
        (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
          ((1 : ℝ) • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      simpa using h1.const_add x
    have hbase : (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0 = x := by
      simp
    have hL : HasFDerivAt (covectorLift (d := d) n w)
        (fderiv ℝ (covectorLift (d := d) n w) x)
        ((fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0) := by
      rw [hbase]
      exact hd.hasFDerivAt
    have hcomp := hL.comp_hasDerivAt 0 hline
    have hconst : (covectorLift (d := d) n w ∘
        fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
        = fun _ : ℝ => w (covectorPhase n x) := by
      funext t
      simp only [Function.comp_apply, covectorLift]
      rw [hphase t]
    rw [hconst] at hcomp
    have hzero : HasDerivAt (fun _ : ℝ => w (covectorPhase n x)) 0 (0 : ℝ) :=
      hasDerivAt_const _ _
    have hval := hcomp.unique hzero
    rw [coordPartial, hval]
  · rw [coordPartial, fderiv_zero_of_not_differentiableAt hd]
    rfl

theorem contDiff_covectorLift_phase (n : Fin (d + 1) → ℝ) :
    ContDiff ℝ ∞ (covectorPhase (d := d) n) := contDiff_covectorPhase n

/-- **The flat d'Alembertian of a covector lift**, at the regularity of a Picard–Lindelöf probe. -/
theorem dalembert_covectorLift_flat (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {n : Fin (d + 1) → ℝ} {w dw ddw : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hw1 : ∀ t ∈ S, HasDerivAt w (dw t) t) (hw2 : ∀ t ∈ S, HasDerivAt dw (ddw t) t)
    {x : Fin (d + 1) → ℝ} (hx : covectorPhase n x ∈ S) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (covectorLift n w) x
      = covectorNormConst eps n * ddw (covectorPhase n x) := by
  have hnhds : covectorPhase (d := d) n ⁻¹' S ∈ nhds x :=
    (hS.preimage (continuous_covectorPhase n)).mem_nhds hx
  have hev : ∀ i : Fin (d + 1), coordPartial i (covectorLift n w) =ᶠ[nhds x]
      fun y => n i * covectorLift n dw y := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    exact coordPartial_covectorLift (hw1 _ hy) i
  have hdwlift : DifferentiableAt ℝ (covectorLift (d := d) n dw) x := by
    have := (hw2 _ hx).comp_hasFDerivAt x
      (differentiableAt_of_contDiff_infty (contDiff_covectorLift_phase n) x).hasFDerivAt
    exact this.differentiableAt
  have hdiff : ∀ i : Fin (d + 1), DifferentiableAt ℝ (coordPartial i (covectorLift n w)) x := by
    intro i
    rw [(hev i).differentiableAt_iff]
    exact hdwlift.const_mul (n i)
  have hsecond : ∀ i : Fin (d + 1),
      coordPartial i (coordPartial i (covectorLift n w)) x
        = n i * (n i * ddw (covectorPhase n x)) := by
    intro i
    rw [coordPartial_congr (hev i) i, coordPartial_const_mul hdwlift (n i) i,
      coordPartial_covectorLift (hw2 _ hx) i]
  rw [ofSignature_dalembert_of_differentiableAt eps heps hdiff, covectorNormConst,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [hsecond i]; ring

/-! ## The transverse product rule -/

/-- **The d'Alembertian is additive on transversally supported factors.** -/
theorem dalembert_mul_transverse (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {f g : (Fin (d + 1) → ℝ) → ℝ} (i₀ : Fin (d + 1))
    (hfT : ∀ i, i ≠ i₀ → ∀ y, coordPartial i f y = 0)
    (hgT : ∀ y, coordPartial i₀ g y = 0)
    {x : Fin (d + 1) → ℝ} {U : Set (Fin (d + 1) → ℝ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hfU : ∀ y ∈ U, DifferentiableAt ℝ f y) (hgU : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hfd : ∀ i, DifferentiableAt ℝ (coordPartial i f) x)
    (hgd : ∀ i, DifferentiableAt ℝ (coordPartial i g) x) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (fun y => f y * g y) x
      = g x * (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert f x
        + f x * (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert g x := by
  have hnhds : U ∈ nhds x := hU.mem_nhds hxU
  have hev : ∀ i : Fin (d + 1), coordPartial i (fun y => f y * g y) =ᶠ[nhds x]
      fun y => f y * coordPartial i g y + g y * coordPartial i f y := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    exact coordPartial_mul (hfU y hy) (hgU y hy) i
  have hdiffprod : ∀ i : Fin (d + 1),
      DifferentiableAt ℝ (coordPartial i (fun y => f y * g y)) x := by
    intro i
    rw [(hev i).differentiableAt_iff]
    exact ((hfU x hxU).mul (hgd i)).add ((hgU x hxU).mul (hfd i))
  have hsecond : ∀ i : Fin (d + 1),
      coordPartial i (coordPartial i (fun y => f y * g y)) x
        = f x * coordPartial i (coordPartial i g) x
          + g x * coordPartial i (coordPartial i f) x := by
    intro i
    have hadd := coordPartial_add (f := fun y => f y * coordPartial i g y)
      (g := fun y => g y * coordPartial i f y) (x := x)
      ((hfU x hxU).mul (hgd i)) ((hgU x hxU).mul (hfd i)) i
    rw [coordPartial_congr (hev i) i, hadd,
      coordPartial_mul (hfU x hxU) (hgd i) i, coordPartial_mul (hgU x hxU) (hfd i) i]
    by_cases hi : i = i₀
    · rw [hi, hgT x]
      have hf0 : coordPartial i₀ (coordPartial i₀ g) x = 0 := by
        have hfun : coordPartial i₀ g = fun _ => (0 : ℝ) := funext hgT
        rw [hfun]
        exact coordPartial_const i₀ 0 x
      rw [hf0]
      ring
    · rw [hfT i hi x]
      have hg0 : coordPartial i (coordPartial i f) x = 0 := by
        have hfun : coordPartial i f = fun _ => (0 : ℝ) := funext (hfT i hi)
        rw [hfun]
        exact coordPartial_const i 0 x
      rw [hg0]
      ring
  rw [ofSignature_dalembert_of_differentiableAt eps heps hdiffprod,
    ofSignature_dalembert_of_differentiableAt eps heps hfd,
    ofSignature_dalembert_of_differentiableAt eps heps hgd,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [hsecond i]; ring

/-! ## Probes for a separable potential -/

/-- **Local probes for a sum potential in two transverse directions.** -/
theorem exists_separable_localProbe (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {n₁ n₂ : Fin (d + 1) → ℝ} (i₀ : Fin (d + 1))
    (hn₁ : ∀ i, i ≠ i₀ → n₁ i = 0) (hn₂ : n₂ i₀ = 0)
    (hQ₁ : covectorNormConst eps n₁ ≠ 0) (hQ₂ : covectorNormConst eps n₂ ≠ 0)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ContDiff ℝ 1 V₁) (hV₂ : ContDiff ℝ 1 V₂) (b₁ b₂ : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n₁ x = b₁ → covectorPhase n₂ x = b₂ → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y)) u x) := by
  obtain ⟨w₁, dw₁, ddw₁, ε₁, hε₁, hw₁a, hd₁, hdd₁, heq₁⟩ :=
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (hV₁.div contDiff_const fun _ => hQ₁) b₁
  obtain ⟨w₂, dw₂, ddw₂, ε₂, hε₂, hw₂a, hd₂, hdd₂, heq₂⟩ :=
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (hV₂.div contDiff_const fun _ => hQ₂) b₂
  refine ⟨fun y => covectorLift n₁ w₁ y * covectorLift n₂ w₂ y, min ε₁ ε₂,
    lt_min hε₁ hε₂, ?_, ?_⟩
  · intro x h1 h2
    show w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x) = 1
    rw [h1, h2, hw₁a, hw₂a, one_mul]
  · intro x hx1 hx2
    have hs1 : covectorPhase n₁ x ∈ Ioo (b₁ - ε₁) (b₁ + ε₁) := by
      obtain ⟨p, q⟩ := hx1
      constructor
      · have := min_le_left ε₁ ε₂; linarith
      · have := min_le_left ε₁ ε₂; linarith
    have hs2 : covectorPhase n₂ x ∈ Ioo (b₂ - ε₂) (b₂ + ε₂) := by
      obtain ⟨p, q⟩ := hx2
      constructor
      · have := min_le_right ε₁ ε₂; linarith
      · have := min_le_right ε₁ ε₂; linarith
    set U : Set (Fin (d + 1) → ℝ) :=
      covectorPhase n₁ ⁻¹' Ioo (b₁ - ε₁) (b₁ + ε₁) ∩
        covectorPhase n₂ ⁻¹' Ioo (b₂ - ε₂) (b₂ + ε₂) with hUdef
    have hU : IsOpen U :=
      (isOpen_Ioo.preimage (continuous_covectorPhase n₁)).inter
        (isOpen_Ioo.preimage (continuous_covectorPhase n₂))
    have hxU : x ∈ U := ⟨hs1, hs2⟩
    have hphase1 : ContDiff ℝ ∞ (covectorPhase (d := d) n₁) := contDiff_covectorPhase n₁
    have hphase2 : ContDiff ℝ ∞ (covectorPhase (d := d) n₂) := contDiff_covectorPhase n₂
    have hfU : ∀ y ∈ U, DifferentiableAt ℝ (covectorLift n₁ w₁) y := by
      intro y hy
      exact ((hd₁ _ hy.1).comp_hasFDerivAt y
        (differentiableAt_of_contDiff_infty hphase1 y).hasFDerivAt).differentiableAt
    have hgU : ∀ y ∈ U, DifferentiableAt ℝ (covectorLift n₂ w₂) y := by
      intro y hy
      exact ((hd₂ _ hy.2).comp_hasFDerivAt y
        (differentiableAt_of_contDiff_infty hphase2 y).hasFDerivAt).differentiableAt
    -- differentiability of the first partials at x
    have hev1 : ∀ i : Fin (d + 1), coordPartial i (covectorLift n₁ w₁) =ᶠ[nhds x]
        fun y => n₁ i * covectorLift n₁ dw₁ y := by
      intro i
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) ?_
      intro y hy
      exact coordPartial_covectorLift (hd₁ _ hy.1) i
    have hev2 : ∀ i : Fin (d + 1), coordPartial i (covectorLift n₂ w₂) =ᶠ[nhds x]
        fun y => n₂ i * covectorLift n₂ dw₂ y := by
      intro i
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) ?_
      intro y hy
      exact coordPartial_covectorLift (hd₂ _ hy.2) i
    have hdw1 : DifferentiableAt ℝ (covectorLift (d := d) n₁ dw₁) x :=
      ((hdd₁ _ hs1).comp_hasFDerivAt x
        (differentiableAt_of_contDiff_infty hphase1 x).hasFDerivAt).differentiableAt
    have hdw2 : DifferentiableAt ℝ (covectorLift (d := d) n₂ dw₂) x :=
      ((hdd₂ _ hs2).comp_hasFDerivAt x
        (differentiableAt_of_contDiff_infty hphase2 x).hasFDerivAt).differentiableAt
    have hfd : ∀ i, DifferentiableAt ℝ (coordPartial i (covectorLift n₁ w₁)) x := by
      intro i
      rw [(hev1 i).differentiableAt_iff]
      exact hdw1.const_mul (n₁ i)
    have hgd : ∀ i, DifferentiableAt ℝ (coordPartial i (covectorLift n₂ w₂)) x := by
      intro i
      rw [(hev2 i).differentiableAt_iff]
      exact hdw2.const_mul (n₂ i)
    have hprod := dalembert_mul_transverse eps heps i₀
      (fun i hi y => coordPartial_covectorLift_of_zero n₁ w₁ (hn₁ i hi) y)
      (fun y => coordPartial_covectorLift_of_zero n₂ w₂ hn₂ y)
      hU hxU hfU hgU hfd hgd
    have hf := dalembert_covectorLift_flat eps heps isOpen_Ioo hd₁ hdd₁ hs1
    have hg := dalembert_covectorLift_flat eps heps isOpen_Ioo hd₂ hdd₂ hs2
    have hE₁ : ddw₁ (covectorPhase n₁ x)
        + V₁ (covectorPhase n₁ x) / covectorNormConst eps n₁ * w₁ (covectorPhase n₁ x) = 0 := by
      have h := heq₁ (covectorPhase n₁ x)
      simpa using h
    have hE₂ : ddw₂ (covectorPhase n₂ x)
        + V₂ (covectorPhase n₂ x) / covectorNormConst eps n₂ * w₂ (covectorPhase n₂ x) = 0 := by
      have h := heq₂ (covectorPhase n₂ x)
      simpa using h
    have hQ1 : covectorNormConst eps n₁ * ddw₁ (covectorPhase n₁ x)
        = -(V₁ (covectorPhase n₁ x) * w₁ (covectorPhase n₁ x)) := by
      field_simp at hE₁
      linarith [hE₁]
    have hQ2 : covectorNormConst eps n₂ * ddw₂ (covectorPhase n₂ x)
        = -(V₂ (covectorPhase n₂ x) * w₂ (covectorPhase n₂ x)) := by
      field_simp at hE₂
      linarith [hE₂]
    show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => covectorLift n₁ w₁ y * covectorLift n₂ w₂ y) x
      + (V₁ (covectorPhase n₁ x) + V₂ (covectorPhase n₂ x))
        * (w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x)) = 0
    rw [hprod, hf, hg]
    show w₂ (covectorPhase n₂ x) * (covectorNormConst eps n₁ * ddw₁ (covectorPhase n₁ x))
        + w₁ (covectorPhase n₁ x) * (covectorNormConst eps n₂ * ddw₂ (covectorPhase n₂ x))
      + (V₁ (covectorPhase n₁ x) + V₂ (covectorPhase n₂ x))
        * (w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x)) = 0
    rw [hQ1, hQ2]
    ring

/-- **A separable potential is determined by clock data.** -/
theorem separable_potential_determined (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {n₁ n₂ : Fin (d + 1) → ℝ} (i₀ : Fin (d + 1))
    (hn₁ : ∀ i, i ≠ i₀ → n₁ i = 0) (hn₂ : n₂ i₀ = 0)
    (hQ₁ : covectorNormConst eps n₁ ≠ 0) (hQ₂ : covectorNormConst eps n₂ ≠ 0)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ContDiff ℝ 1 V₁) (hV₂ : ContDiff ℝ 1 V₂)
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b₁ b₂ : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y)) u x) →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other u x)) :
    other = fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y) := by
  funext x
  obtain ⟨u, ε, hε, hu1, hsolve⟩ :=
    exists_separable_localProbe eps heps i₀ hn₁ hn₂ hQ₁ hQ₂ hV₁ hV₂
      (covectorPhase n₁ x) (covectorPhase n₂ x)
  have hx1 : covectorPhase n₁ x ∈ Ioo (covectorPhase n₁ x - ε) (covectorPhase n₁ x + ε) := by
    constructor <;> linarith
  have hx2 : covectorPhase n₂ x ∈ Ioo (covectorPhase n₂ x - ε) (covectorPhase n₂ x + ε) := by
    constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother _ _ u ε hε hsolve x hx1 hx2) (hsolve x hx1 hx2) ?_
  rw [hu1 x rfl rfl]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
