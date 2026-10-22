import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPotentialStability

/-!
# The potential is determined by the field it produces

The Lipschitz estimate bounds the field in terms of the potential. This file proves the converse
direction of the same correspondence: the map from the equation to its solutions is injective.

Two perturbations that produce the same field from every Cauchy datum have a difference `A` for
which the Duhamel source integral `∫₀ˣ sin((x-s)⟨D⟩)/⟨D⟩ · A(u(s)) ds` vanishes identically.
Differentiating once (the corpus already owns that step, and it needs nothing but continuity of the
source) turns it into `∫₀ˣ cos((x-s)⟨D⟩) A(u(s)) ds = 0`. That integral has derivative `A(u(0))` at
the origin — the cosine propagator is the identity at time zero, so on a shrinking interval the
integrand is uniformly close to its value at the origin and the integral is `x·A(u(0)) + o(x)`.
Hence `A(u(0)) = A(f) = 0` for every `f`.

The second differentiation is the delicate one: away from the origin the derivative of the cosine
Duhamel term involves `⟨D⟩ sin((x-s)⟨D⟩)`, which is unbounded, and that is exactly the obstruction
that forced the smoothing hypothesis elsewhere. At the origin the obstruction is absent, because the
only surviving term is the endpoint one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The Duhamel term of an arbitrary continuous source -/

/-- The Duhamel term of an arbitrary continuous source, in separated form. -/
theorem intervalIntegral_kgSinFreqOp_separated {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (g s))
      = kgSinFreqOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))
        - kgCosOp t (∫ s in (0 : ℝ)..t, kgSinFreqOp s (g s)) := by
  have h := intervalIntegral_kgFieldKernel_separated
    (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E))) hg t
  simpa [kgFieldKernel_apply] using h

/-- **The Duhamel term of a continuous source is differentiable**, with the classical derivative
`∫₀ᵗ cos((t-s)⟨D⟩) g(s) ds`. -/
theorem hasDerivAt_intervalIntegral_kgSinFreqOp {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgSinFreqOp (r - s) (g s))
      (∫ s in (0 : ℝ)..t, kgCosOp (t - s) (g s)) t := by
  have hd := hasDerivAt_kgDuhamel hg t
  rw [kgDuhamel_deriv_eq hg t] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => intervalIntegral_kgSinFreqOp_separated hg r)

/-! ## The cosine Duhamel term at the origin -/

/-- **The cosine Duhamel term has derivative `g 0` at the origin.** Only the continuity of the source
is used. The propagator is the identity at time zero, so on `[0,x]` the integrand differs from `g 0`
by a quantity that tends to zero uniformly, and the integral is `x·g(0) + o(x)`. -/
theorem hasDerivAt_intervalIntegral_kgCosOp_zero {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (g s)) (g 0) 0 := by
  set H : ℝ → Lp ℂ 2 (volume : Measure E) :=
    fun r => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (g s) with hHdef
  have hH0 : H 0 = 0 := by
    rw [hHdef]
    exact intervalIntegral.integral_same
  rw [hasDerivAt_iff_tendsto]
  refine Metric.tendsto_nhds_nhds.mpr fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 4) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    Metric.continuousAt_iff.mp (continuous_kgCosOp_apply (g 0)).continuousAt (ε / 4) (by linarith)
  have h1' : ∀ s : ℝ, |s| < δ₁ → ‖g s - g 0‖ < ε / 4 := by
    intro s hs
    have hd := h₁ (by rwa [Real.dist_eq, sub_zero] : dist s 0 < δ₁)
    rwa [dist_eq_norm] at hd
  have h2' : ∀ τ : ℝ, |τ| < δ₂ → ‖kgCosOp (E := E) τ (g 0) - g 0‖ < ε / 4 := by
    intro τ hτ
    have hd := h₂ (by rwa [Real.dist_eq, sub_zero] : dist τ 0 < δ₂)
    rw [dist_eq_norm] at hd
    simpa [kgCosOp_zero] using hd
  refine ⟨min δ₁ (δ₂ / 2), lt_min hδ₁ (by linarith), fun x hx => ?_⟩
  have hxabs : |x| < min δ₁ (δ₂ / 2) := by rwa [Real.dist_eq, sub_zero] at hx
  have hx1 : |x| < δ₁ := lt_of_lt_of_le hxabs (min_le_left _ _)
  have hx2 : |x| < δ₂ / 2 := lt_of_lt_of_le hxabs (min_le_right _ _)
  show dist (‖x - (0 : ℝ)‖⁻¹ * ‖H x - H 0 - (x - (0 : ℝ)) • g 0‖) 0 < ε
  rw [sub_zero, hH0, sub_zero, Real.norm_eq_abs, Real.dist_eq, sub_zero]
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hε
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) x, ‖kgCosOp (x - s) (g s) - g 0‖ ≤ ε / 2 := by
    intro s hs
    have hsx : |s| ≤ |x| := abs_le_abs_of_mem_uIoc_zero hs
    have hτ : |x - s| < δ₂ := by
      have habs : |x - s| ≤ |x| + |s| := abs_sub x s
      linarith
    have hstep : kgCosOp (x - s) (g s) - g 0
        = kgCosOp (x - s) (g s - g 0) + (kgCosOp (x - s) (g 0) - g 0) := by
      rw [map_sub]
      abel
    rw [hstep]
    have hA : ‖kgCosOp (E := E) (x - s) (g s - g 0)‖ ≤ ‖g s - g 0‖ :=
      norm_kgCosOp_apply_le _ _
    have hB : ‖g s - g 0‖ < ε / 4 := h1' s (lt_of_le_of_lt hsx hx1)
    have hC : ‖kgCosOp (E := E) (x - s) (g 0) - g 0‖ < ε / 4 := h2' _ hτ
    calc ‖kgCosOp (x - s) (g s - g 0) + (kgCosOp (x - s) (g 0) - g 0)‖
        ≤ ‖kgCosOp (E := E) (x - s) (g s - g 0)‖ + ‖kgCosOp (E := E) (x - s) (g 0) - g 0‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 := by linarith
  have hI : IntervalIntegrable (fun s : ℝ => kgCosOp (x - s) (g s)) volume 0 x :=
    (continuous_kgCosOp_comp (continuous_const.sub continuous_id) hg).intervalIntegrable 0 x
  have hconst : (∫ _s in (0 : ℝ)..x, g 0) = x • g 0 := by
    rw [intervalIntegral.integral_const, sub_zero]
  have hsplit : H x - x • g 0 = ∫ s in (0 : ℝ)..x, (kgCosOp (x - s) (g s) - g 0) := by
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, hconst, hHdef]
  have hnorm : ‖H x - x • g 0‖ ≤ ε / 2 * |x| := by
    rw [hsplit]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    simpa using hle
  have hfinal : |x|⁻¹ * ‖H x - x • g 0‖ ≤ ε / 2 := by
    have hmul : |x|⁻¹ * ‖H x - x • g 0‖ ≤ |x|⁻¹ * (ε / 2 * |x|) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    have hcalc : |x|⁻¹ * (ε / 2 * |x|) = ε / 2 := by
      field_simp
    linarith [hmul, hcalc.le, hcalc.ge]
  have hnn : (0 : ℝ) ≤ |x|⁻¹ * ‖H x - x • g 0‖ := by positivity
  rw [abs_of_nonneg hnn]
  linarith

/-! ## The vanishing of the source -/

/-- A continuous source whose Duhamel term vanishes identically vanishes at the origin. -/
theorem eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero
    {g : ℝ → Lp ℂ 2 (volume : Measure E)} (hg : Continuous g)
    (hzero : ∀ x : ℝ, (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (g s)) = 0) :
    g 0 = 0 := by
  have hd1 : ∀ t : ℝ, (∫ s in (0 : ℝ)..t, kgCosOp (t - s) (g s)) = 0 := by
    intro t
    have hD := hasDerivAt_intervalIntegral_kgSinFreqOp hg t
    have hfun : (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgSinFreqOp (r - s) (g s))
        = fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E)) := funext hzero
    rw [hfun] at hD
    exact hD.unique (hasDerivAt_const t 0)
  have hD2 := hasDerivAt_intervalIntegral_kgCosOp_zero hg
  have hfun2 : (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (g s))
      = fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E)) := funext hd1
  rw [hfun2] at hD2
  exact hD2.unique (hasDerivAt_const 0 0)

/-! ## Injectivity of the forward map -/

section Uniqueness

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The potential is determined by the field it produces.** Two bounded perturbations whose
solutions agree for every Cauchy datum and every time are equal. Together with the Lipschitz estimate
this makes the forward map of the inverse problem a continuous injection. -/
theorem eq_of_kgFieldMild_eq (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (heq : ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
      kgFieldMild W₁ f h t = kgFieldMild W₂ f h t) :
    W₁ = W₂ := by
  have hker : ∀ f : Lp ℂ 2 (volume : Measure E), (W₁ - W₂) f = 0 := by
    intro f
    have hcu : Continuous (kgFieldMild W₁ f 0) := continuous_kgFieldMild hb0 hW₁ f 0
    have hg : Continuous fun s : ℝ => (W₁ - W₂) (kgFieldMild W₁ f 0 s) :=
      (W₁ - W₂).continuous.comp hcu
    have hdiff : ∀ s : ℝ, kgFieldMild W₁ f 0 s - kgFieldMild W₂ f 0 s = 0 := fun s =>
      sub_eq_zero.mpr (heq f 0 s)
    have hzero : ∀ x : ℝ,
        (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₁ f 0 s))) = 0 := by
      intro x
      have hsplit := kgFieldMild_sub_potential hb0 hW₁ hW₂ f 0 x
      have h2 : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          (W₂ (kgFieldMild W₁ f 0 s - kgFieldMild W₂ f 0 s))) = 0 := by
        have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) x, kgSinFreqOp (x - s)
            (W₂ (kgFieldMild W₁ f 0 s - kgFieldMild W₂ f 0 s)) = 0 := by
          intro s _
          rw [hdiff s, map_zero, map_zero]
        rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_zero]
      rw [hdiff x, h2, add_zero] at hsplit
      exact hsplit.symm
    have hg0 := eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero hg hzero
    rwa [kgFieldMild_zero hb0 hW₁ f 0] at hg0
  have hsub : W₁ - W₂ = 0 := ContinuousLinearMap.ext fun f => by simp [hker f]
  exact sub_eq_zero.mp hsub

/-- **The solution operator determines the equation.** -/
theorem kgFieldMild_injective_potential (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b) :
    (∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
        kgFieldMild W₁ f h t = kgFieldMild W₂ f h t) ↔ W₁ = W₂ := by
  refine ⟨eq_of_kgFieldMild_eq hb0 hW₁ hW₂, ?_⟩
  rintro rfl f h t
  rfl

end Uniqueness

end GaloisForLFunctions.HTGeometry
