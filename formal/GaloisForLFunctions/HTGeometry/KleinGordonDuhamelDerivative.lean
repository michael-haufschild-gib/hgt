import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelSeparation

/-!
# The product rule for a strongly differentiable operator family

Differentiating the separated Duhamel term needs the derivative of `t ↦ T(t)y(t)` where the operator
family `T` is only *strongly* differentiable — differentiable when applied to a fixed vector. The
usual splitting

`T(s)y(s) - T(t)y(t) = T(s)(y(s) - y(t)) + (T(s) - T(t))y(t)`

works: divided by `s - t` the first term is `T(s)` applied to the slope of `y`, which converges by the
joint continuity of a uniformly bounded strongly continuous family, and the second is the slope of
`s ↦ T(s)y(t)` at a *fixed* vector, which converges by hypothesis. No norm differentiability of `T` is
used, and none is available.

The second half of the file records why the hypothesis is met for the Duhamel integrals: the
half-order propagator carries a factor `⟨D⟩⁻¹` which, being a bounded operator, passes through the
Bochner integral, so `∫₀ᵗ (sin(s⟨D⟩)/⟨D⟩)g(s) ds` lies in the range of `⟨D⟩⁻¹` — exactly the domain on
which the cosine propagator is differentiable.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

/-! ## The product rule -/

section ProductRule

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **The product rule for a uniformly bounded, strongly continuous operator family.** If `T` is
differentiable when applied to the fixed vector `y t`, and `y` is differentiable, then `t ↦ T t (y t)`
is differentiable and the two contributions add. -/
theorem hasDerivAt_strong_apply {T : ℝ → X →L[ℝ] Y} {M : ℝ} (hM : ∀ t, ‖T t‖ ≤ M)
    (hstrong : ∀ x : X, Continuous fun t : ℝ => T t x)
    {y : ℝ → X} {y' : X} {t : ℝ} (hy : HasDerivAt y y' t)
    {d : Y} (hT : HasDerivAt (fun s : ℝ => T s (y t)) d t) :
    HasDerivAt (fun s : ℝ => T s (y s)) (T t y' + d) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hjoint : Continuous fun q : ℝ × X => T q.1 q.2 := continuous_uncurry_of_strong hM hstrong
  have hy2 := hy.tendsto_slope
  have hT2 := hT.tendsto_slope
  have hself : Tendsto (fun s : ℝ => s) (nhdsWithin t {t}ᶜ) (nhds t) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hpair : Tendsto (fun s : ℝ => ((s, slope y t s) : ℝ × X)) (nhdsWithin t {t}ᶜ)
      (nhds (t, y')) := hself.prodMk_nhds hy2
  have h1 : Tendsto (fun s : ℝ => T s (slope y t s)) (nhdsWithin t {t}ᶜ) (nhds (T t y')) :=
    (hjoint.tendsto (t, y')).comp hpair
  have hsum := h1.add hT2
  refine Filter.Tendsto.congr' ?_ hsum
  refine Filter.Eventually.of_forall fun s => ?_
  simp only [slope_def_module]
  rw [map_smul, map_sub, ← smul_add]
  congr 1
  abel

end ProductRule

/-! ## The Duhamel integrals are regular -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The half-order propagator is `⟨D⟩⁻¹` composed with the energy-coordinate sine. -/
theorem kgSinFreqOp_eq_freqInv_comp (t : ℝ) :
    kgSinFreqOp (E := E) t = (kgFreqInvOp).comp (kgSinOp t) :=
  (kgFreqInvOp_comp_kgSinOp t).symm

theorem kgSinFreqOp_apply_freqInv (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgSinFreqOp t x = kgFreqInvOp (kgSinOp t x) := by
  rw [kgSinFreqOp_eq_freqInv_comp]
  rfl

/-- **The Duhamel integral of the half-order propagator lies in the range of `⟨D⟩⁻¹`.** The factor
`⟨D⟩⁻¹` is a bounded operator, so it passes through the Bochner integral. -/
theorem intervalIntegral_kgSinFreqOp_eq {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgSinFreqOp s (g s))
      = kgFreqInvOp (∫ s in (0 : ℝ)..t, kgSinOp s (g s)) := by
  have hsin : Continuous fun s : ℝ => kgSinOp s (g s) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_id hg
  have hI := hsin.intervalIntegrable (μ := volume) 0 t
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgSinFreqOp s (g s) = kgFreqInvOp (kgSinOp s (g s)) := fun s _ =>
    kgSinFreqOp_apply_freqInv s (g s)
  rw [intervalIntegral.integral_congr hpoint,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI]

/-! ## The derivatives of the two Duhamel integrals -/

/-- The first Duhamel integral, whose derivative is the cosine propagator at the endpoint. -/
theorem hasDerivAt_intervalIntegral_kgCosOp {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp s (g s)) (kgCosOp t (g t)) t := by
  have hcos : Continuous fun s : ℝ => kgCosOp s (g s) :=
    continuous_kgCosOp_comp continuous_id hg
  exact intervalIntegral.integral_hasDerivAt_right
    (hcos.intervalIntegrable (μ := volume) 0 t) (hcos.stronglyMeasurableAtFilter _ _)
    hcos.continuousAt

/-- The second Duhamel integral, whose derivative is the energy-coordinate sine at the endpoint. -/
theorem hasDerivAt_intervalIntegral_kgSinOp {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgSinOp s (g s)) (kgSinOp t (g t)) t := by
  have hsin : Continuous fun s : ℝ => kgSinOp s (g s) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_id hg
  exact intervalIntegral.integral_hasDerivAt_right
    (hsin.intervalIntegrable (μ := volume) 0 t) (hsin.stronglyMeasurableAtFilter _ _)
    hsin.continuousAt

end GaloisForLFunctions.HTGeometry
