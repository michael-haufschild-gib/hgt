import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scheffé's lemma

Pointwise convergence of nonnegative densities does not by itself control the mass they carry:
mass can escape.  Scheffé's lemma says that if it demonstrably does not escape — if the total
integrals converge to the total integral of the limit — then the convergence is automatically in
`L¹`, and hence uniform against every bounded weight.

The proof is dominated convergence applied not to the difference but to its positive part.  With
`G = (g − f)⁺` one has `0 ≤ G ≤ g` whenever `f ≥ 0`, so the limit `g` itself dominates, and
`G → 0` pointwise.  The identity

```text
|y| = 2·max(y, 0) − y
```

then converts the vanishing of `∫G` together with the convergence of the integrals into the
vanishing of `∫|f − g|`, since the signed part telescopes against the mass hypothesis.

This is the standard route from pointwise asymptotics of a family of densities to weak convergence
of the measures they define: no equicontinuity, tightness, or uniform-integrability argument is
required once the masses are known to converge.
-/

open MeasureTheory Filter

namespace GaloisForLFunctions

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

/-- **Scheffé's lemma.**  Nonnegative densities converging pointwise, with converging total
integrals, converge in `L¹`. -/
theorem tendsto_integral_abs_sub_of_tendsto_integral
    {f : ι → α → ℝ} {g : α → ℝ}
    (hfnn : ∀ᶠ i in l, 0 ≤ᵐ[μ] f i)
    (hfi : ∀ᶠ i in l, Integrable (f i) μ)
    (hgnn : 0 ≤ᵐ[μ] g) (hgi : Integrable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (nhds (g x)))
    (hint : Tendsto (fun i => ∫ x, f i x ∂μ) l (nhds (∫ x, g x ∂μ))) :
    Tendsto (fun i => ∫ x, |f i x - g x| ∂μ) l (nhds 0) := by
  set G : ι → α → ℝ := fun i x => max (g x - f i x) 0 with hGdef
  -- the positive part vanishes pointwise
  have hGtend : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (nhds 0) := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun i => g x - f i x) l (nhds (g x - g x)) :=
      Filter.Tendsto.sub tendsto_const_nhds hx
    rw [sub_self] at h1
    have hcont : Continuous fun y : ℝ => max y 0 := continuous_id.max continuous_const
    have h2 := (hcont.tendsto (0 : ℝ)).comp h1
    rw [show (fun i => G i x) =
      (fun y : ℝ => max y 0) ∘ fun i => g x - f i x by rfl]
    simpa only [max_self] using h2
  -- the limit density dominates the positive part
  have hgnn' : ∀ᵐ x ∂μ, 0 ≤ g x := by
    filter_upwards [hgnn] with x hx
    simpa using hx
  have hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖G i x‖ ≤ g x := by
    filter_upwards [hfnn] with i hi
    filter_upwards [hi, hgnn'] with x hx hgx
    have hx' : 0 ≤ f i x := by simpa using hx
    have h0 : 0 ≤ G i x := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg h0, hGdef]
    exact max_le (by linarith) hgx
  have hGmeas : ∀ᶠ i in l, AEStronglyMeasurable (G i) μ := by
    filter_upwards [hfi] with i hi
    exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hgi.aestronglyMeasurable.sub hi.aestronglyMeasurable)
  have hGint : Tendsto (fun i => ∫ x, G i x ∂μ) l (nhds 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (bound := g) hGmeas hbound hgi
      hGtend
    rwa [integral_zero] at h
  -- integrability of the positive part
  have hGintegrable : ∀ᶠ i in l, Integrable (G i) μ := by
    filter_upwards [hGmeas, hbound] with i hm hb
    refine Integrable.mono hgi hm ?_
    filter_upwards [hb, hgnn'] with x hx hgx
    rw [Real.norm_eq_abs (g x), abs_of_nonneg hgx]
    exact hx
  -- the algebraic identity, integrated
  have hsplit : ∀ᶠ i in l, ∫ x, |f i x - g x| ∂μ
      = 2 * (∫ x, G i x ∂μ) - ((∫ x, g x ∂μ) - ∫ x, f i x ∂μ) := by
    filter_upwards [hfi, hGintegrable] with i hi hGi
    have habs : ∀ x, |f i x - g x| = 2 * G i x - (g x - f i x) := by
      intro x
      show |f i x - g x| = 2 * max (g x - f i x) 0 - (g x - f i x)
      rcases le_or_gt 0 (g x - f i x) with h | h
      · rw [max_eq_left h, abs_of_nonpos (by linarith)]
        ring
      · rw [max_eq_right h.le, abs_of_pos (by linarith)]
        ring
    have e1 : ∫ x, (2 * G i x - (g x - f i x)) ∂μ
        = (∫ x, 2 * G i x ∂μ) - ∫ x, (g x - f i x) ∂μ := by
      apply integral_sub
      · exact hGi.const_mul 2
      · exact hgi.sub hi
    have e2 : ∫ x, (g x - f i x) ∂μ = (∫ x, g x ∂μ) - ∫ x, f i x ∂μ := by
      apply integral_sub hgi hi
    rw [integral_congr_ae (Filter.Eventually.of_forall habs), e1, integral_const_mul, e2]
  -- assemble
  have hlim : Tendsto (fun i => 2 * (∫ x, G i x ∂μ) - ((∫ x, g x ∂μ) - ∫ x, f i x ∂μ)) l
      (nhds (2 * 0 - ((∫ x, g x ∂μ) - ∫ x, g x ∂μ))) :=
    Filter.Tendsto.sub (hGint.const_mul 2) (Filter.Tendsto.sub tendsto_const_nhds hint)
  rw [sub_self, mul_zero, sub_zero] at hlim
  exact hlim.congr' (hsplit.mono fun i hi => hi.symm)

omit [l.IsCountablyGenerated] in
/-- **From `L¹` convergence of densities to convergence against every bounded weight.**  This is
the form in which weak convergence of the associated measures is used. -/
theorem tendsto_integral_smul_of_tendsto_integral_abs_sub
    {f : ι → α → ℝ} {g w : α → ℝ} {C : ℝ}
    (hw : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (hwm : AEStronglyMeasurable w μ)
    (hfi : ∀ᶠ i in l, Integrable (f i) μ) (hgi : Integrable g μ)
    (hL1 : Tendsto (fun i => ∫ x, |f i x - g x| ∂μ) l (nhds 0)) :
    Tendsto (fun i => ∫ x, w x * f i x ∂μ) l (nhds (∫ x, w x * g x ∂μ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun i => dist_nonneg) ?_
    (by simpa using hL1.const_mul C)
  filter_upwards [hfi] with i hi
  have hwf : Integrable (fun x => w x * f i x) μ := hi.bdd_mul hwm hw
  have hwg : Integrable (fun x => w x * g x) μ := hgi.bdd_mul hwm hw
  rw [Real.dist_eq, ← integral_sub hwf hwg]
  calc |∫ x, (w x * f i x - w x * g x) ∂μ|
      ≤ ∫ x, |w x * f i x - w x * g x| ∂μ := by
        simpa using abs_integral_le_integral_abs (f := fun x => w x * f i x - w x * g x)
    _ ≤ ∫ x, C * |f i x - g x| ∂μ := by
        refine integral_mono_ae ((hwf.sub hwg).abs) (((hi.sub hgi).abs).const_mul C) ?_
        filter_upwards [hw] with x hx
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs] at hx) (abs_nonneg _)
    _ = C * ∫ x, |f i x - g x| ∂μ := integral_const_mul _ _

end GaloisForLFunctions
