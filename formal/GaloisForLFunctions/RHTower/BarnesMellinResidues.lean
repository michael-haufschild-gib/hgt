import GaloisForLFunctions.HTGeometry.SineVerticalDecay
import GaloisForLFunctions.RHTower.BarnesMellinIntegrandAnalysis

/-!
# The residues of the Mellin integrand

The integrand `F(w) = x^{-w} ζ(-sw)(-π/sin(πw))` has two families of simple poles: the integers,
inherited from the reflection kernel, and the single point `w = -1/s`, inherited from the pole of
zeta.  In each case one factor carries the pole and the remaining factors are analytic there, so
the residue is the pole's residue times the value of the analytic part:

```text
Res_{w=k}   F = -(-1)^k x^{-k} ζ(-sk) ,        k ≥ 0 ,
Res_{w=-1/s} F = -(1/s) x^{1/s} · π / sin(π/s) .
```

Read through the contour shift these are, respectively, the descending powers `(-1)^k ζ(-sk) x^{-k}`
of the Barnes tail (with `k = 0` giving the constant `-1/2`) and the leading term
`(π/s) csc(π/s) x^{1/s}`.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- A positive real base raised to minus the variable is entire. -/
theorem analyticAt_const_cpow_neg {x : ℝ} (hx : 0 < x) (p : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ((x : ℝ) : ℂ) ^ (-w)) p := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  refine DifferentiableOn.analyticAt (s := Set.univ) ?_ Filter.univ_mem
  intro w _
  exact (DifferentiableAt.const_cpow (differentiableAt_id.neg) (Or.inl hxne)).differentiableWithinAt

/-- The reflection kernel is analytic off the integers. -/
theorem analyticAt_reflectionKernel {p : ℂ} (hsin : Complex.sin ((Real.pi : ℂ) * p) ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))) p := by
  have hcont : ∀ᶠ w : ℂ in nhds p, Complex.sin ((Real.pi : ℂ) * w) ≠ 0 :=
    ((Complex.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt).eventually_ne
      hsin
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [hcont] with w hw
  refine DifferentiableAt.neg ?_
  exact DifferentiableAt.div (differentiableAt_const _)
    ((Complex.differentiable_sin.comp (differentiable_id.const_mul _)).differentiableAt) hw

/-- The rescaled zeta factor is analytic off the pullback of the zeta pole. -/
theorem analyticAt_zetaComp {s : ℝ} {p : ℂ} (hζ : -(s : ℂ) * p ≠ 1) :
    AnalyticAt ℂ (fun w : ℂ => riemannZeta (-(s : ℂ) * w)) p := by
  have hz := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hζ
  have hlin : AnalyticAt ℂ (fun w : ℂ => -(s : ℂ) * w) p :=
    analyticAt_const.mul analyticAt_id
  exact hz.comp hlin

/-- **The integrand has a simple pole at every nonnegative integer.** -/
theorem barnesIntegrand_simplePole_at_nat {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (k : ℕ) :
    (fun w : ℂ => barnesIntegrand s x w
        - (((x : ℝ) : ℂ) ^ (-(k : ℂ)) * riemannZeta (-(s : ℂ) * (k : ℂ)) * (-(-1) ^ k))
          / (w - (k : ℂ)))
      =O[nhdsWithin ((k : ℂ)) {((k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  have hζ : -(s : ℂ) * (k : ℂ) ≠ 1 := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re] at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hre]
  have hg : AnalyticAt ℂ (fun w : ℂ =>
      ((x : ℝ) : ℂ) ^ (-w) * riemannZeta (-(s : ℂ) * w)) (k : ℂ) :=
    (analyticAt_const_cpow_neg hx _).mul (analyticAt_zetaComp hζ)
  have hh : (fun w : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      - (-(-1) ^ k) / (w - (k : ℂ)))
      =O[nhdsWithin ((k : ℂ)) {((k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
    have hbase := GaloisForLFunctions.HTGeometry.isBigO_inv_sin_sub_inv_at_nat k
    have hneg := hbase.neg_left
    refine hneg.congr' ?_ Filter.EventuallyEq.rfl
    refine Filter.Eventually.of_forall fun w => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hmain := GaloisForLFunctions.HTGeometry.isBigO_analytic_mul_simplePole hg hh
  exact hmain

/-- **The integrand has a simple pole at the pullback of the zeta pole.** -/
theorem barnesIntegrand_simplePole_at_zetaPole {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hsin : Complex.sin ((Real.pi : ℂ) * (-(1 / s : ℝ) : ℂ)) ≠ 0) :
    (fun w : ℂ => barnesIntegrand s x w
        - ((((x : ℝ) : ℂ) ^ (-(-(1 / s : ℝ) : ℂ))
            * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-(1 / s : ℝ) : ℂ))))
            * (-(1 / s : ℝ) : ℂ))
          / (w - (-(1 / s : ℝ) : ℂ)))
      =O[nhdsWithin ((-(1 / s : ℝ) : ℂ)) {((-(1 / s : ℝ) : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  set p : ℂ := ((-(1 / s : ℝ) : ℝ) : ℂ) with hp
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  -- the linear substitution carries the punctured neighbourhood of `p` to that of `1`
  have hmap : Filter.Tendsto (fun w : ℂ => -(s : ℂ) * w)
      (nhdsWithin p {p}ᶜ) (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Filter.Tendsto (fun w : ℂ => -(s : ℂ) * w) (nhds p) (nhds (-(s : ℂ) * p)) :=
        ((continuous_const.mul continuous_id)).tendsto _
      have hval : -(s : ℂ) * p = 1 := by
        rw [hp]
        push_cast
        field_simp
      rw [hval] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hwne : w ≠ p := hw
      intro hcon
      simp only [Set.mem_singleton_iff] at hcon
      refine hwne ?_
      have hval : -(s : ℂ) * p = 1 := by
        rw [hp]; push_cast; field_simp
      have : -(s : ℂ) * w = -(s : ℂ) * p := by rw [hcon, hval]
      exact mul_left_cancel₀ (neg_ne_zero.mpr hsne) this
  have hbase : (fun z : ℂ => riemannZeta z - 1 / (z - 1))
      =O[nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ] (fun _ : ℂ => (1 : ℂ)) :=
    tendsto_riemannZeta_sub_one_div.isBigO_one ℂ
  have hcomp := hbase.comp_tendsto hmap
  have hh : (fun w : ℂ => riemannZeta (-(s : ℂ) * w) - (-(1 / s : ℝ) : ℂ) / (w - p))
      =O[nhdsWithin p {p}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
    refine hcomp.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w - p ≠ 0 := sub_ne_zero.mpr hw
    have hden : -(s : ℂ) * w - 1 = -(s : ℂ) * (w - p) := by
      have hval : -(s : ℂ) * p = 1 := by rw [hp]; push_cast; field_simp
      rw [mul_sub, hval]
    simp only [Function.comp_apply]
    rw [hden]
    have hsw : -(s : ℂ) * (w - p) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hsne) hwne
    rw [show ((-(1 / s : ℝ) : ℝ) : ℂ) = -(1 / (s : ℂ)) by push_cast; ring]
    field_simp
  have hg : AnalyticAt ℂ (fun w : ℂ => ((x : ℝ) : ℂ) ^ (-w)
      * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))) p :=
    (analyticAt_const_cpow_neg hx _).mul (analyticAt_reflectionKernel (by rw [hp] at *; exact hsin))
  have hmain := GaloisForLFunctions.HTGeometry.isBigO_analytic_mul_simplePole hg hh
  refine hmain.congr' ?_ Filter.EventuallyEq.rfl
  refine Filter.Eventually.of_forall fun w => ?_
  rw [barnesIntegrand]
  ring_nf
  rfl

end

end RHTower
