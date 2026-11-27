import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FirstExcursion

/-! # Divergence of the seventh moment on the strong-bond sector -/
open Set Filter MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds
noncomputable section

/-- Even the smaller clock, comparing both onset and wait before and
after normalization to a prescribed coupling norm, has infinite
seventh moment on draws with every longitudinal bond above 1/2. -/
theorem strong_bond_seventh_moment :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      let S := {x : PrefixIndex n→ℝ | ∀ e : Fin (n+1), 1/2 < x ((pathCoeffEquiv n).symm (.inr (e,(2,2))))}
      ∀ j ≤ P/2, let J := fun x => min (crossingOrigin n P (9/80) x) (crossingWait n P j x)
        ∀ r > (0:ℝ), ¬Integrable (fun x => |S.indicator (fun y => min (J y) (J (atRadius r y))) x|^7) μ := by
  filter_upwards [gaussian_strong_bond_seventh_power] with k hk
  intro n P μ S j hj J r hr
  obtain ⟨c,hc,h⟩ := hk
  have hm : Measurable J := (measurable_crossingOrigin ..).min (measurable_crossingWait ..)
  have hnorm : Measurable (coefficientNorm (n:=n)) :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hrad : Measurable (atRadius (n:=n) r) := (measurable_const.div hnorm).smul measurable_id
  have hS : MeasurableSet S := by
    dsimp only [S]
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun _ => measurableSet_lt measurable_const (measurable_pi_apply _)
  let B := min 1 (1/(2*r))
  have hB : 0 < B := lt_min zero_lt_one (by positivity)
  apply not_integrable_boundary_moment μ _ ((hm.min (hm.comp hrad)).indicator hS) 7 hB (half_pos hc)
  intro T hT
  apply ((half_lt_self hc).trans_le (h T hT)).trans_le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  change T*B < S.indicator (fun y => min (J y) (J (atRadius r y))) x
  have hxS : x∈S := hx.1
  rw [indicator_of_mem hxS]
  have hTJ : T < J x := lt_min hx.2.1 (hx.2.2 j hj)
  have ht := zero_lt_one.trans_le hT
  refine lt_min ((mul_le_of_le_one_right ht.le (min_le_left ..)).trans_lt hTJ) ?_
  let i : PrefixIndex n := (pathCoeffEquiv n).symm (.inr (0,(2,2)))
  have hv : 1/2 < coefficientNorm x := (hx.1 0).trans_le
    ((le_abs_self (x i)).trans (abs_coord_le_norm (WithLp.toLp 2 x) i))
  let q := r/coefficientNorm x
  have hq : 0 < q := div_pos hr (by linarith only [hv])
  have hq' : q ≤ 2*r := (div_le_iff₀ (by linarith only [hv])).mpr
    (by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hv.le)])
  have he : q*J (atRadius r x)=J x := by
    change q*min (crossingOrigin n P (9/80) (q • x)) (crossingWait n P j (q • x))=_
    rw [mul_min_of_nonneg _ _ hq.le,smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]
  apply (mul_lt_mul_iff_right₀ hq).mp
  rw [he]
  refine lt_of_le_of_lt ?_ hTJ
  calc
    _ ≤ (2*r)*(T*(1/(2*r))) := mul_le_mul hq' (mul_le_mul_of_nonneg_left (min_le_right ..) ht.le)
      (mul_nonneg ht.le hB.le) (by positivity)
    _ = T := by field_simp

#print axioms strong_bond_seventh_moment
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
