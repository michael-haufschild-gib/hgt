import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSourceMellin

/-!
# Entire Mellin transforms of angular cubic sources

Higher source jets decay exponentially at each reflected cusp. Their frequency powers retain
subexponential coefficient growth, and their height powers are absorbed into half the
exponential decay rate. The exact cusp involution then gives entire Mellin transforms on
both sides and entire normalized angular Dirichlet continuations.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

private def cubicJetProfile (n : ℕ) (c : O → ℂ) (q : ℝ) (z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ n * ((v / q : ℝ) : ℂ) * conj (besselPlaneSeries (1 / 3) c (v / q, z / (q : ℂ)))

private lemma cubicJetProfile_continuousOn (n : ℕ) {c : O → ℂ} (hc : CuspSubexponential c)
    (q : ℝ) (hq : 0 < q) (z : ℂ) :
    ContinuousOn (cubicJetProfile n c q z) (Ioi 0) := by
  have hf : ContinuousOn (fun v => besselPlaneSeries (1 / 3) c (v / q, z / (q : ℂ))) (Ioi 0) :=
    (contDiffOn_besselPlaneSeries (1 / 3) hc).continuousOn.comp
      ((continuous_id.div_const q).prodMk continuous_const).continuousOn
      (fun v hv => ⟨div_pos hv hq, mem_univ _⟩)
  have hv : Continuous (fun v : ℝ => (v : ℂ)) := Complex.continuous_ofReal
  have hvq : Continuous (fun v : ℝ => ((v / q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_id.div_const q)
  exact ((hv.pow n).continuousOn.mul hvq.continuousOn).mul
    (Complex.conjCLE.continuous.comp_continuousOn hf)

private lemma cubicJetProfile_eq_sum (n : ℕ) (c : O → ℂ) (q : ℝ) (hq : 0 < q)
    (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cubicJetProfile n c q z v = (v : ℂ) ^ n *
      conj (∑' h : O, cubicBesselTerm c h (v / q, z / (q : ℂ))) := by
  simp only [cubicBesselTerm_eq_besselPlaneTerm c _ (v / q, z / (q : ℂ)) (div_pos hv hq)]
  rw [tsum_mul_left]
  simp only [map_mul, Complex.conj_ofReal, cubicJetProfile, besselPlaneSeries]
  ring

private lemma cubicJetProfile_isBigO (n : ℕ) {c : O → ℂ} (hc : CuspSubexponential c)
    (q : ℝ) (hq : 0 < q) (z : ℂ) :
    cubicJetProfile n c q z =O[atTop]
      (fun v : ℝ => Real.exp (-(residualBesselDecayRate / (2 * q)) * v)) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselSeries_exponential_decay c hc (1 / q) (by positivity)
  have hpoly := (isLittleO_pow_exp_pos_mul_atTop n
    (show 0 < residualBesselDecayRate / (2 * q) from by
      exact div_pos residualBesselDecayRate_pos (mul_pos (by norm_num) hq))).bound one_pos
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpoly] with v hv hpow
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hpow' : v ^ n ≤ Real.exp ((residualBesselDecayRate / (2 * q)) * v) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hv0.le n),
      abs_of_pos (Real.exp_pos _), one_mul] using hpow
  have hscaled : 1 / q ≤ v / q := div_le_div_of_nonneg_right hv hq.le
  rw [cubicJetProfile_eq_sum n c q hq z v hv0]
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg hv0.le, Complex.norm_conj,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp ((residualBesselDecayRate / (2 * q)) * v) *
        (C * Real.exp (-residualBesselDecayRate * (v / q))) :=
      mul_le_mul hpow' (hb (v / q) hscaled _) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

private lemma higherSourceBarProfile_eq_cubicJetProfile (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile n z v = cubicJetProfile n
      (fun h => cuspHolWeight h ^ (n + 1) * rationalSourceResidualFourierCoefficient h) 1 z v := by
  rw [higherSourceBarProfile_eq_besselPlaneSeries n z v hv]
  simp only [cubicJetProfile, div_one, Complex.ofReal_one, pow_succ]

private lemma higherSourceZFamily_eq_cubicJetProfile (n : ℕ) (j : Fin 3)
    (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceZFamily n j z v = ((sourceCuspScale j : ℂ)⁻¹) ^ n *
      cubicJetProfile n (fun h => cuspAntiholWeight h ^ n * sourceCuspBarCoefficient j h)
        (sourceCuspScale j) z v := by
  rw [higherSourceZFamily_eq_besselPlaneSeries n j z v hv]
  unfold cubicJetProfile
  ring

/-- All normalized initial source jets are continuous on the positive height ray. -/
theorem higherSourceBarProfile_continuousOn (n : ℕ) (z : ℂ) :
    ContinuousOn (higherSourceBarProfile n z) (Ioi 0) := by
  have hc : CuspSubexponential rationalSourceResidualFourierCoefficient :=
    rationalSourceResidualFourierCoefficient_subexponential
  apply (cubicJetProfile_continuousOn n (hc.holWeight_pow (n + 1)) 1 one_pos z).congr
  intro v hv
  exact higherSourceBarProfile_eq_cubicJetProfile n z v hv

/-- All normalized dual cusp jets are continuous on the positive height ray. -/
theorem higherSourceZFamily_continuousOn (n : ℕ) (j : Fin 3) (z : ℂ) :
    ContinuousOn (higherSourceZFamily n j z) (Ioi 0) := by
  have hc : CuspSubexponential (sourceCuspBarCoefficient j) := sourceCuspBarCoefficient_subexponential j
  apply (continuousOn_const.mul (cubicJetProfile_continuousOn n (hc.antiholWeight_pow n)
    (sourceCuspScale j) (sourceCuspScale_pos j) z)).congr
  intro v hv
  exact higherSourceZFamily_eq_cubicJetProfile n j z v hv

/-- Every fixed initial jet retains exponential decay in height. -/
theorem higherSourceBarProfile_isBigO (n : ℕ) (z : ℂ) :
    higherSourceBarProfile n z =O[atTop]
      (fun v : ℝ => Real.exp (-(residualBesselDecayRate / 2) * v)) := by
  have hc : CuspSubexponential rationalSourceResidualFourierCoefficient :=
    rationalSourceResidualFourierCoefficient_subexponential
  have hb := cubicJetProfile_isBigO n (hc.holWeight_pow (n + 1)) 1 one_pos z
  simp only [mul_one] at hb
  apply hb.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
  exact (higherSourceBarProfile_eq_cubicJetProfile n z v hv).symm

/-- The decay rate at a dual cusp depends only on its width, not on jet order. -/
theorem higherSourceZFamily_isBigO (n : ℕ) (j : Fin 3) (z : ℂ) :
    higherSourceZFamily n j z =O[atTop]
      (fun v : ℝ => Real.exp (-(residualBesselDecayRate / (2 * sourceCuspScale j)) * v)) := by
  have hc : CuspSubexponential (sourceCuspBarCoefficient j) := sourceCuspBarCoefficient_subexponential j
  have hb := (cubicJetProfile_isBigO n (hc.antiholWeight_pow n)
    (sourceCuspScale j) (sourceCuspScale_pos j) z).const_mul_left (((sourceCuspScale j : ℂ)⁻¹) ^ n)
  apply hb.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
  exact (higherSourceZFamily_eq_cubicJetProfile n j z v hv).symm

/-- Both actual higher cusp profiles have entire Mellin transforms. -/
theorem SourceCuspDatum.higher_mellin_entire (d : SourceCuspDatum) (n : ℕ) :
    ((∀ s : ℂ, MellinConvergent (higherSourceBarProfile n d.point) s) ∧
      Differentiable ℂ (mellin (higherSourceBarProfile n d.point))) ∧
    ((∀ s : ℂ, MellinConvergent (higherSourceZFamily n d.index d.dualPoint) s) ∧
      Differentiable ℂ (mellin (higherSourceZFamily n d.index d.dualPoint))) := by
  have hA : d.jetMultiplier n ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [d.jetMultiplier_norm n]
    exact inv_ne_zero d.heightScale_pos.ne'
  apply cusp_mellin_entire_both _ _ _ hA d.heightScale
    (residualBesselDecayRate / 2) (residualBesselDecayRate / (2 * sourceCuspScale d.index))
    d.heightScale_pos (half_pos residualBesselDecayRate_pos)
    (div_pos residualBesselDecayRate_pos (mul_pos (by norm_num) (sourceCuspScale_pos d.index)))
    (higherSourceBarProfile_continuousOn n d.point)
    (higherSourceZFamily_continuousOn n d.index d.dualPoint)
    (higherSourceBarProfile_isBigO n d.point)
    (higherSourceZFamily_isBigO n d.index d.dualPoint)
  intro v hv
  rw [d.reflection_higher n v hv, reflectedCuspProfile, Complex.cpow_neg, Complex.cpow_ofNat]
  simp only [div_eq_mul_inv]
  ring

/-- The normalized actual angular Dirichlet transform is entire at every finite source cusp. -/
theorem SourceCuspDatum.angularSourceDirichletTransform_differentiable (d : SourceCuspDatum) (k : ℕ) :
    Differentiable ℂ (angularSourceDirichletTransform k d.point) := by
  have hi : Differentiable ℂ (fun s : ℂ =>
      inverseBesselMellinFactor (sourceCuspRadialScale 0) (s + (3 * k : ℕ))) :=
    (inverseBesselMellinFactor_differentiable _ (sourceCuspRadialScale_pos 0)).comp
      (differentiable_id.add_const _)
  have hm : Differentiable ℂ (fun s : ℂ => mellin (higherSourceBarProfile (6 * k) d.point) (2 * s)) :=
    (d.higher_mellin_entire (6 * k)).1.2.comp (differentiable_id.const_mul 2)
  exact (hi.mul hm).const_mul _

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
