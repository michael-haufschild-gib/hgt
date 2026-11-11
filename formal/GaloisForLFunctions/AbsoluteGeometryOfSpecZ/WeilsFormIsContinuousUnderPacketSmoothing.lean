import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.UnderTheRiemannHypothesisWeilsFormOfAStepPacketIsNonnegative

/-!
# Smoothing preserves the full Weil form

For bounded measurable packets of compact support and finite jump energy,
mollification converges in the full prime–Gamma–pole form. Jensen's inequality
dominates each smoothed jump density by the original density. This permits
finite negative families of step packets to be transferred to smooth tests.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Measurability of autocorrelation needs no continuity of the packet. -/
theorem measurable_packetAutocorr_of_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (packetAutocorr f) := by
  have hm : Measurable fun p : ℝ × ℝ => f p.2 * f (p.2 + p.1) :=
    (hf.comp measurable_snd).mul (hf.comp (measurable_snd.add measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_levyJump_of_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (levyJump f) := by
  have hω : Measurable _root_.RHTower.archLevyDensity := by
    unfold _root_.RHTower.archLevyDensity
    fun_prop
  exact (measurable_const.mul hω).mul
    (measurable_const.sub (measurable_packetAutocorr_of_measurable hf))

private theorem integrable_mollify_integrand (φ : ContDiffBump (0 : ℝ))
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ u, |f u| ≤ M) (u : ℝ) :
    Integrable (fun t => φ.normed volume t * f (u - t)) :=
  integrable_normed_mul φ (hf.comp (measurable_const.sub measurable_id)) (fun _ => hb _)

/-- Mollification respects finite-dimensional packet combinations. -/
theorem mollify_add_bounded (φ : ContDiffBump (0 : ℝ))
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {M N : ℝ} (hfb : ∀ u, |f u| ≤ M) (hgb : ∀ u, |g u| ≤ N) :
    mollify φ (f + g) = mollify φ f + mollify φ g := by
  funext u
  simp only [mollify_apply, Pi.add_apply, mul_add]
  exact integral_add (integrable_mollify_integrand φ hf hfb u)
    (integrable_mollify_integrand φ hg hgb u)

theorem mollify_sub_bounded (φ : ContDiffBump (0 : ℝ))
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {M N : ℝ} (hfb : ∀ u, |f u| ≤ M) (hgb : ∀ u, |g u| ≤ N) :
    mollify φ (f - g) = mollify φ f - mollify φ g := by
  funext u
  simp only [mollify_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_mollify_integrand φ hf hfb u)
    (integrable_mollify_integrand φ hg hgb u)

section Smoothing

variable {g : ℝ → ℝ} (hgm : Measurable g) {M l r : ℝ}
    (hgb : ∀ u, |g u| ≤ M) (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)

include hgm hgb hsupp

/-- Jensen domination and convergence of autocorrelation give convergence of
the entire jump integral, including both singular and infinite tails. -/
theorem tendsto_integral_levyJump_mollify
    (hJ : IntegrableOn (levyJump g) (Set.Ioi 0)) :
    Tendsto (fun i : ℕ => ∫ x in Set.Ioi 0, levyJump (mollify (shrinkingBump i) g) x)
      atTop (𝓝 (∫ x in Set.Ioi 0, levyJump g x)) := by
  refine tendsto_integral_of_dominated_convergence (levyJump g) (fun i => ?_) hJ
    (fun i => ?_) ?_
  · have hm := measurable_levyJump_of_measurable
      (contDiff_mollify (shrinkingBump i) hgm hgb hsupp).continuous.measurable
    exact hm.aestronglyMeasurable.restrict
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hnn := levyJump_nonneg
      (contDiff_mollify (shrinkingBump i) hgm hgb hsupp).continuous
      (hasCompactSupport_mollify (shrinkingBump i) hsupp) hx
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, levyJump, levyJump]
    exact mul_le_mul_of_nonneg_left
      (packetAutocorr_mollify_sub_le (shrinkingBump i) hgm hgb hsupp x)
      (by have := _root_.RHTower.archLevyDensity_pos hx; positivity)
  · exact Eventually.of_forall fun x =>
      ((tendsto_packetAutocorr_mollify hgm hgb hsupp 0).sub
        (tendsto_packetAutocorr_mollify hgm hgb hsupp x)).const_mul
        (2 * _root_.RHTower.archLevyDensity x)

/-- Finite-energy bounded packets are limits of smooth packets in the full
Weil quadratic form, with no sign hypothesis. -/
theorem tendsto_packetForm_mollify (Q : ℕ)
    (hJ : IntegrableOn (levyJump g) (Set.Ioi 0)) :
    Tendsto (fun i : ℕ => packetForm Q (mollify (shrinkingBump i) g)) atTop
      (𝓝 (packetForm Q g)) := by
  have hminus := tendsto_integral_mollify_mul hgm hgb hsupp
    (e := fun u => Real.exp (-u / 2)) (by fun_prop)
  have hplus := tendsto_integral_mollify_mul hgm hgb hsupp
    (e := fun u => Real.exp (u / 2)) (by fun_prop)
  have hmass := tendsto_packetAutocorr_mollify hgm hgb hsupp 0
  have hcontacts : Tendsto (fun i : ℕ => ∑ k ∈ Icc 2 Q,
      contactWeight k * packetAutocorr (mollify (shrinkingBump i) g) (Real.log k)) atTop
      (𝓝 (∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k))) :=
    tendsto_finsetSum _ fun k _ =>
      (tendsto_packetAutocorr_mollify hgm hgb hsupp (Real.log k)).const_mul (contactWeight k)
  have hjump := tendsto_integral_levyJump_mollify hgm hgb hsupp hJ
  exact (((hminus.mul hplus).const_mul 2).add
    ((hmass.const_mul (EF.gammaBracket 0)).add hjump)).sub
      (hcontacts.const_mul 2)

/-- Once the smoothing radius is smaller than the spare support margin,
the truncated contact form includes every contact of the smoothed packet. -/
theorem eventually_zeroSum_mollify_eq_packetForm {Q : ℕ}
    (hQ : r - l < Real.log ((Q : ℝ) + 1)) :
    ∀ᶠ i : ℕ in atTop,
      zeroSum (mollify (shrinkingBump i) g) = packetForm Q (mollify (shrinkingBump i) g) := by
  have hsmall : ∀ᶠ i : ℕ in atTop,
      2 * (shrinkingBump i).rOut ≤ Real.log ((Q : ℝ) + 1) - (r - l) := by
    have ht : Tendsto (fun i : ℕ => 2 * (shrinkingBump i).rOut) atTop (𝓝 (2 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at ht
    exact ht.eventually (Iic_mem_nhds (sub_pos.mpr hQ))
  filter_upwards [hsmall] with i hi
  apply zeroSum_eq_packetForm (contDiff_mollify (shrinkingBump i) hgm hgb hsupp)
    (hasCompactSupport_mollify (shrinkingBump i) hsupp)
  intro n hn
  refine packetAutocorr_eq_zero_of_support (mollify_ne_zero (shrinkingBump i) hsupp) ?_
  have hlog : Real.log ((Q : ℝ) + 1) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn)
  linarith only [hi, hlog]

/-- The zero-side quadratic forms of smooth approximants converge to the
full form of a bounded finite-energy packet. -/
theorem tendsto_zeroSum_mollify {Q : ℕ}
    (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJ : IntegrableOn (levyJump g) (Set.Ioi 0)) :
    Tendsto (fun i : ℕ => zeroSum (mollify (shrinkingBump i) g)) atTop
      (𝓝 (packetForm Q g)) := by
  apply (tendsto_packetForm_mollify hgm hgb hsupp Q hJ).congr'
  filter_upwards [eventually_zeroSum_mollify_eq_packetForm hgm hgb hsupp hQ] with i hi
  exact hi.symm

end Smoothing

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
