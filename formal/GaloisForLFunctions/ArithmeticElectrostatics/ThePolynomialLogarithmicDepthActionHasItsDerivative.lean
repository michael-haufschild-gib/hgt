import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionHasItsDerivative
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialLogarithmicDepthActionIsContinuous
import GaloisForLFunctions.ArithmeticElectrostatics.TheConjugatePacketPaysLogarithmicDepth

/-!
# Polynomial logarithmic depth velocity and initial comparison

Simple heat-root branches differentiate the corrected logarithmic action.
Complete conjugate-packet work bounds its derivative by the negative baseline
rate times the nonreal count. Freezing the final count gives a continuous
comparison through the finite collision set of an initially separable polynomial.
-/

open Polynomial Complex Filter Topology Set
open GaloisForLFunctions.ZeroConfigurationGeometry GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Twice the derivative of the logarithmic profile with respect to squared depth. -/
def elapsedLogDepthClockRate (r A u : ℝ) : ℝ :=
  2 * r * u ^ (r - 1) / (A + u ^ r)

/-- Corrected logarithmic rate at a polynomial heat zero. -/
def polynomialElapsedLogDepthRate (p : ℂ[X]) (r A t : ℝ) (z : ℂ) : ℝ :=
  elapsedLogDepthClockRate r A (z.im ^ 2 + 2 * t) - elapsedLogDepthClockRate r A (2 * t) +
    elapsedLogDepthWeight r A (2 * t) z.im *
      ((heatFlow (t : ℂ) p).derivative.derivative.eval z /
        (heatFlow (t : ℂ) p).derivative.eval z).im

private theorem elapsedLogDepth_baseline_hasDerivAt {t r A : ℝ}
    (ht : 0 < t) (hA : 0 < A) :
    HasDerivAt (fun s => elapsedLogDepthProfile r A (2 * s))
      (elapsedLogDepthClockRate r A (2 * t)) t := by
  have h := (elapsedLogDepth_hasDerivWithinAt (s := univ)
    (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt ht hA (r := r)).hasDerivAt Filter.univ_mem
  simpa only [zero_pow two_ne_zero, zero_add, mul_zero, add_zero,
    elapsedLogDepthClockRate] using h

private theorem corrected_polynomial_logDepth_hasDerivAt
    {y : ℝ → ℝ} {v t r A : ℝ} (ht : 0 < t) (hA : 0 < A) (hy : HasDerivAt y v t) :
    HasDerivAt (fun s => elapsedLogDepthProfile r A (y s ^ 2 + 2 * s) -
        elapsedLogDepthProfile r A (2 * s))
      (elapsedLogDepthClockRate r A (y t ^ 2 + 2 * t) -
        elapsedLogDepthClockRate r A (2 * t) + elapsedLogDepthWeight r A (2 * t) (y t) * v) t := by
  have h := (elapsedLogDepth_hasDerivWithinAt (s := univ) hy.hasDerivWithinAt ht hA
    (r := r)).hasDerivAt Filter.univ_mem
  have hd := h.sub (elapsedLogDepth_baseline_hasDerivAt (r := r) ht hA)
  apply hd.congr_deriv
  unfold elapsedLogDepthClockRate
  ring

/-- The corrected action differentiates by summing the actual root velocities. -/
theorem polynomialElapsedLogDepthAction_hasDerivAt_of_separable
    {p : ℂ[X]} (hp : p ≠ 0) {t r A : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hs : (heatFlow (t : ℂ) p).Separable) :
    HasDerivAt (polynomialElapsedLogDepthAction p r A)
      (∑ z ∈ (heatFlow (t : ℂ) p).roots.toFinset, polynomialElapsedLogDepthRate p r A t z) t := by
  classical
  let S := (heatFlow (t : ℂ) p).roots.toFinset
  obtain ⟨g, hg0, hgd, hroot⟩ := exists_polynomial_heat_root_enumeration hp hs
  have hd (a : S) : HasDerivAt
      (fun s => elapsedLogDepthProfile r A ((g a s).im ^ 2 + 2 * s) -
        elapsedLogDepthProfile r A (2 * s))
      (polynomialElapsedLogDepthRate p r A t a) t := by
    have him : HasDerivAt (fun s => (g a s).im)
        ((heatFlow (t : ℂ) p).derivative.derivative.eval (a : ℂ) /
          (heatFlow (t : ℂ) p).derivative.eval (a : ℂ)).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hgd a)
    simpa only [polynomialElapsedLogDepthRate, hg0] using
      corrected_polynomial_logDepth_hasDerivAt (r := r) ht hA him
  have hds := HasDerivAt.sum (u := S.attach) (fun a _ => hd a)
  have heq : polynomialElapsedLogDepthAction p r A =ᶠ[𝓝 t]
      (fun s => ∑ a ∈ S.attach, (elapsedLogDepthProfile r A ((g a s).im ^ 2 + 2 * s) -
        elapsedLogDepthProfile r A (2 * s))) := by
    filter_upwards [hroot] with s hs'
    unfold polynomialElapsedLogDepthAction
    rw [hs', Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have hfun : (∑ a ∈ S.attach,
      fun s => elapsedLogDepthProfile r A ((g a s).im ^ 2 + 2 * s) -
        elapsedLogDepthProfile r A (2 * s)) =
      (fun s => ∑ a ∈ S.attach, (elapsedLogDepthProfile r A ((g a s).im ^ 2 + 2 * s) -
        elapsedLogDepthProfile r A (2 * s))) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun] at hds
  have hder := hds.congr_of_eventuallyEq heq
  rw [Finset.sum_attach S (polynomialElapsedLogDepthRate p r A t)] at hder
  exact hder

private theorem eval_realPolynomial_conjugate (P : ℝ[X]) (z : ℂ) :
    (P.map ofRealHom).eval (starRingEnd ℂ z) = starRingEnd ℂ ((P.map ofRealHom).eval z) := by
  simpa only [RiemannGaussian.conjugatePolynomial_real_map, Complex.conj_conj] using
    RiemannGaussian.conjugatePolynomial_eval (P.map ofRealHom) (starRingEnd ℂ z)

private theorem polynomialElapsedLogDepthRate_conj (p : ℝ[X]) (r A t : ℝ) (z : ℂ) :
    polynomialElapsedLogDepthRate (p.map ofRealHom) r A t (starRingEnd ℂ z) =
      polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z := by
  unfold polynomialElapsedLogDepthRate elapsedLogDepthWeight elapsedDepthWeight
  simp only [heatFlow_ofReal, Polynomial.derivative_map, eval_realPolynomial_conjugate,
    ← map_div₀, Complex.conj_im, neg_sq]
  ring

private theorem polynomialElapsedLogDepthRate_real (p : ℂ[X]) (r A t : ℝ) {z : ℂ}
    (hz : z.im = 0) : polynomialElapsedLogDepthRate p r A t z = 0 := by
  simp only [polynomialElapsedLogDepthRate, elapsedLogDepthWeight, elapsedDepthWeight, hz,
    zero_pow two_ne_zero, zero_add, sub_self, mul_zero, zero_mul, zero_div, add_zero]

/-- Every nonreal multiplicity copy pays the logarithmic baseline rate. -/
theorem polynomialElapsedLogDepthRate_sum_le {p : ℝ[X]} {t r A : ℝ}
    (ht : 0 < t) (hr : 0 ≤ r) (hA : 0 < A)
    (hs : (heatFlow (t : ℂ) (p.map ofRealHom)).Separable) :
    (∑ z ∈ (heatFlow (t : ℂ) (p.map ofRealHom)).roots.toFinset,
      polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z) ≤
      -elapsedLogDepthClockRate r A (2 * t) * (nonrealRootCount (polyHeat t p) : ℝ) := by
  classical
  let S := (heatFlow (t : ℂ) (p.map ofRealHom)).roots.toFinset
  let U := S.filter (fun z => 0 < z.im)
  have hSv : (heatFlow (t : ℂ) (p.map ofRealHom)).roots = S.val := by
    dsimp only [S]
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots hs)]
  have hU : RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p) = U.val := by
    rw [RiemannGaussian.realPolynomialUpperRootMultiset, ← heatFlow_ofReal, hSv]
    rfl
  have hconj (z : ℂ) (hz : z ∈ S) : starRingEnd ℂ z ∈ S := by
    apply Multiset.mem_toFinset.mpr
    rw [heatFlow_ofReal, ← RiemannGaussian.realPolynomial_roots_map_conj]
    apply Multiset.mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    rw [← heatFlow_ofReal]
    exact Multiset.mem_toFinset.mp hz
  have hcount : nonrealRootCount (polyHeat t p) = 2 * U.card := by
    have hc := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card
      (polyHeat t p)
    rw [realPolynomialRealRootMultiset_eq_map_roots, Multiset.card_map, hU] at hc
    unfold nonrealRootCount
    change (polyHeat t p).roots.card + 2 * U.card = (polyHeat t p).natDegree at hc
    omega
  have hhalf : (∑ z ∈ S, polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z) =
      2 * ∑ z ∈ U, polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z := by
    have h := sum_realPolynomial_even_roots (polyHeat t p)
      (polynomialElapsedLogDepthRate (p.map ofRealHom) r A t)
      (polynomialElapsedLogDepthRate_conj p r A t)
      (fun z hz => polynomialElapsedLogDepthRate_real (p.map ofRealHom) r A t hz)
    rw [← heatFlow_ofReal, hSv, hU] at h
    exact h
  have hquot (z : ℂ) (hz : z ∈ S) :
      (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.derivative.eval z /
          (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.eval z =
        2 * ∑ b ∈ S, (z - b)⁻¹ := by
    have hzm := Multiset.mem_toFinset.mp hz
    have hp' := Polynomial.ne_zero_of_mem_roots hzm
    have hz' := (mem_roots hp').mp hzm
    have hd : (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.eval z ≠ 0 := by
      simpa only [eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) hz'
    exact polynomial_heat_quotient_eq_reciprocal_field (Polynomial.nodup_roots hs) hzm hd
  have hupper := elapsedLogDepth_conjugation_closed_drift_nonpos S hconj hr hA
    (mul_nonneg zero_le_two ht.le)
  change (∑ z ∈ U, (elapsedLogDepthClockRate r A (z.im ^ 2 + 2 * t) +
    elapsedLogDepthWeight r A (2 * t) z.im * (2 * ∑ b ∈ S, (z - b)⁻¹).im)) ≤ 0 at hupper
  have hsum : (∑ z ∈ U, polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z) =
      (∑ z ∈ U, (elapsedLogDepthClockRate r A (z.im ^ 2 + 2 * t) +
        elapsedLogDepthWeight r A (2 * t) z.im * (2 * ∑ b ∈ S, (z - b)⁻¹).im)) -
        elapsedLogDepthClockRate r A (2 * t) * U.card := by
    calc
      _ = ∑ z ∈ U, ((elapsedLogDepthClockRate r A (z.im ^ 2 + 2 * t) +
          elapsedLogDepthWeight r A (2 * t) z.im * (2 * ∑ b ∈ S, (z - b)⁻¹).im) -
          elapsedLogDepthClockRate r A (2 * t)) := by
        apply Finset.sum_congr rfl
        intro z hz
        unfold polynomialElapsedLogDepthRate
        rw [hquot z (Finset.mem_filter.mp hz).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  change (∑ z ∈ S, polynomialElapsedLogDepthRate (p.map ofRealHom) r A t z) ≤ _
  rw [hhalf, hsum, hcount]
  push_cast
  nlinarith only [hupper]

/-- An initially separable polynomial obeys the logarithmic budget through all later collisions. -/
theorem polynomial_log_elapsed_moment_le_initial_of_separable {p : ℝ[X]} (hp : p ≠ 0)
    (hs : (p.map ofRealHom).Separable) {r A b : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hb : 0 ≤ b) :
    polynomialElapsedLogDepthAction (p.map ofRealHom) r A b +
        elapsedLogDepthProfile r A (2 * b) * (nonrealRootCount (polyHeat b p) : ℝ) ≤
      ((p.map ofRealHom).roots.map (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
  have hpC : p.map ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hp
  have hbase : ContinuousOn (fun s : ℝ => elapsedLogDepthProfile r A (2 * s)) (Ici 0) := by
    have hclock : Continuous (fun s : ℝ => 2 * s) := by fun_prop
    have h := (continuous_elapsedLogDepthProfile_clamped hr.le hA).comp hclock
    apply h.continuousOn.congr
    intro s hs'
    exact congrArg (elapsedLogDepthProfile r A)
      (max_eq_left (mul_nonneg zero_le_two (show 0 ≤ s from hs'))).symm
  have hc : ContinuousOn
      (fun s => polynomialElapsedLogDepthAction (p.map ofRealHom) r A s +
        elapsedLogDepthProfile r A (2 * s) * (nonrealRootCount (polyHeat b p) : ℝ)) (Icc 0 b) :=
    ((continuousOn_polynomialElapsedLogDepthAction hpC hr.le hA).mono
      (fun _ hs' => hs'.1)).add ((hbase.mono (fun _ hs' => hs'.1)).mul_const _)
  have h := le_initial_of_forward_intervals_interior hb hc (by
    intro t ht
    obtain ⟨δ, hδ, hreg⟩ := exists_separable_polynomial_heat_forward hpC hs t
    refine ⟨δ, hδ, fun s hs' hsb => ?_⟩
    have hs0 : 0 < s := ht.1.trans hs'.1
    have hD := polynomialElapsedLogDepthAction_hasDerivAt_of_separable
      (r := r) hpC hs0 hA (hreg s hs')
    have hbound := polynomialElapsedLogDepthRate_sum_le hs0 hr.le hA (hreg s hs')
    have hcount : (nonrealRootCount (polyHeat b p) : ℝ) ≤
        (nonrealRootCount (polyHeat s p) : ℝ) := by
      exact_mod_cast antitone_nonrealRootCount_polyHeat hp hsb.le
    have hcoef : 0 ≤ elapsedLogDepthClockRate r A (2 * s) := by
      unfold elapsedLogDepthClockRate
      exact div_nonneg (mul_nonneg (mul_nonneg zero_le_two hr.le)
        (Real.rpow_nonneg (by positivity) _))
        (add_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
    have hpay := mul_le_mul_of_nonneg_left hcount hcoef
    refine ⟨_, (hD.add ((elapsedLogDepth_baseline_hasDerivAt (r := r) hs0 hA).mul_const
      (nonrealRootCount (polyHeat b p) : ℝ))).hasDerivWithinAt, ?_⟩
    nlinarith only [hbound, hpay])
  simpa only [polynomialElapsedLogDepthAction_zero _ hr, mul_zero,
    elapsedLogDepthProfile_zero hr, zero_mul, add_zero] using h

#print axioms polynomialElapsedLogDepthAction_hasDerivAt_of_separable
#print axioms polynomialElapsedLogDepthRate_sum_le
#print axioms polynomial_log_elapsed_moment_le_initial_of_separable

end
end GaloisForLFunctions.ArithmeticElectrostatics
