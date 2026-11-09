import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialLogarithmicDepthActionHasItsDerivative
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatDivisorPaysElapsedDepth

/-!
# The polynomial logarithmic depth budget

Every nonzero real polynomial satisfies the elapsed budget for
`log(A+u^r)−log A`, with `A>0` and `r>0`. Constant perturbations remove
initial multiple roots. A continuous minorant vanishing on the real axis
passes the nonreal moment to the limit without assuming count continuity.
-/

open Polynomial Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- A nonnegative continuous weight has a real-axis-vanishing minorant
agreeing on any prescribed finite nonreal set. -/
theorem exists_real_axis_vanishing_minorant (S : Finset ℂ)
    (hS : ∀ z ∈ S, z.im ≠ 0) (F : ℂ → ℝ) (hF : Continuous F) (hF0 : ∀ z, 0 ≤ F z) :
    ∃ Ψ : ℂ → ℝ, Continuous Ψ ∧ (∀ z, 0 ≤ Ψ z) ∧
      (∀ z, z.im = 0 → Ψ z = 0) ∧ (∀ z, Ψ z ≤ F z) ∧ ∀ z ∈ S, Ψ z = F z := by
  obtain ⟨θ, hθ, hθ0, hθreal, hθle, hθeq⟩ := exists_elapsedDepth_cutoff S hS
    (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  simp only [Real.rpow_zero] at hθle hθeq
  refine ⟨fun z => θ z * F z, hθ.mul hF, fun z => mul_nonneg (hθ0 z) (hF0 z),
    fun z hz => by simp only [hθreal z hz, zero_mul], ?_, ?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right (hθle z) (hF0 z)).trans_eq (one_mul _)
  · intro z hz
    simp only [hθeq z hz, one_mul]

/-- The logarithmic elapsed moment of the complete nonreal polynomial divisor. -/
def polynomialElapsedLogDepthMoment (p : ℝ[X]) (r A t : ℝ) : ℝ :=
  ((((polyHeat t p).map ofRealHom).roots.filter (fun z => z.im ≠ 0)).map
    (fun z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t))).sum

private theorem sum_corrected_profile_add_nonreal_count (S : Multiset ℂ) (F : ℝ → ℝ) (c : ℝ) :
    (S.map (fun z => F (z.im ^ 2 + c) - F c)).sum +
        F c * ((S.filter (fun z => z.im ≠ 0)).card : ℝ) =
      ((S.filter (fun z => z.im ≠ 0)).map (fun z => F (z.im ^ 2 + c))).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    by_cases hz : z.im = 0
    · simpa only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons,
        hz, ne_eq, not_true_eq_false, if_false, zero_pow two_ne_zero,
        zero_add, sub_self] using ih
    · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons,
        hz, ne_eq, not_false_eq_true, if_true, Multiset.map_add, Multiset.sum_add,
        Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_add, Multiset.card_singleton,
        Nat.cast_add, Nat.cast_one]
      linear_combination ih

/-- Restoring the nonreal baseline recovers the full logarithmic moment. -/
theorem polynomialElapsedLogDepthMoment_eq_action (p : ℝ[X]) (r A t : ℝ) :
    polynomialElapsedLogDepthMoment p r A t =
      polynomialElapsedLogDepthAction (p.map ofRealHom) r A t +
        elapsedLogDepthProfile r A (2 * t) * (nonrealRootCount (polyHeat t p) : ℝ) := by
  rw [polynomialElapsedLogDepthMoment, polynomialElapsedLogDepthAction,
    nonrealRootCount_eq, heatFlow_ofReal]
  exact (sum_corrected_profile_add_nonreal_count _ (elapsedLogDepthProfile r A) (2 * t)).symm

/-- A real-axis-vanishing minorant is bounded by the full nonreal profile sum. -/
theorem sum_weight_le_nonreal_profile (S : Multiset ℂ) (Ψ F : ℂ → ℝ)
    (hreal : ∀ z, z.im = 0 → Ψ z = 0) (hbound : ∀ z, Ψ z ≤ F z) :
    (S.map Ψ).sum ≤ ((S.filter (fun z => z.im ≠ 0)).map F).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    by_cases hz : z.im = 0
    · simpa [hz, hreal z hz] using ih
    · simpa [hz] using add_le_add (hbound z) ih

private theorem sum_map_eq_nonreal_filter (S : Multiset ℂ) (Ψ : ℂ → ℝ)
    (hreal : ∀ z, z.im = 0 → Ψ z = 0) :
    (S.map Ψ).sum = ((S.filter (fun z => z.im ≠ 0)).map Ψ).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    by_cases hz : z.im = 0
    · simp [hz, hreal z hz, ih]
    · simp [hz, ih]

/-- The logarithmic root weight is continuous at the real axis. -/
theorem continuous_elapsedLogDepth_height_weight {r A c : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A) (hc : 0 ≤ c) :
    Continuous (fun z : ℂ => elapsedLogDepthProfile r A (z.im ^ 2 + c)) := by
  have hbase : Continuous (fun z : ℂ => z.im ^ 2 + c) :=
    (Complex.continuous_im.pow 2).add continuous_const
  have h := (continuous_elapsedLogDepthProfile_clamped hr hA).comp hbase
  apply h.congr
  intro z
  exact congrArg (elapsedLogDepthProfile r A) (max_eq_left (add_nonneg (sq_nonneg _) hc))

/-- Continuous minorants can be tested against the full logarithmic budget. -/
theorem sum_roots_real_vanishing_weight_le_logElapsedMoment (p : ℝ[X]) (r A t : ℝ)
    (Ψ : ℂ → ℝ) (hreal : ∀ z, z.im = 0 → Ψ z = 0)
    (hbound : ∀ z, Ψ z ≤ elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t)) :
    ((((polyHeat t p).map ofRealHom).roots).map Ψ).sum ≤
      polynomialElapsedLogDepthMoment p r A t :=
  sum_weight_le_nonreal_profile _ Ψ _ hreal hbound

/-- The initial logarithmic budget controls every later fibre, including initial multiple roots. -/
theorem polynomial_log_elapsed_moment_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {r A t : ℝ} (hr : 0 < r) (hA : 0 < A) (ht : 0 ≤ t) :
    polynomialElapsedLogDepthMoment p r A t ≤
      ((p.map ofRealHom).roots.map (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
  classical
  obtain ⟨a, ha, hpa⟩ := exists_separable_constant_perturbations hp
  let Q := (polyHeat t p).map ofRealHom
  let S := (Q.roots.filter (fun z => z.im ≠ 0)).toFinset
  have hS (z : ℂ) (hz : z ∈ S) : z.im ≠ 0 :=
    (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
  obtain ⟨Ψ, hΨ, hΨ0, hΨreal, hΨle, hΨeq⟩ := exists_real_axis_vanishing_minorant S hS
    (fun z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t))
    (continuous_elapsedLogDepth_height_weight hr.le hA (mul_nonneg zero_le_two ht))
    (fun z => elapsedLogDepthProfile_nonneg hA (by positivity) r)
  have hpC : p.map ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hp
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr
    (natDegree_polyHeat t hp).2
  have haC : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using ha.ofReal
  have hl := tendsto_sum_roots_add_C hQ haC hΨ hΨ0
  have hinit : Continuous (fun z : ℂ => elapsedLogDepthProfile r A (z.im ^ 2)) := by
    simpa only [add_zero] using continuous_elapsedLogDepth_height_weight hr.le hA (le_refl (0 : ℝ))
  have hrconv := tendsto_sum_roots_add_C hpC haC hinit
    (fun z => elapsedLogDepthProfile_nonneg hA (sq_nonneg _) r)
  have hQn (n : ℕ) : (polyHeat t (p + C (a n))).map ofRealHom = Q + C (a n : ℂ) := by
    rw [polyHeat_add_constant, Polynomial.map_add, Polynomial.map_C]
    rfl
  have hcompare (n : ℕ) : ((Q + C (a n : ℂ)).roots.map Ψ).sum ≤
      (((p.map ofRealHom) + C (a n : ℂ)).roots.map
        (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
    have hleft := sum_roots_real_vanishing_weight_le_logElapsedMoment
      (p + C (a n)) r A t Ψ hΨreal hΨle
    rw [hQn] at hleft
    have hright : polynomialElapsedLogDepthMoment (p + C (a n)) r A t ≤
        (((p + C (a n)).map ofRealHom).roots.map
          (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
      rw [polynomialElapsedLogDepthMoment_eq_action]
      exact polynomial_log_elapsed_moment_le_initial_of_separable
        (hpa n).2 (hpa n).1.map hr hA ht
    exact hleft.trans (by
      simpa only [Polynomial.map_add, Polynomial.map_C, Complex.ofRealHom_eq_coe] using hright)
  have hfinal : (Q.roots.map Ψ).sum = polynomialElapsedLogDepthMoment p r A t := by
    rw [polynomialElapsedLogDepthMoment, sum_map_eq_nonreal_filter _ Ψ hΨreal]
    apply congrArg Multiset.sum
    exact Multiset.map_congr rfl fun z hz => hΨeq z (Multiset.mem_toFinset.mpr hz)
  rw [← hfinal]
  exact le_of_tendsto_of_tendsto' hl hrconv hcompare

/-- Conjugation splits the logarithmic moment into equal halves. -/
theorem polynomialElapsedLogDepthMoment_eq_twice_upper (p : ℝ[X]) (r A t : ℝ) :
    polynomialElapsedLogDepthMoment p r A t =
      2 * ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t))).sum := by
  let f : ℂ → ℝ := fun z => if z.im = 0 then 0 else elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t)
  have hfreal (z : ℂ) (hz : z.im = 0) : f z = 0 := by simp only [f, hz, if_true]
  have hfeven (z : ℂ) : f (starRingEnd ℂ z) = f z := by
    simp only [f, Complex.conj_im, neg_eq_zero, neg_sq]
  have hM : polynomialElapsedLogDepthMoment p r A t =
      ((((polyHeat t p).map ofRealHom).roots).map f).sum := by
    rw [polynomialElapsedLogDepthMoment, sum_map_eq_nonreal_filter _ f hfreal]
    apply congrArg Multiset.sum
    exact Multiset.map_congr rfl fun z hz => by
      simp only [f, if_neg (Multiset.mem_filter.mp hz).2]
  have hU : (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map f =
      (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t)) :=
    Multiset.map_congr rfl fun z hz => by
      have hi := RiemannGaussian.realPolynomialUpperRootMultiset_im_pos (polyHeat t p) z hz
      simp only [f, if_neg hi.ne']
  rw [hM, sum_realPolynomial_even_roots _ f hfeven hfreal, hU]

/-- The upper polynomial divisor obeys the same initial logarithmic budget. -/
theorem polynomial_upper_log_elapsed_moment_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {r A t : ℝ} (hr : 0 < r) (hA : 0 < A) (ht : 0 ≤ t) :
    ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t))).sum ≤
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map
        (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
  have hinit := sum_realPolynomial_even_roots p (fun z => elapsedLogDepthProfile r A (z.im ^ 2))
    (fun z => by simp only [Complex.conj_im, neg_sq])
    (fun z hz => by simp only [hz, zero_pow two_ne_zero, elapsedLogDepthProfile_zero hr])
  have h := polynomial_log_elapsed_moment_le_initial hp hr hA ht
  rw [polynomialElapsedLogDepthMoment_eq_twice_upper, hinit] at h
  linarith only [h]

#print axioms exists_real_axis_vanishing_minorant
#print axioms polynomial_log_elapsed_moment_le_initial
#print axioms polynomial_upper_log_elapsed_moment_le_initial

end
end GaloisForLFunctions.ArithmeticElectrostatics
