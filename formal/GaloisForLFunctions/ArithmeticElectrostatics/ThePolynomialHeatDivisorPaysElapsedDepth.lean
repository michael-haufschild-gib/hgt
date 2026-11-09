import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireSeparableApproximation
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionIsContinuous
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionHasItsDerivative

/-!
# Every surviving polynomial heat root pays elapsed depth

For every positive exponent, the upper-root sum of `(Im z² + 2t)^q`
is bounded by its initial depth moment. Constant real perturbations remove
initial multiple roots. A continuous weight vanishing on the real axis
passes the inequality to the limit without assuming continuity of the count.
-/

open Polynomial Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Constant real perturbations approaching zero avoid every multiple root. -/
theorem exists_separable_constant_perturbations {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ a : ℕ → ℝ, Tendsto a atTop (𝓝 0) ∧
      ∀ n, (p + C (a n)).Separable ∧ p + C (a n) ≠ 0 := by
  by_cases hd : p.derivative = 0
  · have hpc := Polynomial.eq_C_of_derivative_eq_zero hd
    have hc : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp
      rw [hpc, hz, C_0]
    have hs : p.Separable := by
      rw [hpc, Polynomial.separable_C]
      exact isUnit_iff_ne_zero.mpr hc
    refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => ?_⟩
    simpa only [C_0, add_zero] using And.intro hs hp
  · have hW : Polynomial.wronskian p 1 ≠ 0 := by
      simpa only [Polynomial.wronskian, derivative_one, mul_zero, mul_one,
        zero_sub, neg_ne_zero] using hd
    let bad : Set ℝ := (fun t : ℝ => (t : ℂ)) ⁻¹'
      (RiemannGaussian.polynomialPencilBadParameterFinset p 1 : Set ℂ)
    have hbad : bad.Finite :=
      (RiemannGaussian.polynomialPencilBadParameterFinset p 1).finite_toSet.preimage
        Complex.ofReal_injective.injOn
    have hex (n : ℕ) : ∃ a : ℝ, 0 < a ∧ a < 1 / ((n : ℝ) + 1) ∧
        (p + C a).Separable := by
      have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨a, ha, hnot⟩ := (Set.Ioo_infinite hε).exists_notMem_finite hbad
      refine ⟨a, ha.1, ha.2, ?_⟩
      simpa only [mul_one] using
        RiemannGaussian.polynomialPencil_separable_of_parameter_not_mem
          Polynomial.separable_one hW hnot
    choose a ha0 ha1 has using hex
    have ha : Tendsto a atTop (𝓝 0) := squeeze_zero
      (fun n => (ha0 n).le) (fun n => (ha1 n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨a, ha, fun n => ⟨has n, ?_⟩⟩
    intro hn
    have h := congrArg Polynomial.derivative hn
    simp only [derivative_add, derivative_C, add_zero, derivative_zero] at h
    exact hd h

/-- A real-axis-vanishing continuous minorant agrees with the elapsed weight
on any prescribed finite nonreal set. -/
theorem exists_elapsedDepth_cutoff (S : Finset ℂ)
    (hS : ∀ z ∈ S, z.im ≠ 0) {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    ∃ Ψ : ℂ → ℝ, Continuous Ψ ∧ (∀ z, 0 ≤ Ψ z) ∧
      (∀ z, z.im = 0 → Ψ z = 0) ∧
      (∀ z, Ψ z ≤ (z.im ^ 2 + c) ^ q) ∧
      ∀ z ∈ S, Ψ z = (z.im ^ 2 + c) ^ q := by
  obtain ⟨δ, hδ, hδS⟩ := S.finite_toSet.isCompact.exists_forall_le'
    Complex.continuous_im.abs.continuousOn (fun z hz => abs_pos.mpr (hS z hz))
  let Ψ : ℂ → ℝ := fun z => min 1 (|z.im| / δ) * (z.im ^ 2 + c) ^ q
  have hweight : Continuous (fun z : ℂ => (z.im ^ 2 + c) ^ q) :=
    ((Complex.continuous_im.pow 2).add continuous_const).rpow_const (fun _ => Or.inr hq)
  have hweight0 (z : ℂ) : 0 ≤ (z.im ^ 2 + c) ^ q :=
    Real.rpow_nonneg (add_nonneg (sq_nonneg _) hc) q
  refine ⟨Ψ, (continuous_const.min (Complex.continuous_im.abs.div_const δ)).mul hweight,
    fun z => mul_nonneg (le_min zero_le_one (div_nonneg (abs_nonneg _) hδ.le)) (hweight0 z),
    ?_, ?_, ?_⟩
  · intro z hz
    simp only [Ψ, hz, abs_zero, zero_div, min_eq_right zero_le_one, zero_mul]
  · intro z
    exact (mul_le_mul_of_nonneg_right (min_le_left 1 _) (hweight0 z)).trans_eq (one_mul _)
  · intro z hz
    have hmin : min 1 (|z.im| / δ) = 1 :=
      min_eq_left ((le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hδS z hz))
    simp only [Ψ, hmin, one_mul]

#print axioms exists_separable_constant_perturbations
#print axioms exists_elapsedDepth_cutoff

private theorem sum_map_eq_nonreal_filter (S : Multiset ℂ) (Ψ : ℂ → ℝ)
    (hreal : ∀ z, z.im = 0 → Ψ z = 0) :
    (S.map Ψ).sum = ((S.filter (fun z => z.im ≠ 0)).map Ψ).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    by_cases hz : z.im = 0
    · simp [hz, hreal z hz, ih]
    · simp [hz, ih]

private theorem sum_map_mono_on (S : Multiset ℂ) (F G : ℂ → ℝ)
    (h : ∀ z ∈ S, F z ≤ G z) : (S.map F).sum ≤ (S.map G).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (h z (Multiset.mem_cons_self z S))
      (ih (fun w hw => h w (Multiset.mem_cons_of_mem hw)))

/-- Real roots contribute nothing to a real-axis-vanishing minorant. -/
theorem sum_roots_real_vanishing_weight_le_elapsedMoment (p : ℝ[X]) (q t : ℝ)
    (Ψ : ℂ → ℝ) (hreal : ∀ z, z.im = 0 → Ψ z = 0)
    (hbound : ∀ z, Ψ z ≤ (z.im ^ 2 + 2 * t) ^ q) :
    ((((polyHeat t p).map ofRealHom).roots).map Ψ).sum ≤
      polynomialElapsedDepthMoment p q t := by
  rw [polynomialElapsedDepthMoment_eq_sum, sum_map_eq_nonreal_filter _ Ψ hreal]
  exact sum_map_mono_on _ _ _ (fun z _ => hbound z)

/-- The full nonreal elapsed moment never exceeds the initial depth moment,
including initial multiple roots and all later collisions. -/
theorem polynomial_elapsed_moment_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) :
    polynomialElapsedDepthMoment p q t ≤
      ((p.map ofRealHom).roots.map (fun z => (z.im ^ 2) ^ q)).sum := by
  classical
  obtain ⟨a, ha, hpa⟩ := exists_separable_constant_perturbations hp
  let Q := (polyHeat t p).map ofRealHom
  let S := (Q.roots.filter (fun z => z.im ≠ 0)).toFinset
  have hS (z : ℂ) (hz : z ∈ S) : z.im ≠ 0 :=
    (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
  obtain ⟨Ψ, hΨ, hΨ0, hΨreal, hΨle, hΨeq⟩ := exists_elapsedDepth_cutoff S hS
    hq.le (mul_nonneg zero_le_two ht)
  have hpC : p.map ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hp
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr
    (natDegree_polyHeat t hp).2
  have haC : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using ha.ofReal
  have hl := tendsto_sum_roots_add_C hQ haC hΨ hΨ0
  have hr : Tendsto
      (fun n => (((p.map ofRealHom) + C (a n : ℂ)).roots.map
        (fun z => (z.im ^ 2) ^ q)).sum) atTop
      (𝓝 ((p.map ofRealHom).roots.map (fun z => (z.im ^ 2) ^ q)).sum) := by
    simpa only [add_zero] using
      tendsto_sum_root_depth_powers_add_C hpC haC hq.le (le_refl (0 : ℝ))
  have hQn (n : ℕ) : (polyHeat t (p + C (a n))).map ofRealHom = Q + C (a n : ℂ) := by
    rw [polyHeat_add_constant, Polynomial.map_add, Polynomial.map_C]
    rfl
  have hcompare (n : ℕ) : ((Q + C (a n : ℂ)).roots.map Ψ).sum ≤
      (((p.map ofRealHom) + C (a n : ℂ)).roots.map (fun z => (z.im ^ 2) ^ q)).sum := by
    have hleft := sum_roots_real_vanishing_weight_le_elapsedMoment
      (p + C (a n)) q t Ψ hΨreal hΨle
    rw [hQn] at hleft
    have hright : polynomialElapsedDepthMoment (p + C (a n)) q t ≤
        (((p + C (a n)).map ofRealHom).roots.map (fun z => (z.im ^ 2) ^ q)).sum :=
      polynomial_elapsed_moment_le_initial_of_separable (hpa n).2 (hpa n).1.map hq ht
    exact hleft.trans (by
      simpa only [Polynomial.map_add, Polynomial.map_C, Complex.ofRealHom_eq_coe] using hright)
  have hfinal : (Q.roots.map Ψ).sum = polynomialElapsedDepthMoment p q t := by
    rw [polynomialElapsedDepthMoment_eq_sum, sum_map_eq_nonreal_filter _ Ψ hΨreal]
    apply congrArg Multiset.sum
    exact Multiset.map_congr rfl fun z hz => hΨeq z (Multiset.mem_toFinset.mpr hz)
  rw [← hfinal]
  exact le_of_tendsto_of_tendsto' hl hr hcompare

#print axioms polynomial_elapsed_moment_le_initial

/-- Conjugation splits the full elapsed moment into two equal upper-half sums. -/
theorem polynomialElapsedDepthMoment_eq_twice_upper (p : ℝ[X]) (q t : ℝ) :
    polynomialElapsedDepthMoment p q t =
      2 * ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => (z.im ^ 2 + 2 * t) ^ q)).sum := by
  let f : ℂ → ℝ := fun z => if z.im = 0 then 0 else (z.im ^ 2 + 2 * t) ^ q
  have hfreal (z : ℂ) (hz : z.im = 0) : f z = 0 := by simp only [f, hz, if_true]
  have hfeven (z : ℂ) : f (starRingEnd ℂ z) = f z := by
    simp only [f, Complex.conj_im, neg_eq_zero, neg_sq]
  have hM : polynomialElapsedDepthMoment p q t =
      ((((polyHeat t p).map ofRealHom).roots).map f).sum := by
    rw [polynomialElapsedDepthMoment_eq_sum, sum_map_eq_nonreal_filter _ f hfreal]
    apply congrArg Multiset.sum
    exact Multiset.map_congr rfl fun z hz => by
      simp only [f, if_neg (Multiset.mem_filter.mp hz).2]
  have hU : (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map f =
      (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => (z.im ^ 2 + 2 * t) ^ q) :=
    Multiset.map_congr rfl fun z hz => by
      have hi := RiemannGaussian.realPolynomialUpperRootMultiset_im_pos (polyHeat t p) z hz
      simp only [f, if_neg hi.ne']
  rw [hM, sum_realPolynomial_even_roots _ f hfeven hfreal, hU]

/-- Every surviving upper root pays `2t` inside each positive depth power. -/
theorem polynomial_upper_elapsed_moment_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) :
    ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => (z.im ^ 2 + 2 * t) ^ q)).sum ≤
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map
        (fun z => (z.im ^ 2) ^ q)).sum := by
  have hinit := sum_realPolynomial_even_roots p (fun z => (z.im ^ 2) ^ q)
    (fun z => by simp only [Complex.conj_im, neg_sq])
    (fun z hz => by simp only [hz, zero_pow two_ne_zero, Real.zero_rpow hq.ne'])
  have h := polynomial_elapsed_moment_le_initial hp hq ht
  rw [polynomialElapsedDepthMoment_eq_twice_upper, hinit] at h
  linarith only [h]

#print axioms polynomialElapsedDepthMoment_eq_twice_upper
#print axioms polynomial_upper_elapsed_moment_le_initial

end
end GaloisForLFunctions.ArithmeticElectrostatics
