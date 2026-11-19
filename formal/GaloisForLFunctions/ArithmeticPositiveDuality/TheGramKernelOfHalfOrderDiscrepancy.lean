import GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancyOfAtomicRows

/-!
# The off-diagonal Gram kernel of half-order discrepancy

At the critical order the square of a single atom has a logarithmic
divergence. Two atoms at distinct positive sites still have a finite
pairing, with a logarithm measuring their relative separation.
-/

noncomputable section

open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy

/-- Half-order atom observed on the positive half-line. -/
def halfAtom (p t : ℝ) : ℝ := if 0 < t then cutPower (-(1/2)) (p-t) else 0

private lemma kernel_eq_inv_sqrt {t : ℝ} (ht : 0 < t) :
    cutPower (-(1/2)) t = (Real.sqrt t)⁻¹ := by
  rw [cutPower, if_pos ht, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]

private def gramPrimitive (d u : ℝ) : ℝ :=
  2*Real.log (Real.sqrt u + Real.sqrt (u+d))

private lemma gram_derivative {d u : ℝ} (hd : 0 < d) (hu : 0 < u) :
    HasDerivAt (gramPrimitive d) ((Real.sqrt u)⁻¹ * (Real.sqrt (u+d))⁻¹) u := by
  have hs := Real.sqrt_pos_of_pos hu
  have ht := Real.sqrt_pos_of_pos (add_pos hu hd)
  have h₁ := Real.hasDerivAt_sqrt hu.ne'
  have h₂ := ((hasDerivAt_id u).add_const d).sqrt (add_pos hu hd).ne'
  have hh := (((h₁.add h₂).log (add_pos hs ht).ne').const_mul 2)
  refine hh.congr_deriv ?_
  change 2*((1/(2*Real.sqrt u)+1/(2*Real.sqrt (u+d)))/(Real.sqrt u+Real.sqrt (u+d))) = _
  field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
  ring

private lemma gram_primitive_integral {d p : ℝ} (hd : 0 < d) (hp : 0 ≤ p) :
    (∫ u in 0..p, (Real.sqrt u)⁻¹*(Real.sqrt (u+d))⁻¹) =
      gramPrimitive d p - gramPrimitive d 0 := by
  have hc : ContinuousOn (fun u : ℝ => (Real.sqrt (u+d))⁻¹) (Icc 0 p) := by
    apply (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousOn.inv₀
    intro u hu
    exact (Real.sqrt_pos_of_pos (add_pos_of_nonneg_of_pos hu.1 hd)).ne'
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := p)
    (r := -(1/2)) (by norm_num)).mul_continuousOn (by rwa [uIcc_of_le hp])
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp
  · apply continuousOn_const.mul
    apply ContinuousOn.log (Real.continuous_sqrt.add
      (Real.continuous_sqrt.comp (continuous_id.add continuous_const))).continuousOn
    intro u hu
    exact (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
      (Real.sqrt_pos_of_pos (add_pos_of_nonneg_of_pos hu.1 hd))).ne'
  · exact fun u hu => gram_derivative hd hu.1
  · apply hi.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    rw [uIoc_of_le hp] at hu
    simp only [Real.rpow_neg hu.1.le, ← Real.sqrt_eq_rpow]

/-- Two distinct positive atoms have a finite exact interaction even at half order. -/
theorem halfAtom_cross_integral {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (∫ t, halfAtom p t * halfAtom q t) =
      2*Real.log ((Real.sqrt p + Real.sqrt q) / Real.sqrt (q-p)) := by
  let F := fun u : ℝ => (Real.sqrt u)⁻¹*(Real.sqrt (u+(q-p)))⁻¹
  have heq (t : ℝ) : halfAtom p t * halfAtom q t =
      (Ioo 0 p).indicator (fun t => F (p-t)) t := by
    by_cases ht : t ∈ Ioo 0 p
    · rw [indicator_of_mem ht, halfAtom, halfAtom, if_pos ht.1, if_pos ht.1,
        kernel_eq_inv_sqrt (sub_pos.mpr ht.2), kernel_eq_inv_sqrt (sub_pos.mpr (ht.2.trans hpq))]
      simp only [F, show p-t+(q-p)=q-t by ring]
    · rw [indicator_of_notMem ht]
      by_cases h : 0 < t
      · have h' : ¬ t < p := fun h' => ht ⟨h,h'⟩
        simp [halfAtom, h, cutPower, sub_pos, h']
      · simp [halfAtom,h]
  simp_rw [heq, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hp.le]
  rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero,
    gram_primitive_integral (sub_pos.mpr hpq) hp.le]
  have hs := Real.sqrt_pos_of_pos (sub_pos.mpr hpq)
  rw [Real.log_div (add_pos (Real.sqrt_pos_of_pos hp)
    (Real.sqrt_pos_of_pos (hp.trans hpq))).ne' hs.ne']
  simp [gramPrimitive, show p+(q-p)=q by ring, mul_sub]

/-- Distinct sites contribute an absolutely integrable mixed term. -/
theorem halfAtom_cross_integrable {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    Integrable (fun t => halfAtom p t * halfAtom q t) := by
  by_contra h
  have he := halfAtom_cross_integral hp hpq
  rw [integral_undef h] at he
  have hs := Real.sqrt_pos_of_pos (sub_pos.mpr hpq)
  have hh : 1 < (Real.sqrt p + Real.sqrt q) / Real.sqrt (q-p) := by
    apply (one_lt_div hs).mpr
    exact (Real.sqrt_le_sqrt (sub_le_self _ hp.le)).trans_lt (lt_add_of_pos_left _ (Real.sqrt_pos_of_pos hp))
  exact (mul_pos (by norm_num : (0:ℝ)<2) (Real.log_pos hh)).ne he

/-- Deleting the last ε of a single atom costs exactly log(p/ε). -/
theorem halfAtom_diagonal_truncation {p ε : ℝ} (he : 0 < ε) (hep : ε ≤ p) :
    (∫ t in 0..(p-ε), halfAtom p t^2) = Real.log (p/ε) := by
  have horder : 0 ≤ p-ε := sub_nonneg.mpr hep
  calc
    _ = ∫ t in 0..(p-ε), (p-t)⁻¹ := by
      rw [intervalIntegral.integral_of_le horder, intervalIntegral.integral_of_le horder]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have hpos : 0 < p-t := by linarith only [ht.2, he]
      change halfAtom p t ^ 2 = (p-t)⁻¹
      rw [halfAtom, if_pos ht.1, kernel_eq_inv_sqrt hpos, inv_pow, Real.sq_sqrt hpos.le]
    _ = _ := by
      have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := p-ε) (fun t : ℝ => t⁻¹) p
      simp only [sub_sub_cancel, sub_zero] at h
      rw [h, integral_inv_of_pos he (he.trans_le hep)]

/-- A signed row observed only to the right of the ground point zero. -/
def halfRow (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ := ∑ i ∈ S, w i * halfAtom i t

/-- With separated supports the entire mixed energy has an ordinary finite
double-sum formula; diagonal renormalization is unnecessary. -/
theorem separated_halfRow_pairing (S T : Finset ℕ) (w v : ℕ → ℝ)
    (h : ∀ i ∈ S, ∀ j ∈ T, 0 < i ∧ i < j) :
    (∫ t, halfRow S w t * halfRow T v t) =
      ∑ i ∈ S, ∑ j ∈ T, (w i*v j) *
        (2*Real.log ((Real.sqrt i + Real.sqrt j)/Real.sqrt (j-i : ℝ))) := by
  have hi (i : ℕ) (hi : i ∈ S) (j : ℕ) (hj : j ∈ T) :
      Integrable (fun t => (w i*v j)*(halfAtom i t * halfAtom j t)) :=
    (halfAtom_cross_integrable (Nat.cast_pos.mpr (h i hi j hj).1)
      (Nat.cast_lt.mpr (h i hi j hj).2)).const_mul _
  have expand (t : ℝ) : halfRow S w t * halfRow T v t =
      ∑ i ∈ S, ∑ j ∈ T, (w i*v j)*(halfAtom i t*halfAtom j t) := by
    unfold halfRow
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [expand]
  rw [integral_finsetSum S (fun i hS => integrable_finsetSum T (hi i hS))]
  apply Finset.sum_congr rfl
  intro i hS
  rw [integral_finsetSum T (hi i hS)]
  apply Finset.sum_congr rfl
  intro j hT
  rw [integral_const_mul, halfAtom_cross_integral (Nat.cast_pos.mpr (h i hS j hT).1)
    (Nat.cast_lt.mpr (h i hS j hT).2)]

#print axioms halfAtom_diagonal_truncation
#print axioms separated_halfRow_pairing
#print axioms halfAtom_cross_integral
#print axioms halfAtom_cross_integrable

end GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
