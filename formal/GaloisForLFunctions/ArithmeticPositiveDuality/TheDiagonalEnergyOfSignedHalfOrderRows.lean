import GaloisForLFunctions.ArithmeticPositiveDuality.TheGramKernelOfHalfOrderDiscrepancy

/-!
# Diagonal subtraction for signed half-order discrepancy

All cross terms between distinct sites are integrable. Removing precisely
the squared atom at each site leaves an integrable density with an explicit
logarithmic integral. Its sign can vary. This separates the entire failure
of square integrability from the signed interactions.
-/

noncomputable section
open Finset MeasureTheory Set Filter
namespace GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy

theorem halfAtom_zero_site (t : ℝ) : halfAtom 0 t=0 := by
  by_cases h : 0 < t
  · simp [halfAtom,cutPower,h,h.not_gt]
  · simp [halfAtom,h]

theorem measurable_halfAtom (p : ℝ) : Measurable (halfAtom p) := by
  unfold halfAtom cutPower
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · apply Measurable.ite (measurableSet_lt measurable_const (measurable_const.sub measurable_id))
    · fun_prop
    · exact measurable_const
  · exact measurable_const

/-- A single positive atom has infinite square integral in the sense that
its square fails Bochner integrability. The exact truncated integral can
exceed any proposed finite value. -/
theorem halfAtom_square_not_integrable {p : ℝ} (hp : 0 < p) :
    ¬ Integrable (fun t => halfAtom p t^2) := by
  intro hi
  let A := ∫ t, halfAtom p t^2
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  let ε := p/Real.exp (A+1)
  have he : 0 < ε := div_pos hp (Real.exp_pos _)
  have hep : ε ≤ p := div_le_self hp.le (Real.one_le_exp (by linarith only [hA]))
  have hu := setIntegral_le_integral (s := Ioc 0 (p-ε)) hi
    (ae_of_all _ fun _ => sq_nonneg _)
  rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hep),halfAtom_diagonal_truncation he hep] at hu
  change Real.log (p/(p/Real.exp (A+1))) ≤ A at hu
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hp.ne',Real.log_exp] at hu
  linarith only [hu]

theorem halfAtom_mixed_integrable {i j : ℕ} (hne : i ≠ j) :
    Integrable (fun t => halfAtom i t * halfAtom j t) := by
  by_cases hi : i=0
  · simp [hi,halfAtom_zero_site]
  by_cases hj : j=0
  · simp [hj,halfAtom_zero_site]
  rcases lt_or_gt_of_ne hne with h | h
  · exact halfAtom_cross_integrable (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) (Nat.cast_lt.mpr h)
  · simpa only [mul_comm] using halfAtom_cross_integrable
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) (Nat.cast_lt.mpr h)

/-- The kernel is symmetric in the locations and zero at a ground site. -/
def offDiagonalKernel (i j : ℕ) : ℝ :=
  if i=0 ∨ j=0 then 0 else
    2*Real.log ((Real.sqrt i + Real.sqrt j)/Real.sqrt |(i:ℝ)-j|)

theorem halfAtom_mixed_integral {i j : ℕ} (hne : i ≠ j) :
    (∫ t, halfAtom i t * halfAtom j t) = offDiagonalKernel i j := by
  by_cases hi : i=0
  · simp [hi,halfAtom_zero_site,offDiagonalKernel]
  by_cases hj : j=0
  · simp [hj,halfAtom_zero_site,offDiagonalKernel]
  rw [offDiagonalKernel,if_neg (not_or.mpr ⟨hi,hj⟩)]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_of_neg (sub_neg.mpr (Nat.cast_lt.mpr h)),neg_sub]
    exact halfAtom_cross_integral (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) (Nat.cast_lt.mpr h)
  · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h.le)),add_comm (Real.sqrt i)]
    simpa only [mul_comm (halfAtom i _) (halfAtom j _)] using
      halfAtom_cross_integral (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) (Nat.cast_lt.mpr h)

/-- Subtract each squared weighted atom before integrating. -/
def offDiagonalDensity (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  halfRow S w t^2 - ∑ i ∈ S, (w i * halfAtom i t)^2

private theorem expand_offDiagonal (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :
    offDiagonalDensity S w t = ∑ i ∈ S, ∑ j ∈ S.erase i,
      (w i*w j)*(halfAtom i t*halfAtom j t) := by
  let a := fun i : ℕ => w i*halfAtom i t
  change (∑ i ∈ S, a i)^2 - (∑ i ∈ S, a i^2) = _
  rw [sq,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,← sum_erase_add S (fun j => a i*a j) hi,sq,add_sub_cancel_right]
  exact sum_congr rfl fun j _ => by dsimp only [a]; ring

private theorem weighted_mixed_integrable (w : ℕ → ℝ) (i j : ℕ) (hne : j ≠ i) :
    Integrable (fun t => (w i*w j)*(halfAtom i t*halfAtom j t)) :=
  (halfAtom_mixed_integrable hne.symm).const_mul _

/-- Signed interactions at all distinct sites form an absolutely integrable
remainder, even when neighboring site weights have opposite signs. -/
theorem integrable_offDiagonalDensity (S : Finset ℕ) (w : ℕ → ℝ) :
    Integrable (offDiagonalDensity S w) := by
  change Integrable (fun t => offDiagonalDensity S w t)
  simp_rw [expand_offDiagonal]
  exact integrable_finsetSum S fun i _ => integrable_finsetSum _ fun j hj =>
    weighted_mixed_integrable w i j (mem_erase.mp hj).1

/-- The finite part after subtracting each singular self-interaction. -/
theorem integral_offDiagonalDensity (S : Finset ℕ) (w : ℕ → ℝ) :
    (∫ t, offDiagonalDensity S w t) =
      ∑ i ∈ S, ∑ j ∈ S.erase i, (w i*w j)*offDiagonalKernel i j := by
  simp_rw [expand_offDiagonal]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum _ fun j hj =>
    weighted_mixed_integrable w i j (mem_erase.mp hj).1)]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj => weighted_mixed_integrable w i j (mem_erase.mp hj).1)]
  exact sum_congr rfl fun j hj => by rw [integral_const_mul,halfAtom_mixed_integral (mem_erase.mp hj).1.symm]

/-- Signs at distinct sites cannot cancel the logarithmic divergences.
Zero is an invisible site because the observation half-line is positive. -/
theorem halfRow_square_integrable_iff (S : Finset ℕ) (w : ℕ → ℝ) :
    Integrable (fun t => halfRow S w t^2) ↔ ∀ i ∈ S, 0 < i → w i=0 := by
  constructor
  · intro h i hi hpos
    have hd : Integrable (fun t => ∑ j ∈ S, (w j*halfAtom j t)^2) := by
      simpa only [offDiagonalDensity,sub_sub_cancel] using h.sub' (integrable_offDiagonalDensity S w)
    by_contra hn
    have hsingle : Integrable (fun t => (w i)^2*(halfAtom i t)^2) := by
      apply hd.mono' ((measurable_const.mul ((measurable_halfAtom i).pow_const 2)).aestronglyMeasurable)
      apply ae_of_all
      intro t
      change ‖w i ^ 2 * halfAtom i t ^ 2‖ ≤ _
      rw [← mul_pow,Real.norm_of_nonneg (sq_nonneg _)]
      exact single_le_sum (fun j _ => sq_nonneg (w j*halfAtom j t)) hi
    exact halfAtom_square_not_integrable (Nat.cast_pos.mpr hpos)
      ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hn)) _).mp hsingle)
  · intro h
    have he (t : ℝ) : halfRow S w t=0 := by
      apply sum_eq_zero
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · simp [halfAtom_zero_site]
      · rw [h i hi hp,zero_mul]
    simp_rw [he,zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

end GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
