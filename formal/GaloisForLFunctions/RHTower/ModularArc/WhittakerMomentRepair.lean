import GaloisForLFunctions.RHTower.ModularArcWhittakerStability
import GaloisForLFunctions.RHTower.ModularArcAnnihilatingMeasure
import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature

/-!
# Positive repair of prescribed Whittaker moments

The first `N` cosine Whittaker moments have a positive arc measure with at most
`N+1` atoms and mass `2 Σ_{n<N} |v_n| / K₀(2π(n+1))`. More generally, a positive
trigonometric density realizes its prescribed moments with the same mass.
The minimum principle transfers arc lower bounds to the horocycle. Pairing
with the whole density retains cancellation between its coefficients;
finite atomic cubature then realizes the moments exactly.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

/-- The first `N` cosine Whittaker readings on the modular arc. -/
def arcCosMomentVector (N : ℕ) (u : ArcParam) : Fin N → ℝ :=
  fun n => arcCosMode n u

/-- The absolute moment cost measured in the horocycle Bessel weights. -/
def arcCosMomentCost {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  ∑ n, |v n| / kMoment 0 (arcFreq n)

theorem arcCosMomentCost_nonneg {N : ℕ} (v : Fin N → ℝ) :
    0 ≤ arcCosMomentCost v :=
  Finset.sum_nonneg fun n _ =>
    div_nonneg (abs_nonneg _) (kMoment_zero_pos_of_pos (arcFreq_pos n)).le

/-- The weighted moment cost is absolutely homogeneous. -/
theorem arcCosMomentCost_smul {N : ℕ} (c : ℝ) (v : Fin N → ℝ) :
    arcCosMomentCost (c • v) = |c| * arcCosMomentCost v := by
  simp only [arcCosMomentCost, Pi.smul_apply, smul_eq_mul, abs_mul,
    mul_div_assoc, Finset.mul_sum]

/-- Zero weighted cost forces every prescribed moment to vanish. -/
theorem arcCosMomentCost_eq_zero_iff {N : ℕ} {v : Fin N → ℝ} :
    arcCosMomentCost v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext n
    have hn : |v n| / kMoment 0 (arcFreq n) ≤ arcCosMomentCost v :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin N => |v j| / kMoment 0 (arcFreq j))
        (fun j _ => div_nonneg (abs_nonneg _) (kMoment_zero_pos_of_pos (arcFreq_pos j)).le)
        (Finset.mem_univ n)
    rw [h, div_le_iff₀ (kMoment_zero_pos_of_pos (arcFreq_pos n)), zero_mul] at hn
    exact abs_nonpos_iff.mp hn
  · rintro rfl
    simp only [arcCosMomentCost, Pi.zero_apply, abs_zero, zero_div, Finset.sum_const_zero]

private def arcFunctionalCoeff {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ)) (n : ℕ) : ℝ :=
  if h : n < N then f (Pi.single ⟨n, h⟩ 1) else 0

private theorem arcFunctional_apply {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ))
    (v : Fin N → ℝ) :
    f v = ∑ n, v n * arcFunctionalCoeff f n := by
  have h := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [arcFunctionalCoeff, dif_pos n.2]
  congr 2
  funext j
  simp only [Pi.single_apply]
  change (if n = j then (1 : ℝ) else 0) = if j = n then 1 else 0
  by_cases hnj : n = j
  · subst j
    rfl
  · rw [if_neg hnj, if_neg (Ne.symm hnj)]

private theorem arcFunctional_vector {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ))
    (u : ArcParam) :
    f (arcCosMomentVector N u) =
      whittakerArcSum N (arcFunctionalCoeff f) (fun _ => 0) u (modularArcHeight u) := by
  rw [arcFunctional_apply, whittakerArcSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [arcCosMomentVector, arcCosMode_apply, arcTrig, zero_mul, add_zero]
  ring

private theorem arcFunctional_coeff_bound {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ u, -ε ≤ f (arcCosMomentVector N u)) (n : Fin N) :
    |arcFunctionalCoeff f n| ≤ 4 * ε / kMoment 0 (arcFreq n) := by
  apply (abs_coeff_le_of_ge_on_arc N (arcFunctionalCoeff f) (fun _ => 0) hε ?_ n.2).1
  intro u y hy hu huy
  have huI : u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
    exact ⟨by linarith only [hu₁], hu₂⟩
  have hyh : y = modularArcHeight u := by
    unfold modularArcHeight
    rw [show 1 - u ^ 2 = y ^ 2 by linarith only [huy], Real.sqrt_sq hy.le]
  rw [hyh, ← arcFunctional_vector f ⟨u, huI⟩]
  exact h _

private theorem arcFunctional_cost_bound {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ u, -ε ≤ f (arcCosMomentVector N u))
    (v : Fin N → ℝ) : |f v| ≤ 4 * ε * arcCosMomentCost v := by
  rw [arcFunctional_apply]
  calc
    _ ≤ ∑ n, |v n * arcFunctionalCoeff f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n, 4 * ε * (|v n| / kMoment 0 (arcFreq n)) := by
      refine Finset.sum_le_sum fun n _ => ?_
      rw [abs_mul]
      calc
        _ ≤ |v n| * (4 * ε / kMoment 0 (arcFreq n)) :=
          mul_le_mul_of_nonneg_left (arcFunctional_coeff_bound f hε h n) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [arcCosMomentCost, Finset.mul_sum]

/-- The full trigonometric density associated to the prescribed moments. -/
def arcCosMomentPolynomial {N : ℕ} (v : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ n, (2 * v n / kMoment 0 (arcFreq n)) * Real.cos (arcFreq n * t)

private theorem continuous_arcCosMomentPolynomial {N : ℕ} (v : Fin N → ℝ) :
    Continuous (arcCosMomentPolynomial v) := by
  unfold arcCosMomentPolynomial
  fun_prop

private theorem integral_arcCosMomentPolynomial {N : ℕ} (v : Fin N → ℝ) :
    ∫ t in (0 : ℝ)..1, arcCosMomentPolynomial v t = 0 := by
  unfold arcCosMomentPolynomial
  rw [intervalIntegral.integral_finsetSum fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hn : (n : ℤ) + 1 ≠ 0 := by omega
  have hcos : ∫ t in (0 : ℝ)..1, Real.cos (arcFreq n * t) = 0 := by
    simpa only [arcFreq, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      integral_cos_two_pi_mul_int hn
  rw [hcos, mul_zero]

private theorem arcCosMomentPolynomial_smul {N : ℕ} (c : ℝ) (v : Fin N → ℝ) (t : ℝ) :
    arcCosMomentPolynomial (c • v) t = c * arcCosMomentPolynomial v t := by
  simp only [arcCosMomentPolynomial, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

private theorem arcFunctional_polynomial_integral {N : ℕ}
    (f : StrongDual ℝ (Fin N → ℝ)) (v : Fin N → ℝ) :
    ∫ t in (0 : ℝ)..1,
      whittakerArcSum N (arcFunctionalCoeff f) (fun _ => 0) t 1 *
        arcCosMomentPolynomial v t = f v := by
  simp only [arcCosMomentPolynomial, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun n _ => by
    unfold whittakerArcSum arcTrig
    apply Continuous.intervalIntegrable; fun_prop]
  rw [arcFunctional_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hi : (∫ t in (0 : ℝ)..1,
      whittakerArcSum N (arcFunctionalCoeff f) (fun _ => 0) t 1 *
        ((2 * v n / kMoment 0 (arcFreq n)) * Real.cos (arcFreq n * t))) =
      (2 * v n / kMoment 0 (arcFreq n)) *
        ∫ t in (0 : ℝ)..1,
          whittakerArcSum N (arcFunctionalCoeff f) (fun _ => 0) t 1 *
            Real.cos (arcFreq n * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hi, integral_whittakerArcSum_mul_cos N (arcFunctionalCoeff f) (fun _ => 0) 1 n.2,
    mul_one]
  field_simp [(kMoment_zero_pos_of_pos (arcFreq_pos n)).ne']

private theorem arcFunctional_lower_of_density {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ u, -ε ≤ f (arcCosMomentVector N u))
    (v : Fin N → ℝ) (hv : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 1 + arcCosMomentPolynomial v t) :
    -ε ≤ f v := by
  let W := whittakerArcSum N (arcFunctionalCoeff f) (fun _ => 0)
  have hlow : ∀ t, -ε ≤ W t 1 := by
    intro t
    apply neg_le_whittakerArcSum_of_ge_on_arc N (arcFunctionalCoeff f) (fun _ => 0) hε ?_ le_rfl
    intro u y hy hu huy
    have huI : u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
      exact ⟨by linarith only [hu₁], hu₂⟩
    have hyh : y = modularArcHeight u := by
      unfold modularArcHeight
      rw [show 1 - u ^ 2 = y ^ 2 by linarith only [huy], Real.sqrt_sq hy.le]
    rw [hyh, ← arcFunctional_vector f ⟨u, huI⟩]
    exact h _
  have hW : Continuous fun t => W t 1 := by
    unfold W whittakerArcSum arcTrig
    fun_prop
  have hQ := continuous_arcCosMomentPolynomial v
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1, (W t 1 + ε) * (1 + arcCosMomentPolynomial v t) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    exact mul_nonneg (by linarith only [hlow t]) (hv t ht)
  have heq : (∫ t in (0 : ℝ)..1, (W t 1 + ε) * (1 + arcCosMomentPolynomial v t)) =
      f v + ε := by
    have heq : ∀ t, (W t 1 + ε) * (1 + arcCosMomentPolynomial v t) =
        ((W t 1 * arcCosMomentPolynomial v t + W t 1) +
          ε * arcCosMomentPolynomial v t) + ε := fun t => by ring
    simp_rw [heq]
    rw [intervalIntegral.integral_add (f := fun t =>
          W t 1 * arcCosMomentPolynomial v t + W t 1 + ε * arcCosMomentPolynomial v t)
        (g := fun _ => ε)
        ((((hW.mul hQ).add hW).add (hQ.const_mul ε)).intervalIntegrable 0 1) intervalIntegrable_const,
      intervalIntegral.integral_add (f := fun t => W t 1 * arcCosMomentPolynomial v t + W t 1)
        (g := fun t => ε * arcCosMomentPolynomial v t)
        (((hW.mul hQ).add hW).intervalIntegrable 0 1) ((hQ.const_mul ε).intervalIntegrable 0 1),
      intervalIntegral.integral_add (f := fun t => W t 1 * arcCosMomentPolynomial v t)
        (g := fun t => W t 1) ((hW.mul hQ).intervalIntegrable 0 1) (hW.intervalIntegrable 0 1),
      arcFunctional_polynomial_integral, integral_whittakerArcSum,
      intervalIntegral.integral_const_mul, integral_arcCosMomentPolynomial,
      intervalIntegral.integral_const]
    simp only [mul_zero, add_zero, sub_zero, one_smul]
  rw [heq] at hi
  linarith only [hi]

/-- A nonnegative trigonometric probability density gives an arc moment vector.
The estimate pairs the whole density with the nonnegative shifted Whittaker sum. -/
theorem mem_closure_convexHull_arcCosMomentVector_of_density {N : ℕ} {v : Fin N → ℝ}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 1 + arcCosMomentPolynomial v t) :
    v ∈ closure (convexHull ℝ (range (arcCosMomentVector N))) := by
  by_contra hnot
  obtain ⟨f, s, hvs, hs⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _).closure isClosed_closure hnot
  have hpoint : ∀ u : ArcParam, s < f (arcCosMomentVector N u) := fun u =>
    hs _ (subset_closure (subset_convexHull ℝ _ (mem_range_self u)))
  rcases le_or_gt s 0 with hs0 | hs0
  · have hbound := arcFunctional_lower_of_density f (neg_nonneg.mpr hs0)
      (fun u => by simpa only [neg_neg] using (hpoint u).le) v hv
    linarith only [hbound, hvs]
  · have hf0 := arcFunctional_cost_bound f (ε := 0) le_rfl
      (fun u => by simpa only [neg_zero] using (hs0.trans (hpoint u)).le)
      (arcCosMomentVector N ⟨0, by norm_num⟩)
    simp only [mul_zero, zero_mul] at hf0
    have heq := abs_nonpos_iff.mp hf0
    have hp := hpoint ⟨0, by norm_num⟩
    rw [heq] at hp
    exact (not_lt_of_ge hs0.le) hp

private theorem exists_arcCosMoment_probability_atoms_of_mem {N : ℕ} {v : Fin N → ℝ}
    (hv : v ∈ closure (convexHull ℝ (range (arcCosMomentVector N)))) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n := by
  have hcont : Continuous (arcCosMomentVector N) :=
    continuous_pi fun n => (arcCosMode n).continuous
  have hcompact : IsCompact (range (arcCosMomentVector N)) := isCompact_range hcont
  have hne : (range (arcCosMomentVector N)).Nonempty :=
    ⟨arcCosMomentVector N ⟨0, by norm_num⟩, mem_range_self _⟩
  obtain ⟨w, z, hw, hw1, hz, hsum⟩ := exists_atomic_of_mem_closure_convexHull
    hcompact hne hv
  choose u hu using hz
  refine ⟨w, u, hw, hw1, fun n => ?_⟩
  have hn := congrFun hsum n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hn
  rw [← hn]
  exact Finset.sum_congr rfl fun i _ => by rw [← hu i]; rfl

/-- Positive trigonometric densities can be transferred to at most `N+1` arc atoms
without changing their mass or the prescribed cosine moments. -/
theorem exists_arcCosMoment_atoms_of_density {N : ℕ} (v : Fin N → ℝ) {M : ℝ}
    (hM : 0 < M) (hv : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ M + arcCosMomentPolynomial v t) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = M) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n := by
  have hsmall : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 1 + arcCosMomentPolynomial (M⁻¹ • v) t := by
    intro t ht
    rw [arcCosMomentPolynomial_smul]
    calc
      0 ≤ (M + arcCosMomentPolynomial v t) / M := div_nonneg (hv t ht) hM.le
      _ = 1 + M⁻¹ * arcCosMomentPolynomial v t := by field_simp [hM.ne']
  obtain ⟨w, u, hw, hw1, hmom⟩ := exists_arcCosMoment_probability_atoms_of_mem
    (mem_closure_convexHull_arcCosMomentVector_of_density hsmall)
  refine ⟨fun i => M * w i, u, fun i => mul_nonneg hM.le (hw i), ?_, fun n => ?_⟩
  · rw [← Finset.mul_sum, hw1, mul_one]
  · calc
      ∑ i, M * w i * arcCosMode n (u i) = M * ∑ i, w i * arcCosMode n (u i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
      _ = v n := by
        rw [hmom n]
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]

/-- The full trigonometric density retains the elementary weighted absolute bound. -/
theorem abs_arcCosMomentPolynomial_le {N : ℕ} (v : Fin N → ℝ) (t : ℝ) :
    |arcCosMomentPolynomial v t| ≤ 2 * arcCosMomentCost v := by
  calc
    _ ≤ ∑ n, |(2 * v n / kMoment 0 (arcFreq n)) * Real.cos (arcFreq n * t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n, 2 * (|v n| / kMoment 0 (arcFreq n)) := by
      refine Finset.sum_le_sum fun n _ => ?_
      rw [abs_mul]
      calc
        _ ≤ |2 * v n / kMoment 0 (arcFreq n)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = _ := by
          rw [mul_one, abs_div, abs_mul, abs_two,
            abs_of_pos (kMoment_zero_pos_of_pos (arcFreq_pos n))]
          ring
    _ = _ := by rw [arcCosMomentCost, Finset.mul_sum]

/-- The moment body contains the Bessel-weighted absolute ball of radius `1/2`. -/
theorem mem_closure_convexHull_arcCosMomentVector {N : ℕ} {v : Fin N → ℝ}
    (hv : arcCosMomentCost v ≤ 1 / 2) :
    v ∈ closure (convexHull ℝ (range (arcCosMomentVector N))) := by
  apply mem_closure_convexHull_arcCosMomentVector_of_density
  intro t _
  have h := neg_le_of_abs_le (abs_arcCosMomentPolynomial_le v t)
  linarith only [h, hv]

/-- Every vector in the weighted ball is realized by at most `N+1` probability atoms. -/
theorem exists_arcCosMoment_probability_atoms {N : ℕ} {v : Fin N → ℝ}
    (hv : arcCosMomentCost v ≤ 1 / 2) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n :=
  exists_arcCosMoment_probability_atoms_of_mem (mem_closure_convexHull_arcCosMomentVector hv)

/-- A positive realization of arbitrary finite moments costs at most two units of mass
per unit of Bessel-weighted absolute moment. -/
theorem exists_arcCosMoment_atoms {N : ℕ} (v : Fin N → ℝ) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 2 * arcCosMomentCost v) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n := by
  by_cases hc : arcCosMomentCost v = 0
  · have hv := arcCosMomentCost_eq_zero_iff.mp hc
    subst v
    refine ⟨fun _ => 0, fun _ => ⟨0, by norm_num⟩, fun _ => le_rfl, ?_, ?_⟩
    · simp only [Finset.sum_const_zero, hc, mul_zero]
    · intro n
      simp only [zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  · have hM : 0 < 2 * arcCosMomentCost v := mul_pos (by norm_num)
      (lt_of_le_of_ne (arcCosMomentCost_nonneg v) (Ne.symm hc))
    apply exists_arcCosMoment_atoms_of_density v hM
    intro t _
    have h := neg_le_of_abs_le (abs_arcCosMomentPolynomial_le v t)
    linarith only [h]

end RHTower

end
