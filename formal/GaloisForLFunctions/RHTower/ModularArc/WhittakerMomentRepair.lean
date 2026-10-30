import GaloisForLFunctions.RHTower.ModularArcWhittakerStability
import GaloisForLFunctions.RHTower.ModularArcAnnihilatingMeasure
import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature

/-!
# Positive repair of prescribed Whittaker moments

The first `N` cosine Whittaker moments can be prescribed by a positive measure
on the modular bottom arc with at most `N+1` atoms and mass
`4 Σ_{n<N} |v_n| / K₀(2π(n+1))`. The coefficient stability theorem gives the
weighted convex-hull inclusion; finite atomic cubature realizes it exactly.
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

/-- The moment body contains the Bessel-weighted absolute ball of radius `1/4`. -/
theorem mem_closure_convexHull_arcCosMomentVector {N : ℕ} {v : Fin N → ℝ}
    (hv : arcCosMomentCost v ≤ 1 / 4) :
    v ∈ closure (convexHull ℝ (range (arcCosMomentVector N))) := by
  by_contra hnot
  obtain ⟨f, s, hvs, hs⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _).closure isClosed_closure hnot
  have hpoint : ∀ u : ArcParam, s < f (arcCosMomentVector N u) := fun u =>
    hs _ (subset_closure (subset_convexHull ℝ _ (mem_range_self u)))
  rcases le_or_gt s 0 with hs0 | hs0
  · have hbound := arcFunctional_cost_bound f (neg_nonneg.mpr hs0)
      (fun u => by simpa only [neg_neg] using (hpoint u).le) v
    have hcost := mul_le_mul_of_nonneg_left hv
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (neg_nonneg.mpr hs0))
    have habs : |f v| ≤ -s := by nlinarith only [hbound, hcost]
    have hlo := neg_le_of_abs_le habs
    linarith only [hlo, hvs]
  · have hf0 := arcFunctional_cost_bound f (ε := 0) le_rfl
      (fun u => by simpa only [neg_zero] using (hs0.trans (hpoint u)).le)
      (arcCosMomentVector N ⟨0, by norm_num⟩)
    simp only [mul_zero, zero_mul] at hf0
    have heq := abs_nonpos_iff.mp hf0
    have hp := hpoint ⟨0, by norm_num⟩
    rw [heq] at hp
    exact (not_lt_of_ge hs0.le) hp

/-- Every vector in the weighted moment ball is an exact convex combination of at most
`N+1` arc readings. -/
theorem exists_arcCosMoment_probability_atoms {N : ℕ} {v : Fin N → ℝ}
    (hv : arcCosMomentCost v ≤ 1 / 4) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n := by
  have hcont : Continuous (arcCosMomentVector N) :=
    continuous_pi fun n => (arcCosMode n).continuous
  have hcompact : IsCompact (range (arcCosMomentVector N)) := isCompact_range hcont
  have hne : (range (arcCosMomentVector N)).Nonempty :=
    ⟨arcCosMomentVector N ⟨0, by norm_num⟩, mem_range_self _⟩
  obtain ⟨w, z, hw, hw1, hz, hsum⟩ := exists_atomic_of_mem_closure_convexHull
    hcompact hne (mem_closure_convexHull_arcCosMomentVector hv)
  choose u hu using hz
  refine ⟨w, u, hw, hw1, fun n => ?_⟩
  have hn := congrFun hsum n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hn
  rw [← hn]
  exact Finset.sum_congr rfl fun i _ => by rw [← hu i]; rfl

end RHTower

end


namespace RHTower

open BesselKZero

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

/-- Arbitrary finite cosine moments have a positive arc realization with at most `N+1`
atoms and mass exactly four times their weighted cost. -/
theorem exists_arcCosMoment_atoms {N : ℕ} (v : Fin N → ℝ) :
    ∃ (w : Fin (N + 1) → ℝ) (u : Fin (N + 1) → ArcParam),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 4 * arcCosMomentCost v) ∧
      ∀ n : Fin N, ∑ i, w i * arcCosMode n (u i) = v n := by
  by_cases hc : arcCosMomentCost v = 0
  · have hv := arcCosMomentCost_eq_zero_iff.mp hc
    subst v
    refine ⟨fun _ => 0, fun _ => ⟨0, by norm_num⟩, fun _ => le_rfl, ?_, ?_⟩
    · simp only [Finset.sum_const_zero, hc, mul_zero]
    · intro n
      simp only [zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  · let M := 4 * arcCosMomentCost v
    have hM : 0 < M := mul_pos (by norm_num)
      (lt_of_le_of_ne (arcCosMomentCost_nonneg v) (Ne.symm hc))
    have hsmall : arcCosMomentCost (M⁻¹ • v) ≤ 1 / 4 := by
      rw [arcCosMomentCost_smul, abs_of_pos (inv_pos.mpr hM), inv_mul_eq_div,
        div_le_iff₀ hM]
      dsimp [M]
      linarith only
    obtain ⟨w, u, hw, hw1, hmom⟩ := exists_arcCosMoment_probability_atoms hsmall
    refine ⟨fun i => M * w i, u, fun i => mul_nonneg hM.le (hw i), ?_, fun n => ?_⟩
    · rw [← Finset.mul_sum, hw1, mul_one]
    · calc
        ∑ i, M * w i * arcCosMode n (u i) = M * ∑ i, w i * arcCosMode n (u i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
        _ = v n := by
          rw [hmom n]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]

end RHTower
