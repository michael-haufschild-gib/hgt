import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarHilbertAllocation

/-!
# Hilbert representatives of bounded physical collar prices

Every measurable price between zero and one has an explicit L2 representative.
Its inner product with an allocation is exactly the original physical cost integral.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

def boundedPriceVector (n : ℕ) (Q : ℕ → ℝ → ℝ) (x : ℝ) : AllocationVector n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun k => archLevySinhWeight x * Q k.val x)

theorem memLp_boundedPriceVector (n : ℕ) (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ k, Measurable (Q k))
    (hQb : ∀ k ∈ range (n + 1), ∀ x, 0 ≤ Q k x ∧ Q k x ≤ 1) :
    MemLp (boundedPriceVector n Q) 2 (allocationMeasure n) := by
  have hm : Measurable (boundedPriceVector n Q) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurable.comp
      (measurable_pi_lambda _ (fun k => measurable_archLevySinhWeight.mul (hQ k.val)))
  let C := logarithmicCollarWeightBound n
  apply MemLp.of_bound hm.aestronglyMeasurable (Real.sqrt ((n + 1 : ℝ) * C ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hw0 := (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1)).le
  have hw : archLevySinhWeight x ≤ C := by
    apply div_le_div₀ (Real.exp_pos _).le
    · apply Real.exp_le_exp.mpr
      linarith [hx.2]
    · exact Real.sinh_pos_iff.mpr logarithmicCollarRadius_pos
    · exact Real.sinh_le_sinh.mpr hx.1.le
  have hsq : ‖boundedPriceVector n Q x‖ ^ 2 ≤ (n + 1 : ℝ) * C ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _k : Fin (n + 1), C ^ 2 := by
        apply sum_le_sum
        intro k _
        have hq := hQb k.val (mem_range.mpr k.isLt) x
        have hv0 := mul_nonneg hw0 hq.1
        have hv := (mul_le_of_le_one_right hw0 hq.2).trans hw
        change (archLevySinhWeight x * Q k.val x) ^ 2 ≤ C ^ 2
        nlinarith
      _ = _ := by simp
  have hpos : 0 ≤ (n + 1 : ℝ) * C ^ 2 := mul_nonneg (by positivity) (sq_nonneg C)
  have hsqrt := Real.sq_sqrt hpos
  have hn := Real.sqrt_nonneg ((n + 1 : ℝ) * C ^ 2)
  nlinarith [norm_nonneg (boundedPriceVector n Q x)]

def boundedPriceClass (n : ℕ) (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ k, Measurable (Q k))
    (hQb : ∀ k ∈ range (n + 1), ∀ x, 0 ≤ Q k x ∧ Q k x ≤ 1) : AllocationHilbert n :=
  (memLp_boundedPriceVector n Q hQ hQb).toLp (boundedPriceVector n Q)

theorem boundedPriceClass_inner {n : ℕ} (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ k, Measurable (Q k))
    (hQb : ∀ k ∈ range (n + 1), ∀ x, 0 ≤ Q k x ∧ Q k x ≤ 1)
    (η : PhysicalCollarPartition n) :
    inner ℝ (boundedPriceClass n Q hQ hQb) (allocationClass η) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
        ∑ k ∈ range (n + 1), η.density k x * Q k x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_boundedPriceVector n Q hQ hQb).coeFn_toLp,
    (memLp_allocationVector η).coeFn_toLp] with x hp hη
  change inner ℝ ((memLp_boundedPriceVector n Q hQ hQb).toLp (boundedPriceVector n Q) x)
    ((memLp_allocationVector η).toLp (allocationVector η) x) = _
  rw [hp, hη, PiLp.inner_apply]
  change (∑ k : Fin (n + 1), η.share k.val x * (archLevySinhWeight x * Q k.val x)) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => η.share k x * (archLevySinhWeight x * Q k x))]
  apply sum_congr rfl
  intro k _
  unfold density
  ring

end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

end
