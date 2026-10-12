import GaloisForLFunctions.RHTower.PaperThetaVariationBudget
import GaloisForLFunctions.RHTower.PaperThetaBoundedDomain
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Exact bounded-variation admission for the source-relative theta mode

Every right ray has a finite explicit variation budget. Divisor reflection
pays the other ray; conversely, finite whole-line variation forces the
already-proven native boundedness selector.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

/-- Arbitrary finite partitions telescope against the actual decreasing budget. -/
theorem eVariationOn_flatQuotient_Ici (z : ℂ) (A : ℝ) :
    eVariationOn (flatQuotient z) (Ici A) ≤ ENNReal.ofReal (quotientVariationBudget z A) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have hdec (i : ℕ) : quotientVariationBudget z (u (i+1)) ≤
      quotientVariationBudget z (u i) := quotientVariationBudget_antitone z (hu (Nat.le_succ i))
  calc
    (∑ i ∈ Finset.range n, edist (flatQuotient z (u (i+1))) (flatQuotient z (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal
          (quotientVariationBudget z (u i) - quotientVariationBudget z (u (i+1))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [edist_dist, dist_eq_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa [abs_of_nonpos (sub_nonpos.mpr (hdec i))] using
        flatQuotient_increment_budget z (u i) (u (i+1))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        (quotientVariationBudget z (u i) - quotientVariationBudget z (u (i+1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sub_nonneg.mpr (hdec i)]
    _ = ENNReal.ofReal (quotientVariationBudget z (u 0) - quotientVariationBudget z (u n)) := by
      have ht := Finset.sum_range_sub (fun i => -quotientVariationBudget z (u i)) n
      simpa only [neg_sub_neg] using congrArg ENNReal.ofReal ht
    _ ≤ ENNReal.ofReal (quotientVariationBudget z A) := by
      apply ENNReal.ofReal_le_ofReal
      exact (sub_le_self _ (quotientVariationBudget_nonneg z _)).trans
        (quotientVariationBudget_antitone z (us 0))

theorem boundedVariationOn_flatQuotient_Ici (z : ℂ) (A : ℝ) :
    BoundedVariationOn (flatQuotient z) (Ici A) :=
  ne_top_of_le_ne_top (by finiteness) (eVariationOn_flatQuotient_Ici z A)

/-- The full divisor mode has a paid two-sided source variation budget. -/
theorem eVariationOn_divisor_flatQuotient_le (z : {z : ℂ // XiC z = 0}) :
    eVariationOn (flatQuotient z.val) univ ≤
      ENNReal.ofReal (quotientVariationBudget (-z.val) 0) +
        ENNReal.ofReal (quotientVariationBudget z.val 0) := by
  have href : flatQuotient z.val = flatQuotient (-z.val) ∘ (fun x : ℝ => -x) :=
    funext (flatQuotient_divisor_reflection z)
  have hleft : eVariationOn (flatQuotient z.val) (Iic (0 : ℝ)) ≤
      ENNReal.ofReal (quotientVariationBudget (-z.val) 0) := by
    rw [href]
    refine (eVariationOn.comp_le_of_antitoneOn (flatQuotient (-z.val))
      (s := Ici (0 : ℝ)) (fun x : ℝ => -x) (fun _ _ _ _ h => neg_le_neg h) ?_).trans
      (eVariationOn_flatQuotient_Ici (-z.val) 0)
    intro x hx
    change (0 : ℝ) ≤ -x
    exact neg_nonneg.mpr (show x ≤ 0 from hx)
  have hsplit : eVariationOn (flatQuotient z.val) univ =
      eVariationOn (flatQuotient z.val) (Iic (0 : ℝ)) +
        eVariationOn (flatQuotient z.val) (Ici (0 : ℝ)) := by
    have hs : IsGreatest (Iic (0 : ℝ)) 0 := ⟨by simp, fun _ h => h⟩
    have ht : IsLeast (Ici (0 : ℝ)) 0 := ⟨by simp, fun _ h => h⟩
    have hu : Iic (0 : ℝ) ∪ Ici 0 = univ := by
      ext x
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total x 0
    simpa only [hu] using eVariationOn.union (flatQuotient z.val) hs ht
  rw [hsplit]
  exact add_le_add hleft (eVariationOn_flatQuotient_Ici z.val 0)

theorem boundedVariationOn_divisor_flatQuotient (z : {z : ℂ // XiC z = 0}) :
    BoundedVariationOn (flatQuotient z.val) univ :=
  ne_top_of_le_ne_top (by finiteness) (eVariationOn_divisor_flatQuotient_le z)

/-- Whole-line finite variation has exactly the native divisor-or-zero domain. -/
theorem boundedVariationOn_flatQuotient_iff (z : ℂ) :
    BoundedVariationOn (flatQuotient z) univ ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    apply (bounded_flatQuotient_iff z).mp
    refine ⟨(eVariationOn (flatQuotient z) univ).toReal + ‖flatQuotient z 0‖, fun x => ?_⟩
    have hd : ‖flatQuotient z x - flatQuotient z 0‖ ≤
        (eVariationOn (flatQuotient z) univ).toReal := by
      simpa [dist_eq_norm] using h.dist_le (mem_univ x) (mem_univ 0)
    calc
      ‖flatQuotient z x‖ = ‖(flatQuotient z x - flatQuotient z 0) + flatQuotient z 0‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖flatQuotient z x - flatQuotient z 0‖ + ‖flatQuotient z 0‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hd le_rfl
  · rintro (rfl | hz)
    · simp [BoundedVariationOn, eVariationOn, flatQuotient_zero]
    · exact boundedVariationOn_divisor_flatQuotient ⟨z, hz⟩

end RHTower.PaperThetaEndpoint
