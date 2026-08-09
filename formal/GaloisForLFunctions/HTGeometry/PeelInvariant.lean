import GaloisForLFunctions.HTGeometry.PeelStep

/-!
# The peel restores the shape of the starting vector

After one peel the new starting vector's newest entry is

`(∏_{i<m}Q_i)·[W(Q_m,v_m)/Q_m² + α·q·Q_m']`,

whose leading term carries the factor `(∏_{i<m}Q_i)·α·q`.  Dividing the whole vector by
`Q_m·(∏_{i<m}Q_i)·α·q` — free, by the orbit rescaling law — leaves

`Q_m'/Q_m + W(Q_m,v_m)/(α q Q_m³)`,

and the correction has degree `−deg Q_m − 2 ≤ −3`.  So the rescaled vector is border-shaped again,
which is what lets the peel be iterated down the flag.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-- The newest entry of the first limit vector, in closed form. -/
theorem limVec_one_top {n : ℕ} (hQ : ∀ j, Q j ≠ 0) (α : ℂ) {L : ℕ → CascadeField}
    (hL : L (n + 1) = logFactor (Q (n + 1)) (n + 1)) :
    limVec Q v (n + 1) α L (peelRes Q (n + 1)) 1 (n + 1)
      = prodHead Q (n + 1)
        * (fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)
              / fact (Q (n + 1)) (n + 1) ^ 2
            + fact (Q (n + 1)).derivative (n + 1)
              * (algebraMap ℂ CascadeField α
                * algebraMap ℂ CascadeField ((Q (n + 2)).natDegree : ℂ))) := by
  have hne : fact (Q (n + 1)) (n + 1) ≠ 0 := fact_ne_zero (hQ (n + 1)) (n + 1)
  rw [limVec_succ_of_le Q v α L (peelRes Q (n + 1)) 0 (n + 1) (le_refl (n + 1)),
    gradShift_top, limVec_zero, hL, topShift_logFactor_eq, fpderiv_logSum_top Q v (hQ (n + 1))]
  have hres : peelRes Q (n + 1) 0
      = algebraMap ℂ CascadeField ((Q (n + 1 + 1)).natDegree : ℂ) := rfl
  have hph : prodHead Q (n + 1 + 1) = prodHead Q (n + 1) * fact (Q (n + 1)) (n + 1) :=
    prodHead_succ Q (n + 1)
  rw [hres, hph, logFactor]
  field_simp

/-- **The peel restores the border shape.** -/
theorem borderShape_rescaled {n : ℕ} (hQ : ∀ j, Q j ≠ 0)
    (hq1 : 1 ≤ (Q (n + 1)).natDegree) (hv1 : (v (n + 1)).natDegree = 1)
    {α : ℂ} (hα : α ≠ 0) (hq2 : 1 ≤ (Q (n + 2)).natDegree)
    {L : ℕ → CascadeField} (hL : L (n + 1) = logFactor (Q (n + 1)) (n + 1)) :
    BorderShape Q (n + 1)
      (fun l => (fact (Q (n + 1)) (n + 1) * prodHead Q (n + 1)
          * algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹
        * limVec Q v (n + 1) α L (peelRes Q (n + 1)) 1 l) := by
  have hne : fact (Q (n + 1)) (n + 1) ≠ 0 := fact_ne_zero (hQ (n + 1)) (n + 1)
  have hhead : prodHead Q (n + 1) ≠ 0 := prodHead_ne_zero hQ (n + 1)
  have hcne : (α * ((Q (n + 2)).natDegree : ℂ)) ≠ 0 := by
    refine mul_ne_zero hα ?_
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : (Q (n + 2)).natDegree ≠ 0)
  have hcfield : algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr hcne
  have hαf : algebraMap ℂ CascadeField α ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr hα
  have hqf : algebraMap ℂ CascadeField ((Q (n + 2)).natDegree : ℂ) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr
      (by exact_mod_cast Nat.cast_ne_zero.mpr (by omega : (Q (n + 2)).natDegree ≠ 0))
  -- the explicit difference
  have hdiff : (fact (Q (n + 1)) (n + 1) * prodHead Q (n + 1)
          * algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹
        * limVec Q v (n + 1) α L (peelRes Q (n + 1)) 1 (n + 1)
      - logFactor (Q (n + 1)) (n + 1)
      = fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)
        * ((fact (Q (n + 1)) (n + 1))⁻¹ ^ 3
          * (algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹) := by
    rw [limVec_one_top hQ α hL, logFactor, map_mul]
    field_simp
    ring
  rw [BorderShape]
  rw [hdiff]
  -- the degree bound
  have h1 : TopDegLE (n + 1)
      ((scaledLogWronskian (Q (n + 1)) (v (n + 1))).natDegree : ℤ)
      (fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)) := topDegLE_fact _ _
  have h2 : TopDegLE (n + 1) (-((Q (n + 1)).natDegree : ℤ))
      ((fact (Q (n + 1)) (n + 1))⁻¹) := topDegLE_inv_fact _ (hQ (n + 1))
  have h3 : TopDegLE (n + 1)
      (-((Q (n + 1)).natDegree : ℤ) + (-((Q (n + 1)).natDegree : ℤ)
        + -((Q (n + 1)).natDegree : ℤ)))
      ((fact (Q (n + 1)) (n + 1))⁻¹ ^ 3) := by
    have h := TopDegLE.mul h2 (TopDegLE.mul h2 h2)
    rw [show ((fact (Q (n + 1)) (n + 1))⁻¹ ^ 3)
        = (fact (Q (n + 1)) (n + 1))⁻¹ * ((fact (Q (n + 1)) (n + 1))⁻¹
          * (fact (Q (n + 1)) (n + 1))⁻¹) by ring]
    exact h
  have h4 : TopFree (n + 1)
      ((algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹) := by
    rw [← map_inv₀]
    exact topFree_algebraMap_complex (n + 1) _
  have hW : (scaledLogWronskian (Q (n + 1)) (v (n + 1))).natDegree
      ≤ 2 * (Q (n + 1)).natDegree - 2 := natDegree_scaledLogWronskian_le_sub_two hq1 hv1
  have hmul := TopDegLE.mul h1 (TopDegLE.mul h3 (TopFree.topDegLE h4))
  refine TopDegLE.mono ?_ hmul
  omega

end GaloisForLFunctions.HTGeometry
