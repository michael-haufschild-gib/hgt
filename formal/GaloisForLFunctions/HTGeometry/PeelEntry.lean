import GaloisForLFunctions.HTGeometry.PeelInvariant

/-!
# The border row enters the peel

The logarithmic Jacobian is the orbit matrix of the border row, and the border row satisfies every
hypothesis the peel step consumes: it lies in the low subalgebra, vanishes above its level, is
border-shaped with zero error term, and its value at infinity is the border row one level down.

That last point is what makes the induction's side condition self-sustaining: the limit vector is
always a border row, so the condition `L_m = Q_m'/Q_m` needed by `limVec_one_top` holds at every
level automatically.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-! ## The Jacobian is the border row's orbit -/

/-- **The logarithmic Jacobian is the orbit matrix of the border row.** -/
theorem logJetJacobian_eq_jetOrbitMatrix (Q v : ℕ → Polynomial ℂ) (n : ℕ) :
    logJetJacobian Q v n = jetOrbitMatrix Q v (n + 1) (n + 1) (logBorder Q (n + 1)) := by
  rw [logJetJacobian_eq_orbit]
  rfl

/-! ## The border row's own data -/

theorem logBorder_of_le {m l : ℕ} (h : l ≤ m) : logBorder Q m l = logFactor (Q l) l := by
  rw [logBorder, if_pos h]

theorem logBorder_of_gt {m l : ℕ} (h : m < l) : logBorder Q m l = 0 := by
  rw [logBorder, if_neg (by omega)]

theorem logBorder_mem_lowSub (Q v : ℕ → Polynomial ℂ) (m l : ℕ) :
    logBorder Q m l ∈ lowSub Q v m := by
  by_cases h : l ≤ m
  · rw [logBorder_of_le h]
    exact logFactorQ_mem_lowSub Q v h
  · rw [logBorder_of_gt (by omega : m < l)]
    exact Subalgebra.zero_mem _

theorem logBorder_sub_self (Q : ℕ → Polynomial ℂ) (m : ℕ) :
    logBorder Q m m - logFactor (Q m) m = 0 := by
  rw [logBorder_of_le (le_refl m), sub_self]

theorem logBorder_sub_mem_lowSub (Q v : ℕ → Polynomial ℂ) (m : ℕ) :
    logBorder Q m m - logFactor (Q m) m ∈ lowSub Q v m := by
  rw [logBorder_sub_self]
  exact Subalgebra.zero_mem _

/-! ## Its value at infinity is the border row one level down -/

/-- **The border row converges to the border row one level down.** -/
theorem topLim_logBorder {m' : ℕ} (hq : 1 ≤ (Q (m' + 1)).natDegree) (l : ℕ) :
    TopLim (m' + 1) (logBorder Q (m' + 1) l) (logBorder Q m' l) := by
  by_cases hl : l ≤ m'
  · rw [logBorder_of_le (by omega : l ≤ m' + 1), logBorder_of_le hl]
    exact topLim_const
  · by_cases hl2 : l = m' + 1
    · subst hl2
      rw [logBorder_of_le (le_refl (m' + 1)), logBorder_of_gt (by omega : m' < m' + 1),
        TopLim, sub_zero]
      exact topDegLE_logFactor (m' + 1) hq
    · rw [logBorder_of_gt (by omega : m' + 1 < l), logBorder_of_gt (by omega : m' < l)]
      exact topLim_const

/-! ## The border row is border-shaped, at every level -/

theorem borderShape_logBorder' (Q : ℕ → Polynomial ℂ) (m : ℕ) :
    BorderShape Q m (logBorder Q m) := borderShape_logBorder Q m

/-- The side condition of `limVec_one_top` holds for a border row. -/
theorem logBorder_top_eq (Q : ℕ → Polynomial ℂ) (m : ℕ) :
    logBorder Q m m = logFactor (Q m) m := logBorder_of_le (le_refl m)


/-! ## The shifted operator keeps degree zero on a border row -/

theorem topFree_inv_prodHead {m k : ℕ} (h : k ≤ m) :
    TopFree m ((prodHead Q k)⁻¹) := by
  rw [prodHead, ← Finset.prod_inv_distrib]
  refine topFree_prod _ _ fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  exact topFree_inv_fact (by omega) (Q j)

theorem topDegLE_prodJet_top {m : ℕ} (hv : (v m).natDegree ≤ 1) :
    TopDegLE m 1 (prodJet Q v m) := by
  rw [prodJet_eq]
  have h1 : TopDegLE m 0 (prodHead Q m) := TopFree.topDegLE (topFree_prodHead (le_refl m))
  have h2 : TopDegLE m ((v m).natDegree : ℤ) (fact (v m) m) := topDegLE_fact m (v m)
  have hmul := TopDegLE.mul h1 h2
  refine TopDegLE.mono ?_ hmul
  have : ((v m).natDegree : ℤ) ≤ 1 := by exact_mod_cast hv
  omega

/-- **The shifted operator keeps degree zero away from the newest coordinate.** -/
theorem topDegLE_gradShift_zero {m k : ℕ} (hk : k < m) (hv : (v m).natDegree ≤ 1)
    (hQ : ∀ j, Q j ≠ 0) {u : ℕ → CascadeField} (hmem : ∀ l, u l ∈ lowSub Q v m)
    (hlow : ∀ l, l < m → TopDegLE m 0 (u l)) (htop : TopDegLE m (-1) (u m)) :
    TopDegLE m 0 (gradShift Q v m u k) := by
  rw [gradShift]
  refine TopDegLE.add (TopDegLE.prodDerivation hv (hmem k) (hlow k hk)) ?_
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ m := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · rw [jetResponse_of_gt v hQ hk, mul_assoc]
    have hlog : TopDegLE l 0 (logFactor (Q k) k) :=
      TopFree.topDegLE (topFree_logFactor (by omega) (Q k))
    have hmul := TopDegLE.mul hlog (TopDegLE.mul (topDegLE_prodJet_top (Q := Q) hv) htop)
    refine TopDegLE.mono ?_ hmul
    omega
  · have hfree : TopFree m (jetResponse (Q := Q) v k l) := topFree_jetResponse hlt
    have hmul := TopDegLE.mul (TopFree.topDegLE hfree) (hlow l hlt)
    refine TopDegLE.mono ?_ hmul
    omega

/-! ## The rescaled peel vector converges to the next border row -/

/-- **The rescaled peeled vector converges to the border row one level down.**  This is the side
condition of the induction, and it is self-sustaining. -/
theorem topLim_rescaled_limVec {n : ℕ} (hQ : ∀ j, Q j ≠ 0)
    (hq1 : 1 ≤ (Q (n + 1)).natDegree) (hv1 : (v (n + 1)).natDegree = 1)
    {α : ℂ} (hα : α ≠ 0) (hq2 : 1 ≤ (Q (n + 2)).natDegree) (l : ℕ) :
    TopLim (n + 1)
      ((fact (Q (n + 1)) (n + 1) * prodHead Q (n + 1)
          * algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹
        * limVec Q v (n + 1) α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 1 l)
      (logBorder Q n l) := by
  set c : CascadeField := fact (Q (n + 1)) (n + 1) * prodHead Q (n + 1)
      * algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)) with hcdef
  have hne : fact (Q (n + 1)) (n + 1) ≠ 0 := fact_ne_zero (hQ (n + 1)) (n + 1)
  have hhead : prodHead Q (n + 1) ≠ 0 := prodHead_ne_zero hQ (n + 1)
  have hq2ne : ((Q (n + 2)).natDegree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have hcne : (α * ((Q (n + 2)).natDegree : ℂ)) ≠ 0 := mul_ne_zero hα hq2ne
  have hcfield : algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr hcne
  have hcne0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (mul_ne_zero hne hhead) hcfield
  have hcinv : TopDegLE (n + 1) (-((Q (n + 1)).natDegree : ℤ)) c⁻¹ := by
    rw [hcdef, mul_inv, mul_inv]
    have h1 : TopDegLE (n + 1) (-((Q (n + 1)).natDegree : ℤ))
        ((fact (Q (n + 1)) (n + 1))⁻¹) := topDegLE_inv_fact _ (hQ (n + 1))
    have h2 : TopFree (n + 1) ((prodHead Q (n + 1))⁻¹) :=
      topFree_inv_prodHead (le_refl (n + 1))
    have h3 : TopFree (n + 1)
        ((algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ)))⁻¹) := by
      rw [← map_inv₀]
      exact topFree_algebraMap_complex (n + 1) _
    have hmul := TopDegLE.mul (TopDegLE.mul h1 (TopFree.topDegLE h2)) (TopFree.topDegLE h3)
    refine TopDegLE.mono ?_ hmul
    omega
  by_cases hl : l ≤ n
  · -- below the newest level: the border entry survives, the rest is a degree drop
    rw [logBorder_of_le hl,
      limVec_succ_of_le Q v α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 0 l (by omega),
      limVec_zero]
    have hres : peelRes Q (n + 1) 0
        = algebraMap ℂ CascadeField ((Q (n + 2)).natDegree : ℂ) := rfl
    have hkey : prodHead Q (n + 1 + 1)
        * (algebraMap ℂ CascadeField α * peelRes Q (n + 1) 0) = c := by
      rw [hres, prodHead_succ, hcdef, map_mul]
      ring
    have hsplit : c⁻¹ * (gradShift Q v (n + 1) (logBorder Q (n + 1)) l
          + logFactor (Q l) l * (prodHead Q (n + 1 + 1)
            * (algebraMap ℂ CascadeField α * peelRes Q (n + 1) 0)))
        = c⁻¹ * gradShift Q v (n + 1) (logBorder Q (n + 1)) l + logFactor (Q l) l := by
      rw [hkey, mul_add, mul_comm (logFactor (Q l) l) c, ← mul_assoc,
        inv_mul_cancel₀ hcne0, one_mul]
    rw [hsplit, TopLim, add_sub_cancel_right]
    have hgs : TopDegLE (n + 1) 0 (gradShift Q v (n + 1) (logBorder Q (n + 1)) l) := by
      refine topDegLE_gradShift_zero (by omega) (by omega) hQ
        (fun l' => logBorder_mem_lowSub Q v (n + 1) l') (fun l' hl' => ?_) ?_
      · rw [logBorder_of_le (by omega : l' ≤ n + 1)]
        exact TopFree.topDegLE (topFree_logFactor (by omega) (Q l'))
      · rw [logBorder_of_le (le_refl (n + 1))]
        exact topDegLE_logFactor (n + 1) hq1
    have hmul := TopDegLE.mul hcinv hgs
    refine TopDegLE.mono ?_ hmul
    omega
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [logBorder_of_gt (by omega : n < n + 1), TopLim, sub_zero]
      have hshape := borderShape_rescaled hQ hq1 hv1 hα hq2
        (logBorder_top_eq Q (n + 1))
      rw [BorderShape] at hshape
      have hsplit : (c⁻¹ * limVec Q v (n + 1) α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 1 (n + 1))
          = (c⁻¹ * limVec Q v (n + 1) α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 1 (n + 1)
              - logFactor (Q (n + 1)) (n + 1)) + logFactor (Q (n + 1)) (n + 1) := by
        ring
      rw [hsplit]
      exact TopDegLE.add (TopDegLE.mono (by norm_num) hshape)
        (topDegLE_logFactor (n + 1) hq1)
    · rw [logBorder_of_gt (by omega : n < l),
        limVec_succ_of_gt Q v α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 0 l (by omega),
        mul_zero]
      exact topLim_const

end GaloisForLFunctions.HTGeometry
