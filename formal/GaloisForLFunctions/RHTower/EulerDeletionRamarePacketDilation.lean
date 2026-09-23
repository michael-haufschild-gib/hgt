import GaloisForLFunctions.RHTower.EulerDeletionRamarePhysical
import Zeta23.FromPNTPlus.MellinCalculus

/-!
# Support-sensitive Ramaré packet dilation

The reciprocal dilation in a physical Ramaré packet has a literal `1 / p`
energy factor.  Cofactor support removes the apparent interval below the
unit boundary exactly; no prime packet or cross-prime covariance is discarded.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower.DeletionRamarePhysical

open RHTower.DeletionRamareDilation

private theorem integral_Ioi_eq_integral_Ici_one_of_zero_on_Ioo
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x = 0) :
    (∫ x in Ioi a, f x ^ (2 : ℕ)) = ∫ x in Ici (1 : ℝ), f x ^ (2 : ℕ) := by
  let g : ℝ → ℝ := (Ioi a).indicator (fun x => f x ^ (2 : ℕ))
  have hsupp : Function.support g ⊆ Ici (1 : ℝ) := by
    intro x hx
    change g x ≠ 0 at hx
    by_contra hx1
    have hxlt : x < 1 := lt_of_not_ge hx1
    by_cases hxa : x ∈ Ioi a
    · have hx0 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ha0 hxa, hxlt⟩
      exact hx (by simp [g, hxa, hf x hx0])
    · simp [g, hxa] at hx
  calc
    (∫ x in Ioi a, f x ^ (2 : ℕ)) = ∫ x, g x := by
      symm
      simpa [g] using
        (integral_indicator (μ := volume) (f := fun x => f x ^ (2 : ℕ)) measurableSet_Ioi)
    _ = ∫ x in Ici (1 : ℝ), g x := by
      simpa only [setIntegral_univ, univ_inter] using
        (SetIntegral.integral_eq_integral_inter_of_support_subset
          (s := univ) (t := Ici (1 : ℝ)) (f := g) (μ := volume) hsupp measurableSet_Ici)
    _ = ∫ x in Ici (1 : ℝ) ∩ Ioi a, f x ^ (2 : ℕ) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ x in Ici (1 : ℝ), f x ^ (2 : ℕ) := by
      by_cases ha : a < 1
      · have hinter : Ici (1 : ℝ) ∩ Ioi a = Ici (1 : ℝ) := by
          ext x
          constructor
          · intro hx
            exact hx.1
          · intro hx
            exact ⟨hx, lt_of_lt_of_le ha hx⟩
        rw [hinter]
      · have haeq : a = 1 := le_antisymm ha1 (le_of_not_gt ha)
        subst a
        have hinter : Ici (1 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
          ext x
          constructor
          · exact fun hx => hx.2
          · exact fun hx => ⟨show (1 : ℝ) ≤ x from le_of_lt hx, hx⟩
        rw [hinter]
        change (∫ x, f x ^ (2 : ℕ) ∂volume.restrict (Ioi (1 : ℝ))) =
          ∫ x, f x ^ (2 : ℕ) ∂volume.restrict (Ici (1 : ℝ))
        rw [restrict_Ioi_eq_restrict_Ici]

private theorem integral_Ioi_eq_integral_Ici_of_zero_on_Ioo
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x = 0) :
    (∫ x in Ioi a, f x) = ∫ x in Ici (1 : ℝ), f x := by
  let g : ℝ → ℝ := (Ioi a).indicator f
  have hsupp : Function.support g ⊆ Ici (1 : ℝ) := by
    intro x hx
    change g x ≠ 0 at hx
    by_contra hx1
    have hxlt : x < 1 := lt_of_not_ge hx1
    by_cases hxa : x ∈ Ioi a
    · have hx0 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ha0 hxa, hxlt⟩
      exact hx (by simp [g, hxa, hf x hx0])
    · simp [g, hxa] at hx
  calc
    (∫ x in Ioi a, f x) = ∫ x, g x := by
      symm
      simpa [g] using (integral_indicator (μ := volume) (f := f) measurableSet_Ioi)
    _ = ∫ x in Ici (1 : ℝ), g x := by
      simpa only [setIntegral_univ, univ_inter] using
        (SetIntegral.integral_eq_integral_inter_of_support_subset
          (s := univ) (t := Ici (1 : ℝ)) (f := g) (μ := volume) hsupp measurableSet_Ici)
    _ = ∫ x in Ici (1 : ℝ) ∩ Ioi a, f x := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ x in Ici (1 : ℝ), f x := by
      by_cases ha : a < 1
      · have hinter : Ici (1 : ℝ) ∩ Ioi a = Ici (1 : ℝ) := by
          ext x
          constructor
          · intro hx
            exact hx.1
          · intro hx
            exact ⟨hx, lt_of_lt_of_le ha hx⟩
        rw [hinter]
      · have haeq : a = 1 := le_antisymm ha1 (le_of_not_gt ha)
        subst a
        have hinter : Ici (1 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
          ext x
          constructor
          · exact fun hx => hx.2
          · exact fun hx => ⟨show (1 : ℝ) ≤ x from le_of_lt hx, hx⟩
        rw [hinter]
        change (∫ x, f x ∂volume.restrict (Ioi (1 : ℝ))) =
          ∫ x, f x ∂volume.restrict (Ici (1 : ℝ))
        rw [restrict_Ioi_eq_restrict_Ici]

/-- A Ramaré cofactor's reciprocal dilation has its exact `1 / p` physical
energy factor: the portion below `1` vanishes identically. -/
theorem integral_dilate_cofactor_sq (P : Finset ℕ) (M p : ℕ) (hp : 0 < p) :
    (∫ u in Ioi (1 : ℝ), dilate p (cofactor P M p) u ^ (2 : ℕ)) =
      (1 / (p : ℝ)) * ∫ v in Ioi (1 : ℝ), cofactor P M p v ^ (2 : ℕ) := by
  rw [integral_dilate_sq p hp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp.ne'
  have ha0 : 0 < 1 / (p : ℝ) := by positivity
  have ha1 : 1 / (p : ℝ) ≤ 1 := (div_le_one hpR).mpr hp1
  rw [integral_Ioi_eq_integral_Ici_one_of_zero_on_Ioo (1 / (p : ℝ)) ha0 ha1
    (cofactor P M p) (fun x hx => cofactor_eq_zero_of_mem_Ioo_one P M p hp hx)]
  change (1 / (p : ℝ)) * (∫ v, cofactor P M p v ^ (2 : ℕ) ∂volume.restrict (Ici (1 : ℝ))) = _
  rw [← restrict_Ioi_eq_restrict_Ici]

/-- Exact off-diagonal covariance of two physical Ramaré cofactor dilations.
The only transformation is reciprocal change of variables; the remaining
ratio `p / q` is the cross-prime resonance that EDQ must control. -/
theorem integral_dilate_cofactor_mul_unequal (P : Finset ℕ) (M p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    (∫ u in Ioi (1 : ℝ),
      dilate p (cofactor P M p) u * dilate q (cofactor P M q) u) =
      (1 / (q : ℝ)) * ∫ v in Ioi (1 : ℝ),
        cofactor P M p v * cofactor P M q (((p : ℝ) / (q : ℝ)) * v) := by
  rw [integral_dilate_mul_unequal p q hp hq]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp.ne'
  have ha0 : 0 < 1 / (p : ℝ) := by positivity
  have ha1 : 1 / (p : ℝ) ≤ 1 := (div_le_one hpR).mpr hp1
  rw [integral_Ioi_eq_integral_Ici_of_zero_on_Ioo (1 / (p : ℝ)) ha0 ha1
    (fun v => cofactor P M p v * cofactor P M q (((p : ℝ) / (q : ℝ)) * v))]
  · change (1 / (q : ℝ)) *
      (∫ v, cofactor P M p v * cofactor P M q (((p : ℝ) / (q : ℝ)) * v)
        ∂volume.restrict (Ici (1 : ℝ))) = _
    rw [← restrict_Ioi_eq_restrict_Ici]
  · intro v hv
    rw [cofactor_eq_zero_of_mem_Ioo_one P M p hp hv, zero_mul]

end RHTower.DeletionRamarePhysical
