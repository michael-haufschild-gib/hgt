import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionCrossGram

/-!+# The arithmetic lattice of infinite tent spaces

Divisibility gives nested orthogonal projections. Intersections always use the least
common multiple; for spacings with a common divisor greater than one, the product
itself is that intersection projection.+-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem coprimeProjector_comp_of_dvd (d e : ℕ) (h : d + 2 ∣ e + 2) :
    (coprimeProjector d).comp (coprimeProjector e) = coprimeProjector e := by
  have hx := comp_coprimeProjector_eq e (coprimeProjector d)
    (ContinuousLinearMap.id ℝ Velocity) (fun j =>
      coprimeProjection_tent_of_dvd d e j (h.trans (coprimeCenter_dvd e j)))
  simpa using hx

theorem coprimeProjector_comp_of_dvd_reverse (d e : ℕ) (h : d + 2 ∣ e + 2) :
    (coprimeProjector e).comp (coprimeProjector d) = coprimeProjector e := by
  have hx := congrArg ContinuousLinearMap.adjoint (coprimeProjector_comp_of_dvd d e h)
  simpa only [ContinuousLinearMap.adjoint_comp, coprimeProjector_adjoint] using hx

/-- Index of the spacing given by the least common multiple. -/
def coprimeLcm (d e : ℕ) : ℕ := Nat.lcm (d + 2) (e + 2) - 2

@[simp]
theorem coprimeLcm_add_two (d e : ℕ) :
    coprimeLcm d e + 2 = Nat.lcm (d + 2) (e + 2) := by
  have hp : 0 < Nat.lcm (d + 2) (e + 2) := Nat.lcm_pos (by omega) (by omega)
  have hl := Nat.le_of_dvd hp (Nat.dvd_lcm_left (d + 2) (e + 2))
  unfold coprimeLcm
  omega

theorem coprimeLcm_comm (d e : ℕ) : coprimeLcm d e = coprimeLcm e d := by
  simp only [coprimeLcm, Nat.lcm_comm]

theorem coprimeLcm_dvd_center_iff (d e j : ℕ) :
    coprimeLcm d e + 2 ∣ coprimeCenter e j ↔ d + 2 ∣ coprimeCenter e j := by
  rw [coprimeLcm_add_two]
  exact ⟨fun h => (Nat.dvd_lcm_left _ _).trans h,
    fun h => Nat.lcm_dvd h (coprimeCenter_dvd e j)⟩

/-- A common divisor eliminates every adjacent cross-family interaction. -/
theorem coprimeProjector_comp_eq_lcm (d e : ℕ)
    (hg : 2 ≤ Nat.gcd (d + 2) (e + 2)) :
    (coprimeProjector d).comp (coprimeProjector e) = coprimeProjector (coprimeLcm d e) := by
  have h := comp_coprimeProjector_eq e (coprimeProjector d)
    (coprimeProjector (coprimeLcm d e)) (fun j => by
      simp only [coprimeProjector_apply]
      rw [coprimeProjection_tent_of_common_divisor d e j _ hg
        (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)]
      rw [coprimeProjection_tent_of_common_divisor (coprimeLcm d e) e j (e + 2)
        (by omega) (by simpa using Nat.dvd_lcm_right (d + 2) (e + 2)) (dvd_refl _)]
      simp only [coprimeLcm_dvd_center_iff])
  exact h.trans (coprimeProjector_comp_of_dvd_reverse e (coprimeLcm d e)
    (by simpa using Nat.dvd_lcm_right (d + 2) (e + 2)))

theorem coprimeProjection_commute_of_gcd (d e : ℕ)
    (hg : 2 ≤ Nat.gcd (d + 2) (e + 2)) (q : Velocity) :
    coprimeProjection d (coprimeProjection e q) =
      coprimeProjection e (coprimeProjection d q) := by
  have hde := coprimeProjector_comp_eq_lcm d e hg
  have hed := coprimeProjector_comp_eq_lcm e d (by simpa only [Nat.gcd_comm] using hg)
  rw [coprimeLcm_comm e d] at hed
  exact congrArg (fun A : Velocity →L[ℝ] Velocity => A q) (hde.trans hed.symm)

/-- Simultaneous fixed points are exactly the least-common-multiple tent space. -/
theorem coprimeProjection_lcm_fixed_iff (d e : ℕ) (q : Velocity) :
    coprimeProjection (coprimeLcm d e) q = q ↔
      coprimeProjection d q = q ∧ coprimeProjection e q = q := by
  constructor
  · intro hq
    have hd := congrArg (fun A : Velocity →L[ℝ] Velocity => A q)
      (coprimeProjector_comp_of_dvd d (coprimeLcm d e)
        (by simpa using Nat.dvd_lcm_left (d + 2) (e + 2)))
    have he := congrArg (fun A : Velocity →L[ℝ] Velocity => A q)
      (coprimeProjector_comp_of_dvd e (coprimeLcm d e)
        (by simpa using Nat.dvd_lcm_right (d + 2) (e + 2)))
    change coprimeProjection d (coprimeProjection (coprimeLcm d e) q) =
      coprimeProjection (coprimeLcm d e) q at hd
    change coprimeProjection e (coprimeProjection (coprimeLcm d e) q) =
      coprimeProjection (coprimeLcm d e) q at he
    exact ⟨by simpa only [hq] using hd, by simpa only [hq] using he⟩
  · rintro ⟨hd, he⟩
    obtain ⟨v, rfl⟩ := (coprimeProjection_eq_self_iff d q).1 hd
    have hv : ∀ j, ¬coprimeLcm d e + 2 ∣ coprimeCenter d j → v j = 0 := by
      intro j hj
      have hn : ¬e + 2 ∣ coprimeCenter d j := by
        intro hn
        apply hj
        rw [coprimeLcm_add_two]
        exact Nat.lcm_dvd (coprimeCenter_dvd d j) hn
      have ht := congrArg (fun r : Velocity => primitive r (coprimeCenter d j)) he
      rw [coprimeProjection_eq_extension, primitive_coprimeExtension_nat,
        primitive_coprimeExtension_active] at ht
      simpa [hn] using ht.symm
    have hsum := (coprimeProjector (coprimeLcm d e)).hasSum (hasSum_coprimeExtension d v)
    apply hsum.unique
    apply (hasSum_coprimeExtension d v).congr_fun
    intro j
    simp only [map_smul, coprimeProjector_apply]
    by_cases hj : coprimeLcm d e + 2 ∣ coprimeCenter d j
    · rw [coprimeProjection_tent_of_dvd _ _ _ hj]
    · rw [hv j hj]
      simp

/-- Exact intersection law for the actual closed infinite extension ranges. -/
theorem range_coprimeExtension_inter (d e : ℕ) :
    Set.range (coprimeExtension d) ∩ Set.range (coprimeExtension e) =
      Set.range (coprimeExtension (coprimeLcm d e)) := by
  apply Set.ext
  intro q
  change (∃ v, coprimeExtension d v = q) ∧ (∃ v, coprimeExtension e v = q) ↔
    ∃ v, coprimeExtension (coprimeLcm d e) v = q
  rw [← coprimeProjection_eq_self_iff, ← coprimeProjection_eq_self_iff,
    ← coprimeProjection_eq_self_iff, coprimeProjection_lcm_fixed_iff]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
