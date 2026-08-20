import GaloisForLFunctions.HTGeometry.DifferentialClosureTower
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealTransport

/-!
# The union of the tower is differentially closed

A finite differential system over the union has only finitely many coefficients, so it descends to
one stage of the tower.  If it has a solution in any differential field extension of the union, then
the descended system is consistent — a relation exhibiting one in the radical differential ideal it
generates would push forward, and the solution forbids that — and the next stage of the tower solves
every consistent system over the stage below it.

So the union solves every finite differential system that is solvable at all: it is a differentially
closed field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable (F : Type u) [Field F] [Algebra ℚ F] [Differential F]

/-- Finitely many elements of the union of the tower already live in one stage. -/
theorem exists_stage_forall_mem_range (S : Finset (diffClosure F)) :
    ∃ m : ℕ, ∀ x ∈ S, ∃ a : diffTowerCarrier F m, diffTowerLimitHom F m a = x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert x S _ ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨k, a, ha⟩ :=
        Ring.DirectLimit.exists_of (G := diffTowerCarrier F)
          (f := fun _ _ h => ⇑(diffTowerHom F h)) x
      refine ⟨max m k, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzS
      · refine ⟨diffTowerHom F (le_max_right m k) a, ?_⟩
        rw [diffTowerLimitHom_diffTowerHom]
        exact ha
      · obtain ⟨b, hb⟩ := hm z hzS
        refine ⟨diffTowerHom F (le_max_left m k) b, ?_⟩
        rw [diffTowerLimitHom_diffTowerHom]
        exact hb

/-- A polynomial whose coefficients come from a stage is the coefficient extension of one over that
stage. -/
theorem exists_preimage_of_coeffs_mem_range {ι : Type*} (m : ℕ)
    (p : DifferentialPolynomial ι (diffClosure F))
    (h : ∀ u, ∃ a : diffTowerCarrier F m, diffTowerLimitHom F m a = MvPolynomial.coeff u p) :
    ∃ q : DifferentialPolynomial ι (diffTowerCarrier F m),
      differentialCoeffExtend (ι := ι) (F := diffTowerCarrier F m) (L := diffClosure F) q = p := by
  classical
  refine ⟨∑ u ∈ p.support, MvPolynomial.monomial u (h u).choose, ?_⟩
  refine MvPolynomial.ext _ _ fun v => ?_
  rw [differentialCoeffExtend, MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
  by_cases hv : v ∈ p.support
  · rw [Finset.sum_eq_single v]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
      exact (h v).choose_spec
    · intro u _ hu
      rw [MvPolynomial.coeff_monomial, if_neg hu]
    · intro hcon
      exact absurd hv hcon
  · have hzero : ∀ u ∈ p.support, MvPolynomial.coeff v (MvPolynomial.monomial u (h u).choose) = 0 := by
      intro u hu
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hcon
      exact hv (hcon ▸ hu)
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, map_zero]
    exact (MvPolynomial.notMem_support_iff.mp hv).symm

set_option maxHeartbeats 1600000 in
/-- **The union of the tower is differentially closed.**  A finite differential system over the
union which has a solution in some differential field extension already has one in the union.

Finitely many coefficients live in one stage, so the system descends there; the descended system is
consistent because a relation exhibiting one would push forward to the union, where the given
solution forbids it; and the next stage of the tower solves every consistent system over that
stage. -/
theorem exists_point_of_solution_ext {n : ℕ}
    (T : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F)))
    (E : DiffFieldExt (diffClosure F)) (z : ULift.{u} (Fin n) → E.carrier)
    (hz : ∀ p ∈ T, differentialPolynomialEvalOver (K := diffClosure F) z p = 0) :
    ∃ y : ULift.{u} (Fin n) → diffClosure F,
      ∀ p ∈ T, differentialPolynomialEvalOver (K := diffClosure F) y p = 0 := by
  classical
  letI : Differential (DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F)) :=
    differentialPolynomialOverDifferential _ _
  have hTprop : (1 : DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F))
      ∉ radicalDifferentialIdeal (T : Set (DifferentialPolynomial (ULift.{u} (Fin n))
        (diffClosure F))) := by
    intro hone
    have hker := isRadical_ker_of_field
      ((differentialPolynomialEvalOver (K := diffClosure F) (L := E.carrier) z :
        DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F) →ₐ[diffClosure F] E.carrier) :
          DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F) →+* E.carrier)
      (fun x => differentialPolynomialEvalOver_derivation (K := diffClosure F) z x)
    have hle := radicalDifferentialIdeal_le
      (S := (T : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F))))
      (I := RingHom.ker
        ((differentialPolynomialEvalOver (K := diffClosure F) (L := E.carrier) z :
          DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F) →ₐ[diffClosure F] E.carrier) :
            DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F) →+* E.carrier))
      (fun t ht => hz t (by simpa using ht)) hker.1 hker.2
    have hone0 := hle hone
    rw [RingHom.mem_ker] at hone0
    simp only [map_one] at hone0
    exact one_ne_zero hone0
  obtain ⟨m, hm⟩ := exists_stage_forall_mem_range F
    (T.biUnion (fun p => p.support.image (fun u => MvPolynomial.coeff u p)))
  have hpre : ∀ p ∈ T, ∃ q : DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m),
      differentialCoeffExtend (ι := ULift.{u} (Fin n)) (F := diffTowerCarrier F m)
        (L := diffClosure F) q = p := by
    intro p hp
    refine exists_preimage_of_coeffs_mem_range F m p (fun v => ?_)
    by_cases hv : v ∈ p.support
    · exact hm _ (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩)
    · refine ⟨0, ?_⟩
      rw [map_zero]
      exact (MvPolynomial.notMem_support_iff.mp hv).symm
  choose! qf hqf using hpre
  letI : Differential (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m)) :=
    differentialPolynomialOverDifferential _ _
  have hext_deriv : ∀ x : DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m),
      differentialCoeffExtend (ι := ULift.{u} (Fin n)) (F := diffTowerCarrier F m)
          (L := diffClosure F) (Differential.deriv x)
        = Differential.deriv (differentialCoeffExtend (ι := ULift.{u} (Fin n))
          (F := diffTowerCarrier F m) (L := diffClosure F) x) :=
    fun x => differentialCoeffExtend_deriv (deriv_algebraMap_diffTower F m) x
  have hprop : radicalDifferentialIdeal ((T.image qf : Finset (DifferentialPolynomial
      (ULift.{u} (Fin n)) (diffTowerCarrier F m))) : Set (DifferentialPolynomial
      (ULift.{u} (Fin n)) (diffTowerCarrier F m))) ≠ ⊤ := by
    intro htop
    have hone : (1 : DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))
        ∈ radicalDifferentialIdeal ((T.image qf : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) := by
      rw [htop]; trivial
    have himg := map_mem_radicalDifferentialIdeal
      (differentialCoeffExtend (ι := ULift.{u} (Fin n)) (F := diffTowerCarrier F m)
        (L := diffClosure F))
      hext_deriv ((T.image qf : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) hone
    rw [map_one] at himg
    have hsub : (differentialCoeffExtend (ι := ULift.{u} (Fin n)) (F := diffTowerCarrier F m)
        (L := diffClosure F)) '' ((T.image qf : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m)))
          ⊆ (T : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffClosure F))) := by
      rintro w ⟨q, hq, rfl⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
      rw [hqf p hp]
      exact hp
    exact hTprop (radicalDifferentialIdeal_mono hsub himg)
  obtain ⟨y, hy⟩ := exists_solution_closureStep (diffTowerCarrier F m) n
    (radicalDifferentialIdeal ((T.image qf : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))) : Set (DifferentialPolynomial (ULift.{u} (Fin n)) (diffTowerCarrier F m))))
    (fun x hx => deriv_mem_radicalDifferentialIdeal _ x hx) hprop
  refine ⟨fun i => diffTowerLimitHom F (m + 1) (y i), ?_⟩
  intro p hp
  have hq : differentialPolynomialEvalOver (K := diffTowerCarrier F m) y (qf p) = 0 :=
    hy _ (subset_radicalDifferentialIdeal _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem qf hp)))
  have hmapped := map_differentialPolynomialEvalOver
    (F := diffTowerCarrier F m) (L := (closureStep (diffTowerCarrier F m)).carrier)
    (M := diffClosure F) (diffTowerLimitHom F (m + 1)) (deriv_diffTowerLimitHom F (m + 1))
    (fun a => (algebraMap_diffTower_step F m a).symm) y (qf p)
  rw [hq, map_zero] at hmapped
  rw [← hqf p hp, differentialPolynomialEvalOver_differentialCoeffExtend]
  exact hmapped.symm

/-- A differential field is **differentially closed** when every finite differential system that has
a solution in some differential field extension already has one in the field itself. -/
class IsDifferentiallyClosed (C : Type u) [Field C] [Algebra ℚ C] [Differential C] : Prop where
  exists_point : ∀ {n : ℕ} (T : Finset (DifferentialPolynomial (ULift.{u} (Fin n)) C))
    (E : DiffFieldExt C) (z : ULift.{u} (Fin n) → E.carrier),
    (∀ p ∈ T, differentialPolynomialEvalOver (K := C) z p = 0) →
    ∃ y : ULift.{u} (Fin n) → C, ∀ p ∈ T, differentialPolynomialEvalOver (K := C) y p = 0

instance isDifferentiallyClosed_diffClosure : IsDifferentiallyClosed (diffClosure F) :=
  ⟨fun T E z hz => exists_point_of_solution_ext F T E z hz⟩

end

end GaloisForLFunctions.HTGeometry
