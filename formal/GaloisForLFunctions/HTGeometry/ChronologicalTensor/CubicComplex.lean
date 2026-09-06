import GaloisForLFunctions.HTGeometry.ChronologicalTensor.UnitCapacity
import Mathlib.Topology.Homotopy.Basic

/-!
# The cubic physical probe complex

The five physical cubic gaps give a nonnegative unit simplex with adjacent
products zero. Appending the unused terminal zero identifies this concrete
complex exactly with the physical section that norms genuine pairing families.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def physicalProbeSection (n : ℕ) : Set (Fin n → ℝ) :=
  {g | (∀ q, 0 ≤ g q) ∧ variation g=1 ∧ separatedSupport g ∧
    (∀ q, q.val+1=n → g q=0)}

def cubicProbeSection : Set (Fin 5 → ℝ) :=
  {g | (∀ q, 0 ≤ g q) ∧ g 0+g 1+g 2+g 3+g 4=1 ∧
    g 0*g 1=0 ∧ g 1*g 2=0 ∧ g 2*g 3=0 ∧ g 3*g 4=0}

def cubicProbeExtend (g : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![g 0,g 1,g 2,g 3,g 4,0]

theorem cubicProbeExtend_variation (g : Fin 5 → ℝ) :
    variation (cubicProbeExtend g)=|g 0|+|g 1|+|g 2|+|g 3|+|g 4| := by
  simp [variation,cubicProbeExtend,Fin.sum_univ_succ]
  ring

theorem cubicProbeExtend_physical (g : Fin 5 → ℝ) :
    cubicProbeExtend g ∈ physicalProbeSection 6 ↔ g ∈ cubicProbeSection := by
  constructor
  · rintro ⟨hnn,hvar,hsep,hterm⟩
    have hg : ∀ q, 0 ≤ g q := by
      intro q
      fin_cases q
      all_goals first | exact hnn 0 | exact hnn 1 | exact hnn 2 | exact hnn 3 | exact hnn 4
    refine ⟨hg,?_,?_,?_,?_,?_⟩
    · rw [cubicProbeExtend_variation] at hvar
      simpa only [abs_of_nonneg (hg _)] using hvar
    · exact mul_eq_zero.mpr (hsep 0)
    · exact mul_eq_zero.mpr (hsep 1)
    · exact mul_eq_zero.mpr (hsep 2)
    · exact mul_eq_zero.mpr (hsep 3)
  · rintro ⟨hnn,hsum,h01,h12,h23,h34⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro q
      fin_cases q
      all_goals first | exact hnn 0 | exact hnn 1 | exact hnn 2 | exact hnn 3 | exact hnn 4 | exact le_rfl
    · rw [cubicProbeExtend_variation]
      simpa only [abs_of_nonneg (hnn _)] using hsum
    · intro q
      fin_cases q
      · exact mul_eq_zero.mp h01
      · exact mul_eq_zero.mp h12
      · exact mul_eq_zero.mp h23
      · exact mul_eq_zero.mp h34
      · exact Or.inr rfl
    · intro q hq
      have he : q=5 := Fin.ext (by omega)
      subst q
      rfl

theorem physicalUnitValues_image {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    physicalUnitValues E c =
      (fun g => |familyValue (enumeratedFamilyWindows E)
        (enumeratedFamilyCoefficients E c) g|) '' physicalProbeSection (2*d) := by
  ext y
  constructor
  · rintro ⟨g,hnn,hvar,hsep,hterm,hy⟩
    exact ⟨g,⟨hnn,hvar,hsep,hterm⟩,hy.symm⟩
  · rintro ⟨g,⟨hnn,hvar,hsep,hterm⟩,hy⟩
    exact ⟨g,hnn,hvar,hsep,hterm,hy.symm⟩

theorem physicalProbeSection_six :
    physicalProbeSection 6=cubicProbeExtend '' cubicProbeSection := by
  ext g
  constructor
  · intro hg
    let h : Fin 5 → ℝ := fun q => g q.castSucc
    have he : cubicProbeExtend h=g := by
      ext q
      fin_cases q
      all_goals first | rfl | exact (hg.2.2.2 5 rfl).symm
    exact ⟨h,(cubicProbeExtend_physical h).mp (he.symm ▸ hg),he⟩
  · rintro ⟨h,hh,rfl⟩
    exact (cubicProbeExtend_physical h).mpr hh

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
