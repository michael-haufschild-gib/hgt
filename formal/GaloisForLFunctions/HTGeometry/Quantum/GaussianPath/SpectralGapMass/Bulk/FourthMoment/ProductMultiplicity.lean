import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.PauliUniformCommutatorEnergy

/-! # Bounded multiplicity of nonidentity products of two physical Pauli terms -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
noncomputable section

abbrev Word (n : ℕ) := Fin (n+2) → Option (Fin 3)

/-- Word carried by the ordered pair, after discarding the scalar Pauli phase. -/
def productWord {n : ℕ} (z : PathLabel n × PathLabel n) : Word n :=
  optMulLabel (pathWord z.1) (pathWord z.2)

/-- Ordered factorizations of a word in the onsite and bond Pauli terms. -/
def factors {n : ℕ} (Q : Word n) := univ.filter fun z : PathLabel n × PathLabel n => productWord z=Q

private theorem in_fiber {n : ℕ} {Q : Word n} {z : PathLabel n × PathLabel n}
    (h : z∈factors Q) : productWord z=Q := (mem_filter.mp h).2

private theorem other_factor {n : ℕ} {a b c : PathLabel n}
    (h : optMulLabel (pathWord a) (pathWord b)=optMulLabel (pathWord a) (pathWord c)) : b=c :=
  pathWord_injective ((optMulLabelEquiv (pathWord a)).injective h)

/-- A nonidentity product has at most 42 ordered factorizations. At a site
where it is nonidentity one factor belongs to the 21 incident labels.
After choosing that factor and its position, cancellation determines its partner. -/
theorem nonidentity_factor_count {n : ℕ} (Q : Word n) (hQ : Q≠pauliIdentityLabel (n+2)) :
    (factors Q).card ≤ 42 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, Q v≠none := by
    by_contra! h
    exact hQ (funext h)
  let S := factors Q
  let L := S.filter fun z => pathIncident v z.1
  let R := S.filter fun z => ¬pathIncident v z.1
  have hL : L.card ≤ (pathIncidentLabels v).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    · intro x hx y hy hf
      apply Prod.ext hf
      apply other_factor (a:=x.1)
      have he := (in_fiber (mem_filter.mp hx).1).trans (in_fiber (mem_filter.mp hy).1).symm
      change optMulLabel (pathWord x.1) (pathWord x.2)=optMulLabel (pathWord y.1) (pathWord y.2) at he
      rwa [←hf] at he
  have hR : R.card ≤ (pathIncidentLabels v).card := by
    apply card_le_card_of_injOn Prod.snd
    · intro x hx
      obtain ⟨hF,hno⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      by_contra hbad
      have h := congrFun (in_fiber hF) v
      change optMul (pathWord x.1 v) (pathWord x.2 v)=Q v at h
      rw [pathWord_none_of_not_incidentSite v _ hno,pathWord_none_of_not_incidentSite v _ hbad] at h
      exact hv h.symm
    · intro x hx y hy hs
      apply Prod.ext _ hs
      apply other_factor (a:=x.2)
      have he := (in_fiber (mem_filter.mp hx).1).trans (in_fiber (mem_filter.mp hy).1).symm
      change optMulLabel (pathWord x.1) (pathWord x.2)=optMulLabel (pathWord y.1) (pathWord y.2) at he
      rw [optMulLabel_comm (pathWord x.2) (pathWord x.1),
        optMulLabel_comm (pathWord y.2) (pathWord y.1),←hs] at he
      exact he
  have hcov : S⊆L∪R := by
    intro x hx
    by_cases h : pathIncident v x.1
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,h⟩)
  exact (card_le_card hcov).trans ((card_union_le ..).trans
    (Nat.add_le_add (hL.trans (pathIncidentLabels_card v)) (hR.trans (pathIncidentLabels_card v))))

#print axioms nonidentity_factor_count
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
