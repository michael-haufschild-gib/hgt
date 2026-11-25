import GaloisForLFunctions.HTGeometry.AffineExponentialStableHopfLocus
import GaloisForLFunctions.HTGeometry.LatticeSpanFinite

/-! # Constant linear relations among logarithmic phase differentials -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
open AffineExponentialGroup AffineExponentialSubgroups
open AffineExponentialPointEvaluation AffineExponentialPointClosure
open AffineExponentialProjectionClassification MixedAdditiveProjectionClassification
open AffineExponentialCoLieClassification AffineExponentialInvariantKaehler
open TorusCharacterCoLie LatticeSpanFinite

universe u
noncomputable section
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [CharZero k] [IsAlgClosed k]

/-- Every toric relation on the stable subgroup evaluates at the original
point to the inverse of the translating character, a base-field unit. -/
private theorem constant_character {n : ℕ} {p : Point L n} {c a : Fin n → k}
    (H : AffineExponentialStableHopfLocus k L n p c a) {m : Fin n →₀ ℤ}
    (hm : m∈torusRelationLattice k H.ideal) :
    ∃ b : k, (AlgebraicTorusCharacter.character (torusPart p) m : L)=algebraMap k L b := by
  letI : H.ideal.IsHopfIdeal k := H.isHopfIdeal
  have hz := H.coset_zero (torusRelation k m) ((mem_torusRelationLattice_iff k H.ideal m).mp hm)
  change eval (k:=k) p (rightTranslate H.algebraicPoint⁻¹ (torusRelation k m))=0 at hz
  rw [torusRelation,map_sub,rightTranslate_torusCharacter,map_one,map_sub,map_mul,map_one,sub_eq_zero] at hz
  let b : k := (AlgebraicTorusCharacter.character (torusPart H.algebraicPoint⁻¹) m : k)
  have hb := (eval (k:=k) p).commutes b
  rw [hb,eval_torusCharacter] at hz
  have hb' : algebraMap k L b≠0 := map_ne_zero (algebraMap k L) (Units.ne_zero _)
  refine ⟨b⁻¹,?_⟩
  rw [map_inv₀]
  apply mul_left_cancel₀ hb'
  rwa [mul_inv_cancel₀ hb']

/-- In every mixed invariant relation, the toric coefficients belong to
the span of the integer characters whose values are constants. -/
theorem toric_coefficients_supported_on_constants {n : ℕ} (p : Point L n) (c a : Fin n → k)
    (h : pointKaehlerMap k p (mixedInvariantKaehlerVector k c a)=0) :
    ∃ (r : ℕ) (m : Fin r → (Fin n →₀ ℤ)) (b : Fin r → k),
      (∀ j, ∃ z : k, (AlgebraicTorusCharacter.character (torusPart p) (m j) : L)=algebraMap k L z) ∧
        c=∑ j, b j • integralCast k (m j) := by
  obtain ⟨H⟩ := exists_affineExponentialStableHopfLocus k L p c a h
  letI : H.ideal.IsHopfIdeal k := H.isHopfIdeal
  have hc := ((coLieMap_subgroupQuotient_eq_zero_iff k H.ideal c a).mp H.coLie_zero).1
  obtain ⟨r,m,b,hm,hr⟩ := (mem_latticeSpan_iff_exists_fin k _ c).mp hc
  exact ⟨r,m,b,fun j => constant_character H (hm j),hr⟩

#print axioms toric_coefficients_supported_on_constants
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
