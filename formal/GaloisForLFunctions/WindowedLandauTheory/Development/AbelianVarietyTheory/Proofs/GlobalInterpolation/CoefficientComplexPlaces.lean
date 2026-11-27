import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefficientPadicPlace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexTeichmullerPlace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableComplexEmbeddings

/-! A single complex valuation above each coefficient place realizes its
valuation on the embedded number field and has residue field `Fbar p`. -/

noncomputable section

open NumberField IsLocalRing
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open GlobalTheory.LadicPlace GlobalTheory.TeichPlace

namespace WindowedLandauTheory.NormalizedTypes

private theorem val_nonneg_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [D.val_eq w x hx]
  have hx' : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [← WithZero.log_le_log hx' one_ne_zero, WithZero.log_one]
  unfold vAdd
  norm_cast
  omega

/-- A p-adic realization of the prescribed complex embedding at a
coefficient place, with the corresponding residue identification. -/
structure CoefficientComplexPlace (D : D7) (w : D.what₂.places.Pl) where
  ι : @PadicAlgCl (D.what₂.places.resChar w) ⟨D.what₂.places.resChar_prime w⟩ ≃+* ℂ
  integral_iff : ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1
  κ : IsLocalRing.ResidueField
      ((@padicAlgClIntegers (D.what₂.places.resChar w) ⟨D.what₂.places.resChar_prime w⟩).comap
        ι.symm.toRingHom) ≃+* Fb (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)

namespace CoefficientComplexPlace

variable {D : D7} {w : D.what₂.places.Pl}

/-- The valuation ring transported from the p-adic field. -/
def ring (P : CoefficientComplexPlace D w) : ValuationSubring ℂ :=
  (@padicAlgClIntegers (D.what₂.places.resChar w) ⟨D.what₂.places.resChar_prime w⟩).comap
    P.ι.symm.toRingHom

theorem mem_ring_iff (P : CoefficientComplexPlace D w) (z : ℂ) :
    z ∈ P.ring ↔ ‖P.ι.symm z‖ ≤ 1 := by
  letI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  unfold ring
  rw [ValuationSubring.mem_comap]
  exact mem_padicAlgClIntegers_iff (P.ι.symm z)

theorem embLL_mem_ring_iff (P : CoefficientComplexPlace D w) (x : D.what₂.LL) :
    D.what₂.embLL x ∈ P.ring ↔ 0 ≤ D.what₂.places.val w x :=
  (P.mem_ring_iff _).trans (P.integral_iff x).symm

end CoefficientComplexPlace

/-- The complex coefficient field has a p-adic realization inducing any
prescribed finite place of the number field. -/
theorem nonempty_coefficientComplexPlace (D : D7) (w : D.what₂.places.Pl) :
    Nonempty (CoefficientComplexPlace D w) := by
  let p := D.what₂.places.resChar w
  letI : Fact p.Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨a, ha⟩ := exists_embedding_inducing_place (p := p) (D.plEq w) (resChar_mem D w)
  letI : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  obtain ⟨e, he⟩ := exists_padicAlgCl_ringEquiv_complex_comp_eq p a D.what₂.embLL
  obtain ⟨κ⟩ := nonempty_padicAlgCl_residueField_equiv p
  refine ⟨⟨e, fun x => ?_, (ResidueField.mapEquiv (valuationComapEquiv (padicAlgClIntegers p) e.symm)).trans κ⟩⟩
  have hx : e.symm (D.what₂.embLL x) = a x := by
    rw [← he]
    exact e.symm_apply_apply (a x)
  rw [val_nonneg_iff, ha, hx]

end WindowedLandauTheory.NormalizedTypes
