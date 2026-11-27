import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PadicAlgebraicResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PadicComplexFieldEquiv
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerConjugacy

/-! Transport a p-adic valuation to the complex field and conjugate it to
realize the prescribed multiplicative lift of the residue field. -/

noncomputable section

open IsLocalRing WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes

namespace GlobalTheory.TeichPlace

/-- A field isomorphism identifies a valuation ring and its pullback. -/
def valuationComapEquiv {F K : Type*} [Field F] [Field K] (A : ValuationSubring K)
    (e : F ≃+* K) : A.comap e.toRingHom ≃+* A where
  toFun a := ⟨e a, a.2⟩
  invFun a := ⟨e.symm a, ValuationSubring.mem_comap.mpr (by simp [a.2])⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  map_add' _ _ := Subtype.ext (map_add e _ _)

private theorem isTeich_comap {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    (B : ValuationSubring K) (κ : ResidueField B ≃+* Fbar p) (σ : K ≃+* K)
    (t u : Fbar p →* K) (hσ : ∀ x, σ (u x) = t x) (hu : IsTeich B κ u) :
    IsTeich (B.comap σ.symm.toRingHom)
      ((ResidueField.mapEquiv (valuationComapEquiv B σ.symm)).trans κ) t := by
  let A := B.comap σ.symm.toRingHom
  let e : A ≃+* B := valuationComapEquiv B σ.symm
  intro x
  obtain ⟨hx, hred⟩ := hu x
  have he : σ.symm (t x) = u x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  have hxA : t x ∈ A := ValuationSubring.mem_comap.mpr (he ▸ hx)
  refine ⟨hxA, ?_⟩
  change κ (ResidueField.mapEquiv e (residue A ⟨t x, hxA⟩)) = _
  have hE : (e : A →+* B) ⟨t x, hxA⟩ = ⟨u x, hx⟩ := Subtype.ext he
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue, hE]
  exact hred

/-- A p-adic place on the complex field has residue field `Fbar p`. -/
theorem exists_complex_place_residueField (p : ℕ) [Fact p.Prime] :
    ∃ A : ValuationSubring ℂ, Nonempty (ResidueField A ≃+* Fbar p) := by
  obtain ⟨ι⟩ := nonempty_padicAlgCl_ringEquiv_complex p
  obtain ⟨κ⟩ := nonempty_padicAlgCl_residueField_equiv p
  refine ⟨(padicAlgClIntegers p).comap ι.symm.toRingHom, ⟨?_⟩⟩
  exact (ResidueField.mapEquiv (valuationComapEquiv (padicAlgClIntegers p) ι.symm)).trans κ

/-- A place of the complex field realizes any prescribed injective multiplicative
embedding of the algebraic closure of the prime field as a Teichmüller section. -/
theorem exists_complex_place_isTeich {p : ℕ} [Fact p.Prime] (t : Fbar p →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    ∃ (A : ValuationSubring ℂ) (κ : ResidueField A ≃+* Fbar p), IsTeich A κ t := by
  obtain ⟨B, ⟨κ⟩⟩ := exists_complex_place_residueField p
  have ht' := injective_monoidHom_fbar t ht
  obtain ⟨u, hu, hu'⟩ := exists_teich_reindex B κ t ht'
  obtain ⟨σ, hσ⟩ := exists_complex_aut_fbar t u ht' hu'
  exact ⟨_, _, isTeich_comap B κ σ t u hσ hu⟩

end GlobalTheory.TeichPlace
