import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.DifferentialPhases.HorizontalDescent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.DifferentialPhases.InvariantForms
import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectCharacterLattice

/-! # Independence of the invariant forms of exponential phase coordinates -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
open AffineExponentialPointEvaluation AffineExponentialInvariantKaehler TorusCharacterCoLie
open GaloisForLFunctions.RHTower
universe u
noncomputable section
variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Along an exponential solution, the Lie derivative of its logarithmic
differential equals the Lie derivative of the differential of its action. -/
private theorem horizontal_valueDefect (δ : Derivation k L L) (x y : L) (hy : y≠0)
    (he : δ y=y*δ x) : kaehlerLieDifferential δ (valueDefect (C:=k) x y)=0 := by
  have hinv : δ y⁻¹= -(y⁻¹*δ x) := by
    rw [δ.leibniz_inv,he,smul_eq_mul]
    field_simp
  rw [valueDefect,map_sub,kaehlerLieDifferential_smul_D,kaehlerLieDifferential_D,hinv,he,
    (KaehlerDifferential.D k L).leibniz]
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hy,one_smul,neg_smul]
  abel

private theorem defect_pullback {n : ℕ} (x : Fin n → L) (y : Fin n → Lˣ) (c : Fin n → k) :
    pointKaehlerMap k (ofCoordinates x y) (mixedInvariantKaehlerVector k c (fun i => -c i))=
      ∑ i, c i • valueDefect (C:=k) (x i) (y i:L) := by
  classical
  rw [pointKaehlerMap_mixedInvariantKaehlerVector,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [torusPart_ofCoordinates,additivePart_ofCoordinates,AlgebraicTorusCharacter.character_neg,
    AlgebraicTorusCharacter.character_single,zpow_one,Units.val_inv_eq_inv_val,map_neg,neg_smul]
  rw [←algebraMap_smul L (c i) (valueDefect (C:=k) (x i) (y i:L)),valueDefect,smul_sub,smul_smul,
    sub_eq_add_neg]

/-- In a differential field of characteristic zero with algebraically closed
constants, exponential equations with multiplicatively independent ordinates
modulo constants have independent logarithmic defects over the whole field. -/
theorem independent_value_defects [CharZero k] [IsAlgClosed k] (δ : Derivation k L L)
    (hc : ∀ a, δ a=0 → ∃ b : k, algebraMap k L b=a) {n : ℕ} (x : Fin n → L) (y : Fin n → Lˣ)
    (he : ∀ i, δ (y i:L)=(y i:L)*δ (x i))
    (hi : ∀ m : Fin n →₀ ℤ, (∃ z : k, (AlgebraicTorusCharacter.character y m : L)=algebraMap k L z) → m=0) :
    LinearIndependent L (fun i => valueDefect (C:=k) (x i) (y i:L)) := by
  apply horizontal_independent δ hc (kaehlerLieDifferential δ) (kaehlerLieDifferential_smul δ)
    _ (fun i => horizontal_valueDefect δ _ _ (y i).ne_zero (he i))
  apply Fintype.linearIndependent_iff.mpr
  intro c hrel
  have h := (defect_pullback x y c).trans hrel
  obtain ⟨r,m,b,hm,heq⟩ := toric_coefficients_supported_on_constants (ofCoordinates x y) c (fun i => -c i) h
  have hm0 (j) : m j=0 := hi (m j) (hm j)
  simp only [hm0,map_zero,smul_zero,Finset.sum_const_zero] at heq
  exact fun i => congrFun heq i

#print axioms independent_value_defects
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
