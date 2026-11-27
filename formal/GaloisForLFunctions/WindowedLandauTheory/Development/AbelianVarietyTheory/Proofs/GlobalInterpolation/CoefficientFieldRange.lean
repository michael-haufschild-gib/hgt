import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralModelOverCoefficientField

/-! The coefficient embedding has intermediate-field range. A
representation conjugate into that range has an integral model. -/

noncomputable section

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)

local notation "ℓ" => D.nd.l i
local notation "L" => PadicAlgCl ℓ

/-- The embedded fraction field of the coefficient ring. -/
def coefficientField : IntermediateField ℚ_[ℓ] L :=
  (D.naut.iotaQ i).fieldRange.toIntermediateField (fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[ℓ]) x
    let j : ℤ_[ℓ] →+* FractionRing (D.nd.O i) :=
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[ℓ] (D.nd.O i))
    refine ⟨j a / j b, ?_⟩
    rw [map_div₀, show D.naut.iotaQ i (j a) = _ from D.naut.iotaQ_alg i a,
      show D.naut.iotaQ i (j b) = _ from D.naut.iotaQ_alg i b, map_div₀]
    rfl)

theorem mem_coefficientField_iff (z : L) :
    z ∈ coefficientField D i ↔ ∃ x, D.naut.iotaQ i x = z :=
  Iff.rfl

/-- A basis change putting the entries in the coefficient field can be
followed by a second basis change making the model integral. -/
theorem exists_integral_model_of_conjugate_entries
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (a : ℕ) (ρ : Γ →* GL (Fin a) L) (hc : Continuous fun g => (ρ g).val)
    (P : GL (Fin a) L) (hP : ∀ g s t, (P⁻¹ * ρ g * P).val s t ∈ coefficientField D i) :
    ∃ (r : Γ →* GL (Fin a) (D.nd.O i)) (B : GL (Fin a) L),
      ∀ g, mapRep (iotaOQ D.nd D.naut i) r g = B⁻¹ * ρ g * B := by
  let ρ' := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have he (g : Γ) : ρ' g = P⁻¹ * ρ g * P := by
    change P⁻¹ * ρ g * P⁻¹⁻¹ = _
    rw [inv_inv]
  have hc' : Continuous fun g => (ρ' g).val := by
    simp only [he, Units.val_mul]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, B, hb⟩ := exists_integral_model_of_coefficient_field D i a ρ' hc' (fun g s t => by
    rw [he]
    exact (mem_coefficientField_iff D i _).mp (hP g s t))
  refine ⟨r, P * B, fun g => ?_⟩
  rw [hb, he, mul_inv_rev]
  simp only [mul_assoc]

end WindowedLandauTheory.NormalizedTypes
