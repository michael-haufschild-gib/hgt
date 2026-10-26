import GaloisForLFunctions.ArithmeticPositiveDuality.GramSpaceOfAPositiveDefiniteFunction

/-!
# The Hilbert space of a positive-definite function

The completion `𝓗_Φ` of the pre-Hilbert space of a positive-definite function `Φ` on a group `G`
is a Hilbert space with a unitary representation `π_Φ : G →* (𝓗_Φ ≃ₗᵢ 𝓗_Φ)` and a cyclic vector
`ξ_Φ` such that `Φ(g) = ⟨ξ_Φ, π_Φ(g)ξ_Φ⟩` (`inner_gnsCyclic_gnsRep`): the GNS construction.

Every linear isometry equivalence of a seminormed inner product space extends to its completion
(`LinearIsometryEquiv.completion`), and the left translations of the pre-Hilbert space extend to
a group homomorphism.
-/

open UniformSpace
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

section Completion

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A linear isometry equivalence extends to the completion. -/
def _root_.LinearIsometryEquiv.completion (e : E ≃ₗᵢ[ℂ] E) :
    Completion E ≃ₗᵢ[ℂ] Completion E where
  toFun := Completion.map e
  invFun := Completion.map e.symm
  left_inv x := by
    refine Completion.induction_on x (isClosed_eq (Completion.continuous_map.comp
      Completion.continuous_map) continuous_id) fun a => ?_
    rw [Completion.map_coe e.isometry.uniformContinuous,
      Completion.map_coe e.symm.isometry.uniformContinuous, e.symm_apply_apply]
  right_inv x := by
    refine Completion.induction_on x (isClosed_eq (Completion.continuous_map.comp
      Completion.continuous_map) continuous_id) fun a => ?_
    rw [Completion.map_coe e.symm.isometry.uniformContinuous,
      Completion.map_coe e.isometry.uniformContinuous, e.apply_symm_apply]
  map_add' x y := (AddMonoidHom.completion (e : E →+ E) e.continuous).map_add x y
  map_smul' c x := by
    show Completion.map (e : E → E) (c • x) = c • Completion.map (e : E → E) x
    refine Completion.induction_on x (isClosed_eq (Completion.continuous_map.comp
      (continuous_const_smul c)) ((continuous_const_smul c).comp Completion.continuous_map))
      fun a => ?_
    rw [← Completion.coe_smul, Completion.map_coe e.isometry.uniformContinuous,
      Completion.map_coe e.isometry.uniformContinuous, LinearIsometryEquiv.map_smul,
      Completion.coe_smul]
  norm_map' x := by
    show ‖Completion.map (e : E → E) x‖ = ‖x‖
    refine Completion.induction_on x (isClosed_eq (continuous_norm.comp Completion.continuous_map)
      continuous_norm) fun a => ?_
    rw [Completion.map_coe e.isometry.uniformContinuous, Completion.norm_coe, Completion.norm_coe,
      e.norm_map]

theorem _root_.LinearIsometryEquiv.completion_coe (e : E ≃ₗᵢ[ℂ] E) (a : E) :
    e.completion (a : Completion E) = (e a : Completion E) :=
  Completion.map_coe e.isometry.uniformContinuous a

end Completion

variable {G : Type*} [Group G] (Φ : PosDefFn G)

/-- Left translation as a linear isometry equivalence of the pre-Hilbert space. -/
def gnsIsom (a : G) : PreGNS Φ ≃ₗᵢ[ℂ] PreGNS Φ where
  toLinearEquiv :=
    { gnsTranslate Φ a with
      invFun := gnsTranslate Φ a⁻¹
      left_inv := fun x => by
        show gnsTranslate Φ a⁻¹ (gnsTranslate Φ a x) = x
        rw [← gnsTranslate_mul, inv_mul_cancel, gnsTranslate_one]
      right_inv := fun x => by
        show gnsTranslate Φ a (gnsTranslate Φ a⁻¹ x) = x
        rw [← gnsTranslate_mul, mul_inv_cancel, gnsTranslate_one] }
  norm_map' x := by
    show ‖gnsTranslate Φ a x‖ = ‖x‖
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_gnsTranslate]

theorem gnsIsom_apply (a : G) (x : PreGNS Φ) : gnsIsom Φ a x = gnsTranslate Φ a x := rfl

/-- The GNS Hilbert space: the completion of the pre-Hilbert space. -/
abbrev GNSHilbert : Type _ := Completion (PreGNS Φ)

/-- The GNS representation. -/
def gnsRep : G →* (GNSHilbert Φ ≃ₗᵢ[ℂ] GNSHilbert Φ) where
  toFun a := (gnsIsom Φ a).completion
  map_one' := by
    refine LinearIsometryEquiv.ext fun x => ?_
    refine Completion.induction_on x (isClosed_eq (LinearIsometryEquiv.continuous _)
      (LinearIsometryEquiv.continuous _)) fun a => ?_
    rw [LinearIsometryEquiv.completion_coe, gnsIsom_apply, gnsTranslate_one]
    rfl
  map_mul' a b := by
    refine LinearIsometryEquiv.ext fun x => ?_
    refine Completion.induction_on x (isClosed_eq (LinearIsometryEquiv.continuous _)
      (LinearIsometryEquiv.continuous _)) fun x => ?_
    rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.completion_coe,
      LinearIsometryEquiv.completion_coe, LinearIsometryEquiv.completion_coe, gnsIsom_apply,
      gnsIsom_apply, gnsIsom_apply, gnsTranslate_mul]

theorem gnsRep_coe (a : G) (x : PreGNS Φ) :
    gnsRep Φ a (x : GNSHilbert Φ) = (gnsTranslate Φ a x : GNSHilbert Φ) :=
  LinearIsometryEquiv.completion_coe _ x

/-- The cyclic vector `δ_1`. -/
def gnsCyclic : GNSHilbert Φ := (gnsVec Φ 1 : PreGNS Φ)

/-- **GNS.** `Φ(g) = ⟨ξ_Φ, π_Φ(g)ξ_Φ⟩`. -/
theorem inner_gnsCyclic_gnsRep (g : G) :
    ⟪gnsCyclic Φ, gnsRep Φ g (gnsCyclic Φ)⟫_ℂ = Φ.toFun g := by
  rw [gnsCyclic, gnsRep_coe, Completion.inner_coe, gnsTranslate_gnsVec, mul_one, inner_gnsVec,
    inv_one, one_mul]

theorem gnsRep_gnsCyclic (g : G) :
    gnsRep Φ g (gnsCyclic Φ) = ((gnsVec Φ g : PreGNS Φ) : GNSHilbert Φ) := by
  rw [gnsCyclic, gnsRep_coe, gnsTranslate_gnsVec, mul_one]

end GaloisForLFunctions.ArithmeticPositiveDuality
