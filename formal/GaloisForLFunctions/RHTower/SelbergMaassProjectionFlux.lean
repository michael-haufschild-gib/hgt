import GaloisForLFunctions.RHTower.SelbergMaassInversionPhaseEnergy

/-!
# Inversion loss controls coherent character flux

The actual upper/lower character mismatch is the difference of two orthogonal
corners. The inversion-transfer loss splits exactly into the mismatch square
and a double-complement square. Pairing with an arbitrary derivative vector
therefore bounds the squared character-flux mismatch by the literal arithmetic
phase-displacement energy times derivative energy.
-/

open Complex
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux
open SelbergMaassCongruenceTrace SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionPhaseEnergy
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- Complementary outputs of an actual character projector are orthogonal. -/
theorem character_complement_orthogonal (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    inner ℂ (v-characterProjection N p r v) (characterProjection N p r w)=0 := by
  rw [← characterProjection_self_adjoint]
  simp only [map_sub,characterProjection_idempotent,sub_self,inner_zero_left]

/-- The actual upper/lower mismatch is the difference of its two complementary corners. -/
theorem projection_mismatch_corners (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N (upperBlock N) s v-characterProjection N (lowerBlock N) (-r) v=
      (characterProjection N (upperBlock N) s v-
        characterProjection N (lowerBlock N) (-r) (characterProjection N (upperBlock N) s v))-
      characterProjection N (lowerBlock N) (-r) (v-characterProjection N (upperBlock N) s v) := by
  rw [map_sub]
  abel

/-- Exact original transfer loss is projection mismatch plus the retained double-complement square. -/
theorem transfer_loss_mismatch_identity (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ‖v‖^2-‖inversionTransfer N r s v‖^2=
      ‖characterProjection N (upperBlock N) s v-characterProjection N (lowerBlock N) (-r) v‖^2+
      ‖(v-characterProjection N (upperBlock N) s v)-
        characterProjection N (lowerBlock N) (-r) (v-characterProjection N (upperBlock N) s v)‖^2 := by
  rw [projection_mismatch_corners,norm_sub_sq (𝕜 := ℂ),character_complement_orthogonal]
  simp only [map_zero,mul_zero,sub_zero]
  rw [transfer_loss_decomposition]
  simp_rw [characterProjection_loss]
  ring

/-- Actual inversion loss bounds the complete upper/lower character mismatch. -/
theorem projection_mismatch_le_transfer_loss (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ‖characterProjection N (upperBlock N) s v-characterProjection N (lowerBlock N) (-r) v‖^2 ≤
      ‖v‖^2-‖inversionTransfer N r s v‖^2 := by
  rw [transfer_loss_mismatch_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The actual transfer loss is nonnegative, with no assumed operator bound. -/
theorem transfer_loss_nonneg (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) : 0 ≤ ‖v‖^2-‖inversionTransfer N r s v‖^2 := by
  rw [transfer_loss_mismatch_identity]
  positivity

/-- Difference of original character fluxes is exactly the coherent mismatch pairing. -/
theorem character_flux_difference (N : ℕ) (r s : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    (inner ℂ (characterProjection N (upperBlock N) s v) w).re-
      (inner ℂ (characterProjection N (lowerBlock N) (-r) v) w).re=
    (inner ℂ (characterProjection N (upperBlock N) s v-
      characterProjection N (lowerBlock N) (-r) v) w).re := by
  rw [inner_sub_left,Complex.sub_re]

/-- Quantitative original character-flux mismatch is controlled by inversion loss and derivative energy. -/
theorem character_flux_sq_le_transfer_loss (N : ℕ) (r s : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    ((inner ℂ (characterProjection N (upperBlock N) s v) w).re-
      (inner ℂ (characterProjection N (lowerBlock N) (-r) v) w).re)^2 ≤
      (‖v‖^2-‖inversionTransfer N r s v‖^2)*‖w‖^2 := by
  rw [character_flux_difference]
  let a := characterProjection N (upperBlock N) s v-characterProjection N (lowerBlock N) (-r) v
  have hi : |(inner ℂ a w).re| ≤ ‖a‖*‖w‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm a w)
  have hs : (inner ℂ a w).re^2 ≤ ‖a‖^2*‖w‖^2 := by
    have h := abs_le.mp hi
    nlinarith [norm_nonneg a,norm_nonneg w]
  exact hs.trans (mul_le_mul_of_nonneg_right (projection_mismatch_le_transfer_loss N r s v) (sq_nonneg _))

/-- The bound uses the literal complete arithmetic phase-displacement energy. -/
theorem character_flux_sq_le_phase_energy (N : ℕ) (r s : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    ((inner ℂ (characterProjection N (upperBlock N) s v) w).re-
      (inner ℂ (characterProjection N (lowerBlock N) (-r) v) w).re)^2 ≤
      (((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*
        (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
          ‖v-tripleMotion N r s a b c v‖^2))*‖w‖^2 := by
  rw [triple_displacement_energy]
  exact character_flux_sq_le_transfer_loss N r s v w

end
end GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux
