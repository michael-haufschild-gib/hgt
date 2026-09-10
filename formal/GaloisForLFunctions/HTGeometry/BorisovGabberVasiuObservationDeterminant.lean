import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Observation updates admit an adjugate formula even at rank loss. -/
theorem bgv_det_observation_update {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (t : ℝ) :
    (M + t • vecMulVec v (star v)).det =
      M.det + (t : ℂ) * (star v ⬝ᵥ M.adjugate.mulVec v) := by
  have houter : t • vecMulVec v (star v) = vecMulVec ((t : ℂ) • v) (star v) := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    ac_rfl
  rw [houter, bgv_det_add_vecMulVec, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- The exact design-segment determinant includes singular designs and both endpoints. -/
theorem bgv_finiteDesignGram_segment_det {C : Type*} [Fintype C] [DecidableEq C]
    {n : ℕ} (target : C → Fin n → ℂ) (w : C → ℝ) (c : C) (s : ℝ) :
    (finiteDesignGram target (finiteDesignSegment w c s)).det =
      ((1 - s) • finiteDesignGram target w).det +
        (s : ℂ) * (star (target c) ⬝ᵥ
          (((1 - s) • finiteDesignGram target w).adjugate.mulVec (target c))) := by
  rw [finiteDesignGram_segment, bgv_det_observation_update]

end GaloisForLFunctions.HTGeometry
