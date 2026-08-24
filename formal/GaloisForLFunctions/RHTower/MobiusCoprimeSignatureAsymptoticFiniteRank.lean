import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureFlow
import GaloisForLFunctions.RHTower.MobiusCoprimeInertiaUnbounded
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow

namespace RHTower

open Filter Topology Matrix Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

noncomputable section

/-- Prime number theorem in exact coprimality-signature form. -/
theorem tendsto_abs_finiteMobiusCoprimeSignature_div :
    Tendsto
      (fun N : ℕ => |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)| / (N : ℝ))
      atTop (𝓝 0) := by
  convert RHTower.Sieve.tendsto_abs_mertensM_div using 1
  funext N
  rw [finiteMobiusCoprimeSignature_eq_mertensM]

/-- Any correction that makes a matrix positive semidefinite must have range
dimension at least the matrix's negative inertia. -/
theorem hermNegIndex_le_finrank_correctionRange_of_add_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (H R : Matrix n n ℂ) (hPSD : (H + R).PosSemidef) :
    hermNegIndex H ≤ Module.finrank ℂ (LinearMap.range R.mulVecLin) := by
  obtain ⟨W, hfin, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hneg : ∀ x ∈ W, x ≠ 0 → hermQuad H x < 0 := by
    intro x hx hx0
    have hp := hW x hx hx0
    rw [hermQuad_neg] at hp
    linarith
  let f : W →ₗ[ℂ] LinearMap.range R.mulVecLin :=
    LinearMap.codRestrict (LinearMap.range R.mulVecLin)
      (R.mulVecLin.domRestrict W) (fun x => ⟨x.1, rfl⟩)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hRx : R.mulVec (x : n → ℂ) = 0 := congrArg Subtype.val hx
    by_contra hx0
    have hx0coe : (x : n → ℂ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hP := hPSD.dotProduct_mulVec_nonneg (x : n → ℂ)
    rw [add_mulVec, hRx, add_zero] at hP
    have hre : 0 ≤ hermQuad H (x : n → ℂ) := (Complex.le_def.mp hP).1
    exact (not_lt_of_ge hre) (hneg x x.2 hx0coe)
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  rw [hfin] at hle
  simpa [hermNegIndex] using hle

/-- No correction family of one fixed finite rank can make all finite
coprimality matrices positive semidefinite. -/
theorem finiteMobiusCoprimeMatrixComplex_no_fixedRankCorrection (k : ℕ) :
    ∃ N : ℕ, ∀ R : Matrix (finiteMobiusCoprimeCoordinate N)
        (finiteMobiusCoprimeCoordinate N) ℂ,
      Module.finrank ℂ (LinearMap.range R.mulVecLin) ≤ k →
        ¬ (finiteMobiusCoprimeMatrixComplex N + R).PosSemidef := by
  obtain ⟨N, hN⟩ :=
    finiteMobiusCoprimeMatrixComplex_negativeInertia_unbounded (k + 1)
  refine ⟨N, ?_⟩
  intro R hR hPSD
  have hbound := hermNegIndex_le_finrank_correctionRange_of_add_posSemidef
    (finiteMobiusCoprimeMatrixComplex N) R hPSD
  have hbad : k + 1 ≤ k := hN.trans (hbound.trans hR)
  have hbad' : Nat.succ k ≤ k := by
    rw [Nat.succ_eq_add_one]
    exact hbad
  exact (Nat.not_succ_le_self k) hbad'

end

end RHTower
