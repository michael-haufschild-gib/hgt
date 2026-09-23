import GaloisForLFunctions.RHTower.GaussChannelOperator
import GaloisForLFunctions.RHTower.GaussQuasiInnerSquare

/-!
# Reduced one-prime quasi-inner block energy

The distinguished block in the Connes--Consani decomposition is, after deleting the source
isometries, the real local-factor scalar `(1-p)/p` times the paired circle block
`C_full = B D_full I B`.  This file proves the literal operator identity

`E_p^* E_p = ((p-1)/p)^(2 : ℕ) G_full`,

where the right side is exactly the depth-one `gaussChannelOperator`.  The proof first promotes
circle reflection to an involutive linear isometry, derives its self-adjointness, proves the paired
block self-adjoint, and then combines `C^(2 : ℕ) = G` with the archimedean scale.

This closes the algebraic distinguished-block identification.  It does not identify the full
Hardy defect or prove the depth-one singular-value residue of the actual Gauss channel.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- Circle Hilbert space carrying the reduced Gauss block. -/
abbrev GaussCircleL2 :=
  Lp Complex 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

/-- Circle reflection as an involutive linear isometry. -/
def circleReflectionLinearIsometry : GaussCircleL2 →ₗᵢ[Complex] GaussCircleL2 :=
  Lp.compMeasurePreservingₗᵢ Complex
    (Neg.neg : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
    measurePreserving_neg_circle

@[simp] theorem circleReflectionLinearIsometry_apply (f : GaussCircleL2) :
    circleReflectionLinearIsometry f = circleReflectionCLM f := rfl

/-- Circle reflection is self-adjoint. -/
theorem inner_circleReflectionCLM (u v : GaussCircleL2) :
    inner Complex (circleReflectionCLM u) v = inner Complex u (circleReflectionCLM v) := by
  rw [← circleReflectionLinearIsometry_apply,
    ← circleReflectionLinearIsometry_apply]
  calc
    inner Complex (circleReflectionLinearIsometry u) v =
        inner Complex (circleReflectionLinearIsometry (circleReflectionLinearIsometry u))
          (circleReflectionLinearIsometry v) :=
      (circleReflectionLinearIsometry.inner_map_map
        (circleReflectionLinearIsometry u) v).symm
    _ = inner Complex u (circleReflectionLinearIsometry v) := by
      rw [circleReflectionLinearIsometry_apply,
        circleReflectionLinearIsometry_apply,
        circleReflectionCLM_apply_self]

/-- Moving the adjoint diagonal block through reflection recovers the original diagonal block. -/
theorem circleReflection_gaussDiagonalBlockStar
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (u : GaussCircleL2) :
    circleReflectionCLM (gaussDiagonalBlockStar hm k p u) =
      gaussDiagonalBlock hm k p (circleReflectionCLM u) := by
  have h := congrArg (fun T : GaussCircleL2 →L[Complex] GaussCircleL2 => T u)
    (circleReflection_gaussDiagonalBlock_conj hm k p)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  have hI := congrArg circleReflectionCLM h
  simpa [circleReflectionCLM_apply_self] using hI.symm

/-- The paired block `C = B D I B` is self-adjoint. -/
theorem gaussPairedBlock_inner
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (u v : GaussCircleL2) :
    inner Complex (gaussPairedBlock hm k p u) v =
      inner Complex u (gaussPairedBlock hm k p v) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  simp only [gaussPairedBlock, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [gaussPrimeScaleBlock_inner hp,
    gaussDiagonalBlock_inner hm k p,
    inner_circleReflectionCLM,
    circleReflection_gaussDiagonalBlockStar hm k p,
    ← gaussPrimeScaleBlock_inner hp]

/-- Paired block with the archimedean prefactor restored. -/
def gaussPairedBlockFull
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    GaussCircleL2 →L[Complex] GaussCircleL2 :=
  (gaussArchScale m : Complex) • gaussPairedBlock hm k p

/-- The fully scaled paired block remains self-adjoint. -/
theorem gaussPairedBlockFull_inner
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (u v : GaussCircleL2) :
    inner Complex (gaussPairedBlockFull hm k p u) v =
      inner Complex u (gaussPairedBlockFull hm k p v) := by
  rw [gaussPairedBlockFull, smul_apply,
    smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, gaussPairedBlock_inner]

/-- Hilbert adjoint of the fully scaled paired block is itself. -/
theorem adjoint_gaussPairedBlockFull
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (gaussPairedBlockFull hm k p) =
      gaussPairedBlockFull hm k p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact gaussPairedBlockFull_inner hm k p u v

/-- Exact modulus square of the fully scaled paired block. -/
theorem gaussPairedBlockFull_modulusSq
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (gaussPairedBlockFull hm k p) ∘L
        gaussPairedBlockFull hm k p = gaussQuasiInnerGFull hm k p := by
  rw [adjoint_gaussPairedBlockFull, gaussPairedBlockFull,
    gaussQuasiInnerGFull_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_apply, map_smul, smul_smul]
  rw [show gaussPairedBlock hm k p (gaussPairedBlock hm k p u) =
      gaussQuasiInnerG hm k p u by
    have h := congrArg (fun T : GaussCircleL2 →L[Complex] GaussCircleL2 => T u)
      (gaussPairedBlock_sq hm k p)
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using h]
  have hscale :
      ((gaussArchScale m : Complex) * (gaussArchScale m : Complex)) =
        ((gaussArchScale m ^ (2 : ℕ) : ℝ) : Complex) := by
    push_cast
    ring
  rw [hscale]

/-- Reduced depth-one distinguished block after removing the source isometries. -/
def gaussOnePrimeReducedDefect (p : Nat.Primes) :
    GaussCircleL2 →L[Complex] GaussCircleL2 :=
  ((((1 : ℝ) - (p : ℝ)) / (p : ℝ)) : Complex) •
    gaussPairedBlockFull (le_refl 1) (0 : Fin 1) p

/-- The reduced one-prime defect is self-adjoint. -/
theorem gaussOnePrimeReducedDefect_inner (p : Nat.Primes) (u v : GaussCircleL2) :
    inner Complex (gaussOnePrimeReducedDefect p u) v =
      inner Complex u (gaussOnePrimeReducedDefect p v) := by
  rw [gaussOnePrimeReducedDefect, smul_apply,
    smul_apply, inner_smul_left, inner_smul_right]
  rw [gaussPairedBlockFull_inner]
  simp

/-- Hilbert adjoint of the reduced one-prime defect is itself. -/
theorem adjoint_gaussOnePrimeReducedDefect (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (gaussOnePrimeReducedDefect p) =
      gaussOnePrimeReducedDefect p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact gaussOnePrimeReducedDefect_inner p u v

/-- Literal reduced source-block energy equals the actual depth-one Gauss channel. -/
theorem gaussOnePrimeReducedDefect_modulusSq (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (gaussOnePrimeReducedDefect p) ∘L
        gaussOnePrimeReducedDefect p =
      gaussChannelOperator (le_refl 1) (0 : Fin 1) p := by
  rw [adjoint_gaussOnePrimeReducedDefect, gaussOnePrimeReducedDefect,
    gaussChannelOperator]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_apply, map_smul, smul_smul, pow_one]
  rw [show gaussPairedBlockFull (le_refl 1) (0 : Fin 1) p
      (gaussPairedBlockFull (le_refl 1) (0 : Fin 1) p u) =
        gaussQuasiInnerGFull (le_refl 1) (0 : Fin 1) p u by
    have h := congrArg (fun T : GaussCircleL2 →L[Complex] GaussCircleL2 => T u)
      (gaussPairedBlockFull_modulusSq (le_refl 1) (0 : Fin 1) p)
    simpa only [adjoint_gaussPairedBlockFull,
      ContinuousLinearMap.coe_comp, Function.comp_apply] using h]
  have hp0 : ((p : ℝ) : Complex) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hscale :
      (((((1 : ℝ) - (p : ℝ)) / (p : ℝ)) : Complex) *
          ((((1 : ℝ) - (p : ℝ)) / (p : ℝ)) : Complex)) =
        (gaussLocalFactorWeight 1 p : Complex) := by
    rw [gaussLocalFactorWeight]
    norm_num
    field_simp
    ring
  rw [hscale]

end

end RHTower
