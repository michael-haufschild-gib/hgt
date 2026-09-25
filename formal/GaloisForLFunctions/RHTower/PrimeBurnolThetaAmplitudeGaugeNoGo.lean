import GaloisForLFunctions.RHTower.PrimeBurnolThetaCubicTraceCancellation

/-!
# Amplitude-gauge blindness of Burnol--theta holonomy

The literal Burnol Gram has a separate nonzero amplitude at each prime-depth label.  Rescaling
those amplitudes by a diagonal unit on both sides of the Gram commutes with the blockwise theta
frame.  The resulting modular holonomy is conjugate to the original one, although every Gram
entry acquires the product of its two endpoint weights.

Thus conjugacy-invariant finite holonomy readouts cannot, by themselves, retain the coefficient
normalization of the prime source.  This does not exclude a source-framed singular cofinal
boundary: such a boundary would have to retain the amplitude gauge or break its continuity.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Ring A]

/-- Congruence by any unit commuting with the frame changes the modular holonomy only by
conjugacy.  This is the precise amplitude-gauge law used below. -/
theorem sourceFrameModularHolonomy_congruence
    (c u d : Aˣ) (hd : Commute d u) :
    sourceFrameModularHolonomy (d * c * d) u =
      d⁻¹ * sourceFrameModularHolonomy c u * d := by
  have hdui : d⁻¹ * u = u * d⁻¹ := hd.inv_left.eq
  have hdiu : d * u⁻¹ = u⁻¹ * d := hd.inv_right.eq
  have hconj : d⁻¹ * u * d = u := by rw [hdui]; group
  simp only [sourceFrameModularHolonomy, mul_inv_rev]
  calc
    d⁻¹ * (c⁻¹ * d⁻¹) * u * (d * c * d) * u⁻¹ =
        d⁻¹ * c⁻¹ * (d⁻¹ * u * d) * c * (d * u⁻¹) := by group
    _ = d⁻¹ * c⁻¹ * u * c * (u⁻¹ * d) := by rw [hconj, hdiu]
    _ = d⁻¹ * c⁻¹ * u * c * u⁻¹ * d := by group
    _ = d⁻¹ * (c⁻¹ * u * c * u⁻¹) * d := by group

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry Matrix
open scoped Kronecker

noncomputable section

/-- An independently chosen nonzero amplitude rescaling at each prime-depth label, repeated on
both theta coordinates. -/
def primeBurnolThetaAmplitudeGaugeUnit {N : ℕ} (w : Fin N → ℂˣ) :
    (Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)ˣ where
  val := primeBurnolThetaPrimeDepthMask (fun i => (w i : ℂ))
  inv := primeBurnolThetaPrimeDepthMask (fun i => (↑((w i)⁻¹) : ℂ))
  val_inv := by
    simp [primeBurnolThetaPrimeDepthMask, Matrix.diagonal_mul_diagonal]
  inv_val := by
    simp [primeBurnolThetaPrimeDepthMask, Matrix.diagonal_mul_diagonal]

@[simp] theorem coe_primeBurnolThetaAmplitudeGaugeUnit {N : ℕ}
    (w : Fin N → ℂˣ) :
    (↑(primeBurnolThetaAmplitudeGaugeUnit w) :
      Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) =
      primeBurnolThetaPrimeDepthMask (fun i => (w i : ℂ)) := rfl

/-- Every amplitude gauge commutes with the actual primewise theta frame. -/
theorem primeBurnolThetaAmplitudeGaugeUnit_commutes_frame {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) (w : Fin N → ℂˣ) :
    Commute (primeBurnolThetaAmplitudeGaugeUnit w)
      (primeBurnolThetaFrameUnit pe a) := by
  apply Units.ext
  exact primeBurnolThetaPrimeDepthMask_commutes_frame pe a (fun i => (w i : ℂ))

/-- The complete literal Burnol--theta holonomy is conjugate under every independent
prime-depth amplitude rescaling. -/
theorem primeBurnolThetaAmplitudeGauge_holonomy_conjugacy {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) (w : Fin N → ℂˣ) :
    sourceFrameModularHolonomy
      (primeBurnolThetaAmplitudeGaugeUnit w *
        primeBurnolDoubledGramUnit pe hpe kappa *
        primeBurnolThetaAmplitudeGaugeUnit w)
      (primeBurnolThetaFrameUnit pe a) =
      (primeBurnolThetaAmplitudeGaugeUnit w)⁻¹ *
        primeBurnolThetaModularHolonomy pe hpe kappa a *
        primeBurnolThetaAmplitudeGaugeUnit w := by
  exact sourceFrameModularHolonomy_congruence
    (primeBurnolDoubledGramUnit pe hpe kappa)
    (primeBurnolThetaFrameUnit pe a)
    (primeBurnolThetaAmplitudeGaugeUnit w)
    (primeBurnolThetaAmplitudeGaugeUnit_commutes_frame pe a w)

/-- The same congruence changes each *literal* doubled Gram entry by its endpoint amplitudes.
Thus the conjugacy class and the coefficient-level source have different information content. -/
theorem primeBurnolThetaAmplitudeGauge_doubledGram_apply {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (w : Fin N → ℂˣ)
    (i j : PrimeBurnolThetaIndex N) :
    ((↑(primeBurnolThetaAmplitudeGaugeUnit w *
        primeBurnolDoubledGramUnit pe hpe kappa *
        primeBurnolThetaAmplitudeGaugeUnit w) :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) i j) =
      (w i.1 : ℂ) *
        (primeBurnolWindowGramMatrix pe kappa ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j * (w j.1 : ℂ) := by
  simp only [Units.val_mul, coe_primeBurnolThetaAmplitudeGaugeUnit,
    coe_primeBurnolDoubledGramUnit]
  simp [primeBurnolThetaPrimeDepthMask, Matrix.diagonal_mul, Matrix.mul_diagonal]

end

end RHTower
