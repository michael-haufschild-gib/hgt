import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization

/-!
# Finite OAM-port obstruction for the PTR Floquet ladder

## PTR proof-chain position

The literal PTR realization contains a three-port OAM readout and a rotating
order-four constitutive harmonic.  A nonzero helical charge locks Floquet grade
`n` to OAM label `ℓ + n m`.  This file proves that the existing three-port
readout cannot faithfully encode even grades `0,1,2,3`: their OAM labels are
distinct, while a faithful encoding would inject `Fin 4` into `Fin 3`.

This closes only the *finite three-port boundary-readout* producer.  It does
not exclude an infinite OAM carrier or a physical mode-folding law that proves
which distinct labels may be identified.  Those are the exact surviving PTR
boundary data needed before a temporal-Maxwell model can produce the required
infinite conormal ladder.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A three-port readout is faithful on the first four Floquet grades when a
port collision can occur only for equal locked OAM labels. -/
def PhotonicThreePortFaithfulFirstFourOAMSidebands (ell m : ℤ) : Prop :=
  ∃ port : Fin 4 → Fin 3,
    ∀ n k : Fin 4, port n = port k →
      floquetSidebandAngularMomentum ell m (n : ℤ) =
        floquetSidebandAngularMomentum ell m (k : ℤ)

/-- Nonzero helical charge makes the first four locked OAM labels distinct. -/
theorem photonicFirstFourOAMLabels_injective
    {ell m : ℤ} (hm : m ≠ 0) :
    Function.Injective (fun n : Fin 4 =>
      floquetSidebandAngularMomentum ell m (n : ℤ)) := by
  intro n k h
  have hmul : (n : ℤ) * m = (k : ℤ) * m := by
    change ell + (n : ℤ) * m = ell + (k : ℤ) * m at h
    exact add_left_cancel h
  have hcast : (n : ℤ) = (k : ℤ) := mul_right_cancel₀ hm hmul
  apply Fin.ext
  exact_mod_cast hcast

/-- The literal three-port OAM readout cannot be a faithful realization of the
first four sidebands of any nontrivial rotating Floquet ladder. -/
theorem not_photonicThreePortFaithfulFirstFourOAMSidebands
    (ell m : ℤ) (hm : m ≠ 0) :
    ¬ PhotonicThreePortFaithfulFirstFourOAMSidebands ell m := by
  rintro ⟨port, hfaithful⟩
  have hinjective : Function.Injective port := by
    intro n k hport
    apply photonicFirstFourOAMLabels_injective hm
    exact hfaithful n k hport
  have hcard := Fintype.card_le_of_injective port hinjective
  norm_num at hcard

end RHTower
