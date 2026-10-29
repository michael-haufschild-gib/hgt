import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueWindowsControlEveryGramPacket
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ActualPrimeWindowsDiagonalizeAffineRamanujanModes

/-!
# Actual affine prime windows with moving affine parameters

A fixed conductor has only finitely many residue coordinates. The uniform
source comparison therefore permits both affine parameters to vary with
height. The conductor and multiplicative window remain fixed.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

private theorem sum_abs_affineRamanujanResidue_le {q : ℕ} [NeZero q] (n h : ℕ) :
    (∑ r : ZMod q, |affineRamanujanResidue q n h r|) ≤
      (q : ℝ) * q.totient := by
  have hb := sum_le_sum (s := (univ : Finset (ZMod q)))
    (fun r _ => BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient
      q (r.val * n + h))
  simpa only [affineRamanujanResidue, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul] using hb

/-- One horizon controls every affine multiplier and shift, including
choices depending arbitrarily on the height. -/
theorem eventually_affineRamanujanPrimeWindow_uniform {q : ℕ} (hq : 0 < q)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ n h : ℕ,
      |affineRamanujanPrimeWindow q n h A B N -
          (Real.log B - Real.log A) * ramanujanLagCoefficient q n *
            ramanujanLagCoefficient q h / (q.totient : ℝ)| ≤ ε := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hM : 0 < (q : ℝ) * q.totient := mul_pos hqR hφ
  filter_upwards [eventually_residuePrimeWindow_uniform (q := q) hA hAB (div_pos hε hM)] with N hN
  intro n h
  have hb := hN (affineRamanujanResidue q n h)
  rw [← affineRamanujanPrimeWindow_eq_residue, primeClassKappa_affineRamanujanResidue] at hb
  have he : ramanujanLagCoefficient q n * ramanujanLagCoefficient q h /
        (q.totient : ℝ) * (Real.log B - Real.log A) =
      (Real.log B - Real.log A) * ramanujanLagCoefficient q n *
        ramanujanLagCoefficient q h / (q.totient : ℝ) := by ring
  rw [he] at hb
  refine hb.trans ?_
  calc
    _ ≤ (ε / ((q : ℝ) * q.totient)) * ((q : ℝ) * q.totient) :=
      mul_le_mul_of_nonneg_left (sum_abs_affineRamanujanResidue_le n h)
        (div_nonneg hε.le hM.le)
    _ = ε := div_mul_cancel₀ ε hM.ne'

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_affineRamanujanPrimeWindow_uniform
