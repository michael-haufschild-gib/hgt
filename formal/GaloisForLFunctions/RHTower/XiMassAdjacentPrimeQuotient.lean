import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeMask

/-!
# Adjacent-prime bounded ideal and surviving scalar Xi mass quotient

Subtracting any scalar multiple of the actual adjacent-prime mask preserves fixed-line boundedness.
Consequently, modulo critical-weight `ℓ¹` errors and this genuine cross-prime direction, the Xi mass
prime-mask quotient remains exactly one-dimensional: its scalar constant mode is equivalent to the
valuation-one open core, hence to the Riemann hypothesis under the established route equivalence.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiMassRemoveUnitAdjacentPrimeMask
    (w : Nat.Primes → ℂ) (b : ℂ) (p : Nat.Primes) : ℂ :=
  w p - b * xiMassUnitAdjacentPrimeMask p

theorem xiMassPrimeMaskedLayer_eq_removeUnitAdjacent_add
    {w : Nat.Primes → ℂ} {b c : ℂ} {a d : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖xiMassRemoveUnitAdjacentPrimeMask w b p - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    xiMassPrimeMaskedLayer w a τ =
      xiMassPrimeMaskedLayer (xiMassRemoveUnitAdjacentPrimeMask w b) a τ +
        b * xiMassPrimeMaskedLayer xiMassUnitAdjacentPrimeMask a τ := by
  have hv : Summable (fun p : Nat.Primes =>
      xiMassRemoveUnitAdjacentPrimeMask w b p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) :=
    summable_xiMassPrimeMaskedAtom hhalf hda hτ hdev
  have hm : Summable (fun p : Nat.Primes =>
      xiMassUnitAdjacentPrimeMask p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) :=
    summable_xiMassUnitAdjacentPrimeMaskedAtom hhalf hda hτ
  unfold xiMassPrimeMaskedLayer
  calc
    (∑' p : Nat.Primes,
        w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) =
      ∑' p : Nat.Primes,
        (xiMassRemoveUnitAdjacentPrimeMask w b p *
            xiMassCenteredPrimeAtom a τ (p : ℕ) +
          b * (xiMassUnitAdjacentPrimeMask p *
            xiMassCenteredPrimeAtom a τ (p : ℕ))) := by
      apply tsum_congr
      intro p
      unfold xiMassRemoveUnitAdjacentPrimeMask
      ring
    _ = (∑' p : Nat.Primes,
        xiMassRemoveUnitAdjacentPrimeMask w b p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) +
      ∑' p : Nat.Primes,
        b * (xiMassUnitAdjacentPrimeMask p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) :=
      hv.tsum_add (hm.mul_left b)
    _ = (∑' p : Nat.Primes,
        xiMassRemoveUnitAdjacentPrimeMask w b p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) +
      b * ∑' p : Nat.Primes,
        xiMassUnitAdjacentPrimeMask p *
          xiMassCenteredPrimeAtom a τ (p : ℕ) := by
      rw [tsum_mul_left]

theorem xiMassPrimeMaskedLineBound_iff_removeUnitAdjacent
    {w : Nat.Primes → ℂ} {b c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖xiMassRemoveUnitAdjacentPrimeMask w b p - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ ↔
      XiMassPrimeMaskedLineBound
        (xiMassRemoveUnitAdjacentPrimeMask w b) a σ := by
  obtain ⟨B, hB⟩ := xiMassUnitAdjacentPrimeMask_lineBound hhalf hda hσ
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + ‖b‖ * B, fun u => ?_⟩
    have heq := xiMassPrimeMaskedLayer_eq_removeUnitAdjacent_add
      hhalf hda (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev
    have hremove :
        xiMassPrimeMaskedLayer
            (xiMassRemoveUnitAdjacentPrimeMask w b) a
              ((σ : ℂ) + u * I) =
          xiMassPrimeMaskedLayer w a ((σ : ℂ) + u * I) -
            b * xiMassPrimeMaskedLayer xiMassUnitAdjacentPrimeMask a
              ((σ : ℂ) + u * I) := by
      rw [heq]
      ring
    rw [hremove]
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB u) (norm_nonneg _)))
  · rintro ⟨C, hC⟩
    refine ⟨C + ‖b‖ * B, fun u => ?_⟩
    rw [xiMassPrimeMaskedLayer_eq_removeUnitAdjacent_add
      hhalf hda (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev]
    exact (norm_add_le _ _).trans (add_le_add (hC u) (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB u) (norm_nonneg _)))

theorem xiMassPrimeMaskedLineBound_of_unitAdjacent_scalar_eq_zero
    {w : Nat.Primes → ℂ} {b c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c = 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖xiMassRemoveUnitAdjacentPrimeMask w b p - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ := by
  rw [xiMassPrimeMaskedLineBound_iff_removeUnitAdjacent
    hhalf hda hσ hdev]
  exact xiMassPrimeMaskedLineBound_of_scalar_eq_zero
    hhalf hda hσ hc hdev

theorem xiMassPrimeMaskedLineBound_iff_valuationOne_mod_unitAdjacent
    {w : Nat.Primes → ℂ} {b c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖xiMassRemoveUnitAdjacentPrimeMask w b p - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  exact (xiMassPrimeMaskedLineBound_iff_removeUnitAdjacent
    hhalf hda hσ hdev).trans
      (xiMassPrimeMaskedLineBound_iff_valuationOne
        hhalf hda hσ hc hdev)

theorem riemannHypothesis_iff_xiMassPrimeMaskedLineBound_mod_unitAdjacent
    {w : Nat.Primes → ℂ} {b c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖xiMassRemoveUnitAdjacentPrimeMask w b p - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    RiemannHypothesis ↔ XiMassPrimeMaskedLineBound w a σ := by
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    hhalf hda hσ).trans
      (xiMassPrimeMaskedLineBound_iff_valuationOne_mod_unitAdjacent
        hhalf hda hσ hc hdev).symm

end

end RHTower
