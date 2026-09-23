import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization

/-!
# PTR infinite conormal ladder is never finite energy

The source-defined prime half-density sidebands form one bilateral geometric
eigenfamily. Opposite grades multiply to one, so their squared norms cannot
both decay. The exact ladder is therefore outside the unweighted sideband
Hilbert space for every spectral parameter, including the critical line.

This rules out an exact finite-energy Maxwell boundary map with this ladder
as its output. The positive survivor is precise: the same ladder is
bilateral-moderate exactly on the critical line, so PTR requires a
distributional or singularly rigged boundary trace rather than an ordinary
bounded finite-energy sideband output. No Maxwell realization or RH is claimed.
-/

open Filter

namespace RHTower

noncomputable section
set_option autoImplicit false

/-- A nonzero bilateral geometric eigenfamily cannot have summable squared
norms on both sideband tails. -/
theorem bilateralEigenFamily_not_summable_norm_sq (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ Summable (fun e : ℤ => ‖bilateralEigenFamily lam e‖ ^ (2 : ℕ)) := by
  intro hs
  let g : ℤ → ℝ := fun e => ‖bilateralEigenFamily lam e‖ ^ (2 : ℕ)
  have hp : Tendsto (fun n : ℕ => g (n : ℤ)) atTop (nhds 0) := by
    exact (hs.comp_injective Int.ofNat_injective).tendsto_atTop_zero
  have hn : Tendsto (fun n : ℕ => g (-(n : ℤ))) atTop (nhds 0) := by
    apply Summable.tendsto_atTop_zero
    exact hs.comp_injective (by
      intro m n h
      exact Int.ofNat_injective (neg_injective h))
  have hpair (n : ℕ) :
      bilateralEigenFamily lam (n : ℤ) *
          bilateralEigenFamily lam (-(n : ℤ)) = 1 := by
    unfold bilateralEigenFamily
    rw [neg_neg]
    rw [← zpow_add₀ hlam]
    simp
  have hnorm (n : ℕ) : g (n : ℤ) * g (-(n : ℤ)) = 1 := by
    dsimp [g]
    rw [← mul_pow, ← norm_mul, hpair]
    simp
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    convert hp.mul hn using 1
    · funext n
      exact (hnorm n).symm
    · simp
  have h : (0 : ℝ) = 1 := tendsto_nhds_unique hzero tendsto_const_nhds
  simp at h

/-- The literal prime-calibrated complex-PTC conormal sidebands are never an
unweighted finite-energy `ℓ²(ℤ)` boundary vector. -/
theorem photonicPrimePCMConormalSideband_not_summable_norm_sq
    (p : Nat.Primes) (s : ℂ) :
    ¬ Summable (fun e : ℤ =>
      ‖photonicPrimePCMConormalSideband p s e‖ ^ (2 : ℕ)) := by
  rw [photonicPrimePCMConormalSideband_eq_bilateralEigenFamily]
  exact bilateralEigenFamily_not_summable_norm_sq
    (bilateralHalfDensityCharacter (p : ℕ) s)
    (bilateralHalfDensityCharacter_ne_zero p.property.pos s)

/-- Sharp survivor: this source ladder is moderate precisely on the critical
line, while remaining outside finite-energy sideband space there. -/
theorem photonicPrimePCMConormalSideband_moderate_not_finiteEnergy_iff
    (p : Nat.Primes) (s : ℂ) :
    (bilateralModerate (photonicPrimePCMConormalSideband p s) ∧
      ¬ Summable (fun e : ℤ =>
        ‖photonicPrimePCMConormalSideband p s e‖ ^ (2 : ℕ))) ↔
      s.re = 1 / 2 := by
  rw [bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half]
  simp [photonicPrimePCMConormalSideband_not_summable_norm_sq p s]

end

end RHTower
