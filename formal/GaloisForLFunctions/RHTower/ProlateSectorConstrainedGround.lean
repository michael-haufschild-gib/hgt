import GaloisForLFunctions.RHTower.ProlateSectorGroundVector
import GaloisForLFunctions.RHTower.ProlateNegativeSectorLadder

/-!
# The constrained ground value of the leakage operator, in each Fourier sector

Combining the sector Rayleigh floor with the sector ground vector identifies the exact secular
root as the constrained leakage ground value of the operator `B = I − T²` on a Fourier sector of
the even carrier: no vector of the sector with vanishing integral has smaller leakage form, and one
of them realizes the value.  Both Fourier parities carry this, eventually in the aperture, because
their leakage ladders are ladder envelopes and their two head constraint coordinates converge to
nonzero Hermite values.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The Fourier-even sector index map. -/
def positiveSectorIndex (j : ℕ) : ℕ := 2 * j

/-- The Fourier-odd sector index map. -/
def negativeSectorIndex (j : ℕ) : ℕ := 2 * j + 1

theorem positiveSectorIndex_injective : Function.Injective positiveSectorIndex := by
  intro i j h
  simp only [positiveSectorIndex] at h
  omega

theorem negativeSectorIndex_injective : Function.Injective negativeSectorIndex := by
  intro i j h
  simp only [negativeSectorIndex] at h
  omega

/-- `μ` is the simple constrained leakage ground value of a prolate sector: it is a floor for the
leakage form of every vector of the sector annihilated by the integral functional, some nonzero
such vector realizes it, and the vectors realizing it form a single complex line. -/
def IsSectorConstrainedGround (a : ℝ) (σ : ℕ → ℕ) (μ : ℝ) : Prop :=
  (∀ (x : ℕ → ℂ) (f : evenSubspace),
      HasSum (fun j : ℕ => x j • sectorMode a σ j) f →
      inner ℂ (evenCentralIndicator a) f = 0 →
      μ * ‖f‖ ^ 2 ≤ (inner ℂ (evenProlateLeakage a f) f : ℂ).re) ∧
    ∃ f : evenSubspace,
      (∃ x : ℕ → ℂ, HasSum (fun j : ℕ => x j • sectorMode a σ j) f) ∧
        f ≠ 0 ∧
        inner ℂ (evenCentralIndicator a) f = 0 ∧
        (inner ℂ (evenProlateLeakage a f) f : ℂ).re = μ * ‖f‖ ^ 2 ∧
        ∀ (y : ℕ → ℂ) (g : evenSubspace),
          HasSum (fun j : ℕ => y j • sectorMode a σ j) g →
          inner ℂ (evenCentralIndicator a) g = 0 →
          (inner ℂ (evenProlateLeakage a g) g : ℂ).re = μ * ‖g‖ ^ 2 →
          ∃ c : ℂ, g = c • f

/-- **The secular ground root is the simple constrained leakage ground value of the sector.** -/
theorem isSectorConstrainedGround {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0) :
    IsSectorConstrainedGround a σ
      (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ)) := by
  refine ⟨fun x f hf hcon =>
    sector_rayleigh_ge_infiniteSecularRoot ha hσ h01 h12 hd2 hℓ0 hℓ1 hf hcon, ?_⟩
  obtain ⟨f, hf⟩ := exists_hasSum_sectorGround ha hσ h01 h12 hd2 hℓ0 hℓ1
  obtain ⟨hne, hcon, hval⟩ := sectorGround_properties ha hσ h01 h12 hd2 hℓ0 hℓ1 hf
  refine ⟨f, ⟨fun j => ((sectorGroundCoeff a σ j : ℝ) : ℂ), hf⟩, hne, hcon, hval, ?_⟩
  intro y g hg hgcon hgval
  set c : ℂ := y 0 / ((sectorGroundCoeff a σ 0 : ℝ) : ℂ) with hcdef
  have hcoeff : ∀ j : ℕ, y j = c * ((sectorGroundCoeff a σ j : ℝ) : ℂ) :=
    sector_coeff_eq_of_rayleigh_eq ha hσ h01 h12 hd2 hℓ0 hℓ1 hg hgcon hgval
  have hsm : HasSum
      (fun j : ℕ => c • (((sectorGroundCoeff a σ j : ℝ) : ℂ) • sectorMode a σ j)) (c • f) :=
    hf.const_smul c
  have hfun : (fun j : ℕ => c • (((sectorGroundCoeff a σ j : ℝ) : ℂ) • sectorMode a σ j))
      = fun j : ℕ => y j • sectorMode a σ j := by
    funext j
    rw [smul_smul, ← hcoeff j]
  rw [hfun] at hsm
  exact ⟨c, hg.unique hsm⟩

/-- **The Fourier-even sector, eventually in the aperture.** -/
theorem eventually_isSectorConstrainedGround_positive :
    ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex
      (infiniteSecularRoot (sectorLeakage a positiveSectorIndex)
        (sectorCoord a positiveSectorIndex)) := by
  have hne0 : constrainedProlateHermiteCoordinate 0 ≠ 0 := by
    rw [constrainedProlateHermiteCoordinate_zero_eq]
    positivity
  have hne1 : constrainedProlateHermiteCoordinate 1 ≠ 0 := by
    rw [constrainedProlateHermiteCoordinate_one_eq]
    positivity
  filter_upwards [ladderEnvelope_evenProlateSignedLeakage.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_atTop 0).eventually_ne hne0,
    (tendsto_norm_evenProlateConstraintCoord_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with a hs h0 h1 ha
  exact isSectorConstrainedGround ha positiveSectorIndex_injective
    hs.1.2.1 hs.1.2.2 hs.2 h0 h1

/-- **The Fourier-odd sector, eventually in the aperture.** -/
theorem eventually_isSectorConstrainedGround_negative :
    ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex
      (infiniteSecularRoot (sectorLeakage a negativeSectorIndex)
        (sectorCoord a negativeSectorIndex)) := by
  have hne0 : constrainedProlateNegativeCoordinate 0 ≠ 0 := by
    rw [constrainedProlateNegativeCoordinate_zero]
    positivity
  have hne1 : constrainedProlateNegativeCoordinate 1 ≠ 0 := by
    rw [constrainedProlateNegativeCoordinate_one]
    positivity
  filter_upwards [ladderEnvelope_evenProlateSignedLeakage_negative.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 0).eventually_ne hne0,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with a hs h0 h1 ha
  exact isSectorConstrainedGround ha negativeSectorIndex_injective
    hs.1.2.1 hs.1.2.2 hs.2 h0 h1

end RHTower

end
