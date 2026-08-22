import GaloisForLFunctions.HTGeometry.CriticalSheetScaleUnit
import GaloisForLFunctions.HTGeometry.CriticalSchurTailIntegrality
import GaloisForLFunctions.HTGeometry.SubringPolynomialCoefficients

/-!
# Every Schur coordinate of every sheet is integral at the upper Schur place

The corpus proves the Schur coordinates lie in the *source* Schur valuation subring — the place of
the canonical embedding.  A general sheet induces a *different* place on the source field, and the
collision argument needs all the coordinates to be integral at that one too.

```text
criticalSourceRaw_of_le          a raw coordinate above the depth is an observation coordinate
criticalSheetRaw_mem             ** every raw coordinate of every sheet lands in W **
criticalSheetPullbackSubring     the pullback of W along a sheet, as a subring of the source field
criticalSourceNormalizedPositive_mem_pullback
criticalSourceSchurCoordinates_mem_pullback
                                 ** and so does every Schur coordinate **
```

The raw coordinates split in two: below the depth they are the low coefficients of the sheet's fibre
point, integral by `criticalGeometricSheetToSchurFieldFibre_coefficients_mem`; above it they are
*observation* coordinates, which a sheet fixes and which are integral at the observation Schur place.

The passage to the Schur coordinates is `SubringPolynomialCoefficients` — no division occurs in the
truncated reciprocal — together with `CriticalSheetScaleUnit`, which makes the normalising scale a
unit of `W` at every sheet.  Note that `σ⁻¹(W) ⊇ criticalSchurSourceValuationSubring` is **false**
for a general sheet: distinct sheets induce distinct places over the same base, which is exactly why
only some sheets collide.  What is true, and what is proved here, is that the coordinates are
integral — the identification of the places themselves needs the residues.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- A raw source coordinate above the depth is an observation coordinate. -/
theorem criticalSourceRaw_of_le (hm : 0 < m) (hn : 0 < n) {j : Fin (m + n)} (hj : m ≤ (j : ℕ)) :
    criticalSourceRaw K m n j
      = algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
          (criticalObservationRaw K m n ⟨(j : ℕ) - m, by omega⟩) := by
  apply Subtype.ext
  change criticalAmbientRaw K m n (j : ℕ) = criticalAmbientRaw K m n (m + ((j : ℕ) - m))
  congr 1
  omega

/-- **Every raw source coordinate of every sheet lands in the upper Schur valuation ring.** -/
theorem criticalSheetRaw_mem (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (j : Fin (m + n)) :
    σ (criticalSourceRaw K m n j)
      ∈ criticalNormalClosureSchurValuationSubring K (by omega : 0 < m) (by omega : 0 < n) := by
  by_cases hj : (j : ℕ) < m
  · have hmem := (criticalGeometricSheetToSchurFieldFibre_coefficients_mem K hm hn
      (criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ)).1 ⟨(j : ℕ), hj⟩
    have hcoeff : (criticalGeometricSheetToSchurFieldFibre K (by omega : 0 < m)
          (by omega : 0 < n) σ).1.1.coeff ((⟨(j : ℕ), hj⟩ : Fin m) : ℕ)
        = σ (criticalSourceRaw K m n j) := by
      show ((criticalSourceRawLow K m n).map σ.toRingHom).coeff (j : ℕ) = _
      rw [Polynomial.coeff_map, criticalSourceRawLow, lowPolynomial_coeff, dif_pos hj]
      rfl
    rwa [hcoeff] at hmem
  · have hle : m ≤ (j : ℕ) := Nat.le_of_not_gt hj
    rw [criticalSourceRaw_of_le K (by omega) (by omega) hle, σ.commutes]
    exact criticalNormalClosureSchurValuationSubring_observation_mem K (by omega) (by omega)
      ⟨criticalObservationRaw K m n ⟨(j : ℕ) - m, by omega⟩,
        criticalObservationRaw_mem_observationValuationSubring K (by omega) (by omega) _⟩

/-- The pullback of the upper Schur valuation ring along a sheet, as a subring of the source. -/
def criticalSheetPullbackSubring (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) : Subring (criticalSourceField K m n) :=
  Subring.comap (σ : criticalSourceField K m n →+* criticalNormalClosure K m n)
    (criticalNormalClosureSchurValuationSubring K hm hn).toSubring

@[simp] theorem mem_criticalSheetPullbackSubring (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) (x : criticalSourceField K m n) :
    x ∈ criticalSheetPullbackSubring K hm hn σ ↔
      σ x ∈ criticalNormalClosureSchurValuationSubring K hm hn := Iff.rfl

/-- The normalised positive coordinates of a sheet land in the pullback subring. -/
theorem criticalSourceNormalizedPositive_mem_pullback (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (j : Fin (m + n - 1)) :
    criticalSourceNormalizedPositive K (by omega : 0 < m) (by omega : 0 < n) j
      ∈ criticalSheetPullbackSubring K (by omega) (by omega) σ := by
  have hraw := criticalSheetRaw_mem K hm hn σ (Fin.cast (by omega) j.succ)
  have hscale := isUnit_criticalSheetScale K hm hn σ
  obtain ⟨w, hw⟩ := hscale.exists_right_inv
  have hne : σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)) ≠ 0 := by
    intro h0
    have : (0 : criticalNormalClosure K m n) * (w : criticalNormalClosure K m n) = 1 := by
      rw [← h0]
      exact congrArg Subtype.val hw
    simp at this
  have hval : σ (criticalSourceNormalizedPositive K (by omega : 0 < m) (by omega : 0 < n) j)
      = σ (criticalSourceRaw K m n (Fin.cast (by omega) j.succ))
        * (σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)))⁻¹ := by
    show σ (normalizedFiniteJet (criticalSourceRawReindexed K _ _) j.succ) = _
    rw [normalizedFiniteJet, if_neg (by simp [Fin.succ_ne_zero]), map_div₀, div_eq_mul_inv]
    rfl
  rw [mem_criticalSheetPullbackSubring, hval]
  refine Subring.mul_mem _ hraw ?_
  have hinv : (σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)))⁻¹
      = (w : criticalNormalClosure K m n) :=
    inv_eq_of_mul_eq_one_right (congrArg Subtype.val hw)
  rw [hinv]
  exact w.property

/-- **Every Schur coordinate of every sheet lands in the pullback of the upper Schur valuation
ring.** -/
theorem criticalSourceSchurCoordinates_mem_pullback (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (i : Fin (m + n - 1 + 1)) :
    criticalSourceSchurCoordinates K (by omega : 0 < m) (by omega : 0 < n) i
      ∈ criticalSheetPullbackSubring K (by omega) (by omega) σ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [← criticalSourceScale_eq_schurCoordinate_zero K (by omega) (by omega)]
    exact criticalSheetScale_mem K hm hn σ
  · show criticalSourceReciprocalSquareReversed K (by omega : 0 < m) (by omega : 0 < n) j
      ∈ criticalSheetPullbackSubring K (by omega) (by omega) σ
    show finiteReciprocalSquarePositive
        (criticalSourceNormalizedPositive K (by omega : 0 < m) (by omega : 0 < n)) j.rev ∈ _
    exact finiteReciprocalSquarePositive_mem _ _
      (criticalSourceNormalizedPositive_mem_pullback K hm hn σ) _

end

end GaloisForLFunctions.HTGeometry
