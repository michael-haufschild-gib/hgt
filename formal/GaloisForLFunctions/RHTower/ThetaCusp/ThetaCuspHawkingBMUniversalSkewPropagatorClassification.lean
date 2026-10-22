import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo

/-!
# HB universal skew-propagator classification

The target-scaled symplectic rotations used by the universal Peierls carrier are not a restricted
ansatz.  Every complex-linear endomorphism whose coordinate source pairing is skew has matrix

`[[0, -T], [T, 0]]`

for one unique complex scalar `T`.  This follows by testing skewness on the two coordinate basis
vectors and reconstructing the map by linearity.

This closes the algebraic arbitrary-map loophole in the universal two-dimensional carrier:
target-scaled rotations exhaust all skew complex-linear propagators.  Global BM rigidity is kept
in a separate downstream module so this classification has no Hardy-theorem dependency.

`[NEW] [CLASSIFICATION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Every skew propagator on the universal two-dimensional carrier is its unique scalar
symplectic rotation. -/
theorem hbUniversalPeierls_skewPropagator_eq_targetScaledRotation
    (Delta : HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier)
    (hskew : ∀ f g : HBUniversalPeierlsCarrier,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta f g =
        -d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta g f) :
    Delta = hbUniversalPeierlsPropagator (Delta (1, 0)).2 := by
  have h11 := hskew (1, 0) (1, 0)
  have h22 := hskew (0, 1) (0, 1)
  have h12 := hskew (1, 0) (0, 1)
  simp [d4GaugeFixedTeukolskyPeierlsSourcePairing, hbUniversalPeierlsPairing] at h11 h22 h12
  have ha : (Delta (1, 0)).1 = 0 := by
    linear_combination h11 / 2
  have hd : (Delta (0, 1)).2 = 0 := by
    linear_combination h22 / 2
  have hc : (Delta (0, 1)).1 = -(Delta (1, 0)).2 := by
    linear_combination h12
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hdecomp : (x, y) = x • ((1, 0) : HBUniversalPeierlsCarrier) +
      y • ((0, 1) : HBUniversalPeierlsCarrier) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul, map_smul]
  ext <;> simp [hbUniversalPeierlsPropagator, ha, hd, hc] <;> ring

/-- Scalar parameter of a universal-carrier skew propagator exists uniquely. -/
theorem hbUniversalPeierls_skewPropagator_existsUnique_targetScaledRotation
    (Delta : HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier)
    (hskew : ∀ f g : HBUniversalPeierlsCarrier,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta f g =
        -d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta g f) :
    ∃! T : ℂ, Delta = hbUniversalPeierlsPropagator T := by
  refine ⟨(Delta (1, 0)).2,
    hbUniversalPeierls_skewPropagator_eq_targetScaledRotation Delta hskew, ?_⟩
  intro T hT
  have hcoord := congrArg
    (fun L : HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier => (L (1, 0)).2) hT
  simpa [hbUniversalPeierlsPropagator] using hcoord.symm

end

end RHTower
