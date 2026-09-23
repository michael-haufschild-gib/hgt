import GaloisForLFunctions.RHTower.ProlateIndexedJointSpectrum
import GaloisForLFunctions.RHTower.ProlateCanonicalRadialFamily
import GaloisForLFunctions.RHTower.ProlateBandEigenMass

/-!
# Indexed prolate separation spectrum

The canonical radial data previously carried only an eventual liveness theorem.  Global liveness
of every signed index upgrades that data to an exact family at every positive aperture.  Full
Slepian eigenvalue simplicity then transfers regular prolate separation collisions back to squared
finite-Fourier collisions, which the indexed spectrum rules out.  Hence both angular separation
values `chi` and radial ratios `s = -chi/c²` distinguish every pair of actual indices.
-/

noncomputable section

namespace RHTower

/-- Canonical radial data are exact at every positive aperture and every index. -/
theorem signedModeRadialData_isExact_of_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (signedModeRadialData a n).IsExact a n :=
  signedModeRadialData_isExact ha n (evenProlateSignedValue_ne_zero ha n)

/-- Distinct actual signed indices carry distinct prolate separation eigenvalues. -/
theorem signedModeRadialData_chi_injective
    {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun n => (signedModeRadialData a n).chi) := by
  intro m n hchi
  change (signedModeRadialData a m).chi =
    (signedModeRadialData a n).chi at hchi
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  rcases hm with ⟨hmPhiSmooth, hmPhiNe, hmPhiEven, hmPhiOne, hmRdef,
    hmRSmooth, hmREven, hmROne, hmBand, hmProlate, hmSdef, hmSnonneg,
    hmEnd, hmOde⟩
  rcases hn with ⟨hnPhiSmooth, hnPhiNe, hnPhiEven, hnPhiOne, hnRdef,
    hnRSmooth, hnREven, hnROne, hnBand, hnProlate, hnSdef, hnSnonneg,
    hnEnd, hnOde⟩
  have hmRNe : (signedModeRadialData a m).R ≠ 0 := by
    intro hzero
    have hzeroOne := congrFun hzero 1
    rw [hmROne] at hzeroOne
    exact one_ne_zero hzeroOne
  have hnRNe : (signedModeRadialData a n).R ≠ 0 := by
    intro hzero
    have hzeroOne := congrFun hzero 1
    rw [hnROne] at hzeroOne
    exact one_ne_zero hzeroOne
  have hmRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a)
          (signedModeRadialData a m).R x =
        evenProlateSignedValue a m ^ (2 : ℕ) * (signedModeRadialData a m).R x := by
    rw [hmRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hmBand
  have hnRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ (2 : ℕ) * (signedModeRadialData a n).R x := by
    rw [hnRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hnBand
  have hnProlate' : ∀ x : ℝ,
      prolateSLAction (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x =
        (signedModeRadialData a m).chi * (signedModeRadialData a n).R x := by
    intro x
    rw [hchi]
    exact hnProlate x
  have hsq : evenProlateSignedValue a m ^ (2 : ℕ) =
      evenProlateSignedValue a n ^ (2 : ℕ) :=
    bandEigenvalue_eq_of_same_even_prolate_eigen
      hmRSmooth hnRSmooth hmRNe hnRNe hmREven hnREven
      (pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha m))
      (pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n))
      hmRBand hnRBand hmProlate hnProlate'
  exact evenProlateSignedValue_sq_injective ha hsq

/-- Radial separation ratios also distinguish every actual signed index. -/
theorem signedModeRadialData_s_injective
    {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun n => (signedModeRadialData a n).s) := by
  intro m n hs
  change (signedModeRadialData a m).s =
    (signedModeRadialData a n).s at hs
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  have hmS := hm.2.2.2.2.2.2.2.2.2.2.1
  have hnS := hn.2.2.2.2.2.2.2.2.2.2.1
  apply signedModeRadialData_chi_injective ha
  change (signedModeRadialData a m).chi =
    (signedModeRadialData a n).chi
  have hc : signedModeRadialBandwidth a ≠ 0 := by
    dsimp [signedModeRadialBandwidth]
    positivity
  rw [hmS, hnS] at hs
  dsimp [radialSeparationRatio] at hs
  field_simp [hc] at hs
  linarith

end RHTower
