import GaloisForLFunctions.RHTower.ProlateOscillatorIndexProperness
import GaloisForLFunctions.RHTower.ProlateSharpSeparationMode

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **Eventual uniqueness of the subunit oscillator mode.**  At every sufficiently large physical
aperture, every smooth nonzero even joint band/prolate mode with oscillator separation below one
is exactly the canonical signed index-zero eigenline. -/
theorem eventually_every_subunit_even_joint_prolate_is_canonical_zero :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      ∀ (lam eta : ℝ) (Phi : ℝ → ℝ),
        lam ≠ 0 →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi →
        Phi ≠ 0 → Function.Even Phi →
        (∀ x : ℝ,
          bandTransform (indexedOscillatorBandwidth a) Phi x = lam * Phi x) →
        (∀ x : ℝ,
          prolateSLAction (indexedOscillatorBandwidth a) Phi x = eta * Phi x) →
        indexedOscillatorBandwidth a *
            radialSeparationRatio (indexedOscillatorBandwidth a) eta < 1 →
        evenProlateSignedValue (a : ℝ) 0 ^ (2 : ℕ) = lam ∧
          eta = (signedModeRadialData (a : ℝ) 0).chi ∧
          ∃ r : ℝ, ∀ x : ℝ,
            Phi x = r * (signedModeRadialData (a : ℝ) 0).R x := by
  have hfirst :=
    eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation
      1 (ε := 1) zero_lt_one
  filter_upwards [hfirst] with a hfirstA
  norm_num at hfirstA
  intro lam eta Phi hlam hsm hne heven hband hprolate hsubunit
  obtain ⟨n, hnlam, hneta, hnline⟩ :=
    exists_canonical_signedIndex_of_even_joint_prolate a.property hlam hsm hne heven
      (by simpa [indexedOscillatorBandwidth] using hband)
      (by simpa [indexedOscillatorBandwidth] using hprolate)
  have hD := signedModeRadialData_isExact_of_pos a.property n
  have hmuN : indexedOscillatorSeparation n a =
      indexedOscillatorBandwidth a *
        radialSeparationRatio (indexedOscillatorBandwidth a) eta := by
    rw [indexedOscillatorSeparation, hD.2.2.2.2.2.2.2.2.2.2.1]
    simp only [indexedOscillatorBandwidth]
    rw [hneta]
  have hnzero : n = 0 := by
    by_contra hn
    have honeLe : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have horder := indexedOscillatorSeparation_monotone a honeLe
    change indexedOscillatorSeparation 1 a ≤ indexedOscillatorSeparation n a at horder
    rw [hmuN] at horder
    linarith
  subst n
  exact ⟨hnlam, hneta, hnline⟩

/-- The variationally guaranteed subunit mode is therefore the canonical index-zero mode itself,
not an aperture-dependent choice of spectral branch. -/
theorem eventually_indexedOscillatorSeparation_zero_lt_one :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation 0 a < 1 := by
  filter_upwards [eventually_every_subunit_even_joint_prolate_is_canonical_zero] with a hclass
  obtain ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, hsubunit⟩ :=
    exists_even_joint_prolate_eigen_bandwidth_separation_lt_one
      (indexedOscillatorBandwidth_pos a)
  have hident := hclass lam eta Phi hlam hsm hne heven hband hprolate hsubunit
  have hD := signedModeRadialData_isExact_of_pos a.property 0
  rw [indexedOscillatorSeparation, hD.2.2.2.2.2.2.2.2.2.2.1]
  simpa [indexedOscillatorBandwidth, hident.2.1] using hsubunit

/-- Canonical mode zero approaches its oscillator rung strictly from below. -/
theorem eventually_indexedOscillatorSeparation_zero_mem_Ioo
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation 0 a ∈ Ioo (1 - epsilon) 1 := by
  filter_upwards
    [eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation
      0 hepsilon,
     eventually_indexedOscillatorSeparation_zero_lt_one] with a hlow hupp
  constructor
  · simpa using hlow
  · exact hupp

end GaloisForLFunctions.RHTower
