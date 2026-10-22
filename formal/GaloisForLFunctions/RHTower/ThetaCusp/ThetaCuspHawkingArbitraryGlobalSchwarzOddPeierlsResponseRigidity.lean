import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction

/-!
# Arbitrary-global Schwarz-odd Peierls response rigidity

For every complex-linear endomorphism of the global finite-support Xi carrier, Peierls skewness and
channel-Schwarz oddness force each literal same-fibre plus/minus source response to be Schwarz-real.
No diagonal, local, finite-range, bounded, or fibre-preserving hypothesis is used. The literal unit
BM boundary concomitant is Schwarz-real exactly on the critical line. Hence existence of any global
propagator satisfying skewness, Schwarz oddness, and universal exact unit BM incidence is equivalent
to RH.

`[NEW] [FULL LINEAR PROPAGATOR] [SCHWARZ REAL RESPONSE] [NO DIAGONALITY] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Peierls skewness for an arbitrary global complex-linear propagator. -/
def HBXiPeierlsGlobalPropagatorSkew
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) : Prop :=
  ∀ f g : HBXiPeierlsCarrier,
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta g f

/-- Channel-Schwarz oddness for an arbitrary global complex-linear propagator. -/
def HBXiPeierlsGlobalPropagatorChannelSchwarzOdd
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) : Prop :=
  ∀ f : HBXiPeierlsCarrier,
    hbXiPeierlsCanonicalChannelSchwarz (Delta f) =
      -Delta (hbXiPeierlsCanonicalChannelSchwarz f)

/-- Universal exact unit BM incidence for an arbitrary global complex-linear propagator. -/
def HBXiPeierlsGlobalPropagatorUniversalUnitSourceIncidence
    (n : ℕ) (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier) : Prop :=
  ∀ q : XiZeroCopy,
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta
        (hbXiPeierlsPlusSource 1 q) (hbXiPeierlsMinusSource 1 q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q

/-- The literal unit BM boundary concomitant is Schwarz-real exactly on the critical line. -/
theorem d4BMXiSecondHarmonicUnitSourceBoundaryConcomitant_schwarzReal_iff
    (n : ℕ) (q : XiZeroCopy) :
    (starRingEnd ℂ)
        (d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q ↔
        (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant_eq_radialWeight_mul_normSq]
  constructor
  · intro h
    by_contra hline
    have ha : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
        (by norm_num) q).not.mpr hline
    have hnormReal : Complex.normSq
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) ≠ 0 :=
      (Complex.normSq_eq_zero.not).2 ha
    have hnorm : ((Complex.normSq
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact hnormReal
    apply hbXiPeierlsRadialWeight_not_schwarzReal n q
    apply mul_right_cancel₀ hnorm
    simpa [map_mul] using h
  · intro hline
    have ha : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
        (by norm_num) q).2 hline
    rw [ha]
    simp

/-- Peierls skewness, pairing Schwarz reality, and propagator Schwarz oddness force every literal
same-fibre plus/minus source response to be Schwarz-real. No matrix-support condition is used. -/
theorem hbXiPeierlsGlobalPropagator_sourceResponse_schwarzReal
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hskew : HBXiPeierlsGlobalPropagatorSkew Delta)
    (hodd : HBXiPeierlsGlobalPropagatorChannelSchwarzOdd Delta)
    (amplitude : ℂ) (q : XiZeroCopy) :
    (starRingEnd ℂ)
        (d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta
          (hbXiPeierlsPlusSource amplitude q)
          (hbXiPeierlsMinusSource amplitude q)) =
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta
        (hbXiPeierlsPlusSource amplitude q)
        (hbXiPeierlsMinusSource amplitude q) := by
  let p := hbXiPeierlsPlusSource amplitude q
  let m := hbXiPeierlsMinusSource amplitude q
  have hpS : hbXiPeierlsCanonicalChannelSchwarz p = m := by
    dsimp [p, m]
    exact hbXiPeierlsCanonicalChannelSchwarz_plusSource amplitude q
  have hmS : hbXiPeierlsCanonicalChannelSchwarz m = p := by
    dsimp [p, m]
    exact hbXiPeierlsCanonicalChannelSchwarz_minusSource amplitude q
  have hschwarz := hbXiPeierlsPairing_channelSchwarz (Delta p) m
  rw [hodd p, hpS, hmS] at hschwarz
  have hschwarz' :
      -hbXiPeierlsPairing (Delta m) p =
        (starRingEnd ℂ) (hbXiPeierlsPairing (Delta p) m) := by
    simpa using hschwarz
  have hskew' := hskew p m
  change hbXiPeierlsPairing (Delta p) m =
      -hbXiPeierlsPairing (Delta m) p at hskew'
  change (starRingEnd ℂ) (hbXiPeierlsPairing (Delta p) m) =
    hbXiPeierlsPairing (Delta p) m
  exact (hskew'.trans hschwarz').symm

/-- At one Xi copy, exact unit BM incidence for an arbitrary skew, Schwarz-odd global propagator
forces criticality. -/
theorem hbXiPeierlsGlobalPropagator_unitSourceIncidence_forces_criticalLine
    (Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hskew : HBXiPeierlsGlobalPropagatorSkew Delta)
    (hodd : HBXiPeierlsGlobalPropagatorChannelSchwarzOdd Delta)
    (n : ℕ) (q : XiZeroCopy)
    (hincidence :
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing Delta
          (hbXiPeierlsPlusSource 1 q) (hbXiPeierlsMinusSource 1 q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (d4BMXiSecondHarmonicUnitSourceBoundaryConcomitant_schwarzReal_iff n q).1
  rw [← hincidence]
  exact hbXiPeierlsGlobalPropagator_sourceResponse_schwarzReal
    Delta hskew hodd 1 q

/-- Full-operator endpoint: an arbitrary global complex-linear Peierls propagator can obey
skewness, causal Schwarz oddness, and universal literal unit BM incidence exactly when RH holds. -/
theorem exists_hbXiPeierlsGlobalPropagator_skew_channelSchwarzOdd_and_universalUnitSourceIncidence_iff_rh
    (n : ℕ) :
    (∃ Delta : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier,
      HBXiPeierlsGlobalPropagatorSkew Delta ∧
        HBXiPeierlsGlobalPropagatorChannelSchwarzOdd Delta ∧
          HBXiPeierlsGlobalPropagatorUniversalUnitSourceIncidence n Delta) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨Delta, hskew, hodd, hincidence⟩
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    change (q.1 : ℂ).re = 1 / 2
    exact hbXiPeierlsGlobalPropagator_unitSourceIncidence_forces_criticalLine
      Delta hskew hodd n q (hincidence q)
  · intro hRH
    refine ⟨hbXiPeierlsWeightedPropagator (fun _ => 0),
      hbXiPeierlsWeightedSourcePairing_skew (fun _ => 0), ?_, ?_⟩
    · apply (hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff
        (fun _ : XiZeroCopy => (0 : ℂ))).2
      intro q
      simp
    · intro q
      apply (hbXiPeierlsUnitDiagonalSourceIncidence_iff n (fun _ => 0) q).2
      exact Or.inl (xi_divisor_support_re_eq_half_of_rh hRH q.1)

end

end RHTower
