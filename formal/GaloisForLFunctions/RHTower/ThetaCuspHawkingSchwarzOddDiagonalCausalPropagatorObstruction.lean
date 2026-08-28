import GaloisForLFunctions.RHTower.ThetaCuspHawkingDiagonalPeierlsSourceIncidenceRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification

/-!
# Schwarz-odd diagonal causal-propagator obstruction

Channel-Schwarz oddness of an arbitrary copy-diagonal Peierls propagator is equivalent to
copywise Schwarz reality of its Green-jump weights. The canonical BM radial weight is non-real on
every Xi copy because its imaginary part is the negative, nonzero Xi height. Consequently, a
copy-diagonal global jump can realize universal exact unit BM incidence and obey the Schwarz-odd
causal law simultaneously exactly when RH holds.

`[NEW] [CAUSAL PROPAGATOR] [SCHWARZ ODDNESS] [GREEN-JUMP OBSTRUCTION] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- A weighted causal propagator is odd under canonical channel Schwarz transport. -/
def HBXiPeierlsWeightedPropagatorChannelSchwarzOdd
    (w : XiZeroCopy → ℂ) : Prop :=
  ∀ f : HBXiPeierlsCarrier,
    hbXiPeierlsCanonicalChannelSchwarz
        (hbXiPeierlsWeightedPropagator w f) =
      -hbXiPeierlsWeightedPropagator w
        (hbXiPeierlsCanonicalChannelSchwarz f)

/-- Exact classification: channel-Schwarz oddness of a copy-diagonal propagator is precisely
copywise Schwarz reality of its Green-jump weights. -/
theorem hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff
    (w : XiZeroCopy → ℂ) :
    HBXiPeierlsWeightedPropagatorChannelSchwarzOdd w ↔
      ∀ q : XiZeroCopy, (starRingEnd ℂ) (w q) = w q := by
  constructor
  · intro h q
    have hq := congrArg (fun x : HBXiPeierlsCarrier => x.1 q)
      (h (Finsupp.single q 1, (0 : HBXiPeierlsPacket)))
    simpa [hbXiPeierlsCanonicalChannelSchwarz_apply,
      hbXiPeierlsWeightedPropagator_apply, map_mul] using hq
  · intro h f
    apply Prod.ext <;> ext q
    · simp [hbXiPeierlsCanonicalChannelSchwarz_apply,
        hbXiPeierlsWeightedPropagator_apply, map_mul, h q]
    · simp [hbXiPeierlsCanonicalChannelSchwarz_apply,
        hbXiPeierlsWeightedPropagator_apply, map_mul, h q]

/-- The canonical BM radial Green-jump weight has imaginary part equal to negative Xi height. -/
theorem hbXiPeierlsRadialWeight_im
    (n : ℕ) (q : XiZeroCopy) :
    (hbXiPeierlsRadialWeight n q).im = -(q.1 : ℂ).im := by
  change (-d4BMXiPlusPlusComplementaryExponent n q).im = _
  rw [Complex.neg_im, d4BMXiPlusPlusComplementaryExponent_im]

/-- Every canonical BM radial Green-jump weight is genuinely non-Schwarz-real. -/
theorem hbXiPeierlsRadialWeight_not_schwarzReal
    (n : ℕ) (q : XiZeroCopy) :
    (starRingEnd ℂ) (hbXiPeierlsRadialWeight n q) ≠
      hbXiPeierlsRadialWeight n q := by
  intro h
  have him := congrArg Complex.im h
  rw [Complex.conj_im, hbXiPeierlsRadialWeight_im] at him
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

/-- The canonical BM diagonal propagator is not Schwarz-odd, witnessed at every Xi copy. -/
theorem hbXiPeierlsRadialWeight_propagator_not_channelSchwarzOdd
    (n : ℕ) (q : XiZeroCopy) :
    ¬ HBXiPeierlsWeightedPropagatorChannelSchwarzOdd
        (hbXiPeierlsRadialWeight n) := by
  intro h
  have hreal :=
    (hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff
      (hbXiPeierlsRadialWeight n)).1 h
  exact hbXiPeierlsRadialWeight_not_schwarzReal n q (hreal q)

/-- A copy-diagonal global Peierls jump realizes literal unit BM incidence and satisfies the
causal Schwarz-odd law exactly when RH holds. -/
theorem exists_hbXiPeierlsUniversalUnitDiagonalSourceIncidence_and_channelSchwarzOdd_iff_rh
    (n : ℕ) :
    (∃ w : XiZeroCopy → ℂ,
      HBXiPeierlsUniversalUnitDiagonalSourceIncidence n w ∧
        HBXiPeierlsWeightedPropagatorChannelSchwarzOdd w) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨w, hincidence, hodd⟩
    have hreal :=
      (hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff w).1 hodd
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    change (q.1 : ℂ).re = 1 / 2
    rcases (hbXiPeierlsUnitDiagonalSourceIncidence_iff n w q).1
        (hincidence q) with hline | hweight
    · exact hline
    · exfalso
      apply hbXiPeierlsRadialWeight_not_schwarzReal n q
      simpa [hweight] using hreal q
  · intro hRH
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro q
      apply (hbXiPeierlsUnitDiagonalSourceIncidence_iff n (fun _ => 0) q).2
      exact Or.inl (xi_divisor_support_re_eq_half_of_rh hRH q.1)
    · apply (hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff
        (fun _ : XiZeroCopy => (0 : ℂ))).2
      intro q
      simp

end

end RHTower
