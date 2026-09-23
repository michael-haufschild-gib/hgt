import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTransferCollisionRigidity

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Opposite-helicity amplitudes with prescribed common ingoing horizon value. -/
def d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed
    (q : XiZeroCopy) (horizon : ℂ) : ℂ × ℂ :=
  (horizon / d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q),
    horizon / d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q))

theorem d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed_reflect
    (q : XiZeroCopy) (horizon : ℂ) :
    d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
        (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon).1 = horizon := by
  change d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
    (horizon / d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q)) = horizon
  field_simp [d4BMGaugeFixedSecondHarmonicGreen_ne_zero]

theorem d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed_conj
    (q : XiZeroCopy) (horizon : ℂ) :
    d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) *
        (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon).2 = horizon := by
  change d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) *
    (horizon / d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q)) = horizon
  field_simp [d4BMGaugeFixedSecondHarmonicGreen_ne_zero]

theorem d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed_ne_zero
    (q : XiZeroCopy) {horizon : ℂ} (hhorizon : horizon ≠ 0) :
    d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp only [Prod.fst_zero] at hfirst
  exact (div_ne_zero hhorizon
    (d4BMGaugeFixedSecondHarmonicGreen_ne_zero (xiZeroCopyReflectEquiv q)))
    (by simpa [d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed] using hfirst)

/-- Common horizon data leave only reflected-minus-conjugated boundary transfer. -/
theorem d4BMXiFESchwarzFoldedOrthogonalRadiation_eq_boundaryDefect
    (q : XiZeroCopy) (mixing : ℂ × ℂ) (horizon : ℂ)
    (hreflect :
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * mixing.1 =
        horizon)
    (hconj :
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * mixing.2 =
        horizon) :
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q mixing =
      WithLp.toLp 2 ![0, 0, 0,
        (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) -
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q)) * horizon] := by
  ext i
  fin_cases i
  · simp [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
      d4BMGaugeFixedActualOrthogonalHelicityRadiation,
      d4BMGaugeFixedSecondHarmonicRadiationMap]
  · simp [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
      d4BMGaugeFixedActualOrthogonalHelicityRadiation,
      d4BMGaugeFixedSecondHarmonicRadiationMap]
  · change
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * mixing.1 -
        d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * mixing.2 = 0
    rw [hreflect, hconj, sub_self]
  · change
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
            d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * mixing.1 -
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
            d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * mixing.2 =
        (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) -
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q)) * horizon
    rw [mul_assoc, hreflect, mul_assoc, hconj]
    ring

theorem d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq
    (q : XiZeroCopy) (horizon : ℂ) :
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
        (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon) =
      WithLp.toLp 2 ![0, 0, 0,
        (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) -
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q)) * horizon] := by
  exact d4BMXiFESchwarzFoldedOrthogonalRadiation_eq_boundaryDefect q _ horizon
    (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed_reflect q horizon)
    (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed_conj q horizon)

/-- Squared optical size of the horizon-matched folded boundary defect. -/
def d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux
    (q : XiZeroCopy) (horizon : ℂ) : ℝ :=
  ‖d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
    (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon)‖ ^ (2 : ℕ)

theorem d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_eq
    (q : XiZeroCopy) (horizon : ℂ) :
    d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux q horizon =
      Complex.normSq
          (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) -
            d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q)) *
        Complex.normSq horizon := by
  rw [d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux,
    d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq,
    EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, Complex.normSq_eq_norm_sq]
  ring

/-- Nonzero common horizon data are folded-dark exactly on the critical line. -/
theorem d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
    (q : XiZeroCopy) {horizon : ℂ} (hhorizon : horizon ≠ 0) :
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
        (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq]
  constructor
  · intro h
    have hboundary := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 3) h
    simp at hboundary
    have htransfer :
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) := by
      apply sub_eq_zero.mp
      exact hboundary.resolve_right hhorizon
    exact
      (d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff q).mp htransfer
  · intro hline
    have htransfer :=
      (d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff q).mpr hline
    ext i
    fin_cases i <;> simp [htransfer]

theorem d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_eq_zero_iff
    (q : XiZeroCopy) {horizon : ℂ} (hhorizon : horizon ≠ 0) :
    d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux q horizon = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hnorm :
        ‖d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
          (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q horizon)‖ = 0 := by
      exact sq_eq_zero_iff.mp hzero
    exact
      (d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
        q hhorizon).mp (norm_eq_zero.mp hnorm)
  · intro hline
    have hvector :=
      (d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
        q hhorizon).mpr hline
    simp [d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux, hvector]

/-- Every off-line copy has positive folded boundary defect at nonzero common horizon data. -/
theorem d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_pos
    (q : XiZeroCopy) {horizon : ℂ} (hhorizon : horizon ≠ 0)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux q horizon := by
  have hne : d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux q horizon ≠ 0 := by
    intro hzero
    exact hoff
      ((d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_eq_zero_iff
        q hhorizon).mp hzero)
  exact lt_of_le_of_ne
    (by simp [d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux]) hne.symm

/-- Folded radiation of an arbitrary nonlinear horizon-normalized carrier. -/
def d4BMXiFESchwarzNonlinearCarrierFoldedOrthogonalRadiation
    {State : Type*} (carrier : State → ℂ)
    (q : XiZeroCopy) (state : State) : d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
    (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q (carrier state))

theorem d4BMXiFESchwarzNonlinearCarrierFoldedOrthogonalRadiation_eq_zero_iff
    {State : Type*} (carrier : State → ℂ)
    (q : XiZeroCopy) (state : State) (hcarrier : carrier state ≠ 0) :
    d4BMXiFESchwarzNonlinearCarrierFoldedOrthogonalRadiation carrier q state = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
    q hcarrier

/-- Canonical unit-horizon folded darkness on every Xi divisor copy. -/
def d4BMXiCanonicalHorizonFoldedDarkAtEveryCopy : Prop :=
  ∀ q : XiZeroCopy,
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q
      (d4BMXiFESchwarzHorizonNormalizedOrthogonalSeed q 1) = 0

/-- Universal folded darkness is exactly the Riemann hypothesis. -/
theorem d4BMXiCanonicalHorizonFoldedDarkAtEveryCopy_iff_riemannHypothesis :
    d4BMXiCanonicalHorizonFoldedDarkAtEveryCopy ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    let q : XiZeroCopy := xiFirstZeroCopy rho
    have hline :=
      (d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
        q (by norm_num : (1 : ℂ) ≠ 0)).mp (h q)
    simpa [q, xiFirstZeroCopy] using hline
  · intro hRH q
    apply
      (d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff
        q (by norm_num : (1 : ℂ) ≠ 0)).mpr
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (q.1 : ℂ)
      (xi_eq_zero_of_mem_divisor_support q.1)

end

end RHTower
