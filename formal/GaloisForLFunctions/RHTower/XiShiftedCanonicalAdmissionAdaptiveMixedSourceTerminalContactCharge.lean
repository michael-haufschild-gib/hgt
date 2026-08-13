import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAllDegreeCapital
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdjacentEdgeArithmeticAction
import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactSourceWallResidue

/-!
# Terminal contact charge of the adaptive mixed arithmetic source

The all-degree adaptive mixed/completed `P^sharp` source reserve has one distinguished final
summand.  Removing that summand leaves a retained reserve, while the literal source action itself
defines a terminal charge before any reflection or observation map is applied.  In every positive
right chamber this charge is exactly

`4 (N + 1) beta_(N+1) = 4 (N + 1) h_(N+1) / h_N`.

At a strict shifted-Xi frontier the numerator is precisely the newborn admission norm.  Hence an
arbitrary finite first contact of order `d` lands in this source channel with an exact positive
order-`d` residue.  The other reserve terms are retained rather than being asked to report the
contact.
-/

open Filter Matrix Polynomial Set Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- All all-degree source reserve except the newborn terminal Jacobi mass. -/
noncomputable def xiShiftedCanonicalAdmissionAllDegreeRetainedSourceReserve
    (y : ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N,
      (HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) j -
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) (j + 1)) ^ 2) +
    2 * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) 0 ^ 2 +
    8 * (∑ j ∈ Finset.range N,
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) j) +
    4 * (N + 1 : ℝ) *
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) N

/-- Source-first terminal channel left after the literal top source pays every lower connector and
the retained reserve.  This is defined from the adaptive mixed/completed source action, not from a
Jacobi coordinate or a reporting functional. -/
noncomputable def xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge
    (w : ℝ) (N : ℕ) : ℝ :=
  2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w N -
    xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy (w ^ 2) N -
    xiShiftedCanonicalAdmissionAllDegreeRetainedSourceReserve (w ^ 2) N

/-- Exact, unconditional accounting identity defining the terminal channel inside the literal
source aggregate. -/
theorem two_mul_adaptiveMixedCompletedSourceAction_eq_connector_add_retained_add_terminalCharge
    (w : ℝ) (N : ℕ) :
    2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w N =
      xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy (w ^ 2) N +
        xiShiftedCanonicalAdmissionAllDegreeRetainedSourceReserve (w ^ 2) N +
        xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge w N := by
  rw [xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge]
  ring

/-- The previous all-degree reserve is retained reserve plus exactly one newborn Jacobi mass. -/
theorem allDegreeSourceReserve_eq_retained_add_terminalBeta
    (y : ℝ) (N : ℕ) :
    xiShiftedCanonicalAdmissionAllDegreeSourceReserve y N =
      xiShiftedCanonicalAdmissionAllDegreeRetainedSourceReserve y N +
        4 * (N + 1 : ℝ) *
          HTGeometry.monicOrthoBeta
            (fun k => (xiShiftedReciprocalMoment y k).re) (N + 1) := by
  rw [xiShiftedCanonicalAdmissionAllDegreeSourceReserve,
    xiShiftedCanonicalAdmissionAllDegreeRetainedSourceReserve]
  ring

/-- **Arithmetic source law for the terminal channel.**  In a positive source chamber, the part
of the literal adaptive mixed/completed aggregate not spent on lower connectors or retained
reserve is exactly weighted newborn Jacobi mass. -/
theorem adaptiveMixedTerminalSourceCharge_eq_terminalBeta
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge w N =
      4 * (N + 1 : ℝ) *
        HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (N + 1) := by
  rw [xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge,
    two_mul_adaptiveMixedCompletedSourceAction_eq_allDegreeConnectorEnergy_add_reserve
      hw hN hH,
    allDegreeSourceReserve_eq_retained_add_terminalBeta]
  ring

/-- The norm-ratio/Jacobi-edge identification needs only the leading solve block.  No following
positive extension is required. -/
theorem xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta_of_head_posDef
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef) :
    xiShiftedCanonicalAdmissionAdjacentEdge y n =
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) m).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionAdjacentEdge]
  simp only [Nat.succ_sub_one]
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hH,
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hprev]
  rfl

/-- Inside a positive source chamber, terminal charge is exactly weighted newborn admission edge.
The edge identification itself uses only the shallower leading block. -/
theorem adaptiveMixedTerminalSourceCharge_eq_terminalAdmissionEdge
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge w N =
      4 * (N + 1 : ℝ) *
        xiShiftedCanonicalAdmissionAdjacentEdge (w ^ 2) (N + 1) := by
  rw [adaptiveMixedTerminalSourceCharge_eq_terminalBeta hw hN hH]
  have hhead : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (N + 1)).PosDef := by
    have hseq : xiShiftedRealMomentSequence w =
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) := by
      rfl
    rw [← hseq]
    exact xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta_of_head_posDef
    (by omega) hhead]

/-- Exact source-channel residue at an order-`d` strict-frontier contact. -/
noncomputable def xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue
    (n d : ℕ) : ℝ :=
  4 * (n + 2 : ℝ) * xiShiftedStrictFrontierAdmissionNormContactCoefficient n d /
    xiShiftedCanonicalAdmissionNorm
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1)

/-- **Strict contact lands in the arithmetic source terminal channel.**  After intrinsic order-`d`
scaling, the literal source-first terminal charge converges to its exact norm-ratio residue. -/
theorem tendsto_adaptiveMixedTerminalSourceCharge_div_pow_at_strictFrontierContact
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0) :
    Tendsto
      (fun u : ℝ =>
        xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge
            (Real.sqrt
              (xiShiftedHigherBlockTerminalFrontier (n + 1) + u)) (n + 1) /
          u ^ d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue n d)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let C := xiShiftedStrictFrontierAdmissionNormContactCoefficient n d
  let H : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 1)
  let B : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hsolve : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have htop : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    change (xiShiftedMomentHankelMatrix y (n + 2)).PosDef
    exact hface.1
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef htop
  have hHval : 0 < H y := by
    dsimp only [H]
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hsolve]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hadd : Tendsto (fun u : ℝ => y + u) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have hfull : Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 y) := by
      simpa using (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 (y + 0)))
    exact hfull.mono_left nhdsWithin_le_nhds
  have hHcont : ContinuousAt H y := by
    dsimp only [H]
    exact continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy (n + 1) hsolve.det_pos.ne'
  have hHtend : Tendsto (fun u : ℝ => H (y + u))
      (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := hHcont.tendsto.comp hadd
  have hBtend : Tendsto (fun u : ℝ => B (y + u) / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [B, y, C, xiShiftedStrictFrontierAdmissionNormContactCoefficient] using
      tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
        hne hstrict hd hzero
  have hratio : Tendsto
      (fun u : ℝ => 4 * (n + 2 : ℝ) * ((B (y + u) / u ^ d) / H (y + u)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (n + 2 : ℝ) * (C / H y))) :=
    (hBtend.div hHtend hHval.ne').const_mul (4 * (n + 2 : ℝ))
  have hright : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (n + 3)).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      (add_pos hy hu).le (by simpa only [y] using lt_add_of_pos_right _ hu)
  have hlimit : 4 * (n + 2 : ℝ) * (C / H y) =
      xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue n d := by
    dsimp only [xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue,
      C, H, y]
    ring
  rw [hlimit] at hratio
  apply hratio.congr'
  filter_upwards [hright, self_mem_nhdsWithin] with u hHu hu
  change 0 < u at hu
  have hyv : 1 / 2 < Real.sqrt (y + u) := by
    have hphysicalRight : 1 / 4 < y + u := by
      dsimp only [y]
      linarith
    nlinarith [Real.sq_sqrt (add_pos hy hu).le, Real.sqrt_nonneg (y + u)]
  have hsquare : (Real.sqrt (y + u)) ^ 2 = y + u :=
    Real.sq_sqrt (add_pos hy hu).le
  have hsource := adaptiveMixedTerminalSourceCharge_eq_terminalAdmissionEdge
    hyv (by omega : 0 < n + 1) (by
      have hseq : xiShiftedRealMomentSequence (Real.sqrt (y + u)) =
          (fun k => (xiShiftedReciprocalMoment (y + u) k).re) := by
        funext k
        rw [xiShiftedRealMomentSequence, hsquare]
      rw [hseq]
      simpa only [Nat.add_assoc] using hHu)
  have hedge : xiShiftedCanonicalAdmissionAdjacentEdge (y + u) (n + 2) =
      B (y + u) / H (y + u) := by
    rfl
  rw [hsource, hsquare, hedge]
  push_cast
  ring

/-- Positive first-contact coefficient gives a strictly positive terminal source-channel residue. -/
theorem xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue_pos
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    0 < xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue n d := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hsolve : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hsolve]
    have htop : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
      change (xiShiftedMomentHankelMatrix y (n + 2)).PosDef
      exact hface.1
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef htop) (by omega)
  have hC := xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos hsigned
  rw [xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue]
  exact div_pos (mul_pos (by positivity) hC) (by simpa only [y] using hnorm)

/-- Complete terminal-channel law at one strict frontier.  One contact order simultaneously records
the first live arithmetic coefficient and the exact positive residue of the literal source
aggregate's newborn channel. -/
def XiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeLaw (n : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧
    (∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0) ∧
    0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) ∧
    0 < xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue n d ∧
    Tendsto
      (fun u : ℝ =>
        xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge
            (Real.sqrt
              (xiShiftedHigherBlockTerminalFrontier (n + 1) + u)) (n + 1) /
          u ^ d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue n d))

/-- Every occupied physical strict frontier has an exact finite positive source terminal charge. -/
theorem xiShiftedStrictFrontier_adaptiveMixedTerminalSourceChargeLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeLaw n := by
  have hcontact := xiShiftedStrictFrontier_finiteArithmeticContactLaw
    hne hstrict hphysical
  dsimp only [XiShiftedStrictFrontierFiniteArithmeticContactLaw] at hcontact
  obtain ⟨d, hd, hzero, hsigned, _⟩ := hcontact
  exact ⟨d, hd, hzero, hsigned,
    xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue_pos
      hne hstrict hsigned,
    tendsto_adaptiveMixedTerminalSourceCharge_div_pow_at_strictFrontierContact
      hne hstrict hphysical hd hzero⟩

/-- Cofinal false-RH phase expressed entirely in the terminal channel of the source aggregate. -/
def XiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      XiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeLaw n

/-- False RH forces cofinally many exact positive terminal charges of the literal source
aggregate. -/
theorem xiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase := by
  have hphase := xiShiftedCofinalFiniteArithmeticContactPhase_of_not_riemannHypothesis hnot
  intro A
  obtain ⟨n, hne, hA, hstrict, hphysical, _⟩ := hphase A
  exact ⟨n, hne, hA, hstrict, hphysical,
    xiShiftedStrictFrontier_adaptiveMixedTerminalSourceChargeLaw
      hne hstrict hphysical⟩

/-- Excluding the cofinal terminal-source-charge phase is exactly RH.  This is a phase
classification, not exclusion of that phase. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase := by
  constructor
  · intro hRH hphase
    obtain ⟨n, hne, _⟩ := hphase 0
    rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
    exact Set.not_nonempty_empty hne
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalAdaptiveMixedTerminalSourceChargePhase_of_not_riemannHypothesis hnotRH)

end

end XiShiftedCanonicalAdmission
end RHTower
