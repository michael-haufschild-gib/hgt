import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceTailDegreeLaw

/-!
# All-degree capital of the adaptive mixed arithmetic source

The top-degree literal adaptive mixed/completed `P^sharp` source action is not merely positive and
does not merely pay one adjacent degree edge.  It has an exact arithmetic decomposition which pays
the entire lower-degree connector path simultaneously.  After subtracting all squared adjacent
Jacobi-diagonal connectors from twice the top action, the remainder is exactly a sum of four
positive reserves:

* discrete curvature of the Jacobi diagonal;
* base-diagonal mass;
* interior Jacobi off-diagonal mass;
* terminal Jacobi off-diagonal mass.

Thus this is a source law, formed before reflection aggregation, rather than a fixed linear report.
On a common complete positive ray the same one top-degree source account gives a finite integral
capital for every internal cumulative-flux connector at once.
-/

open Matrix Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

private theorem alphaReserveIdentity (a : ℕ → ℝ) (N : ℕ) :
    4 * (∑ j ∈ Finset.range N, a j ^ 2) + 2 * a N ^ 2 -
        ∑ j ∈ Finset.range N, (a j + a (j + 1)) ^ 2 =
      (∑ j ∈ Finset.range N, (a j - a (j + 1)) ^ 2) + 2 * a 0 ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith [ih]

/-- Total squared adjacent-diagonal connector cost below top admission degree `N`. -/
noncomputable def xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy
    (y : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) j +
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) (j + 1)) ^ 2

/-- Positive remainder after twice the top source action pays every lower-degree connector. -/
noncomputable def xiShiftedCanonicalAdmissionAllDegreeSourceReserve
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
      (HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) N +
        HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (N + 1))

/-- **Exact all-degree arithmetic source law.**  Twice the literal adaptive mixed/completed
`P^sharp` source action splits into the full lower-degree connector energy and an explicit
arithmetic reserve. -/
theorem two_mul_adaptiveMixedCompletedSourceAction_sub_allDegreeConnectorEnergy_eq_reserve
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w N -
        xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy (w ^ 2) N =
      xiShiftedCanonicalAdmissionAllDegreeSourceReserve (w ^ 2) N := by
  let a : ℕ → ℝ := fun j => HTGeometry.monicOrthoAlpha
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) j
  have halpha := alphaReserveIdentity a N
  rw [xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
    hw hN hH, xiShiftedCanonicalAdmissionCumulativeJacobiDissipation]
  dsimp only [xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy,
    xiShiftedCanonicalAdmissionAllDegreeSourceReserve, a] at halpha ⊢
  nlinarith [halpha]

/-- Producer form of the exact law: full adaptive mixed/completed source action is connector cost
plus arithmetic reserve, with no observation map between them. -/
theorem two_mul_adaptiveMixedCompletedSourceAction_eq_allDegreeConnectorEnergy_add_reserve
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w N =
      xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy (w ^ 2) N +
        xiShiftedCanonicalAdmissionAllDegreeSourceReserve (w ^ 2) N := by
  have h :=
    two_mul_adaptiveMixedCompletedSourceAction_sub_allDegreeConnectorEnergy_eq_reserve
      hw hN hH
  linarith

/-- Terminal Jacobi mass makes the all-degree source reserve strictly positive. -/
theorem allDegreeConnectorEnergy_lt_two_mul_adaptiveMixedCompletedSourceAction
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy (w ^ 2) N <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w N := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbetaN : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedRealMomentSequence w) N :=
    HTGeometry.monicOrthoBeta_pos_below hbelow hN (by omega)
  have hbetaN1 : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedRealMomentSequence w) (N + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  have hseq : xiShiftedRealMomentSequence w =
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) := by
    rfl
  rw [hseq] at hbetaN hbetaN1
  have hreserve : 0 <
      xiShiftedCanonicalAdmissionAllDegreeSourceReserve (w ^ 2) N := by
    dsimp only [xiShiftedCanonicalAdmissionAllDegreeSourceReserve]
    have hsquares : 0 ≤ ∑ j ∈ Finset.range N,
        (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) j -
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (j + 1)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hbase : 0 ≤ 2 * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) 0 ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hbetasum : 0 ≤ 8 * (∑ j ∈ Finset.range N,
        HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) j) := by
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun j hj => ?_)
      by_cases hj0 : j = 0
      · subst j
        simp [HTGeometry.monicOrthoBeta]
      · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.pos_of_ne_zero hj0)
          (by
            have hjN := Finset.mem_range.mp hj
            omega)).le
    have hterminal : 0 < 4 * (N + 1 : ℝ) *
        (HTGeometry.monicOrthoBeta
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) N +
          HTGeometry.monicOrthoBeta
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (N + 1)) := by
      positivity
    linarith
  rw [←
    two_mul_adaptiveMixedCompletedSourceAction_sub_allDegreeConnectorEnergy_eq_reserve
      hw hN hH] at hreserve
  linarith

/-- Simultaneous Dirichlet density of all internal cumulative-flux degree connectors.  Degree zero
is excluded because cumulative-flux trace law starts at positive admission degree. -/
noncomputable def xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity
    (y : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 N,
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (j + 1) -
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux y j) ^ 2

/-- One top-degree adaptive mixed source action pays every internal degree connector at the same
mass. -/
theorem internalDegreeFluxDirichletDensity_lt_two_mul_adaptiveMixedCompletedSourceAction
    {y : ℝ} (hy : 1 / 4 < y) {N : ℕ} (hN : 0 < N)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
        (Real.sqrt y) N := by
  have hsq : (Real.sqrt y) ^ 2 = y :=
    Real.sq_sqrt (le_trans (by norm_num) hy.le)
  have hsqrt : 1 / 2 < Real.sqrt y := by
    nlinarith [Real.sqrt_nonneg y]
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (N + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (N + 2)).PosDef
    rwa [hsq]
  have hstrict :=
    allDegreeConnectorEnergy_lt_two_mul_adaptiveMixedCompletedSourceAction
      hsqrt hN hHsqrt
  rw [hsq] at hstrict
  have heq : xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N =
      ∑ j ∈ Finset.Ico 1 N,
        (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) j +
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) (j + 1)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjIco := Finset.mem_Ico.mp hj
    have hHj : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (Real.sqrt y)) (j + 3)).PosDef := by
      apply xiShiftedMomentHankel_posDef_of_le (by omega) hHsqrt
    have hedge :=
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux_succ_sub_eq_adjacentAlpha
        (w := Real.sqrt y) hjIco.1 hHj
    rw [hsq] at hedge
    have hseq : xiShiftedRealMomentSequence (Real.sqrt y) =
        (fun k => (xiShiftedReciprocalMoment y k).re) := by
      funext k
      rw [xiShiftedRealMomentSequence, hsq]
    rw [hseq] at hedge
    rw [hedge]
  have hsubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have hle : (∑ j ∈ Finset.Ico 1 N,
        (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) j +
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) (j + 1)) ^ 2) ≤
      xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy y N := by
    dsimp only [xiShiftedCanonicalAdmissionAllDegreeConnectorEnergy]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j _ _ => sq_nonneg _)
  rw [heq]
  exact lt_of_le_of_lt hle hstrict

/-- **Common full-tail degree capital.**  On a complete positive ray, all internal degree
connectors are jointly square-integrable and their total Dirichlet capital is paid by twice one
top-degree entry flux. -/
theorem integrableOn_Ioi_internalDegreeFluxDirichletDensity_and_integral_le_two_mul_entryFlux
    {a : ℝ} (ha : 1 / 4 < a) {N : ℕ} (hN : 0 < N)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    IntegrableOn
        (fun y => xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N)
        (Ioi a) ∧
      (∫ y in Ioi a,
          xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N) ≤
        2 * xiShiftedCanonicalAdmissionCumulativeJacobiFlux a N := by
  let E : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N
  let J : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
      (Real.sqrt y) N
  have htail := integral_Ioi_literalMassSourceAction_eq_currentFlux ha hN hH
  have hJint : IntegrableOn J (Ioi a) := by
    simpa only [J] using htail.1
  have hmajorInt : IntegrableOn (fun y => 2 * J y) (Ioi a) :=
    hJint.const_mul 2
  have hpoint : ∀ y ∈ Ioi a, E y < 2 * J y := by
    intro y hy
    dsimp only [E, J]
    exact internalDegreeFluxDirichletDensity_lt_two_mul_adaptiveMixedCompletedSourceAction
      (lt_trans ha hy) hN (hH y (Set.mem_Ici.mpr hy.le))
  have hEcont : ContinuousOn E (Ioi a) := by
    dsimp only [E, xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity]
    refine continuousOn_finsetSum _ fun j hj => ?_
    intro y hy
    have hjIco := Finset.mem_Ico.mp hj
    have hyquarter : 1 / 4 < y := lt_trans ha hy
    have hHtop := hH y (Set.mem_Ici.mpr hy.le)
    have hHnext : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((j + 1) + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHtop
    have hHcurrent : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (j + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHtop
    have hnext := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter (by omega : 0 < j + 1) hHnext
    have hcurrent := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter hjIco.1 hHcurrent
    exact ((hnext.sub hcurrent).continuousAt.pow 2).continuousWithinAt
  have hEaes : AEStronglyMeasurable E (volume.restrict (Ioi a)) :=
    hEcont.aestronglyMeasurable measurableSet_Ioi
  have hnormBound : ∀ᵐ y ∂volume.restrict (Ioi a), ‖E y‖ ≤ 2 * J y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => ?_)
    have hlt := hpoint y hy
    have hEnonneg : 0 ≤ E y := by
      dsimp only [E, xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hEnonneg]
    exact hlt.le
  have hEint : IntegrableOn E (Ioi a) :=
    hmajorInt.mono' hEaes hnormBound
  have hleAE : ∀ᵐ y ∂volume.restrict (Ioi a), E y ≤ 2 * J y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => (hpoint y hy).le)
  have hintegral := integral_mono_ae hEint hmajorInt hleAE
  refine ⟨hEint, ?_⟩
  dsimp only [E, J] at hintegral ⊢
  rw [integral_const_mul, htail.2] at hintegral
  exact hintegral

private theorem internalDegreeFlux_telescope (F : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Ico 1 N, (F (j + 1) - F j)) = F N - F 1 := by
  rw [Finset.sum_Ico_eq_sub _ hN, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- **Aggregate degree-amplitude source law.**  Cauchy compression of the whole internal degree
path is still paid by the same one top-degree source action.  This controls total degree
displacement rather than reporting individual edges. -/
theorem cumulativeJacobiFlux_sub_degreeOne_sq_lt_two_mul_degreeLength_mul_sourceAction
    {y : ℝ} (hy : 1 / 4 < y) {N : ℕ} (hN : 2 ≤ N)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y N -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux y 1) ^ 2 <
      2 * (N - 1 : ℕ) *
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
          (Real.sqrt y) N := by
  let F : ℕ → ℝ := fun j =>
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux y j
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.Ico 1 N) (f := fun j => F (j + 1) - F j)
  have htel := internalDegreeFlux_telescope F (by omega : 1 ≤ N)
  have hcard : ((Finset.Ico 1 N).card : ℝ) = (N - 1 : ℕ) := by
    rw [Nat.card_Ico]
  rw [htel, hcard] at hcs
  have hdensity :=
    internalDegreeFluxDirichletDensity_lt_two_mul_adaptiveMixedCompletedSourceAction
      hy (by omega : 0 < N) hH
  dsimp only [F] at hcs
  dsimp only [xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity]
    at hdensity
  have hfactor : 0 < (N - 1 : ℕ) := by omega
  have hscaled := mul_lt_mul_of_pos_left hdensity
    (show (0 : ℝ) < (N - 1 : ℕ) by exact_mod_cast hfactor)
  exact lt_of_le_of_lt hcs
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled)

/-- Aggregate cumulative-flux displacement between degree one and top degree is square-integrable
on every complete positive ray. -/
theorem integrableOn_Ioi_cumulativeJacobiFlux_sub_degreeOne_sq_and_integral_le
    {a : ℝ} (ha : 1 / 4 < a) {N : ℕ} (hN : 2 ≤ N)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    IntegrableOn
        (fun y =>
          (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y N -
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux y 1) ^ 2)
        (Ioi a) ∧
      (∫ y in Ioi a,
          (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y N -
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux y 1) ^ 2) ≤
        2 * (N - 1 : ℕ) *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux a N := by
  let A : ℝ → ℝ := fun y =>
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y N -
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux y 1) ^ 2
  let D : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N
  have hD :=
    integrableOn_Ioi_internalDegreeFluxDirichletDensity_and_integral_le_two_mul_entryFlux
      ha (by omega : 0 < N) hH
  have hDint : IntegrableOn D (Ioi a) := by simpa only [D] using hD.1
  have hfactorNonneg : (0 : ℝ) ≤ (N - 1 : ℕ) := by positivity
  have hmajorInt : IntegrableOn (fun y => (N - 1 : ℕ) * D y) (Ioi a) :=
    hDint.const_mul (N - 1 : ℕ)
  have hpoint : ∀ y ∈ Ioi a, A y ≤ (N - 1 : ℕ) * D y := by
    intro y hy
    let F : ℕ → ℝ := fun j =>
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux y j
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := Finset.Ico 1 N) (f := fun j => F (j + 1) - F j)
    have htel := internalDegreeFlux_telescope F (by omega : 1 ≤ N)
    have hcard : ((Finset.Ico 1 N).card : ℝ) = (N - 1 : ℕ) := by
      rw [Nat.card_Ico]
    rw [htel, hcard] at hcs
    simpa only [A, D, F,
      xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity] using hcs
  have hAcont : ContinuousOn A (Ioi a) := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_trans ha hy
    have hHtop := hH y (Set.mem_Ici.mpr hy.le)
    have hHone : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (1 + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHtop
    have hnext := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter (by omega : 0 < N) hHtop
    have hone := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter (by omega : 0 < 1) hHone
    exact ((hnext.sub hone).continuousAt.pow 2).continuousWithinAt
  have hAaes : AEStronglyMeasurable A (volume.restrict (Ioi a)) :=
    hAcont.aestronglyMeasurable measurableSet_Ioi
  have hnormBound : ∀ᵐ y ∂volume.restrict (Ioi a),
      ‖A y‖ ≤ (N - 1 : ℕ) * D y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => ?_)
    have hAnonneg : 0 ≤ A y := by dsimp only [A]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hAnonneg]
    exact hpoint y hy
  have hAint : IntegrableOn A (Ioi a) :=
    hmajorInt.mono' hAaes hnormBound
  have hleAE : ∀ᵐ y ∂volume.restrict (Ioi a),
      A y ≤ (N - 1 : ℕ) * D y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => hpoint y hy)
  have hintegral := integral_mono_ae hAint hmajorInt hleAE
  have hscaled := mul_le_mul_of_nonneg_left hD.2 hfactorNonneg
  refine ⟨hAint, ?_⟩
  dsimp only [A, D] at hintegral ⊢
  rw [integral_const_mul] at hintegral
  calc
    (∫ y in Ioi a,
        (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y N -
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux y 1) ^ 2) ≤
        (N - 1 : ℕ) *
          (∫ y in Ioi a,
            xiShiftedCanonicalAdmissionInternalDegreeFluxDirichletDensity y N) := hintegral
    _ ≤ (N - 1 : ℕ) *
        (2 * xiShiftedCanonicalAdmissionCumulativeJacobiFlux a N) := hscaled
    _ = 2 * (N - 1 : ℕ) *
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux a N := by ring

end
end XiShiftedCanonicalAdmission
end RHTower
