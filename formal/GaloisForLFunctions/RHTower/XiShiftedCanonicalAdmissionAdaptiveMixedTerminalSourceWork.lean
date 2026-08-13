import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceTerminalContactCharge
import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierIntegerHolonomy

/-!
# Adaptive mixed terminal source work

This module differentiates the literal adaptive mixed/completed terminal source channel in the
squared-mass coordinate. Its primitive is a division-free adjacent-norm Wronskian: admitted
current and newborn amplitudes are paired bilinearly with odd Gamma norm flux before any
reflection aggregation or finite observation.

At a strict order-`d` contact, cleared work has exact order `d - 1`. Consequently the derivative
of literal terminal source charge has an exact strictly positive order-`d - 1` residue. The proof
uses only admitted solve blocks and right-germ positivity already present at the strict frontier;
it does not assume positivity at the next frontier and never divides by newborn charge.
-/

open Filter Matrix Polynomial Set Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

/-- Division-free adjacent-norm Wronskian. Odd Gamma norm flux is paired with admitted current and newborn amplitudes before reflection aggregation. -/
noncomputable def xiShiftedCanonicalAdmissionClearedTerminalSourceWork (y : ℝ) (N : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionNorm y N *
      xiShiftedCanonicalAdmissionNormFlux y (N + 1) -
    xiShiftedCanonicalAdmissionNorm y (N + 1) *
      xiShiftedCanonicalAdmissionNormFlux y N

/-- Quotient rule turning cleared bilinear work into motion of the terminal admission edge. Only the two admitted solve determinants are used. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionTerminalEdge_eq_clearedSourceWork
    {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : 0 < N)
    (hdetN : (xiShiftedMomentHankelMatrix y N).det ≠ 0)
    (hdetNext : (xiShiftedMomentHankelMatrix y (N + 1)).det ≠ 0)
    (hnorm : xiShiftedCanonicalAdmissionNorm y N ≠ 0) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionAdjacentEdge v (N + 1))
      (xiShiftedCanonicalAdmissionClearedTerminalSourceWork y N / xiShiftedCanonicalAdmissionNorm y N ^ 2) y := by
  have hcur := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    hy hN hdetN
  have hnext := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    hy (by omega : 0 < N + 1) hdetNext
  have hquot := hnext.div hcur hnorm
  change HasDerivAt
    (fun v => xiShiftedCanonicalAdmissionNorm v (N + 1) /
      xiShiftedCanonicalAdmissionNorm v N) _ y
  exact hquot.congr_deriv (by rw [xiShiftedCanonicalAdmissionClearedTerminalSourceWork]; ring)

/-- Weighted terminal-edge derivative in the arithmetic source normalization. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionWeightedTerminalEdge_eq_clearedSourceWork
    {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : 0 < N)
    (hdetN : (xiShiftedMomentHankelMatrix y N).det ≠ 0)
    (hdetNext : (xiShiftedMomentHankelMatrix y (N + 1)).det ≠ 0)
    (hnorm : xiShiftedCanonicalAdmissionNorm y N ≠ 0) :
    HasDerivAt
      (fun v => 4 * (N + 1 : ℝ) *
        xiShiftedCanonicalAdmissionAdjacentEdge v (N + 1))
      (4 * (N + 1 : ℝ) *
        xiShiftedCanonicalAdmissionClearedTerminalSourceWork y N / xiShiftedCanonicalAdmissionNorm y N ^ 2) y := by
  have h := hasDerivAt_xiShiftedCanonicalAdmissionTerminalEdge_eq_clearedSourceWork hy hN hdetN hdetNext hnorm
  simpa only [mul_div_assoc] using h.const_mul (4 * (N + 1 : ℝ))

/-- A nonvanishing admitted head norm has zero logarithmic residue. This removes the current-edge contribution at strict contact. -/
theorem tendsto_xiShiftedCanonicalAdmissionEffectivityRate_mul_offset_zero_of_succ_posDef
    {y : ℝ} (hy : 0 < y) {m : ℕ} (hm : 0 < m)
    (hH : (xiShiftedMomentHankelMatrix y (m + 1)).PosDef) :
    Tendsto
      (fun u : ℝ => u * xiShiftedCanonicalAdmissionEffectivityRate (y + u) m)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let F : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (m + 1)).det
  let H : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) m).det
  let q : ℝ → ℝ := fun u => F u / H u
  let N : ℝ → ℝ := fun u => xiShiftedCanonicalAdmissionNorm (y + u) m
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hF : AnalyticAt ℝ F 0 := by
    simpa only [F] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (m + 1)).analyticAt
  have hHa : AnalyticAt ℝ H 0 := by
    simpa only [H] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy m).analyticAt
  have hH0 : H 0 ≠ 0 := by
    simpa only [H, add_zero] using hhead.det_pos.ne'
  have hq : AnalyticAt ℝ q 0 := by
    change AnalyticAt ℝ (F / H) 0
    exact hF.div hHa hH0
  have hheadEv := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hhead
  have hqNorm : q =ᶠ[𝓝 0] N := by
    filter_upwards [hheadEv] with u hu
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y + u) hu.det_pos.ne'
    dsimp only [q, F, H, N]
    rw [hdetEq]
    exact mul_div_cancel_left₀ _ hu.det_pos.ne'
  have hNanalytic : AnalyticAt ℝ N 0 := hq.congr hqNorm
  have hN0 : N 0 ≠ 0 := by
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y) hhead.det_pos.ne'
    have htop : 0 < (xiShiftedMomentHankelMatrix y (m + 1)).det := hH.det_pos
    intro hz
    have hz' : xiShiftedCanonicalAdmissionNorm y m = 0 := by
      simpa only [N, add_zero] using hz
    rw [hz', mul_zero] at hdetEq
    linarith
  have horder : analyticOrderAt N 0 = 0 :=
    hNanalytic.analyticOrderAt_eq_zero.mpr hN0
  have hlogFull :=
    hNanalytic.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast horder
  have hmono : 𝓝[>] (0 : ℝ) ≤ nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
    apply nhdsWithin_mono
    intro u hu
    exact hu.ne'
  have hlog : Tendsto (fun u : ℝ => u * logDeriv N u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_zero, Nat.cast_zero] using hlogFull.mono_left hmono
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hH
  have heq : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      logDeriv N u = -xiShiftedCanonicalAdmissionEffectivityRate (y + u) m := by
    filter_upwards [hposAdd.filter_mono inf_le_left, self_mem_nhdsWithin] with u hHu hu
    have hflow :=
      hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef
        (add_pos hy hu) hm hHu
    have hshift : HasDerivAt N
        (-xiShiftedCanonicalAdmissionEffectivityRate (y + u) m *
          xiShiftedCanonicalAdmissionNorm (y + u) m) u := by
      simpa [N, Function.comp_def] using
        hflow.comp u ((hasDerivAt_const u y).add (hasDerivAt_id u))
    have hheadu : (xiShiftedMomentHankelMatrix (y + u) m).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHu
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y + u) hheadu.det_pos.ne'
    have hNormPos : 0 < xiShiftedCanonicalAdmissionNorm (y + u) m := by
      nlinarith [hHu.det_pos, hheadu.det_pos]
    rw [logDeriv_apply, hshift.deriv]
    dsimp only [N]
    field_simp [hNormPos.ne']
  have hneg : Tendsto (fun u : ℝ => -(u * logDeriv N u))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [neg_zero] using hlog.neg
  refine hneg.congr' ?_
  filter_upwards [heq] with u hu
  rw [hu, mul_neg, neg_neg]

/-- Cleared source work lowers every finite strict-contact order by exactly one and preserves its native positive coefficient. -/
theorem tendsto_xiShiftedStrictFrontierClearedTerminalSourceWork_div_pow_pred
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    let C := xiShiftedStrictFrontierAdmissionNormContactCoefficient n d
    Tendsto
      (fun u : ℝ => xiShiftedCanonicalAdmissionClearedTerminalSourceWork (y + u) (n + 1) / u ^ (d - 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((d : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1) * C)) := by
  dsimp only
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let C := xiShiftedStrictFrontierAdmissionNormContactCoefficient n d
  let H : ℝ → ℝ := fun u => xiShiftedCanonicalAdmissionNorm (y + u) (n + 1)
  let B : ℝ → ℝ := fun u => xiShiftedCanonicalAdmissionNorm (y + u) (n + 2)
  let E0 : ℝ → ℝ := fun u =>
    xiShiftedCanonicalAdmissionEffectivityRate (y + u) (n + 1)
  let E1 : ℝ → ℝ := fun u =>
    xiShiftedCanonicalAdmissionEffectivityRate (y + u) (n + 2)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hHface : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef := hface.1
  have hHcont : Tendsto H (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedCanonicalAdmissionNorm y (n + 1))) := by
    have hdet : (xiShiftedMomentHankelMatrix y (n + 1)).det ≠ 0 :=
      (xiShiftedMomentHankel_posDef_of_le
        (by omega : n + 1 ≤ n + 2) hHface).det_pos.ne'
    have hc := continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy (n + 1) hdet
    have hadd : Tendsto (fun u : ℝ => y + u) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      have hfull : Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 y) := by
        simpa using (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 (y + 0)))
      exact hfull.mono_left inf_le_left
    exact hc.tendsto.comp hadd
  have hBcontact : Tendsto (fun u : ℝ => B u / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [B, y, C, xiShiftedStrictFrontierAdmissionNormContactCoefficient] using
      tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
        hne hstrict hd hzero
  have hE0 : Tendsto (fun u : ℝ => u * E0 u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [E0] using tendsto_xiShiftedCanonicalAdmissionEffectivityRate_mul_offset_zero_of_succ_posDef hy (by omega) hHface
  have hE1 : Tendsto (fun u : ℝ => u * E1 u)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(d : ℝ))) := by
    simpa only [E1, y] using
      tendsto_xiShiftedStrictFrontierAdmissionEffectivity_integerResidue
        hne hstrict hd hzero hsource
  have hdiff : Tendsto (fun u : ℝ => u * (E0 u - E1 u))
      (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
    have h := hE0.sub hE1
    convert h using 1
    · funext u
      ring
    · ring
  have hprod := hHcont.mul (hBcontact.mul hdiff)
  have hprod' : Tendsto
      (fun u : ℝ => H u * ((B u / u ^ d) * (u * (E0 u - E1 u))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((d : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1) * C)) := by
    convert hprod using 1
    · ring
  have hright : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      (xiShiftedMomentHankelMatrix (y + u) (n + 3)).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      (add_pos hy hu).le (by simpa only [y] using lt_add_of_pos_right _ hu)
  apply hprod'.congr'
  filter_upwards [hright, self_mem_nhdsWithin] with u hHu hu
  have hcurH : (xiShiftedMomentHankelMatrix (y + u) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hHu
  have hcurRaw := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    (add_pos hy hu) (by omega : 0 < n + 1)
      (xiShiftedMomentHankel_posDef_of_le (by omega) hcurH).det_pos.ne'
  have hcurEff :=
    hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef
      (add_pos hy hu) (by omega : 0 < n + 1) hcurH
  have hnextRaw := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    (add_pos hy hu) (by omega : 0 < n + 2) hcurH.det_pos.ne'
  have hnextEff :=
    hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef
      (add_pos hy hu) (by omega : 0 < n + 2) hHu
  have hcurEq := hcurRaw.unique hcurEff
  have hnextEq := hnextRaw.unique hnextEff
  dsimp only [xiShiftedCanonicalAdmissionClearedTerminalSourceWork, H, B, E0, E1]
  rw [hcurEq, hnextEq]
  have hu0 : u ≠ 0 := hu.ne'
  rw [show u ^ d = u ^ (d - 1) * u by
    calc
      u ^ d = u ^ ((d - 1) + 1) := by
        exact congrArg (fun k : ℕ => u ^ k) (Nat.sub_add_cancel hd).symm
      _ = u ^ (d - 1) * u := by rw [pow_succ]]
  field_simp [hu0]
  ring

/-- Positivity of the order-lowered cleared-work coefficient. -/
theorem xiShiftedStrictFrontierClearedTerminalSourceWorkLeadingCoefficient_pos
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    0 < (d : ℝ) *
      xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) *
      xiShiftedStrictFrontierAdmissionNormContactCoefficient n d := by
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  have hhead : (xiShiftedMomentHankelMatrix
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hface.1) (by omega)
  have hC := xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos hsigned
  positivity

/-- Literal adaptive mixed/completed terminal source charge expressed in squared-mass coordinate. -/
noncomputable def xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass (y : ℝ) (N : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceCharge (Real.sqrt y) N

/-- In an admitted physical chamber, literal source charge equals its weighted terminal admission edge. -/
theorem adaptiveMixedTerminalSourceChargeAtMass_eq_terminalAdmissionEdge
    {y : ℝ} (hy : 1 / 4 < y) {N : ℕ} (hN : 0 < N)
    (hH : (xiShiftedMomentHankelMatrix y (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass y N =
      4 * (N + 1 : ℝ) * xiShiftedCanonicalAdmissionAdjacentEdge y (N + 1) := by
  have hsquare : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by positivity)
  have hsqrt : 1 / 2 < Real.sqrt y := by
    nlinarith [Real.sqrt_nonneg y]
  have hseq : xiShiftedRealMomentSequence (Real.sqrt y) =
      (fun k => (xiShiftedReciprocalMoment y k).re) := by
    funext k
    rw [xiShiftedRealMomentSequence, hsquare]
  have hsource := adaptiveMixedTerminalSourceCharge_eq_terminalAdmissionEdge
    hsqrt hN (by rw [hseq]; exact hH)
  simpa only [xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass, hsquare] using hsource

/-- Arithmetic producer law: derivative of literal adaptive mixed/completed source charge is cleared bilinear source work, formed before reflection aggregation. -/
theorem hasDerivAt_adaptiveMixedTerminalSourceChargeAtMass_eq_clearedSourceWork
    {y : ℝ} (hy : 1 / 4 < y) {N : ℕ} (hN : 0 < N)
    (hH : (xiShiftedMomentHankelMatrix y (N + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass v N)
      (4 * (N + 1 : ℝ) * xiShiftedCanonicalAdmissionClearedTerminalSourceWork y N /
        xiShiftedCanonicalAdmissionNorm y N ^ 2) y := by
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hheadN : (xiShiftedMomentHankelMatrix y N).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hheadNext : (xiShiftedMomentHankelMatrix y (N + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hedge := hasDerivAt_xiShiftedCanonicalAdmissionWeightedTerminalEdge_eq_clearedSourceWork hy0 hN hheadN.det_pos.ne'
    hheadNext.det_pos.ne' (by
      have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
        (y := y) hheadN.det_pos.ne'
      intro hz
      rw [hz, mul_zero] at hdetEq
      linarith [hheadNext.det_pos])
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hy0 hH
  have hto0 : Tendsto (fun v : ℝ => v - y) (𝓝 y) (𝓝 0) := by
    simpa using (tendsto_id.sub_const y :
      Tendsto (fun v : ℝ => v - y) (𝓝 y) (𝓝 (y - y)))
  have hposY : ∀ᶠ v : ℝ in 𝓝 y,
      (xiShiftedMomentHankelMatrix v (N + 2)).PosDef := by
    filter_upwards [hto0.eventually hposAdd] with v hv
    have harg : y + (v - y) = v := by ring
    rw [harg] at hv
    exact hv
  have hphysical : ∀ᶠ v : ℝ in 𝓝 y, 1 / 4 < v := Ioi_mem_nhds hy
  apply hedge.congr_of_eventuallyEq
  filter_upwards [hposY, hphysical] with v hv hvphysical
  exact adaptiveMixedTerminalSourceChargeAtMass_eq_terminalAdmissionEdge hvphysical hN hv

/-- Exact residue of literal source-charge motion at a strict order-d contact. -/
noncomputable def xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue (n d : ℕ) : ℝ :=
  4 * (n + 2 : ℝ) * (d : ℝ) *
      xiShiftedStrictFrontierAdmissionNormContactCoefficient n d /
    xiShiftedCanonicalAdmissionNorm
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1)

/-- Literal source-charge derivative has exact order d-1 at every physical strict contact. -/
theorem tendsto_adaptiveMixedTerminalSourceWork_div_pow_pred_at_strictFrontierContact
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    Tendsto
      (fun u : ℝ =>
        deriv (fun v => xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass v (n + 1)) (y + u) /
          u ^ (d - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue n d)) := by
  dsimp only
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let H : ℝ → ℝ := fun u => xiShiftedCanonicalAdmissionNorm (y + u) (n + 1)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hnorm : xiShiftedCanonicalAdmissionNorm y (n + 1) ≠ 0 := by
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y) hhead.det_pos.ne'
    intro hz
    rw [hz, mul_zero] at hdetEq
    linarith [hface.1.det_pos]
  have hW : Tendsto
      (fun u : ℝ => xiShiftedCanonicalAdmissionClearedTerminalSourceWork (y + u) (n + 1) / u ^ (d - 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((d : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1) *
        xiShiftedStrictFrontierAdmissionNormContactCoefficient n d)) := by
    simpa only [y] using tendsto_xiShiftedStrictFrontierClearedTerminalSourceWork_div_pow_pred hne hstrict hd hzero hsource
  have hHcont : Tendsto H (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedCanonicalAdmissionNorm y (n + 1))) := by
    have hc := continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy (n + 1) hhead.det_pos.ne'
    have hadd : Tendsto (fun u : ℝ => y + u) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      have hfull : Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 y) := by
        simpa using (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 (y + 0)))
      exact hfull.mono_left inf_le_left
    exact hc.tendsto.comp hadd
  have hratio := (hW.div (hHcont.pow 2) (pow_ne_zero 2 hnorm)).const_mul
    (4 * (n + 2 : ℝ))
  have hlimit : 4 * (n + 2 : ℝ) *
        (((d : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1) *
          xiShiftedStrictFrontierAdmissionNormContactCoefficient n d) /
          xiShiftedCanonicalAdmissionNorm y (n + 1) ^ 2) =
      xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue n d := by
    rw [xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue]
    dsimp only [y]
    field_simp [hnorm]
  rw [hlimit] at hratio
  have hratio' : Tendsto
      (fun u : ℝ => 4 * (n + 2 : ℝ) *
        ((xiShiftedCanonicalAdmissionClearedTerminalSourceWork (y + u) (n + 1) / u ^ (d - 1)) / H u ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue n d)) := by
    simpa only [H, Pi.div_apply] using hratio
  have hright : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      (xiShiftedMomentHankelMatrix (y + u) (n + 3)).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      (add_pos hy hu).le (by simpa only [y] using lt_add_of_pos_right _ hu)
  apply hratio'.congr'
  filter_upwards [hright, self_mem_nhdsWithin] with u hHu hu
  have hmass : 1 / 4 < y + u := by
    dsimp only [y]
    exact lt_trans hphysical (lt_add_of_pos_right _ hu)
  have hder := hasDerivAt_adaptiveMixedTerminalSourceChargeAtMass_eq_clearedSourceWork hmass (by omega : 0 < n + 1) (by
    simpa only [Nat.add_assoc] using hHu)
  rw [hder.deriv]
  dsimp only [H]
  push_cast
  ring

/-- The literal source-work residue is strictly positive. -/
theorem xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue_pos
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    0 < xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue n d := by
  have hWpos := xiShiftedStrictFrontierClearedTerminalSourceWorkLeadingCoefficient_pos hne hstrict hd hsigned
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  have hhead : (xiShiftedMomentHankelMatrix
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) := by
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := xiShiftedHigherBlockTerminalFrontier (n + 1)) hhead.det_pos.ne'
    nlinarith [hface.1.det_pos, hhead.det_pos]
  have hrewrite : xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue n d =
      4 * (n + 2 : ℝ) *
        (((d : ℝ) * xiShiftedCanonicalAdmissionNorm
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) *
          xiShiftedStrictFrontierAdmissionNormContactCoefficient n d) /
        xiShiftedCanonicalAdmissionNorm
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) ^ 2) := by
    rw [xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue]
    field_simp [hnorm.ne']
  rw [hrewrite]
  positivity

end XiShiftedCanonicalAdmission
end RHTower
