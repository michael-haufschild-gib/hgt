import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierNativeSourceContactResidue
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity

/-!
# Strict-frontier integer holonomy

Every finite shifted-Xi strict-frontier contact has two intrinsic coordinates forced by the same
first live Padé defect: positive arithmetic-source amplitude and integer logarithmic residue.
This module proves the arbitrary analytic-order residue theorem, transfers contact order through
the exact Schur quotient to the actual admission norm, sharpens effectivity flow to the exact
one-successor positivity available at birth, and closes the false-RH alternative cofinally.
-/

noncomputable section

open Filter Function Set
open scoped Topology

theorem AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast
    {f : ℝ → ℝ} {x : ℝ} {d : ℕ}
    (hf : AnalyticAt ℝ f x) (horder : analyticOrderAt f x = d) :
    Tendsto (fun w => (w - x) * logDeriv f w)
      (nhdsWithin x {x}ᶜ) (nhds (d : ℝ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp horder
  have hfgEq : f =ᶠ[nhds x] (fun z => (z - x) ^ d * g z) := by
    filter_upwards [hfg] with z hz
    simpa only [smul_eq_mul] using hz
  have hgNonzero : ∀ᶠ w in nhds x, g w ≠ 0 :=
    hg.continuousAt.tendsto.eventually_ne hg0
  have hgAnalytic : ∀ᶠ w in nhds x, AnalyticAt ℝ g w := hg.eventually_analyticAt
  have hlog : ∀ᶠ w in nhdsWithin x {x}ᶜ,
      logDeriv f w = (d : ℝ) / (w - x) + logDeriv g w := by
    filter_upwards [hfgEq.filter_mono nhdsWithin_le_nhds,
      hfgEq.deriv.filter_mono nhdsWithin_le_nhds,
      hgNonzero.filter_mono nhdsWithin_le_nhds,
      hgAnalytic.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hfw hdfw hgw hga hw
    have hwx : w ≠ x := by simpa using hw
    have hpow : (w - x) ^ d ≠ 0 := pow_ne_zero d (sub_ne_zero.mpr hwx)
    have hmul := logDeriv_mul (f := fun z : ℝ => (z - x) ^ d) (g := g)
      w hpow hgw (by fun_prop) hga.differentiableAt
    rw [logDeriv_apply, hdfw, hfw]
    rw [← logDeriv_apply, hmul, logDeriv_fun_pow (by fun_prop) d]
    have hlinear : logDeriv (fun z : ℝ => z - x) w = 1 / (w - x) := by
      simp [logDeriv_apply]
    rw [hlinear]
    ring
  have hlogContinuous : ContinuousAt (logDeriv g) x := by
    change ContinuousAt (deriv g / g) x
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have hsub : Tendsto (fun w : ℝ => w - x) (nhdsWithin x {x}ᶜ) (nhds 0) := by
    have h : ContinuousAt (fun w : ℝ => w - x) x :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hrem : Tendsto (fun w : ℝ => (w - x) * logDeriv g w)
      (nhdsWithin x {x}ᶜ) (nhds 0) := by
    convert hsub.mul (hlogContinuous.tendsto.mono_left nhdsWithin_le_nhds) using 1
    all_goals simp
  rw [tendsto_congr' (show
    (fun w : ℝ => (w - x) * logDeriv f w) =ᶠ[nhdsWithin x {x}ᶜ]
      (fun w => (d : ℝ) + (w - x) * logDeriv g w) by
        filter_upwards [hlog, self_mem_nhdsWithin] with w hw hne
        have hwx : w ≠ x := by simpa using hne
        rw [hw]
        field_simp [sub_ne_zero.mpr hwx]
        )]
  simpa using tendsto_const_nhds.add hrem

namespace RHTower

open Matrix Polynomial Topology

/-- Exact effectivity flow under the sharp one-successor positivity hypothesis. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      (-xiShiftedCanonicalAdmissionEffectivityRate y n *
        xiShiftedCanonicalAdmissionNorm y n) y := by
  have hhead : (xiShiftedMomentHankelMatrix y n).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
    (y := y) hhead.det_pos.ne'
  have hsuccdet : 0 < (xiShiftedMomentHankelMatrix y (n + 1)).det := hH.det_pos
  have hNpos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    nlinarith [hhead.det_pos]
  have hodd : xiShiftedCanonicalAdmissionOddCurrent y n =
      xiShiftedCanonicalAdmissionAlpha y n *
        xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionAlpha]
    field_simp [hNpos.ne']
  have hraw := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    hy hn hhead.det_pos.ne'
  refine hraw.congr_deriv ?_
  rw [xiShiftedCanonicalAdmissionNormFlux,
    xiShiftedCanonicalAdmissionEffectivityRate, hodd]
  push_cast
  ring

private theorem analyticOrderAt_strictFrontierNewbornDet_eq_contact
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    analyticOrderAt
      (fun u : ℝ => (xiShiftedMomentHankelMatrix
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 3)).det) 0 = d := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hf : AnalyticAt ℝ
      (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 3)).det) 0 :=
    (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 3)).analyticAt
  change analyticOrderAt
    (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 3)).det) 0 = d
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro j hj
    simpa only [y] using
      iteratedDeriv_strictFrontierNewbornDet_eq_zero_of_lt_contact
        hne hstrict hzero hj
  · exact (iteratedDeriv_strictFrontierNewbornDet_pos_of_nativeSource
      hne hstrict hd hzero hsource).ne'

private theorem tendsto_strictFrontierNewbornDet_logDeriv_residue
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    Tendsto
      (fun u : ℝ => u * logDeriv
        (fun v : ℝ => (xiShiftedMomentHankelMatrix
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + v) (n + 3)).det) u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (d : ℝ)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hf : AnalyticAt ℝ
      (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 3)).det) 0 :=
    (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 3)).analyticAt
  have horder := analyticOrderAt_strictFrontierNewbornDet_eq_contact
    hne hstrict hd hzero hsource
  simpa only [y, sub_zero] using
    hf.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast horder

private theorem analyticAt_and_order_strictFrontierAdmissionNorm
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
    let m := n + 2
    AnalyticAt ℝ (fun u : ℝ => xiShiftedCanonicalAdmissionNorm (y + u) m) 0 ∧
      analyticOrderAt (fun u : ℝ => xiShiftedCanonicalAdmissionNorm (y + u) m) 0 = d := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let F : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (m + 1)).det
  let H : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) m).det
  let q : ℝ → ℝ := fun u => F u / H u
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef := by
    simpa only [y, m] using hface.1
  have hF : AnalyticAt ℝ F 0 := by
    simpa only [F] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (m + 1)).analyticAt
  have hH : AnalyticAt ℝ H 0 := by
    simpa only [H] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy m).analyticAt
  have hH0 : H 0 ≠ 0 := by
    simpa only [H, add_zero] using hhead.det_pos.ne'
  have hq : AnalyticAt ℝ q 0 := by
    change AnalyticAt ℝ (F / H) 0
    exact hF.div hH hH0
  have hForder : analyticOrderAt F 0 = d := by
    simpa only [F, y, m, Nat.add_assoc] using
      analyticOrderAt_strictFrontierNewbornDet_eq_contact
        hne hstrict hd hzero hsource
  obtain ⟨g, hg, hg0, hFg⟩ := hF.analyticOrderAt_eq_natCast.mp hForder
  have hqorder : analyticOrderAt q 0 = d := by
    rw [hq.analyticOrderAt_eq_natCast]
    refine ⟨fun u => g u / H u, hg.div hH hH0, div_ne_zero hg0 hH0, ?_⟩
    filter_upwards [hFg] with u hu
    dsimp only [q]
    rw [hu]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hheadEv := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hhead
  have hqNorm : q =ᶠ[nhds 0]
      (fun u => xiShiftedCanonicalAdmissionNorm (y + u) m) := by
    filter_upwards [hheadEv] with u hu
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y + u) hu.det_pos.ne'
    dsimp only [q, F, H]
    rw [hdetEq]
    exact mul_div_cancel_left₀ _ hu.det_pos.ne'
  exact ⟨hq.congr hqNorm,
    (analyticOrderAt_congr hqNorm).symm.trans hqorder⟩

/-- Every finite strict-frontier contact has exact integer logarithmic residue in its newborn
canonical admission norm. -/
theorem tendsto_xiShiftedStrictFrontierAdmissionNorm_logDeriv_integerResidue
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    Tendsto
      (fun u : ℝ => u * logDeriv
        (fun v : ℝ => xiShiftedCanonicalAdmissionNorm
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + v) (n + 2)) u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (d : ℝ)) := by
  have hdata := analyticAt_and_order_strictFrontierAdmissionNorm
    hne hstrict hd hzero hsource
  dsimp only at hdata
  have hfull := hdata.1.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast hdata.2
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
    apply nhdsWithin_mono
    intro u hu
    simp only [Set.mem_Ioi] at hu
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu.ne'
  simpa only [sub_zero] using hfull.mono_left hmono

/-- Contact order is exactly the negative residue of the sharp one-successor effectivity rate. -/
theorem tendsto_xiShiftedStrictFrontierAdmissionEffectivity_integerResidue
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    Tendsto
      (fun u : ℝ => u * xiShiftedCanonicalAdmissionEffectivityRate
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(d : ℝ))) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hnorm := tendsto_xiShiftedStrictFrontierAdmissionNorm_logDeriv_integerResidue
    hne hstrict hd hzero hsource
  have hpos : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (m + 1)).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hH : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (n + 3)).PosDef := by
      apply xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      · exact (add_pos hy hu).le
      · simpa only [y] using
          (lt_add_of_pos_right (xiShiftedHigherBlockTerminalFrontier (n + 1)) hu)
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (m + 1)).PosDef
    simpa only [m, Nat.add_assoc, Nat.reduceAdd] using hH
  have hlog : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      logDeriv (fun v : ℝ => xiShiftedCanonicalAdmissionNorm (y + v) m) u =
        -xiShiftedCanonicalAdmissionEffectivityRate (y + u) m := by
    filter_upwards [hpos, self_mem_nhdsWithin] with u hH hu
    have hhead : (xiShiftedMomentHankelMatrix (y + u) m).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    have hdetEq := det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y + u) hhead.det_pos.ne'
    have hsuccdet : 0 < (xiShiftedMomentHankelMatrix (y + u) (m + 1)).det := hH.det_pos
    have hNpos : 0 < xiShiftedCanonicalAdmissionNorm (y + u) m := by
      nlinarith [hhead.det_pos]
    have hflow :=
      hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef
        (add_pos hy hu) (by omega : 0 < m) hH
    have hshift : HasDerivAt
        (fun v : ℝ => xiShiftedCanonicalAdmissionNorm (y + v) m)
        (-xiShiftedCanonicalAdmissionEffectivityRate (y + u) m *
          xiShiftedCanonicalAdmissionNorm (y + u) m) u := by
      simpa [Function.comp_def] using
        hflow.comp u ((hasDerivAt_const u y).add (hasDerivAt_id u))
    rw [logDeriv_apply, hshift.deriv]
    field_simp [hNpos.ne']
  have hneg := hnorm.neg
  refine hneg.congr' ?_
  filter_upwards [hlog] with u hu
  rw [hu]
  ring

/-- Two-coordinate strict-frontier law: positive arithmetic amplitude and integer logarithmic
holonomy are forced by the same first live Padé contact. -/
def XiShiftedStrictFrontierIntegerHolonomyLaw (n : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧
    (∀ k < 2 * (n + 2) + d, xiShiftedStrictFrontierPadeDefect n k = 0) ∧
    0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) ∧
    0 < xiShiftedStrictFrontierAllContactSourceWallResidue n d ∧
    Tendsto (xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall n d)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) ∧
    XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n) ∧
    Tendsto
      (fun u : ℝ => u * logDeriv
        (fun v : ℝ => xiShiftedCanonicalAdmissionNorm
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + v) (n + 2)) u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (d : ℝ)) ∧
    Tendsto
      (fun u : ℝ => u * xiShiftedCanonicalAdmissionEffectivityRate
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(d : ℝ)))

/-- Every occupied physical strict frontier carries amplitude and integer-holonomy coordinates. -/
theorem xiShiftedStrictFrontier_integerHolonomyLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierIntegerHolonomyLaw n := by
  have hwall := xiShiftedStrictFrontier_allContactSourceWallResidueLaw
    hne hstrict hphysical
  dsimp only [XiShiftedStrictFrontierAllContactSourceWallResidueLaw] at hwall
  obtain ⟨d, hd, hzero, hsigned, hresidue, hwallLimit, hsource⟩ := hwall
  exact ⟨d, hd, hzero, hsigned, hresidue, hwallLimit, hsource,
    tendsto_xiShiftedStrictFrontierAdmissionNorm_logDeriv_integerResidue
      hne hstrict hd hzero hsource,
    tendsto_xiShiftedStrictFrontierAdmissionEffectivity_integerResidue
      hne hstrict hd hzero hsource⟩

/-- False-RH phase with cofinally many positive-amplitude, integer-charged strict frontiers. -/
def XiShiftedCofinalIntegerHolonomyPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      XiShiftedStrictFrontierIntegerHolonomyLaw n

theorem xiShiftedCofinalIntegerHolonomyPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalIntegerHolonomyPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict, hphysical,
    xiShiftedStrictFrontier_integerHolonomyLaw hne hstrict hphysical⟩

theorem not_xiShiftedCofinalIntegerHolonomyPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalIntegerHolonomyPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Premise-free phase closure in the two intrinsic contact coordinates. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalIntegerHolonomyPhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalIntegerHolonomyPhase := by
  constructor
  · exact not_xiShiftedCofinalIntegerHolonomyPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalIntegerHolonomyPhase_of_not_riemannHypothesis hnotRH)

/-- Closed RH-or-cofinal-integer-holonomy dichotomy. -/
theorem riemannHypothesis_or_xiShiftedCofinalIntegerHolonomyPhase :
    RiemannHypothesis ∨ XiShiftedCofinalIntegerHolonomyPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalIntegerHolonomyPhase_of_not_riemannHypothesis hRH)

end RHTower
