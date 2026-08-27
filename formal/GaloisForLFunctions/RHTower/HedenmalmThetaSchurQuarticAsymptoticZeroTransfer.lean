import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticDivisorCharge
import GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticChargeFlag
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

open Complex Filter Metric Set Topology Matrix
open scoped BigOperators Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- Reindexing from the source cutoff to `Fin` preserves the honest stage determinant. -/
theorem thetaSourceSignedOrdinaryDet_eq_stageFinDet (k : ℕ) (z : ℂ) :
    thetaSourceSignedOrdinaryDet k z =
      ((1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
        (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) -
        z • thetaSourceSignedStageFinMatrix k).det := by
  let e := Fintype.equivFin ↥(thetaSourceSignedCutoff k)
  let A : Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ :=
    1 - z • HilbertSchmidt.blockMatrix (thetaSourceSignedKernel k)
      (thetaSourceSignedCutoff k)
  have hmatrix :
      (1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
        (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) -
          z • thetaSourceSignedStageFinMatrix k = (Matrix.reindex e e) A := by
    ext i j
    simp [A, e, thetaSourceSignedStageFinMatrix,
      GaloisForLFunctions.HTGeometry.blockFin, Matrix.reindex_apply, Matrix.one_apply]
  rw [thetaSourceSignedOrdinaryDet, hmatrix]
  change A.det = ((Matrix.reindex e e) A).det
  exact (Matrix.det_reindex_self e A).symm

/-- Forget the source-specific name of a theta Schur packet. -/
def ThetaSourceStageSchurPacket.toFiniteMatrixSchurPacket
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    FiniteMatrixSchurPacket (thetaSourceSignedStageFinMatrix k) where
  U := S.U
  T := S.T
  unitary_left := S.unitary_left
  unitary_right := S.unitary_right
  triangular := S.triangular
  conjugates_matrix := S.conjugates_stage

/-- Reciprocal local quartic reporter attached to a determinant zero. -/
def thetaSourceReciprocalPositiveQuarticCharge (z : ℂ) : ℝ :=
  sourcePairPositiveQuarticCharge (z⁻¹).re (z⁻¹).im

theorem continuousAt_thetaSourceReciprocalPositiveQuarticCharge
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt thetaSourceReciprocalPositiveQuarticCharge z := by
  have hinv : ContinuousAt (fun w : ℂ => w⁻¹) z := continuousAt_id.inv₀ hz
  have hre : ContinuousAt (fun w : ℂ => (w⁻¹).re) z :=
    by simpa [Function.comp_def] using Complex.continuous_re.continuousAt.comp hinv
  have him : ContinuousAt (fun w : ℂ => (w⁻¹).im) z :=
    by simpa [Function.comp_def] using Complex.continuous_im.continuousAt.comp hinv
  unfold thetaSourceReciprocalPositiveQuarticCharge sourcePairPositiveQuarticCharge
  exact (continuousAt_const.mul (him.pow 2)).mul <|
    (continuousAt_const.mul (hre.pow 2)).add (continuousAt_const.mul (him.pow 2))

theorem thetaSourceReciprocalPositiveQuarticCharge_pos_of_im_ne_zero
    {z : ℂ} (him : z.im ≠ 0) :
    0 < thetaSourceReciprocalPositiveQuarticCharge z := by
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    exact him (by simp)
  have hinvIm : (z⁻¹).im ≠ 0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr him)
      ((Complex.normSq_eq_zero.not.mpr hz0))
  have hnonneg := sourcePairPositiveQuarticCharge_nonneg (z⁻¹).re (z⁻¹).im
  have hne : thetaSourceReciprocalPositiveQuarticCharge z ≠ 0 := by
    intro hzero
    apply hinvIm
    exact (sourcePairPositiveQuarticCharge_eq_zero_iff _ _).mp hzero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Source-side asymptotic GTA selector: arbitrarily late actual theta stages admit a Schur packet
with arbitrarily small positive quartic charge. -/
def ThetaSourceSchurPositiveQuarticChargeCofinallySmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
    ∃ S : ThetaSourceStageSchurPacket k,
      thetaSourceStageSchurPositiveQuarticCharge S < ε

/-- An off-real normalized-Xi zero forces one fixed positive reciprocal quartic lower bound on
every Schur packet of every sufficiently late actual theta stage. -/
theorem eventually_thetaSourceStageSchurPositiveQuarticCharge_gt_of_XiC_zero_im_ne_zero
    {z : ℂ} (hz : XiC z = 0) (him : z.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
      c < thetaSourceStageSchurPositiveQuarticCharge S := by
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    exact him (by simp)
  let qz : ℝ := thetaSourceReciprocalPositiveQuarticCharge z
  have hqz : 0 < qz :=
    thetaSourceReciprocalPositiveQuarticCharge_pos_of_im_ne_zero him
  have hqcont : ContinuousAt thetaSourceReciprocalPositiveQuarticCharge z :=
    continuousAt_thetaSourceReciprocalPositiveQuarticCharge hz0
  have hqnear : ∀ᶠ w in 𝓝 z,
      qz / 2 < thetaSourceReciprocalPositiveQuarticCharge w :=
    (tendsto_order.1 hqcont).1 (qz / 2) (half_lt_self hqz)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hqnear
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, XiC w = 0 := by
    intro hev
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ 0)
    exact XiC_zero_ne hall
  have hpunct : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
    (XiC_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let r : ℝ := min (η / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hη) (half_pos hδ)
  have hrη : r < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hsphereXi : ∀ w ∈ sphere z r, XiC w ≠ 0 := by
    intro w hw
    apply hδsub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ)
    · exact Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')
  have hsphere : ∀ w ∈ sphere z r, XiC w / XiC 0 ≠ 0 := by
    intro w hw hzero
    exact hsphereXi w hw ((div_eq_zero_iff.mp hzero).resolve_right XiC_zero_ne)
  have hlocal : ∀ᶠ k in atTop, ∃ w ∈ closedBall z r,
      thetaSourceSignedOrdinaryDet k w = 0 :=
    eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
      thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
      ((analyticOnNhd_univ_iff_differentiable.mp XiC_analytic).div_const (XiC 0))
      (Eventually.of_forall differentiable_thetaSourceSignedOrdinaryDet)
      hr (by simp [hz]) hsphere
  refine ⟨qz / 2, half_pos hqz, ?_⟩
  filter_upwards [hlocal] with k hk
  intro S
  obtain ⟨w, hwball, hwzero⟩ := hk
  have hw0 : w ≠ 0 := by
    intro hw
    subst w
    simp [thetaSourceSignedOrdinaryDet] at hwzero
  have hqw : qz / 2 < thetaSourceReciprocalPositiveQuarticCharge w := by
    apply hηsub
    exact Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hwball).trans_lt hrη)
  have hstage :
      ((1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
        (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) -
        w • thetaSourceSignedStageFinMatrix k).det = 0 := by
    rw [← thetaSourceSignedOrdinaryDet_eq_stageFinDet]
    exact hwzero
  have hlower :=
    sourcePairPositiveQuarticCharge_inv_le_finiteMatrixSchurPositiveQuarticCharge
      S.toFiniteMatrixSchurPacket hstage hw0
  change thetaSourceReciprocalPositiveQuarticCharge w ≤
    thetaSourceStageSchurPositiveQuarticCharge S at hlower
  exact hqw.trans_le hlower

/-- Cofinal smallness of actual theta-stage Schur quartic charge closes RH. -/
theorem riemannHypothesis_of_thetaSourceSchurPositiveQuarticChargeCofinallySmall
    (hsmall : ThetaSourceSchurPositiveQuarticChargeCofinallySmall) :
    RiemannHypothesis := by
  rw [_root_.RHTower.riemannHypothesis_iff_XiC_zeros_real]
  intro z hz
  by_contra him
  obtain ⟨c, hc, hevent⟩ :=
    eventually_thetaSourceStageSchurPositiveQuarticCharge_gt_of_XiC_zero_im_ne_zero hz him
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  obtain ⟨k, hk, S, hS⟩ := hsmall c hc N
  exact (not_lt_of_ge (hN k hk S).le) hS

/-- Exact all-stage vanishing implies the weaker cofinal-smallness selector. -/
theorem thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_flag
    (hflag : ThetaSourceSchurQuarticChargeFlag) :
    ThetaSourceSchurPositiveQuarticChargeCofinallySmall := by
  intro ε hε N
  let S : ThetaSourceStageSchurPacket N :=
    Classical.choice (nonempty_thetaSourceStageSchurPacket N)
  refine ⟨N, le_rfl, S, ?_⟩
  rw [hflag N S]
  exact hε

end
end RHTower.HedenmalmThetaSource
