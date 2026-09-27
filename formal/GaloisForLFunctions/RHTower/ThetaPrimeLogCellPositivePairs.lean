import GaloisForLFunctions.RHTower.ThetaPrimeLogCellCoercivity
import GaloisForLFunctions.RHTower.ThetaFarPositiveBumpPairs

/-!
# Positive source pairs spanning complete prime-log cells

Smooth nonnegative bumps realize the entire selected cell as their open
difference interval. Every interior lag has a strictly positive ground cross
correlation. Thus any proper prime-power atom present in the cell really
contributes; it has not been removed by a support-avoidance construction.
Both full Weil energies are nevertheless strictly positive.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem thetaGroundShiftCross_pos_of_balls
    (phi psi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi) {c r h : ℝ}
    (hps : Function.support phi = Metric.ball 0 r)
    (hqs : Function.support psi = Metric.ball c r)
    (hp : ∀ x, 0 ≤ phi x) (hq : ∀ x, 0 ≤ psi x)
    (hh : c - 2 * r < h ∧ h < c + 2 * r) :
    0 < thetaGroundShiftCross phi psi h := by
  let x : ℝ := (c - h) / 2
  have hx : x ∈ Function.support phi := by
    rw [hps, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    dsimp only [x]
    constructor <;> linarith [hh.1, hh.2]
  have hy : x + h ∈ Function.support psi := by
    rw [hqs, Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [x]
    constructor <;> linarith [hh.1, hh.2]
  have hp' : 0 < phi x := (hp x).lt_of_ne' hx
  have hq' : 0 < psi (x + h) := (hq (x + h)).lt_of_ne' hy
  have hk := contDiff_thetaCuspFullSource.continuous
  have hcont : Continuous (fun y : ℝ => (thetaCuspFullSource y * phi y) *
      (thetaCuspFullSource (y + h) * psi (y + h))) :=
    (hk.mul phi.continuous).mul
      ((hk.mul psi.continuous).comp (continuous_id.add continuous_const))
  apply integral_pos_of_integrable_nonneg_nonzero hcont
    (integrable_thetaGroundShiftCross phi psi hc h)
  · intro y
    exact mul_nonneg (mul_nonneg (thetaCuspTiltSource.pos y).le (hp y))
      (mul_nonneg (thetaCuspTiltSource.pos (y + h)).le (hq (y + h)))
  · exact (mul_pos (mul_pos (thetaCuspTiltSource.pos x) hp')
      (mul_pos (thetaCuspTiltSource.pos (x + h)) hq')).ne'

/-- Actual nonzero positive pairs on cofinally many full prime-log cells, with every
interior translation active in their ground cross correlation. -/
theorem exists_cofinal_primeLogCell_positive_full_pairs (N : ℕ) :
    ∃ (n : ℕ) (phi psi : 𝓢(ℝ, ℝ)) (c r : ℝ), N ≤ n ∧ 0 < r ∧
      c - 2 * r = xiMassNthPrimeLogHeight n ∧
      c + 2 * r = xiMassNthPrimeLogHeight (n + 1) ∧
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      Function.support phi = Metric.ball 0 r ∧ Function.support psi = Metric.ball c r ∧
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧ 0 < phi 0 ∧ 0 < psi c ∧
      (∀ h ∈ Ioo (xiMassNthPrimeLogHeight n) (xiMassNthPrimeLogHeight (n + 1)),
        0 < thetaGroundShiftCross phi psi h) ∧
      0 < thetaRealArithmeticQuadratic (phi + psi) ∧
      0 < thetaRealArithmeticQuadratic (phi - psi) := by
  obtain ⟨kappa, hk, hcoercive⟩ := exists_thetaReal_cofinal_primeLogCell_coercivity
  obtain ⟨n, hn, hcell⟩ := hcoercive N
  let c := (xiMassNthPrimeLogHeight n + xiMassNthPrimeLogHeight (n + 1)) / 2
  let r := (xiMassNthPrimeLogHeight (n + 1) - xiMassNthPrimeLogHeight n) / 4
  have hlog : xiMassNthPrimeLogHeight n < xiMassNthPrimeLogHeight (n + 1) :=
    nthPrimeSubtype_log_strictMono (Nat.lt_succ_self n)
  have hr : 0 < r := div_pos (sub_pos.mpr hlog) (by positivity)
  have hleft : c - 2 * r = xiMassNthPrimeLogHeight n := by dsimp only [c, r]; ring
  have hright : c + 2 * r = xiMassNthPrimeLogHeight (n + 1) := by dsimp only [c, r]; ring
  let F : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  let H : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩
  let phi : 𝓢(ℝ, ℝ) := F.hasCompactSupport.toSchwartzMap F.contDiff
  let psi : 𝓢(ℝ, ℝ) := H.hasCompactSupport.toSchwartzMap H.contDiff
  have hps : Function.support phi = Metric.ball 0 r := F.support_eq
  have hqs : Function.support psi = Metric.ball c r := H.support_eq
  have hp0 : 0 < phi 0 := F.pos_of_mem_ball (by simpa only [Metric.mem_ball, dist_self] using hr)
  have hqc : 0 < psi c := H.pos_of_mem_ball (by simpa only [Metric.mem_ball, dist_self] using hr)
  have henergy := hcell phi psi F.hasCompactSupport H.hasCompactSupport 0 c r hr.le
    hps.subset hqs.subset (by simpa only [sub_zero] using hleft.ge)
    (by simpa only [sub_zero] using hright.le)
  have hm : 0 < thetaGroundNormSq (thetaComplexify phi) :=
    thetaGroundNormSq_pos_of_ne_zero _ (by
      rw [thetaComplexify_apply]
      exact Complex.ofReal_ne_zero.mpr hp0.ne')
  have hpos : 0 < kappa * (thetaGroundNormSq (thetaComplexify phi) +
      thetaGroundNormSq (thetaComplexify psi)) :=
    mul_pos hk (add_pos_of_pos_of_nonneg hm (thetaGroundNormSq_nonneg _))
  refine ⟨n, phi, psi, c, r, hn, hr, hleft, hright, F.hasCompactSupport, H.hasCompactSupport,
    hps, hqs, fun _ => F.nonneg, fun _ => H.nonneg, hp0, hqc, ?_,
    hpos.trans_le henergy.1, hpos.trans_le henergy.2⟩
  intro h hh
  apply thetaGroundShiftCross_pos_of_balls phi psi F.hasCompactSupport hps hqs
    (fun _ => F.nonneg) (fun _ => H.nonneg)
  rwa [hleft, hright]

end RHTower
