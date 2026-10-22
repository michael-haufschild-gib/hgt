import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularSourceProjection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceCompleteL2Meromorphy

/-! Radial L² meromorphy of the actual complete angular source integral. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Integrating the complete source against its actual scalar testing field preserves radial L² admission. -/
theorem continuedAngularSourceProjection_memLp (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (continuedAngularSourceProjection q branch u a w) 2 radialMeasure := by
  have hm := (reducedCoefficient_memLp_horizon (physicalRate q branch) w a
    (continuedOnset (physicalRate q branch) w) (abs_lt.mp hwr).1).mul_const (scalarResidualPeriod q u)
  have hc := memLp_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    (continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr i).mul_const
      (scalarCutoffPeriod u (principalExponent q i)))
  apply (hm.add hc).ae_eq
  filter_upwards with t
  exact (continuedAngularSourceProjection_eq q branch u a w t).symm

/-- The radial L² class of the actual quotient integral, before any channel rewriting. -/
def continuedAngularSourceL2 (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) : Lp ℂ 2 radialMeasure :=
  l2Family radialMeasure (continuedAngularSourceProjection q branch u a) w

private theorem radialFamily_mul_const (F : ℂ → ℝ → ℂ) (w c : ℂ) (hF : MemLp (F w) 2 radialMeasure) :
    l2Family radialMeasure (fun v t => F v t*c) w = c • l2Family radialMeasure F w := by
  exact l2Family_smul radialMeasure F (fun v t => F v t*c) w c hF (fun t => by
    simp only [smul_eq_mul]
    ring)

/-- The integrated source class equals the exact sum of all four original radial channel classes. -/
theorem continuedAngularSourceL2_assembly (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    continuedAngularSourceL2 q branch u a w =
      scalarResidualPeriod q u • l2Family radialMeasure
        (fun v => reducedCoefficient (physicalRate q branch) v a (continuedOnset (physicalRate q branch) v)) w+
      ∑ i : Fin 3, scalarCutoffPeriod u (principalExponent q i) •
        l2Family radialMeasure (fun v => continuedCutoffRadialCoefficient q branch v a i) w := by
  let M (v : ℂ) := reducedCoefficient (physicalRate q branch) v a (continuedOnset (physicalRate q branch) v)
  let C (i : Fin 3) (v : ℂ) := continuedCutoffRadialCoefficient q branch v a i
  have hM : MemLp (M w) 2 radialMeasure := reducedCoefficient_memLp_horizon
    (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) (abs_lt.mp hwr).1
  have hC (i : Fin 3) : MemLp (C i w) 2 radialMeasure :=
    continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr i
  unfold continuedAngularSourceL2
  have hproj : continuedAngularSourceProjection q branch u a =
      (fun v t => M v t*scalarResidualPeriod q u+∑ i : Fin 3, C i v t*scalarCutoffPeriod u (principalExponent q i)) := by
    funext v t
    exact continuedAngularSourceProjection_eq q branch u a v t
  rw [hproj]
  rw [l2Family_add _ _ _ _ (hM.mul_const _) (memLp_finsetSum Finset.univ (fun i _ => (hC i).mul_const _)),
    l2Family_sum _ _ _ (fun i => (hC i).mul_const _),radialFamily_mul_const M w _ hM]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact radialFamily_mul_const (C i) w _ (hC i)

/-- The actual complete angular integral has a meromorphic germ in the radial L² norm. -/
theorem continuedAngularSourceL2_meromorphicAt (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MeromorphicAt (continuedAngularSourceL2 q branch u a) w := by
  have hconst (c : ℂ) : MeromorphicAt (fun _ : ℂ => c) w := analyticAt_const.meromorphicAt
  have hm := (hconst (scalarResidualPeriod q u)).smul
    (continuedReducedCoefficient_l2_analyticAt q branch w a (abs_lt.mp hwr).1).meromorphicAt
  have hc := MeromorphicAt.fun_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ =>
    (hconst (scalarCutoffPeriod u (principalExponent q i))).smul
      (continuedCutoffRadialCoefficient_l2_meromorphicAt q branch w a hw hwr i))
  apply (hm.add hc).congr
  have hn : ∀ᶠ v in 𝓝[≠] w, v.im ≠ 0 ∧ |v.re| < 2 :=
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn] with v hv
  exact (continuedAngularSourceL2_assembly q branch u a v hv.1 hv.2).symm

end
end RHTower.D4BMJointSource
