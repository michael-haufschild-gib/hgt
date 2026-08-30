import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodProbabilityNondivisibility
import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization
import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Sufficient macro formation and species exit for the theta cusp likelihood

The normalized theta cusp likelihoods form an exponential family in the seam variable, so the
total gap of an independent depth-`d` packet is a sufficient statistic: one Markov kernel,
independent of the tilt, recovers the whole packet from its total gap.  Consequently the macro
law carries exactly `d` times the one-packet relative entropy and the `d`-th power of the
one-packet Hellinger affinity.  At depth two the macro law charges the gap `6`, which the
one-particle law does not charge, so exact sufficient formation necessarily leaves the
one-particle atomic-support species.
-/

namespace RHTower

open MeasureTheory ProbabilityTheory InformationTheory
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The theta seam base measure and the likelihood ratio -/

/-- The untilted seam carrier `δ₀ + ν`. -/
def thetaCuspLikelihoodBaseMeasure : Measure ℝ :=
  Measure.dirac 0 + thetaCuspHigherLikelihoodSpectralMeasure

theorem withDensity_dirac_zero (B : ℝ) :
    (Measure.dirac (0 : ℝ)).withDensity (fun t => ENNReal.ofReal (Real.exp (-B * t)))
      = Measure.dirac 0 := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_dirac,
    Measure.dirac_apply' _ hs]
  by_cases h : (0 : ℝ) ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- The normalized likelihood is the exponentially tilted seam carrier. -/
theorem thetaCuspLikelihoodProbabilityMeasure_eq (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B
      = (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ •
        (thetaCuspLikelihoodBaseMeasure.withDensity
          (fun t => ENNReal.ofReal (Real.exp (-B * t)))) := by
  rw [thetaCuspLikelihoodProbabilityMeasure, thetaCuspLikelihoodSeamTiltedMeasure,
    thetaCuspLikelihoodBaseMeasure, withDensity_add_measure, withDensity_dirac_zero]
  congr 2

/-- **(FCAP.40)**  The likelihood ratio of two members of the family is the exponential of the
seam variable. -/
theorem thetaCuspLikelihood_withDensity_ratio {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    thetaCuspLikelihoodProbabilityMeasure B
      = (thetaCuspLikelihoodProbabilityMeasure B₀).withDensity
        (fun t => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
          / thetaCuspLikelihoodPartition B * Real.exp (-(B - B₀) * t))) := by
  have hZ : 0 < thetaCuspLikelihoodPartition B := thetaCuspLikelihoodPartition_pos hB
  have hZ₀ : 0 < thetaCuspLikelihoodPartition B₀ := thetaCuspLikelihoodPartition_pos hB₀
  rw [thetaCuspLikelihoodProbabilityMeasure_eq B, thetaCuspLikelihoodProbabilityMeasure_eq B₀,
    withDensity_smul_measure, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hdens : (fun t : ℝ => ENNReal.ofReal (Real.exp (-B₀ * t))
      * ENNReal.ofReal (thetaCuspLikelihoodPartition B₀ / thetaCuspLikelihoodPartition B
        * Real.exp (-(B - B₀) * t)))
      = fun t : ℝ => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
        / thetaCuspLikelihoodPartition B) * ENNReal.ofReal (Real.exp (-B * t)) := by
    funext t
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show Real.exp (-B₀ * t) * (thetaCuspLikelihoodPartition B₀
        / thetaCuspLikelihoodPartition B * Real.exp (-(B - B₀) * t))
      = thetaCuspLikelihoodPartition B₀ / thetaCuspLikelihoodPartition B
        * (Real.exp (-B₀ * t) * Real.exp (-(B - B₀) * t)) by ring, ← Real.exp_add]
    congr 2
    ring
  have hmulfun : (fun t : ℝ => ENNReal.ofReal (Real.exp (-B₀ * t)))
      * (fun t : ℝ => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
        / thetaCuspLikelihoodPartition B * Real.exp (-(B - B₀) * t)))
      = fun t : ℝ => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
        / thetaCuspLikelihoodPartition B) * ENNReal.ofReal (Real.exp (-B * t)) := hdens
  rw [hmulfun, show (fun t : ℝ => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
      / thetaCuspLikelihoodPartition B) * ENNReal.ofReal (Real.exp (-B * t)))
    = (ENNReal.ofReal (thetaCuspLikelihoodPartition B₀ / thetaCuspLikelihoodPartition B))
      • (fun t : ℝ => ENNReal.ofReal (Real.exp (-B * t))) from rfl,
    withDensity_smul _ (by fun_prop), smul_smul]
  congr 1
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp [hZ₀]) ENNReal.ofReal_ne_top, one_mul]

/-! ## The depth-`d` packet, its total gap and its macro law -/

/-- The total gap of a depth-`d` packet. -/
def thetaSumStat (d : ℕ) (x : Fin d → ℝ) : ℝ := ∑ i, x i

theorem measurable_thetaSumStat (d : ℕ) : Measurable (thetaSumStat d) := by
  unfold thetaSumStat; fun_prop

/-- The independent depth-`d` theta packet `P_B^{⊗ d}`. -/
def thetaPacket (d : ℕ) (B : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => thetaCuspLikelihoodProbabilityMeasure B

/-- **(FCAP.41)**  The macro law `M_{d,B}` is the total-gap image of the depth-`d` packet. -/
def thetaMacroLaw (d : ℕ) (B : ℝ) : Measure ℝ :=
  (thetaPacket d B).map (thetaSumStat d)

/-- The depth-`d` likelihood ratio, read on the total gap. -/
def thetaTiltDensity (d : ℕ) (B B₀ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((thetaCuspLikelihoodPartition B₀ / thetaCuspLikelihoodPartition B) ^ d
    * Real.exp (-(B - B₀) * s))

theorem measurable_thetaTiltDensity (d : ℕ) (B B₀ : ℝ) :
    Measurable (thetaTiltDensity d B B₀) := by
  unfold thetaTiltDensity; fun_prop

theorem isProbabilityMeasure_thetaPacket {d : ℕ} {B : ℝ} (hB : 0 < B) :
    IsProbabilityMeasure (thetaPacket d B) := by
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB
  show IsProbabilityMeasure (Measure.pi fun _ : Fin d => thetaCuspLikelihoodProbabilityMeasure B)
  infer_instance

/-- **(FCAP.46)**  The depth-`d` likelihood ratio depends on the packet only through its total
gap. -/
theorem thetaPacket_eq_withDensity {d : ℕ} {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    thetaPacket d B
      = (thetaPacket d B₀).withDensity (thetaTiltDensity d B B₀ ∘ thetaSumStat d) := by
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB₀
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (thetaCuspLikelihoodPartition B₀
    / thetaCuspLikelihoodPartition B * Real.exp (-(B - B₀) * t)) with hgdef
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hEq : (thetaCuspLikelihoodProbabilityMeasure B₀).withDensity g
      = thetaCuspLikelihoodProbabilityMeasure B :=
    (thetaCuspLikelihood_withDensity_ratio hB hB₀).symm
  haveI : SigmaFinite ((thetaCuspLikelihoodProbabilityMeasure B₀).withDensity g) := by
    rw [hEq]; infer_instance
  rw [thetaPacket, thetaPacket,
    show (fun _ : Fin d => thetaCuspLikelihoodProbabilityMeasure B)
      = fun _ : Fin d => (thetaCuspLikelihoodProbabilityMeasure B₀).withDensity g from
        funext fun _ => hEq.symm,
    ← pi_withDensity (fun _ : Fin d => thetaCuspLikelihoodProbabilityMeasure B₀)
      (f := fun _ => g) (fun _ => hgm)]
  congr 1
  funext x
  simp only [Function.comp_apply, thetaTiltDensity, thetaSumStat, hgdef]
  have hZ : 0 < thetaCuspLikelihoodPartition B := thetaCuspLikelihoodPartition_pos hB
  have hZ₀ : 0 < thetaCuspLikelihoodPartition B₀ := thetaCuspLikelihoodPartition_pos hB₀
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => mul_nonneg (div_nonneg hZ₀.le hZ.le) (Real.exp_nonneg _))]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, Finset.mul_sum]

/-- **(FCAP.43)**, macro half.  The macro law of a tilted member is the tilt of the macro law. -/
theorem thetaMacroLaw_eq_withDensity {d : ℕ} {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    thetaMacroLaw d B = (thetaMacroLaw d B₀).withDensity (thetaTiltDensity d B B₀) := by
  rw [thetaMacroLaw, thetaMacroLaw, thetaPacket_eq_withDensity hB hB₀,
    GaloisForLFunctions.HTGeometry.map_withDensity_comp _ (measurable_thetaSumStat d)
      (measurable_thetaTiltDensity d B B₀)]

/-! ## The recovery kernel -/

/-- The joint law of the total gap and the packet. -/
def thetaJoint (d : ℕ) (B : ℝ) : Measure (ℝ × (Fin d → ℝ)) :=
  (thetaPacket d B).map (fun x => (thetaSumStat d x, x))

theorem measurable_thetaJointMap (d : ℕ) :
    Measurable (fun x : Fin d → ℝ => (thetaSumStat d x, x)) :=
  (measurable_thetaSumStat d).prodMk measurable_id

theorem isProbabilityMeasure_thetaJoint {d : ℕ} {B : ℝ} (hB : 0 < B) :
    IsProbabilityMeasure (thetaJoint d B) := by
  haveI := isProbabilityMeasure_thetaPacket (d := d) hB
  constructor
  rw [thetaJoint, Measure.map_apply (measurable_thetaJointMap d) MeasurableSet.univ]
  simp

theorem thetaJoint_fst (d : ℕ) (B : ℝ) :
    (thetaJoint d B).fst = thetaMacroLaw d B := by
  rw [Measure.fst, thetaJoint, Measure.map_map measurable_fst (measurable_thetaJointMap d)]
  rfl

theorem thetaJoint_snd (d : ℕ) (B : ℝ) :
    (thetaJoint d B).map Prod.snd = thetaPacket d B := by
  rw [thetaJoint, Measure.map_map measurable_snd (measurable_thetaJointMap d)]
  exact Measure.map_id

/-- **(FCAP.42)**  The recovery kernel: the baseline conditional law of the packet given its
total gap.  It does not depend on the tilt. -/
def thetaRecoveryKernel (d : ℕ) {B₀ : ℝ} (hB₀ : 0 < B₀) : Kernel ℝ (Fin d → ℝ) :=
  haveI := isProbabilityMeasure_thetaJoint (d := d) hB₀
  (thetaJoint d B₀).condKernel

theorem isMarkovKernel_thetaRecoveryKernel {d : ℕ} {B₀ : ℝ} (hB₀ : 0 < B₀) :
    IsMarkovKernel (thetaRecoveryKernel d hB₀) := by
  haveI := isProbabilityMeasure_thetaJoint (d := d) hB₀
  exact Measure.instIsMarkovKernelCondKernel _

/-- **(FCAP.45)**  Baseline disintegration of the joint law along the total gap. -/
theorem thetaJoint_disintegration (d : ℕ) {B₀ : ℝ} (hB₀ : 0 < B₀) :
    (thetaMacroLaw d B₀) ⊗ₘ (thetaRecoveryKernel d hB₀) = thetaJoint d B₀ := by
  haveI := isProbabilityMeasure_thetaJoint (d := d) hB₀
  rw [← thetaJoint_fst d B₀, thetaRecoveryKernel]
  exact (thetaJoint d B₀).disintegrate _

theorem thetaJoint_eq_withDensity {d : ℕ} {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    thetaJoint d B
      = (thetaJoint d B₀).withDensity (fun p => thetaTiltDensity d B B₀ p.1) := by
  have hcomp : thetaTiltDensity d B B₀ ∘ thetaSumStat d
      = (fun p : ℝ × (Fin d → ℝ) => thetaTiltDensity d B B₀ p.1)
        ∘ (fun x : Fin d → ℝ => (thetaSumStat d x, x)) := rfl
  rw [thetaJoint, thetaJoint, thetaPacket_eq_withDensity hB hB₀, hcomp]
  exact GaloisForLFunctions.HTGeometry.map_withDensity_comp (thetaPacket d B₀)
    (measurable_thetaJointMap d)
    (g := fun p : ℝ × (Fin d → ℝ) => thetaTiltDensity d B B₀ p.1)
    ((measurable_thetaTiltDensity d B B₀).comp measurable_fst)

/-- **(FCAP.43)**  One tilt-independent Markov kernel disintegrates every member of the family
along the total gap. -/
theorem thetaMacro_compProd_eq_thetaJoint {d : ℕ} {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    (thetaMacroLaw d B) ⊗ₘ (thetaRecoveryKernel d hB₀) = thetaJoint d B := by
  haveI := isProbabilityMeasure_thetaJoint (d := d) hB₀
  haveI := isMarkovKernel_thetaRecoveryKernel (d := d) hB₀
  haveI : IsProbabilityMeasure (thetaMacroLaw d B₀) := by
    rw [← thetaJoint_fst d B₀]; infer_instance
  rw [thetaMacroLaw_eq_withDensity hB hB₀,
    ← GaloisForLFunctions.HTGeometry.compProd_withDensity_fst _ _
      (measurable_thetaTiltDensity d B B₀),
    thetaJoint_disintegration d hB₀, ← thetaJoint_eq_withDensity hB hB₀]

/-- **(FCAP.43)**  Exact sufficient recovery: the depth-`d` packet is the macro law pushed
through the tilt-independent recovery kernel. -/
theorem thetaPacket_eq_macro_recovery {d : ℕ} {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    ((thetaMacroLaw d B) ⊗ₘ (thetaRecoveryKernel d hB₀)).map Prod.snd = thetaPacket d B := by
  rw [thetaMacro_compProd_eq_thetaJoint hB hB₀, thetaJoint_snd d B]

/-! ## Conservation of information -/

/-- **(FCAP.44)**, relative entropy.  The macro law carries exactly `d` times the one-packet
relative entropy. -/
theorem klDiv_thetaMacroLaw {d : ℕ} {B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    klDiv (thetaMacroLaw d B) (thetaMacroLaw d C)
      = d * klDiv (thetaCuspLikelihoodProbabilityMeasure B)
        (thetaCuspLikelihoodProbabilityMeasure C) := by
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hC
  haveI := isProbabilityMeasure_thetaPacket (d := d) hB
  haveI := isProbabilityMeasure_thetaPacket (d := d) hC
  simp only [thetaMacroLaw]
  rw [← GaloisForLFunctions.HTGeometry.klDiv_map_eq_of_density_comp
      (measurable_thetaSumStat d) (measurable_thetaTiltDensity d B C)
      (thetaPacket_eq_withDensity hB hC),
    thetaPacket, thetaPacket, GaloisForLFunctions.HTGeometry.klDiv_pi,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **(FCAP.44)**, Hellinger affinity.  The macro law carries exactly the `d`-th power of the
one-packet affinity. -/
theorem bhattacharyya_thetaMacroLaw {d : ℕ} {B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    bhattacharyya (thetaMacroLaw d B) (thetaMacroLaw d C)
      = bhattacharyya (thetaCuspLikelihoodProbabilityMeasure B)
        (thetaCuspLikelihoodProbabilityMeasure C) ^ d := by
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hC
  haveI := isProbabilityMeasure_thetaPacket (d := d) hB
  haveI := isProbabilityMeasure_thetaPacket (d := d) hC
  simp only [thetaMacroLaw]
  rw [← bhattacharyya_map_eq_of_density_comp (measurable_thetaSumStat d)
      (measurable_thetaTiltDensity d B C) (thetaPacket_eq_withDensity hB hC),
    thetaPacket, thetaPacket, bhattacharyya_pi]

/-! ## Species exit at depth two -/

theorem thetaMacroLaw_two (B : ℝ) (hB : 0 < B) :
    thetaMacroLaw 2 B
      = thetaCuspLikelihoodProbabilityMeasure B ∗ thetaCuspLikelihoodProbabilityMeasure B := by
  haveI := thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB
  have hmp := measurePreserving_piFinTwo
    (fun _ : Fin 2 => thetaCuspLikelihoodProbabilityMeasure B)
  have hcomp : thetaSumStat 2
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) := by
    funext x
    simp [thetaSumStat, Fin.sum_univ_two, MeasurableEquiv.piFinTwo]
  rw [thetaMacroLaw, thetaPacket, hcomp,
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ).measurable,
    hmp.map_eq, Measure.conv]

/-- **Theorem 8.1, species exit.**  The depth-two macro law charges the gap `6`, which the
one-particle law does not charge.  Exact sufficient formation therefore leaves the one-particle
atomic-support species. -/
theorem thetaMacroLaw_two_singleton_six_ne_zero (B : ℝ) (hB : 0 < B) :
    thetaMacroLaw 2 B {6} ≠ 0 ∧ thetaCuspLikelihoodProbabilityMeasure B {6} = 0 := by
  refine ⟨?_, thetaCuspLikelihoodProbabilityMeasure_singleton_six B⟩
  rw [thetaMacroLaw_two B hB]
  exact thetaCuspLikelihoodProbabilityMeasure_selfConv_singleton_six_ne_zero B

/-- **Theorem 8.1.**  Exact sufficient macro formation for the theta cusp family, together with
the information conservation laws and the depth-two species exit. -/
theorem thetaSufficientMacroFormation_certificate (d : ℕ) {B B₀ : ℝ} (hB : 0 < B) (hB₀ : 0 < B₀) :
    ((thetaMacroLaw d B) ⊗ₘ (thetaRecoveryKernel d hB₀)).map Prod.snd = thetaPacket d B
      ∧ (thetaPacket d B).map (thetaSumStat d) = thetaMacroLaw d B
      ∧ klDiv (thetaMacroLaw d B) (thetaMacroLaw d B₀)
          = d * klDiv (thetaCuspLikelihoodProbabilityMeasure B)
            (thetaCuspLikelihoodProbabilityMeasure B₀)
      ∧ bhattacharyya (thetaMacroLaw d B) (thetaMacroLaw d B₀)
          = bhattacharyya (thetaCuspLikelihoodProbabilityMeasure B)
            (thetaCuspLikelihoodProbabilityMeasure B₀) ^ d
      ∧ thetaMacroLaw 2 B {6} ≠ 0
      ∧ thetaCuspLikelihoodProbabilityMeasure B {6} = 0 :=
  ⟨thetaPacket_eq_macro_recovery hB hB₀, rfl, klDiv_thetaMacroLaw hB hB₀,
    bhattacharyya_thetaMacroLaw hB hB₀,
    (thetaMacroLaw_two_singleton_six_ne_zero B hB).1,
    (thetaMacroLaw_two_singleton_six_ne_zero B hB).2⟩

end

end RHTower
