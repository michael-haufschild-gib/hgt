import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamHarmonicField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorLaurentMaster

/-!
# The Laurent particular vector–vector response as a metric field

The explicit decaying particular master field `A/r + B/r³` of the vector–vector harmonic master
equation, reconstructed through the Kodama–Ishibashi radial functions and dressed by the envelope
and a harmonic profile, is an actual metric field solving the sourced linearized Einstein equation
with the vector–vector harmonic source tensor in every component at every exterior point
(`vvLaurentMetricField_einstein`). At every Xi occurrence, either physical branch, and every
nonpositive real angular eigenvalue this needs no hypothesis beyond the profile being a harmonic
(`physical_vvLaurentMetricField_einstein`).
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet GaloisForLFunctions.HTGeometry.ScalarTwoJet
  GaloisForLFunctions.HTGeometry.TwistedRadial
open RHTower.D4BMFundamentalScalarMetric (envelope)
open RHTower.D4BMMetricReconstruction (angularPoint ofMetricField)
open Set
open scoped ContDiff
noncomputable section

/-- The Laurent particular response, reconstructed and dressed, solves the sourced Einstein equation. -/
theorem vvLaurentMetricField_einstein (s μ a : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (hres : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) (Y : (Fin 2 → ℝ) → ℂ)
    (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = μ * Y z / (z 1 : ℂ) ^ 2 - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField s a
        (recF0R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recF1R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recF2R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recHR s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        Y) p.val) (-3) i j +
      harmonicSourceTensor μ (envelope (2 * s) a p.val) (p.val 3) (vvSrcTT s μ (p.val 1)) (vvSrcTR s μ (p.val 1))
        (vvSrcRR s μ (p.val 1)) (vvSrcT s μ (p.val 1)) (vvSrcR s μ (p.val 1)) (vvSrcTF s μ (p.val 1)) (vvSrcL s μ (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 :=
  harmonicMetricField_einstein s μ a hs hμ (vvLaurentMaster_sourcedData s μ hs hμ hres)
    (vvLaurentMaster_contDiffOn s μ) (vvSrcTT_contDiffOn _ _) (vvSrcTR_contDiffOn _ _) (vvSrcRR_contDiffOn _ _)
    (vvSrcT_contDiffOn _ _) (vvSrcR_contDiffOn _ _) (vvSrcTF_contDiffOn _ _) (vvSrcL_contDiffOn _ _) Y hY hYeig p i j

/-- At every Xi occurrence, physical branch and nonpositive real angular eigenvalue `−k²`, the
Laurent particular response is a sourced Einstein solution for every harmonic profile. -/
theorem physical_vvLaurentMetricField_einstein (q : XiZeroCopy) (branch : Bool) (k : ℝ) (a : ℂ)
    (Y : (Fin 2 → ℝ) → ℂ) (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = -(k : ℂ) ^ 2 * Y z / (z 1 : ℂ) ^ 2 - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    let s := D4BMModularCore.physicalRate q branch
    let μ : ℂ := -(k : ℂ) ^ 2
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField s a
        (recF0R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recF1R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recF2R s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        (recHR s μ (vvLaurentMaster s μ) (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ))
        Y) p.val) (-3) i j +
      harmonicSourceTensor μ (envelope (2 * s) a p.val) (p.val 3) (vvSrcTT s μ (p.val 1)) (vvSrcTR s μ (p.val 1))
        (vvSrcRR s μ (p.val 1)) (vvSrcT s μ (p.val 1)) (vvSrcR s μ (p.val 1)) (vvSrcTF s μ (p.val 1)) (vvSrcL s μ (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 := by
  intro s μ
  obtain ⟨hr, hi⟩ := physicalLaurentRate_bounds q branch
  have hs : s ≠ 0 := fun h => hi (congrArg Complex.im h)
  have hμ : (2 : ℂ) - μ ≠ 0 := by
    show (2 : ℂ) - (-(k : ℂ) ^ 2) ≠ 0
    exact_mod_cast (show (2 : ℝ) - (-k ^ 2) ≠ 0 by nlinarith [sq_nonneg k])
  have hres := laurentPole_ne_zero s hr hi (-k ^ 2)
  push_cast at hres
  exact vvLaurentMetricField_einstein s μ a hs hμ hres Y hY hYeig p i j

end
end RHTower.D4BMScalarStream
