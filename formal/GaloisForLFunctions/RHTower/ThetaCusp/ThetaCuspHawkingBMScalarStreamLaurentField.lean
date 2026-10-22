import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamHarmonicField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamLaurentMaster

/-!
# The Laurent particular scalar–scalar response as a metric field

The explicit particular master field `r + A/r + B/r³` of the scalar–scalar harmonic master
equation, reconstructed through the Kodama–Ishibashi radial functions and dressed by the envelope
and a harmonic profile, is an actual metric field solving the sourced linearized Einstein equation
with the scalar–scalar harmonic source tensor in every component at every exterior point
(`ssLaurentMetricField_einstein`). At every Xi occurrence, either physical branch, and every
nonpositive real angular eigenvalue this needs no hypothesis beyond the profile being a harmonic
(`physical_ssLaurentMetricField_einstein`).
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
theorem ssLaurentMetricField_einstein (s μ a : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (hres : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) (Y : (Fin 2 → ℝ) → ℂ)
    (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = μ * Y z / (z 1 : ℂ) ^ (2 : ℕ) - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField s a
        (recF0R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recF1R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recF2R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recHR s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        Y) p.val) (-3) i j +
      harmonicSourceTensor μ (envelope (2 * s) a p.val) (p.val 3) (srcTT s μ (p.val 1)) (srcTR s μ (p.val 1))
        (srcRR s μ (p.val 1)) (srcT s μ (p.val 1)) (srcR s μ (p.val 1)) (srcTF s μ (p.val 1)) (srcL s μ (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 :=
  harmonicMetricField_einstein s μ a hs hμ (ssLaurentMaster_sourcedData s μ hs hμ hres)
    (ssLaurentMaster_contDiffOn s μ) (srcTT_contDiffOn _ _) (srcTR_contDiffOn _ _) (srcRR_contDiffOn _ _)
    (srcT_contDiffOn _ _) (srcR_contDiffOn _ _) (srcTF_contDiffOn _ _) (srcL_contDiffOn _ _) Y hY hYeig p i j

/-- At every Xi occurrence, physical branch and nonpositive real angular eigenvalue `−k²`, the
Laurent particular response is a sourced Einstein solution for every harmonic profile. -/
theorem physical_ssLaurentMetricField_einstein (q : XiZeroCopy) (branch : Bool) (k : ℝ) (a : ℂ)
    (Y : (Fin 2 → ℝ) → ℂ) (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = -(k : ℂ) ^ (2 : ℕ) * Y z / (z 1 : ℂ) ^ (2 : ℕ) - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    let s := D4BMModularCore.physicalRate q branch
    let μ : ℂ := -(k : ℂ) ^ (2 : ℕ)
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField s a
        (recF0R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recF1R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recF2R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        (recHR s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ) (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ))
        Y) p.val) (-3) i j +
      harmonicSourceTensor μ (envelope (2 * s) a p.val) (p.val 3) (srcTT s μ (p.val 1)) (srcTR s μ (p.val 1))
        (srcRR s μ (p.val 1)) (srcT s μ (p.val 1)) (srcR s μ (p.val 1)) (srcTF s μ (p.val 1)) (srcL s μ (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 := by
  intro s μ
  obtain ⟨hr, hi⟩ := physicalLaurentRate_bounds q branch
  have hs : s ≠ 0 := fun h => hi (congrArg Complex.im h)
  have hμ : (2 : ℂ) - μ ≠ 0 := by
    show (2 : ℂ) - (-(k : ℂ) ^ (2 : ℕ)) ≠ 0
    exact_mod_cast (show (2 : ℝ) - (-k ^ (2 : ℕ)) ≠ 0 by nlinarith [sq_nonneg k])
  have hres := laurentPole_ne_zero s hr hi (-k ^ (2 : ℕ))
  push_cast at hres
  exact ssLaurentMetricField_einstein s μ a hs hμ hres Y hY hYeig p i j

end
end RHTower.D4BMScalarStream
