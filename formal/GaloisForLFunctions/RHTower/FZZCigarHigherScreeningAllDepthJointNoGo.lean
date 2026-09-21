import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningOrderedSourceNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthAllDepthJointHermitianNoGo

/-!
# FZZ-P higher-screening joint all-depth orientation no-go

The complete restored cleared higher two-puncture screening source is real and
reflection-symmetric. This leaf applies the all-depth joint Hermitian law to
that literal source. Hence no joint all-depth summation of its two screening
depths can generate FZZ-P orientation.

Proof-chain role:
`literal cleared higher screening source -> joint all-depth Ward current ->
oriented source term -> FZZ-P`. The joint all-depth branch is closed. The
remaining source burden is now exact: derive a physical ordered/non-joint
summation or an independently non-Hermitian phase-frame/full-Ward coupling.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The complete restored cleared source sampled at two natural screening
depths. -/
def fzzScreeningHigherClearedAllDepthJointKernel
    (parameter : ℕ → ℝ) (i j : ℕ) : ℂ :=
  (fzzScreeningHigherClearedSource (parameter i) (parameter j) : ℂ)

/-- The literal cleared higher-screening kernel is Hermitian at every pair of
screening depths. -/
theorem fzzScreeningHigherClearedAllDepthJointKernel_depthHermitian
    (parameter : ℕ → ℝ) (i j : ℕ) :
    fzzScreeningHigherClearedAllDepthJointKernel parameter i j =
      star (fzzScreeningHigherClearedAllDepthJointKernel parameter j i) := by
  unfold fzzScreeningHigherClearedAllDepthJointKernel
  rw [fzzScreeningHigherClearedSource_symm]
  simp

/-- No joint all-depth accumulation of the complete restored cleared
higher-screening source has FZZ-P orientation. -/
theorem fzzRadialCouplingAllDepthJointHigherClearedScreening_im_eq_zero
    (u parameter : ℕ → ℝ) (v p : ℝ) :
    (fzzRadialCouplingAllDepthJointComplexKernel u
      (fzzScreeningHigherClearedAllDepthJointKernel parameter) v p).im = 0 := by
  apply fzzRadialCouplingAllDepthJointComplexKernel_im_eq_zero_of_depthHermitian
    u (fzzScreeningHigherClearedAllDepthJointKernel parameter) v p
  exact fzzScreeningHigherClearedAllDepthJointKernel_depthHermitian parameter

/-- **All-depth higher-screening FZZ-P route kill.** No natural screening
depth profile and no joint all-depth source accumulation of the literal
cleared higher source yields a nonzero oriented Ward contribution. -/
theorem not_exists_fzzRadialCouplingAllDepthJointHigherClearedScreening_im_ne_zero :
    ¬ ∃ (u parameter : ℕ → ℝ) (v p : ℝ),
      (fzzRadialCouplingAllDepthJointComplexKernel u
        (fzzScreeningHigherClearedAllDepthJointKernel parameter) v p).im ≠ 0 := by
  rintro ⟨u, parameter, v, p, hnonzero⟩
  exact hnonzero
    (fzzRadialCouplingAllDepthJointHigherClearedScreening_im_eq_zero u parameter v p)

end

end GaloisForLFunctions.RHTower
