import GaloisForLFunctions.HTGeometry.UniformThirdOrderJet
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
The literal logarithmic height at the source horizon.

The original source profile contains the factor
`(1 + sqrt (1 - z)) ^ (2s - w)`.  Reaching its source pole requires the
degree-two endpoint jet of its logarithmic height with a genuine cubic tail.
This file proves that exact real endpoint input without replacing the radial
coordinate by an asymptotic model.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section
set_option autoImplicit false

/-- The literal positive horizon height retained by the source profile. -/
def literalSourceHorizonHeight (z : ℝ) : ℝ := 1 + Real.sqrt (1 - z)

def literalSourceHorizonHeightFirst (z : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * (1 - z) ^ (-(1 / 2 : ℝ))

def literalSourceHorizonHeightSecond (z : ℝ) : ℝ :=
  -(1 / 4 : ℝ) * (1 - z) ^ (-(3 / 2 : ℝ))

/-- The first two derivatives of the actual positive horizon height. -/
theorem literalSourceHorizonHeight_derivatives {z : ℝ} (hz : z < 1) :
    HasDerivAt literalSourceHorizonHeight (literalSourceHorizonHeightFirst z) z ∧
      HasDerivAt literalSourceHorizonHeightFirst (literalSourceHorizonHeightSecond z) z := by
  have hpos : 0 < 1 - z := by linarith
  have hins : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    change HasDerivAt ((fun _ : ℝ => 1) - id) (-1) z
    simpa using (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)
  have hp0 := Real.hasDerivAt_rpow_const (x := 1 - z) (p := (1 / 2 : ℝ)) (Or.inl hpos.ne')
  have hp1 := Real.hasDerivAt_rpow_const (x := 1 - z) (p := (-1 / 2 : ℝ)) (Or.inl hpos.ne')
  have hd0 := hp0.comp z hins
  have hd1 := hp1.comp z hins
  constructor
  · have ht := (hasDerivAt_const z (1 : ℝ)).add hd0
    have he : literalSourceHorizonHeight =
        (fun x : ℝ => 1) + (fun x : ℝ => x ^ (1 / 2 : ℝ)) ∘ (fun x : ℝ => 1 - x) := by
      funext x
      simp [literalSourceHorizonHeight, Real.sqrt_eq_rpow, Function.comp_apply]
    rw [he]
    apply ht.congr_deriv
    dsimp [literalSourceHorizonHeightFirst]
    ring_nf
  · have ht := hd1.const_mul (-(1 / 2 : ℝ))
    have he : literalSourceHorizonHeightFirst = fun x : ℝ => -(1 / 2 : ℝ) *
        ((fun y : ℝ => y ^ (-1 / 2 : ℝ)) ∘ (fun y : ℝ => 1 - y)) x := by
      funext x
      simp only [literalSourceHorizonHeightFirst, Function.comp_apply]
      congr 2
      ring
    rw [he]
    apply ht.congr_deriv
    dsimp [literalSourceHorizonHeightSecond]
    ring_nf

/-- The literal logarithmic height whose complex exponential is the source power. -/
def literalSourceHorizonLog (z : ℝ) : ℝ := Real.log (literalSourceHorizonHeight z)

def literalSourceHorizonLogFirst (z : ℝ) : ℝ :=
  literalSourceHorizonHeightFirst z / literalSourceHorizonHeight z

def literalSourceHorizonLogSecond (z : ℝ) : ℝ :=
  (literalSourceHorizonHeightSecond z * literalSourceHorizonHeight z -
    literalSourceHorizonHeightFirst z * literalSourceHorizonHeightFirst z) /
      literalSourceHorizonHeight z ^ 2

/-- The exact first two derivatives of the source logarithmic height. -/
theorem literalSourceHorizonLog_derivatives {z : ℝ} (hz : z < 1) :
    HasDerivAt literalSourceHorizonLog (literalSourceHorizonLogFirst z) z ∧
      HasDerivAt literalSourceHorizonLogFirst (literalSourceHorizonLogSecond z) z := by
  have hh : literalSourceHorizonHeight z ≠ 0 := by
    dsimp [literalSourceHorizonHeight]
    positivity
  have hd := literalSourceHorizonHeight_derivatives hz
  constructor
  · have ht := (Real.hasDerivAt_log hh).comp z hd.1
    change HasDerivAt (Real.log ∘ literalSourceHorizonHeight) (literalSourceHorizonLogFirst z) z
    simpa only [literalSourceHorizonLogFirst, div_eq_mul_inv, mul_comm] using ht
  · have hquot := hd.2.div hd.1 hh
    change HasDerivAt (literalSourceHorizonHeightFirst / literalSourceHorizonHeight)
      (literalSourceHorizonLogSecond z) z
    simpa only [literalSourceHorizonLogSecond] using hquot

/-- The source logarithmic height has the exact endpoint coefficients needed by
the cubic source-pole subtraction. -/
theorem literalSourceHorizonLog_zero_jets :
    literalSourceHorizonLog 0 = Real.log 2 ∧
      literalSourceHorizonLogFirst 0 = -(1 / 4 : ℝ) ∧
        literalSourceHorizonLogSecond 0 / 2 = -(3 / 32 : ℝ) := by
  constructor
  · norm_num [literalSourceHorizonLog, literalSourceHorizonHeight]
  constructor <;>
    norm_num [literalSourceHorizonLogFirst, literalSourceHorizonLogSecond,
      literalSourceHorizonHeightFirst, literalSourceHorizonHeightSecond,
      literalSourceHorizonHeight]

/-- On the physical half-cutoff, the literal source logarithmic height is smooth
through the third derivative. -/
theorem literalSourceHorizonLog_contDiffOn :
    ContDiffOn ℝ 3 literalSourceHorizonLog (Icc (0 : ℝ) (1 / 2)) := by
  have hlin : ContDiff ℝ 3 (fun z : ℝ => 1 - z) := by fun_prop
  have hpow : ContDiffOn ℝ 3 (fun y : ℝ => y ^ (1 / 2 : ℝ)) (Icc (1 / 2) 1) := by
    intro y hy
    exact (Real.contDiffAt_rpow_const (n := 3) (p := (1 / 2 : ℝ))
      (Or.inl (by linarith [hy.1]))).contDiffWithinAt
  have hmap : MapsTo (fun z : ℝ => 1 - z) (Icc (0 : ℝ) (1 / 2)) (Icc (1 / 2) 1) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hroot : ContDiffOn ℝ 3 (fun z : ℝ => (1 - z) ^ (1 / 2 : ℝ))
      (Icc (0 : ℝ) (1 / 2)) := by
    change ContDiffOn ℝ 3 ((fun y : ℝ => y ^ (1 / 2 : ℝ)) ∘ (fun z : ℝ => 1 - z))
      (Icc (0 : ℝ) (1 / 2))
    exact hpow.comp hlin.contDiffOn hmap
  have hroot' : ContDiffOn ℝ 3 (fun z : ℝ => Real.sqrt (1 - z))
      (Icc (0 : ℝ) (1 / 2)) := by
    apply hroot.congr
    intro z hz
    rw [Real.sqrt_eq_rpow]
  have hplus : ContDiffOn ℝ 3 (fun z : ℝ => 1 + Real.sqrt (1 - z))
      (Icc (0 : ℝ) (1 / 2)) := by
    fun_prop
  have hlog := hplus.log (fun z hz => by positivity)
  change ContDiffOn ℝ 3 (fun z : ℝ => Real.log (1 + Real.sqrt (1 - z)))
    (Icc (0 : ℝ) (1 / 2))
  exact hlog

theorem literalSourceHorizonLog_complex_contDiffOn :
    ContDiffOn ℝ 3 (fun z : ℝ => (literalSourceHorizonLog z : ℂ))
      (Icc (0 : ℝ) (1 / 2)) := by
  have h := (Complex.ofRealCLM.contDiff.contDiffOn).comp literalSourceHorizonLog_contDiffOn
    (mapsTo_univ _ _)
  change ContDiffOn ℝ 3 (Complex.ofReal ∘ literalSourceHorizonLog)
    (Icc (0 : ℝ) (1 / 2)) at h
  exact h

/-- The literal source logarithmic height has a parameter-uniform degree-two
endpoint jet and a genuine cubic tail. The coefficient fields remain the actual
within-derivatives so this result can be composed with the frequency-dependent
complex exponential without changing its source normalization. -/
theorem exists_literalSourceHorizonLog_uniformJet3 (S : Set ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasUniformJet3 S (1 / 2)
        (fun _ z => (literalSourceHorizonLog z : ℂ))
        (fun _ => (literalSourceHorizonLog 0 : ℂ))
        (fun _ => derivWithin (fun z : ℝ => (literalSourceHorizonLog z : ℂ))
          (Icc 0 (1 / 2)) 0)
        (fun _ => iteratedDerivWithin 2 (fun z : ℝ => (literalSourceHorizonLog z : ℂ))
          (Icc 0 (1 / 2)) 0 / 2) C := by
  let I : Set ℝ := Icc (0 : ℝ) (1 / 2)
  have hunique : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by norm_num)
  have hcont := literalSourceHorizonLog_complex_contDiffOn.continuousOn_iteratedDerivWithin
    (m := 3) (by norm_num) hunique
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0 / 2, div_nonneg (le_max_right _ _) (by norm_num), ?_⟩
  exact hasUniformJet3_of_deriv3_bound (S := S) (b := 1 / 2) (by norm_num)
    (fun _ _ => literalSourceHorizonLog_complex_contDiffOn)
    (fun _ _ z hz => (hC z hz).trans (le_max_left _ _))

end
end GaloisForLFunctions.HTGeometry
