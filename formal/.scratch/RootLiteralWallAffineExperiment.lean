import GaloisForLFunctions.RHTower.SuzukiGammaCompletedWallMixedCauchyKernel

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

def rootAnchoredAtomGram (p : ℝ) : ℝ :=
  2 * (1 - Real.exp (-|p| / 2))

def rootSecantGram (q : ℝ) : ℝ :=
  2 * (1 - Real.exp (-|q| / 2))

def rootMidpointAffineQuadratic (p λ : ℝ) : ℝ :=
  rootAnchoredAtomGram p -
    2 * λ * suzukiCauchyAnchoredSecantGram p (p / 2) +
      λ ^ 2 * rootSecantGram (p / 2)

def rootMidpointCoefficient (p : ℝ) : ℝ :=
  (1 + Real.exp (-p / 4)) / 2

def rootMidpointAffineNodes (p : ℝ) : Fin 3 → ℝ :=
  Fin.cases 0 (Fin.cases (-p / 2) (fun _ => -p))

def rootMidpointAffineCoefficients (λ : ℝ) : Fin 3 → ℝ :=
  Fin.cases 1 (Fin.cases (-λ) (fun _ => λ - 1))

def rootMidpointAffineCauchyEnergy (p λ : ℝ) : ℝ :=
  realKernelPacketEnergy cauchyHalfExponentialKernel
    (rootMidpointAffineNodes p) (rootMidpointAffineCoefficients λ)

theorem root_mixed_half_eq {p : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredSecantGram p (p / 2) =
      1 - Real.exp (-p / 2) := by
  rw [suzukiCauchyAnchoredSecantGram]
  have hhalf : 0 ≤ p / 2 := by linarith
  have hzero : 0 ≤ p - p / 2 := by linarith
  rw [abs_of_nonneg hhalf]
  have htwo : |2 * (p / 2)| = p := by
    rw [show 2 * (p / 2) = p by ring, abs_of_nonneg hp]
  rw [htwo]
  have hsub : |p - p / 2| = p / 2 := by
    rw [show p - p / 2 = p / 2 by ring, abs_of_nonneg hhalf]
  rw [hsub]
  have hlast : |p - 2 * (p / 2)| = 0 := by ring_nf
  rw [hlast]
  ring

theorem root_atom_eq {p : ℝ} (hp : 0 ≤ p) :
    rootAnchoredAtomGram p = 2 * (1 - Real.exp (-p / 2)) := by
  rw [rootAnchoredAtomGram, abs_of_nonneg hp]

theorem root_secant_half_eq {p : ℝ} (hp : 0 ≤ p) :
    rootSecantGram (p / 2) = 2 * (1 - Real.exp (-p / 4)) := by
  rw [rootSecantGram, abs_of_nonneg (by linarith : 0 ≤ p / 2)]
  congr 3
  ring

theorem root_midpoint_affine_complete_square {p λ : ℝ} (hp : 0 ≤ p) :
    rootMidpointAffineQuadratic p λ =
      rootMidpointAffineQuadratic p (rootMidpointCoefficient p) +
        rootSecantGram (p / 2) * (λ - rootMidpointCoefficient p) ^ 2 := by
  rw [rootMidpointAffineQuadratic, rootMidpointCoefficient,
    root_atom_eq hp, root_secant_half_eq hp, root_mixed_half_eq hp]
  ring

theorem root_midpoint_affine_canonical_eq {p : ℝ} (hp : 0 ≤ p) :
    rootMidpointAffineQuadratic p (rootMidpointCoefficient p) =
      (1 - Real.exp (-p / 2)) * (3 - Real.exp (-p / 4)) / 2 := by
  rw [rootMidpointAffineQuadratic, rootMidpointCoefficient,
    root_atom_eq hp, root_secant_half_eq hp, root_mixed_half_eq hp]
  ring

theorem root_secant_nonneg {q : ℝ} : 0 ≤ rootSecantGram q := by
  rw [rootSecantGram]
  positivity

theorem root_midpoint_affine_cauchyEnergy_eq_quadratic
    {p λ : ℝ} (hp : 0 ≤ p) :
    rootMidpointAffineCauchyEnergy p λ = rootMidpointAffineQuadratic p λ := by
  rw [rootMidpointAffineCauchyEnergy, realKernelPacketEnergy]
  simp only [Fin.sum_univ_succ, rootMidpointAffineNodes,
    rootMidpointAffineCoefficients, Fin.cases_zero, Fin.cases_succ]
  have hhalf : cauchyHalfExponentialKernel (p / 2) =
      Real.exp (-p / 4) := by
    rw [cauchyHalfExponentialKernel, abs_of_nonneg (by linarith : 0 ≤ p / 2)]
    congr 1
    ring
  have hfull : cauchyHalfExponentialKernel p =
      Real.exp (-p / 2) := by
    rw [cauchyHalfExponentialKernel, abs_of_nonneg hp]
  have hhalfneg : cauchyHalfExponentialKernel (-p / 2) =
      Real.exp (-p / 4) := by
    rw [show -p / 2 = -(p / 2) by ring, cauchyHalfExponentialKernel,
      abs_neg, abs_of_nonneg (by linarith : 0 ≤ p / 2)]
    congr 1
    ring
  have hfullneg : cauchyHalfExponentialKernel (-p) =
      Real.exp (-p / 2) := by
    rw [cauchyHalfExponentialKernel, abs_neg, abs_of_nonneg hp]
  rw [show -p / 2 - 0 = -p / 2 by ring,
    show -p - 0 = -p by ring,
    show 0 - -p / 2 = p / 2 by ring,
    show -p - -p / 2 = -p / 2 by ring,
    show 0 - -p = p by ring,
    show -p / 2 - -p = p / 2 by ring,
    hhalf, hfull, hhalfneg, hfullneg,
    rootMidpointAffineQuadratic, root_atom_eq hp,
    root_secant_half_eq hp, root_mixed_half_eq hp]
  ring

theorem root_midpoint_affine_half_atom_lower
    {p λ : ℝ} (hp : 0 < p) :
    rootAnchoredAtomGram p / 2 ≤ rootMidpointAffineQuadratic p λ := by
  rw [root_midpoint_affine_complete_square hp.le]
  have hsq : 0 ≤ rootSecantGram (p / 2) *
      (λ - rootMidpointCoefficient p) ^ 2 :=
    mul_nonneg root_secant_nonneg (sq_nonneg _)
  rw [root_midpoint_affine_canonical_eq hp.le,
    root_atom_eq hp.le]
  have hExp : Real.exp (-p / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

end

end GaloisForLFunctions.RHTower
