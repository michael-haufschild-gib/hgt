import GaloisForLFunctions.RHTower.SlepianKernelScaledFubini
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Simplicity of regular even prolate separation modes

Compact-interior ODE uniqueness makes each regular even separation line one-dimensional.  This
module lifts that pointwise statement through the canonical band representatives: inside every
live even Slepian band eigenspace, a fixed prolate separation value has multiplicity at most one.
-/

noncomputable section

namespace RHTower

/-- A regular even separation value determines one live band eigenvalue and one entire exterior
eigenline.  Aperture ODE uniqueness gives proportionality on `[-1,1]`; the two global band
eigenrelations then propagate that proportionality to every real point. -/
theorem eq_const_mul_of_same_even_joint_prolate_eigen
    {c lamPhi lamPsi chi : ℝ} {Phi Psi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (hPhiNe : Phi ≠ 0) (hPsiNe : Psi ≠ 0)
    (hPhiEven : Function.Even Phi) (hPsiEven : Function.Even Psi)
    (hlamPhi : lamPhi ≠ 0) (hlamPsi : lamPsi ≠ 0)
    (hPhiBand : ∀ x : ℝ, bandTransform c Phi x = lamPhi * Phi x)
    (hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lamPsi * Psi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x) :
    lamPhi = lamPsi ∧ ∃ mu : ℝ, Phi = fun x => mu * Psi x := by
  have hlam : lamPhi = lamPsi := bandEigenvalue_eq_of_same_even_prolate_eigen
    hPhiSmooth hPsiSmooth hPhiNe hPsiNe hPhiEven hPsiEven hlamPhi hlamPsi
    hPhiBand hPsiBand hPhiProlate hPsiProlate
  obtain ⟨mu, hEq⟩ := eqOn_Icc_const_mul_of_even_joint_prolate_eigen
    hPhiSmooth hPsiSmooth hPsiNe hPhiEven hPsiEven hlamPsi hPsiBand
    hPhiProlate hPsiProlate
  have hBandProp : ∀ x : ℝ, bandTransform c Phi x = mu * bandTransform c Psi x := by
    intro x
    rw [bandTransform, bandTransform, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
    change sincKernelSmooth c x y * Phi y =
      mu * (sincKernelSmooth c x y * Psi y)
    rw [hEq hyIcc]
    ring
  refine ⟨hlam, mu, funext fun x => ?_⟩
  apply mul_left_cancel₀ hlamPhi
  calc
    lamPhi * Phi x = bandTransform c Phi x := (hPhiBand x).symm
    _ = mu * bandTransform c Psi x := hBandProp x
    _ = mu * (lamPsi * Psi x) := by rw [hPsiBand x]
    _ = lamPhi * (mu * Psi x) := by rw [hlam]; ring

/-- Eigenvectors of the even prolate action with the same separation value are proportional. -/
theorem prolateOnEvenEigenspace_eigenvectors_proportional
    {c lam chi : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {f g : evenBandEigenspace c lam}
    (hf : prolateOnEvenEigenspace hc hlam f = chi • f)
    (hg : prolateOnEvenEigenspace hc hlam g = chi • g)
    (hg0 : g ≠ 0) :
    ∃ mu : ℝ, f = mu • g := by
  let bf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨f.1, f.2.1⟩
  let bg : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨g.1, g.2.1⟩
  let Phi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam bf
  let Psi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam bg
  have hPf : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bf = chi • bf := by
    apply Subtype.ext
    exact congrArg (fun w : evenBandEigenspace c lam => w.1) hf
  have hPg : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bg = chi • bg := by
    apply Subtype.ext
    exact congrArg (fun w : evenBandEigenspace c lam => w.1) hg
  have hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x := by
    have hrep := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hPf
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (chi • bf) x =
        chi * GaloisForLFunctions.RHTower.eigenRep c lam bf x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam chi bf x
    rw [hsmul] at hx
    exact hx
  have hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x := by
    have hrep := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hPg
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (chi • bg) x =
        chi * GaloisForLFunctions.RHTower.eigenRep c lam bg x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam chi bg x
    rw [hsmul] at hx
    exact hx
  have hPsiNe : Psi ≠ 0 := by
    intro hzero
    have hclass := GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bg
    have hclassZero : GaloisForLFunctions.RHTower.bandClass Psi
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bg) = 0 := by
      have hstep := GaloisForLFunctions.RHTower.bandClass_congr
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bg)
        continuous_const hzero
      rw [hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    apply hg0
    apply Subtype.ext
    rw [← hclass]
    exact hclassZero
  obtain ⟨mu, hEq⟩ := eqOn_Icc_const_mul_of_even_joint_prolate_eigen
    (GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam bf)
    (GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam bg)
    hPsiNe f.2.2 g.2.2 hlam
    (GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam bg)
    hPhiProlate hPsiProlate
  have hscaled : Continuous (fun x : ℝ => mu * Psi x) :=
    continuous_const.mul (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bg)
  have hclassEq : GaloisForLFunctions.RHTower.bandClass Phi
      (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf) =
      GaloisForLFunctions.RHTower.bandClass (fun x => mu * Psi x) hscaled :=
    bandClass_eq_of_eqOn_Icc
      (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf) hscaled hEq
  have hval : f.1 = mu • g.1 := by
    calc
      f.1 = GaloisForLFunctions.RHTower.bandClass Phi
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf) :=
        (GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bf).symm
      _ = GaloisForLFunctions.RHTower.bandClass (fun x => mu * Psi x) hscaled := hclassEq
      _ = mu • GaloisForLFunctions.RHTower.bandClass Psi
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bg) :=
        GaloisForLFunctions.RHTower.bandClass_smul
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bg) mu hscaled
      _ = mu • g.1 := by
        rw [GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bg]
  exact ⟨mu, Subtype.ext hval⟩

/-- Every separation eigenspace of the prolate action inside a fixed live even band eigenspace
has dimension at most one. -/
theorem finrank_prolateOnEvenEigenspace_eigenspace_le_one
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) (chi : ℝ) :
    Module.finrank ℝ
      (Module.End.eigenspace (prolateOnEvenEigenspace hc hlam) chi) ≤ 1 := by
  classical
  let E := Module.End.eigenspace (prolateOnEvenEigenspace hc hlam) chi
  by_cases hne : ∃ g : E, g ≠ 0
  · obtain ⟨g, hg0⟩ := hne
    apply finrank_le_one g
    intro f
    have hfEig : prolateOnEvenEigenspace hc hlam f.1 = chi • f.1 :=
      Module.End.mem_eigenspace_iff.mp f.2
    have hgEig : prolateOnEvenEigenspace hc hlam g.1 = chi • g.1 :=
      Module.End.mem_eigenspace_iff.mp g.2
    have hg0' : (g.1 : evenBandEigenspace c lam) ≠ 0 := by
      intro h
      exact hg0 (Subtype.ext h)
    obtain ⟨mu, hfg⟩ :=
      prolateOnEvenEigenspace_eigenvectors_proportional hc hlam hfEig hgEig hg0'
    exact ⟨mu, Subtype.ext hfg.symm⟩
  · push Not at hne
    apply finrank_le_one (0 : E)
    intro f
    refine ⟨0, ?_⟩
    simp [hne f]

end RHTower

end
