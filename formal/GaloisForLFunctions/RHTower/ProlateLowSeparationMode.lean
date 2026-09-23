import GaloisForLFunctions.RHTower.ProlateBandOperatorInjective
import GaloisForLFunctions.RHTower.ProlateGaussianTrialPositive
import GaloisForLFunctions.RHTower.ProlateEvenEigenspaceQuadratic
import GaloisForLFunctions.RHTower.ProlateRadialODEBridge

/-!
# A prolate mode with separation ratio below one half

Every large bandwidth carries an even joint band/prolate eigenfunction whose radial separation
ratio is below `1/2`, so that its exterior turning point lies strictly inside the aperture.

The proof is variational.  The centred Gaussian has prolate Rayleigh quotient strictly above
`-(c²/2)`; its band class decomposes over the eigenspaces of the compact symmetric band operator;
the operator is injective, so the eigenvalue `0` contributes nothing; every component of an even
profile is even; and the prolate action is symmetric, so the Gaussian's Rayleigh value is the sum of
the components' Rayleigh values.  If every mode had separation ratio above `1/2`, each summand would
be at most `-(c²/2)` times the component's squared norm, and the total would contradict the
Gaussian estimate.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- **A high prolate eigenvalue exists, at whatever threshold the Gaussian trial reaches.**  If the
centred Gaussian's prolate Rayleigh numerator exceeds `-K` times its squared norm, then some even
joint band/prolate eigenfunction has prolate eigenvalue above `-K`.

The proof is variational.  The Gaussian's band class decomposes over the eigenspaces of the compact
symmetric band operator; the operator is injective, so the eigenvalue `0` contributes nothing; every
component of an even profile is even; and the prolate action is symmetric, so the Gaussian's
Rayleigh value is the sum of the components' Rayleigh values.  If every mode had eigenvalue at most
`-K`, each summand would be at most `-K` times the component's squared norm, and the total would
contradict the Gaussian estimate. -/
theorem exists_even_joint_prolate_eigen_gt_of_rayleigh_gt {c K : ℝ} (hc0 : 0 < c)
    (hgauss : -K * (∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      -K < eta := by
  by_contra hcon
  push Not at hcon
  -- the Gaussian test vector
  set g : ℝ → ℝ := gaussianTrial c with hg
  have hgc : Continuous g := continuous_gaussianTrial c
  have hgeven : Function.Even g := even_gaussianTrial c
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_gaussianTrial c
  have hgd1 : Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hgsm).1
  have hgd2 : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).1
  have hgd3 : Continuous (deriv (deriv g)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hgsm).2).2).continuous
  have hLgc : Continuous (prolateSLAction c g) :=
    (GaloisForLFunctions.RHTower.contDiff_prolateSLAction hgsm).continuous
  set v := GaloisForLFunctions.RHTower.bandClass g hgc with hv
  set Lv := GaloisForLFunctions.RHTower.bandClass (prolateSLAction c g) hLgc with hLv
  -- the per-eigenvalue estimate
  have hstep : ∀ μ : ℝ,
      (inner ℝ Lv (bandComponent c v μ) : ℝ)
        ≤ -K * (inner ℝ v (bandComponent c v μ) : ℝ) := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      rw [bandComponent_zero_eq_zero hc0 v]
      simp
    · set u := bandComponent c v μ with hu
      have humem : u ∈ evenBandEigenspace c μ :=
        bandComponent_mem_evenBandEigenspace hgc hgeven hμ
      set bu : evenBandEigenspace c μ := ⟨u, humem⟩ with hbu
      set bf : GaloisForLFunctions.RHTower.bandEigenspace c μ := ⟨u, humem.1⟩ with hbf
      set Phi := GaloisForLFunctions.RHTower.eigenRep c μ bf with hPhi
      have hPhic : Continuous Phi := GaloisForLFunctions.RHTower.continuous_eigenRep c μ bf
      have hPhism : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi :=
        GaloisForLFunctions.RHTower.contDiff_eigenRep hc0 hμ bf
      have hPhiclass : GaloisForLFunctions.RHTower.bandClass Phi hPhic = u :=
        GaloisForLFunctions.RHTower.bandClass_eigenRep hμ bf
      have hLPhic : Continuous (prolateSLAction c Phi) :=
        (GaloisForLFunctions.RHTower.contDiff_prolateSLAction hPhism).continuous
      -- the prolate action moves across the pairing
      have hsymm := prolateSLAction_band_symmetric hgd1 hgd2 hgd3
        (GaloisForLFunctions.RHTower.differentiable_eigenRep hc0 hμ bf)
        (GaloisForLFunctions.RHTower.differentiable_deriv_eigenRep hc0 hμ bf)
        (GaloisForLFunctions.RHTower.continuous_deriv2_eigenRep hc0 hμ bf) c
      have hmove : (inner ℝ Lv u : ℝ)
          = (inner ℝ v (GaloisForLFunctions.RHTower.bandClass
              (prolateSLAction c Phi) hLPhic) : ℝ) := by
        rw [hLv, ← hPhiclass, GaloisForLFunctions.RHTower.inner_bandClass_eq,
          hv, GaloisForLFunctions.RHTower.inner_bandClass_eq]
        rw [show (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * Phi x)
            = ∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c g x from
          intervalIntegral.integral_congr fun x _ => mul_comm _ _]
        exact hsymm
      -- the prolate image lies in the eigenspace
      have hTmem : GaloisForLFunctions.RHTower.bandClass (prolateSLAction c Phi) hLPhic
          ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ :=
        GaloisForLFunctions.RHTower.prolate_bandClass_mem hc0 hμ bf
      have hproj : (inner ℝ v (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ)
          = (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ) :=
        inner_eq_inner_bandComponent c v _ hTmem
      -- the quadratic form is at most `-(c²/2)` times the squared norm
      have hquad : (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ) ≤ -K * ‖u‖ ^ (2 : ℕ) := by
        by_contra hgt
        push Not at hgt
        have hform : (inner ℝ (prolateOnEvenEigenspace hc0 hμ bu) bu : ℝ)
            = (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
              (prolateSLAction c Phi) hLPhic) : ℝ) := by
          have hval : ((prolateOnEvenEigenspace hc0 hμ bu : evenBandEigenspace c μ) :
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
              = GaloisForLFunctions.RHTower.bandClass (prolateSLAction c Phi) hLPhic := rfl
          rw [show (inner ℝ (prolateOnEvenEigenspace hc0 hμ bu) bu : ℝ)
              = (inner ℝ ((prolateOnEvenEigenspace hc0 hμ bu : evenBandEigenspace c μ) :
                  GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
                ((bu : evenBandEigenspace c μ) :
                  GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ) from rfl, hval]
          exact real_inner_comm _ _
        have hnorm : ‖bu‖ = ‖u‖ := rfl
        have hlt : -K * ‖bu‖ ^ (2 : ℕ)
            < (inner ℝ (prolateOnEvenEigenspace hc0 hμ bu) bu : ℝ) := by
          rw [hnorm, hform]
          exact hgt
        obtain ⟨eta, Phi', heta, hsm, hne, heven, hband, hprolate⟩ :=
          exists_joint_even_prolate_eigen_gt hc0 hμ hlt
        exact absurd heta (not_lt.mpr (hcon μ eta Phi' hμ hsm hne heven hband hprolate))
      have hselfinner : (inner ℝ v u : ℝ) = ‖u‖ ^ (2 : ℕ) := inner_self_bandComponent c v μ
      rw [hmove, hproj, hselfinner]
      exact hquad
  -- sum the estimate
  have hsum1 : HasSum (fun μ : ℝ => (inner ℝ Lv (bandComponent c v μ) : ℝ))
      (inner ℝ Lv v : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ Lv) (hasSum_bandComponent c v)
  have hsum2 : HasSum (fun μ : ℝ => -K * (inner ℝ v (bandComponent c v μ) : ℝ))
      (-K * (inner ℝ v v : ℝ)) :=
    HasSum.mul_left _ (ContinuousLinearMap.hasSum (innerSL ℝ v) (hasSum_bandComponent c v))
  have hle : (inner ℝ Lv v : ℝ) ≤ -K * (inner ℝ v v : ℝ) :=
    hasSum_le hstep hsum1 hsum2
  -- but the Gaussian says the opposite
  rw [hLv, hv, GaloisForLFunctions.RHTower.inner_bandClass_eq,
    GaloisForLFunctions.RHTower.inner_bandClass_eq] at hle
  rw [show (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x)
      = ∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x from rfl,
    show (∫ x in (-1 : ℝ)..1, g x * g x)
      = ∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x from rfl] at hle
  linarith [hgauss, hle]

/-- **A low separation mode exists.**  At every bandwidth `c ≥ 400` some even joint band/prolate
eigenfunction has radial separation ratio strictly below `1/2`. -/
theorem exists_even_joint_prolate_eigen_separation_lt_half {c : ℝ} (hc : 400 ≤ c) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      radialSeparationRatio c eta < 1 / 2 := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcsq : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  obtain ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, heta⟩ :=
    exists_even_joint_prolate_eigen_gt_of_rayleigh_gt (K := c ^ (2 : ℕ) / 2) hc0
      (prolate_gaussian_rayleigh_gt hc)
  refine ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, ?_⟩
  rw [radialSeparationRatio, div_lt_div_iff₀ hcsq (by norm_num : (0 : ℝ) < 2)]
  nlinarith [heta]

end RHTower
