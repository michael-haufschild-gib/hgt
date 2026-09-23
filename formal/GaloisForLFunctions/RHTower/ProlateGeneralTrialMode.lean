import GaloisForLFunctions.RHTower.ProlateLowSeparationMode

/-!
# Variational mode extraction from an arbitrary even trial function

The prolate mode-extraction argument uses nothing about the Gaussian beyond smoothness and
evenness: the trial function's band class decomposes over the eigenspaces of the compact symmetric
band operator, the prolate action is symmetric, and one summand must reach the trial value.  So the
same extraction runs from any smooth even trial function, which is what feeds Hermite trial
functions into the prolate spectrum.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- **Mode extraction from an arbitrary even trial function.**  If a smooth even trial function has
prolate Rayleigh numerator above `-K` times its squared aperture norm, then some even joint
band/prolate eigenfunction has prolate eigenvalue above `-K`. -/
theorem exists_even_joint_prolate_eigen_gt_of_trial {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (htrial : -K * (∫ x in (-1 : ℝ)..1, g x * g x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      -K < eta := by
  by_contra hcon
  push Not at hcon
  -- the test vector
  have hgc : Continuous g := hgsm.continuous
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
  linarith [htrial, hle]


end RHTower
