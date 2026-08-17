import GaloisForLFunctions.RHTower.ProlateLowSeparationMode
import GaloisForLFunctions.HTGeometry.SymmetricFormEigenvalueThreshold

/-!
# Trial functions orthogonal to every high mode have low Rayleigh quotient

The variational machine produces *one* joint mode above a Rayleigh threshold.  Its counting version
— the one an excited-mode ladder needs — is the contrapositive statement with an orthogonality
constraint:

> if a trial function is orthogonal to every even joint band/prolate eigenfunction whose prolate
> eigenvalue exceeds `−K`, then its own prolate Rayleigh quotient is at most `−K`.

The proof is the same decomposition over the eigenspaces of the compact band operator, with one
change: on each eigenspace the quadratic form is bounded not because *all* prolate eigenvalues there
are below the threshold, but because the component is orthogonal to the eigenvectors above it.  That
step is the finite-dimensional half of the min–max principle.

Taking the orthogonality hypothesis vacuous recovers the existing machine, and taking an
`(n+1)`-dimensional trial space gives the count: a space of trial functions all of whose Rayleigh
quotients exceed `−K` cannot be orthogonal to all high modes, so the high modes cannot be spanned by
fewer than `n+1` of them.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- An eigenvector of the prolate operator on an even band eigenspace is realized by an even joint
band/prolate eigenfunction. -/
theorem exists_eigenRep_of_prolate_eigenvector {c lam eta : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (w : evenBandEigenspace c lam) (hw : w ≠ 0)
    (hev : prolateOnEvenEigenspace hc hlam w = eta • w) :
    ∃ Phi : ℝ → ℝ, ∃ hPhic : Continuous Phi,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      GaloisForLFunctions.RHTower.bandClass Phi hPhic
        = (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by
  set bf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨w.1, w.2.1⟩ with hbf
  refine ⟨GaloisForLFunctions.RHTower.eigenRep c lam bf,
    GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf,
    GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam bf, ?_, w.2.2,
    fun x => GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam bf x, ?_,
    GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bf⟩
  · intro hzero
    have hclass := GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bf
    have hstep : GaloisForLFunctions.RHTower.bandClass
        (GaloisForLFunctions.RHTower.eigenRep c lam bf)
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf)
        = GaloisForLFunctions.RHTower.bandClass (fun _ : ℝ => (0 : ℝ)) continuous_const :=
      GaloisForLFunctions.RHTower.bandClass_congr _ _ hzero
    have hbot : (bf : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) = 0 := by
      rw [← hclass, hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    exact hw (Subtype.ext hbot)
  · intro x
    have hvaleq :
        GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bf = eta • bf := by
      apply Subtype.ext
      exact congrArg (fun z : evenBandEigenspace c lam => z.1) hev
    have hrepeq := congrArg
      (fun z : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam z) hvaleq
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrepeq
    have hx := congrFun hrepeq x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (eta • bf) x =
        eta * GaloisForLFunctions.RHTower.eigenRep c lam bf x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam eta bf x
    rw [hsmul] at hx
    exact hx

/-- **The counting form of the variational machine.**  A trial function orthogonal to every even
joint mode above `−K` has prolate Rayleigh quotient at most `−K`. -/
theorem rayleigh_le_of_orthogonal_to_high_modes {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (horth : ∀ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi → Phi ≠ 0 → Function.Even Phi →
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) →
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) → -K < eta →
      (∫ x in (-1 : ℝ)..1, g x * Phi x) = 0) :
    (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x)
      ≤ -K * ∫ x in (-1 : ℝ)..1, g x * g x := by
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
      have hTmem : GaloisForLFunctions.RHTower.bandClass (prolateSLAction c Phi) hLPhic
          ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ :=
        GaloisForLFunctions.RHTower.prolate_bandClass_mem hc0 hμ bf
      have hproj : (inner ℝ v (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ)
          = (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ) :=
        inner_eq_inner_bandComponent c v _ hTmem
      -- the quadratic form on the eigenspace, via orthogonality to the high eigenvectors
      have hquad : (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ) ≤ -K * ‖u‖ ^ 2 := by
        letI : FiniteDimensional ℝ (evenBandEigenspace c μ) :=
          finiteDimensional_evenBandEigenspace hμ
        set T := prolateOnEvenEigenspace hc0 hμ with hT
        have hsym : T.IsSymmetric := isSymmetric_prolateOnEvenEigenspace hc0 hμ
        have hform : (inner ℝ (T bu) bu : ℝ)
            = (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
              (prolateSLAction c Phi) hLPhic) : ℝ) := by
          have hval : ((T bu : evenBandEigenspace c μ) :
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
              = GaloisForLFunctions.RHTower.bandClass (prolateSLAction c Phi) hLPhic := rfl
          rw [show (inner ℝ (T bu) bu : ℝ)
              = (inner ℝ ((T bu : evenBandEigenspace c μ) :
                  GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
                ((bu : evenBandEigenspace c μ) :
                  GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ) from rfl, hval]
          exact real_inner_comm _ _
        have hnorm : ‖bu‖ = ‖u‖ := rfl
        have hmain := GaloisForLFunctions.HTGeometry.inner_le_of_orthogonal_to_eigenvectors_above
          hsym (-K) bu ?_
        · rw [← hform, hnorm] at *
          exact hmain
        · intro eta w hwne hwev hwgt
          obtain ⟨Psi, hPsic, hPsism, hPsine, hPsieven, hPsiband, hPsiprolate, hPsiclass⟩ :=
            exists_eigenRep_of_prolate_eigenvector hc0 hμ w hwne hwev
          have hzero : (∫ x in (-1 : ℝ)..1, g x * Psi x) = 0 :=
            horth μ eta Psi hμ hPsism hPsine hPsieven hPsiband hPsiprolate hwgt
          have hvw : (inner ℝ v (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ)
              = 0 := by
            rw [hv, ← hPsiclass, GaloisForLFunctions.RHTower.inner_bandClass_eq]
            exact hzero
          have huw : (inner ℝ u (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ)
              = 0 := by
            rw [← inner_eq_inner_bandComponent c v _ w.2.1]
            exact hvw
          exact huw
      have hselfinner : (inner ℝ v u : ℝ) = ‖u‖ ^ 2 := inner_self_bandComponent c v μ
      rw [hmove, hproj, hselfinner]
      exact hquad
  have hsum1 : HasSum (fun μ : ℝ => (inner ℝ Lv (bandComponent c v μ) : ℝ))
      (inner ℝ Lv v : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ Lv) (hasSum_bandComponent c v)
  have hsum2 : HasSum (fun μ : ℝ => -K * (inner ℝ v (bandComponent c v μ) : ℝ))
      (-K * (inner ℝ v v : ℝ)) :=
    HasSum.mul_left _ (ContinuousLinearMap.hasSum (innerSL ℝ v) (hasSum_bandComponent c v))
  have hle : (inner ℝ Lv v : ℝ) ≤ -K * (inner ℝ v v : ℝ) :=
    hasSum_le hstep hsum1 hsum2
  rw [hLv, hv, GaloisForLFunctions.RHTower.inner_bandClass_eq,
    GaloisForLFunctions.RHTower.inner_bandClass_eq] at hle
  exact hle

/-- **A trial above the threshold meets a high mode.**  Contrapositive of the counting form: a trial
function whose Rayleigh quotient exceeds `−K` has nonzero pairing with some even joint mode above
`−K`. -/
theorem exists_high_mode_not_orthogonal {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (hray : -K * (∫ x in (-1 : ℝ)..1, g x * g x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      -K < eta ∧ (∫ x in (-1 : ℝ)..1, g x * Phi x) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle := rayleigh_le_of_orthogonal_to_high_modes hc0 hgsm hgeven
    (fun lam eta Phi h1 h2 h3 h4 h5 h6 h7 => hcon lam eta Phi h1 h2 h3 h4 h5 h6 h7)
  linarith

/-- **The induction step of an excited ladder.**  If the trial function is orthogonal to a subspace
`W` and its Rayleigh quotient exceeds `−K`, then some even joint mode above `−K` has band class
outside `W`. -/
theorem exists_high_mode_notMem_of_orthogonal_trial {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (hray : -K * (∫ x in (-1 : ℝ)..1, g x * g x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x)
    (W : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
    (hgW : GaloisForLFunctions.RHTower.bandClass g hgsm.continuous ∈ Wᗮ) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ) (hPhic : Continuous Phi), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      -K < eta ∧ GaloisForLFunctions.RHTower.bandClass Phi hPhic ∉ W := by
  obtain ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, hgt, hpair⟩ :=
    exists_high_mode_not_orthogonal hc0 hgsm hgeven hray
  refine ⟨lam, eta, Phi, hsm.continuous, hlam, hsm, hne, heven, hband, hprolate, hgt, ?_⟩
  intro hmem
  refine hpair ?_
  have hzero : (inner ℝ (GaloisForLFunctions.RHTower.bandClass g hgsm.continuous)
      (GaloisForLFunctions.RHTower.bandClass Phi hsm.continuous) : ℝ) = 0 := by
    have := (Submodule.mem_orthogonal W _).1 hgW _ hmem
    rw [real_inner_comm] at this
    exact this
  rw [GaloisForLFunctions.RHTower.inner_bandClass_eq] at hzero
  exact hzero

end RHTower

end
