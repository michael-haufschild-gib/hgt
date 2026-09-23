import GaloisForLFunctions.RHTower.ProlateEvenEigenspaceRelativeBound
import GaloisForLFunctions.RHTower.ProlateGeneralTrialMode

/-!
# The prolate trial form on the complement of the high modes

The variational extraction says that a trial function whose prolate Rayleigh numerator exceeds
`-K` times its squared aperture norm produces a joint mode with prolate eigenvalue above `-K`.
Its relative form is the statement needed for a dimension count: a trial function *orthogonal to
every* joint even mode with prolate eigenvalue above `-K` has Rayleigh numerator at most `-K`
times its squared norm.

The proof is the same decomposition, with the finite-dimensional step replaced by the relative
eigenspace bound: on each even band eigenspace, orthogonality to the high modes puts all the mass
on prolate coordinates with eigenvalue at most `-K`.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- A joint even band/prolate mode whose prolate eigenvalue exceeds `-K`. -/
def IsHighProlateMode (c K : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ lam eta : ℝ, lam ≠ 0 ∧ -K < eta ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
    (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
    (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x)

/-- **Mode reconstruction.**  A nonzero prolate eigenvector of an even band eigenspace is the band
class of a genuine smooth even joint band/prolate mode with the same eigenvalue. -/
theorem exists_mode_of_evenEigenspace_eigenvector
    {c lam eta : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {v : evenBandEigenspace c lam} (hv : v ≠ 0)
    (heig : prolateOnEvenEigenspace hc hlam v = eta • v) :
    ∃ (Phi : ℝ → ℝ) (hPhic : Continuous Phi),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      GaloisForLFunctions.RHTower.bandClass Phi hPhic
        = (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by
  set bf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨v.1, v.2.1⟩ with hbf
  refine ⟨GaloisForLFunctions.RHTower.eigenRep c lam bf,
    GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf,
    GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam bf, ?_, v.2.2,
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
    exact hv (Subtype.ext hbot)
  · intro x
    have hvaleq :
        GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bf = eta • bf := by
      apply Subtype.ext
      exact congrArg (fun w : evenBandEigenspace c lam => w.1) heig
    have hrepeq := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hvaleq
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrepeq
    have hx := congrFun hrepeq x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (eta • bf) x =
        eta * GaloisForLFunctions.RHTower.eigenRep c lam bf x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam eta bf x
    rw [hsmul] at hx
    exact hx

/-- **Relative trial bound.**  A smooth even trial function orthogonal on the aperture to every
joint even mode with prolate eigenvalue above `-K` has prolate Rayleigh numerator at most `-K`
times its squared aperture norm. -/
theorem prolate_trial_le_of_orthogonal_high {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (horth : ∀ Phi : ℝ → ℝ, IsHighProlateMode c K Phi →
      (∫ x in (-1 : ℝ)..1, Phi x * g x) = 0) :
    (∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x)
      ≤ -K * ∫ x in (-1 : ℝ)..1, g x * g x := by
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
      -- the quadratic form is at most `-K` times the squared norm
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
      have horthE : ∀ (w : evenBandEigenspace c μ) (eta : ℝ), -K < eta →
          prolateOnEvenEigenspace hc0 hμ w = eta • w → (inner ℝ w bu : ℝ) = 0 := by
        intro w eta heta hweig
        by_cases hw0 : w = 0
        · rw [hw0]
          simp
        · obtain ⟨Psi, hPsic, hPsism, hPsine, hPsieven, hPsiband, hPsiprolate, hPsiclass⟩ :=
            exists_mode_of_evenEigenspace_eigenvector hc0 hμ hw0 hweig
          have hzero : (∫ x in (-1 : ℝ)..1, Psi x * g x) = 0 :=
            horth Psi ⟨μ, eta, hμ, heta, hPsism, hPsine, hPsieven, hPsiband, hPsiprolate⟩
          have hwv : (inner ℝ (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
              v : ℝ) = 0 := by
            rw [← hPsiclass, hv, GaloisForLFunctions.RHTower.inner_bandClass_eq]
            exact hzero
          have hproj2 : (inner ℝ v (w : GaloisForLFunctions.RHTower.RealIntervalL2
                (-1 : ℝ) 1) : ℝ)
              = (inner ℝ u (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ) :=
            inner_eq_inner_bandComponent c v _ w.2.1
          have hgoal : (inner ℝ (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
              u : ℝ) = 0 := by
            rw [real_inner_comm, ← hproj2, real_inner_comm]
            exact hwv
          exact hgoal
      have hquad : (inner ℝ u (GaloisForLFunctions.RHTower.bandClass
            (prolateSLAction c Phi) hLPhic) : ℝ) ≤ -K * ‖u‖ ^ (2 : ℕ) := by
        have hrel := prolate_form_le_of_orthogonal_high hc0 hμ horthE
        rw [hform, hnorm] at hrel
        exact hrel
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
  exact hle

/-- The span of the band classes of all joint even modes with prolate eigenvalue above `-K`. -/
def highProlateSpan (c K : ℝ) :
    Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :=
  Submodule.span ℝ {w | ∃ (Phi : ℝ → ℝ) (hPhic : Continuous Phi),
    IsHighProlateMode c K Phi ∧ w = GaloisForLFunctions.RHTower.bandClass Phi hPhic}

theorem bandClass_mem_highProlateSpan {c K : ℝ} {Phi : ℝ → ℝ} (hPhic : Continuous Phi)
    (h : IsHighProlateMode c K Phi) :
    GaloisForLFunctions.RHTower.bandClass Phi hPhic ∈ highProlateSpan c K :=
  Submodule.subset_span ⟨Phi, hPhic, h, rfl⟩

/-- **A live trial function meets the high-mode span.**  A smooth even trial function whose prolate
Rayleigh numerator exceeds `-K` times its squared aperture norm cannot be orthogonal to every joint
even mode with prolate eigenvalue above `-K`. -/
theorem bandClass_notMem_orthogonal_highProlateSpan {c K : ℝ} (hc0 : 0 < c)
    {g : ℝ → ℝ} (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgeven : Function.Even g)
    (hpos : -K * (∫ x in (-1 : ℝ)..1, g x * g x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x) :
    GaloisForLFunctions.RHTower.bandClass g hgsm.continuous ∉ (highProlateSpan c K)ᗮ := by
  intro hmem
  have horth : ∀ Phi : ℝ → ℝ, IsHighProlateMode c K Phi →
      (∫ x in (-1 : ℝ)..1, Phi x * g x) = 0 := by
    intro Phi hPhi
    obtain ⟨lam, eta, hlam, heta, hsm, hne, heven, hband, hprolate⟩ := hPhi
    have hPhic : Continuous Phi := hsm.continuous
    have hin := (Submodule.mem_orthogonal _ _).1 hmem
      (GaloisForLFunctions.RHTower.bandClass Phi hPhic)
      (bandClass_mem_highProlateSpan hPhic
        ⟨lam, eta, hlam, heta, hsm, hne, heven, hband, hprolate⟩)
    rwa [GaloisForLFunctions.RHTower.inner_bandClass_eq] at hin
  have hle := prolate_trial_le_of_orthogonal_high hc0 hgsm hgeven horth
  linarith [hpos, hle]

/-- **Trial spaces avoid the orthogonal complement of the high-mode span.**  If every nonzero
vector of a subspace is the band class of a smooth even function whose prolate Rayleigh numerator
exceeds `-K` times its squared aperture norm, then that subspace meets the orthogonal complement of
the high-mode span only in zero. -/
theorem disjoint_trialSpace_orthogonal_highProlateSpan {c K : ℝ} (hc0 : 0 < c)
    (V : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
    (hV : ∀ w ∈ V, w ≠ 0 → ∃ (g : ℝ → ℝ) (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g),
      Function.Even g ∧ w = GaloisForLFunctions.RHTower.bandClass g hgsm.continuous ∧
      -K * (∫ x in (-1 : ℝ)..1, g x * g x)
        < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x) :
    Disjoint V (highProlateSpan c K)ᗮ := by
  rw [Submodule.disjoint_def]
  intro w hwV hwO
  by_contra hne
  obtain ⟨g, hgsm, hgeven, hweq, hpos⟩ := hV w hwV hne
  exact bandClass_notMem_orthogonal_highProlateSpan hc0 hgsm hgeven hpos (hweq ▸ hwO)

/-- **Dimension count from disjointness.**  Orthogonal projection onto the high-mode span is
injective on any subspace meeting its orthogonal complement only in zero. -/
theorem rank_le_of_disjoint_orthogonal {c K : ℝ}
    (V : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
    [(highProlateSpan c K).HasOrthogonalProjection]
    (hdisj : Disjoint V (highProlateSpan c K)ᗮ) :
    Module.rank ℝ V ≤ Module.rank ℝ (highProlateSpan c K) := by
  set f : V →ₗ[ℝ] (highProlateSpan c K) :=
    ((highProlateSpan c K).orthogonalProjectionOnto :
      GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
        (highProlateSpan c K)).toLinearMap.comp V.subtype with hf
  refine LinearMap.rank_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  have hmem : (m : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
      ∈ (highProlateSpan c K)ᗮ :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.1 hm
  exact Subtype.ext ((Submodule.disjoint_def.1 hdisj) _ m.2 hmem)

/-- **Dimension count.**  A trial space on which the prolate form stays above `-K` injects into the
high-mode span, so the span is at least as large. -/
theorem rank_trialSpace_le_highProlateSpan {c K : ℝ} (hc0 : 0 < c)
    (V : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
    [(highProlateSpan c K).HasOrthogonalProjection]
    (hV : ∀ w ∈ V, w ≠ 0 → ∃ (g : ℝ → ℝ) (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g),
      Function.Even g ∧ w = GaloisForLFunctions.RHTower.bandClass g hgsm.continuous ∧
      -K * (∫ x in (-1 : ℝ)..1, g x * g x)
        < ∫ x in (-1 : ℝ)..1, prolateSLAction c g x * g x) :
    Module.rank ℝ V ≤ Module.rank ℝ (highProlateSpan c K) :=
  rank_le_of_disjoint_orthogonal V (disjoint_trialSpace_orthogonal_highProlateSpan hc0 V hV)

end RHTower
