import GaloisForLFunctions.RHTower.ProlateReflection

/-!
# The eigencomponents of an even profile are even

The Slepian band transform commutes with reflection, so each band eigenspace is reflection
invariant.  For an even profile this forces every eigencomponent to be even: the odd part of the
component's smooth representative is itself a band eigenfunction, is orthogonal to the even profile,
and — by the projection property of the component — therefore orthogonal to itself.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- The band class of a continuous global band eigenfunction lies in the band eigenspace. -/
theorem bandClass_mem_bandEigenspace {c lam : ℝ} {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (hψband : ∀ x : ℝ, bandTransform c ψ x = lam * ψ x) :
    GaloisForLFunctions.RHTower.bandClass ψ hψc ∈
      GaloisForLFunctions.RHTower.bandEigenspace c lam := by
  have htransform : Continuous (bandTransform c ψ) :=
    GaloisForLFunctions.RHTower.continuous_bandTransform c hψc
  have hmul : Continuous fun x => lam * ψ x := continuous_const.mul hψc
  refine GaloisForLFunctions.RHTower.mem_bandEigenspace_iff.mpr ?_
  have hclassEig :
      GaloisForLFunctions.RHTower.bandClass (bandTransform c ψ) htransform =
        GaloisForLFunctions.RHTower.bandClass (fun x => lam * ψ x) hmul := by
    apply Lp.ext
    filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass (bandTransform c ψ) htransform,
      GaloisForLFunctions.RHTower.coeFn_bandClass (fun x => lam * ψ x) hmul] with x hx₁ hx₂
    rw [hx₁, hx₂]
    exact hψband x
  rw [GaloisForLFunctions.RHTower.bandOperatorL2_bandClass, hclassEig,
    GaloisForLFunctions.RHTower.bandClass_smul]

/-- **The eigencomponent of an even profile is even.** -/
theorem bandComponent_mem_evenBandEigenspace {c : ℝ} {g : ℝ → ℝ} (hgc : Continuous g)
    (hgeven : Function.Even g) {μ : ℝ} (hμ : μ ≠ 0) :
    bandComponent c (GaloisForLFunctions.RHTower.bandClass g hgc) μ ∈
      evenBandEigenspace c μ := by
  set v := GaloisForLFunctions.RHTower.bandClass g hgc with hv
  set u := bandComponent c v μ with hu
  have humem : u ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ := bandComponent_mem c v μ
  set bu : GaloisForLFunctions.RHTower.bandEigenspace c μ := ⟨u, humem⟩ with hbu
  set Phi := GaloisForLFunctions.RHTower.eigenRep c μ bu with hPhi
  have hPhic : Continuous Phi := GaloisForLFunctions.RHTower.continuous_eigenRep c μ bu
  have hPhiband : ∀ x : ℝ, bandTransform c Phi x = μ * Phi x :=
    GaloisForLFunctions.RHTower.bandTransform_eigenRep hμ bu
  have hPhiclass : GaloisForLFunctions.RHTower.bandClass Phi hPhic = u :=
    GaloisForLFunctions.RHTower.bandClass_eigenRep hμ bu
  set Po := oddPart Phi with hPo
  have hPoc : Continuous Po := continuous_oddPart hPhic
  have hPoband : ∀ x : ℝ, bandTransform c Po x = μ * Po x :=
    bandTransform_oddPart hPhic hPhiband
  have hPomem : GaloisForLFunctions.RHTower.bandClass Po hPoc ∈
      GaloisForLFunctions.RHTower.bandEigenspace c μ :=
    bandClass_mem_bandEigenspace hPoc hPoband
  -- the even profile is orthogonal to the odd part
  have h1 : (inner ℝ v (GaloisForLFunctions.RHTower.bandClass Po hPoc) : ℝ) = 0 := by
    rw [hv, GaloisForLFunctions.RHTower.inner_bandClass_eq]
    exact integral_even_mul_odd_eq_zero hgc hPoc hgeven (odd_oddPart Phi)
  have h2 : (inner ℝ v (GaloisForLFunctions.RHTower.bandClass Po hPoc) : ℝ)
      = (inner ℝ u (GaloisForLFunctions.RHTower.bandClass Po hPoc) : ℝ) :=
    inner_eq_inner_bandComponent c v _ hPomem
  have h3 : (inner ℝ u (GaloisForLFunctions.RHTower.bandClass Po hPoc) : ℝ)
      = ∫ y in (-1 : ℝ)..1, Phi y * Po y := by
    rw [← hPhiclass, GaloisForLFunctions.RHTower.inner_bandClass_eq]
  have hcross : (∫ y in (-1 : ℝ)..1, evenPart Phi y * Po y) = 0 :=
    integral_even_mul_odd_eq_zero (continuous_evenPart hPhic) hPoc (even_evenPart Phi)
      (odd_oddPart Phi)
  have h4 : (∫ y in (-1 : ℝ)..1, Phi y * Po y) = ∫ y in (-1 : ℝ)..1, Po y * Po y := by
    have hsplit : (∫ y in (-1 : ℝ)..1, Phi y * Po y)
        = (∫ y in (-1 : ℝ)..1, evenPart Phi y * Po y)
          + ∫ y in (-1 : ℝ)..1, Po y * Po y := by
      have hi1 : IntervalIntegrable (fun y : ℝ => evenPart Phi y * Po y) volume (-1) 1 := by
        apply Continuous.intervalIntegrable
        exact (continuous_evenPart hPhic).mul hPoc
      have hi2 : IntervalIntegrable (fun y : ℝ => Po y * Po y) volume (-1) 1 := by
        apply Continuous.intervalIntegrable
        exact hPoc.mul hPoc
      rw [← intervalIntegral.integral_add hi1 hi2]
      refine intervalIntegral.integral_congr fun y _ => ?_
      show Phi y * Po y = evenPart Phi y * Po y + Po y * Po y
      rw [← evenPart_add_oddPart Phi y]
      rw [hPo]
      ring
    rw [hsplit, hcross, zero_add]
  have h5 : (inner ℝ (GaloisForLFunctions.RHTower.bandClass Po hPoc)
      (GaloisForLFunctions.RHTower.bandClass Po hPoc) : ℝ) = 0 := by
    rw [GaloisForLFunctions.RHTower.inner_bandClass_eq]
    rw [← h4, ← h3, ← h2, h1]
  have h6 : GaloisForLFunctions.RHTower.bandClass Po hPoc = 0 := inner_self_eq_zero.mp h5
  have h7 : Po = 0 := by
    have hrec := eigenExtension_bandClass_eq_self_of_bandEigen hμ hPoc hPoband
    rw [h6] at hrec
    rw [← hrec]
    have := map_zero (eigenExtensionLinearMap c μ)
    exact this
  have h8 : Function.Even Phi := by
    intro x
    have hx := congrFun h7 x
    rw [hPo] at hx
    unfold oddPart at hx
    have hx0 : Phi x - Phi (-x) = 0 := by
      have : (Phi x - Phi (-x)) / 2 = 0 := hx
      linarith
    linarith
  have hmem := bandClass_mem_evenBandEigenspace hμ hPhic h8 hPhiband
  rw [hPhiclass] at hmem
  exact hmem

end RHTower
