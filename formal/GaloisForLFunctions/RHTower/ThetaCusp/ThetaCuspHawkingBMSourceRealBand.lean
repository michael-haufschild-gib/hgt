import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRealSourceCoercivity
import GaloisForLFunctions.HTGeometry.CompactPatchGenericity

/-! Uniform nonvanishing near the complete real physical interval, including the pole endpoint. -/
namespace RHTower.D4BMJointSource
open Complex Set GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- One positive imaginary-width works for every real part in the closed physical strip. -/
theorem nonstationarySourceDefect_uniform_real_band :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) →
      |w.im| ≤ δ → nonstationarySourceDefect w ≠ (86/625:ℂ) := by
  let K := Icc (-(3/2):ℝ) (-1)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let z : ℝ × K → ℂ := fun p => (p.2.val:ℂ)+(p.1:ℂ)*Complex.I
  have hz : Continuous z :=
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hzK : ∀ p, (z p).re ∈ Icc (-(3/2):ℝ) (-1) := by
    intro p
    simpa only [z,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
      using p.2.property
  let g : ℝ → K → ℂ := fun t u => nonstationarySourceDefect (z (t,u))-(86/625:ℂ)
  have hg : Continuous (fun p : ℝ × K => g p.1 p.2) :=
    (nonstationarySourceDefect_continuousOn.comp_continuous hz hzK).sub continuous_const
  have hopen : IsOpen {t : ℝ | ∀ u ∈ (univ : Set K), g t u ≠ 0} :=
    isOpen_setOf_forall_mem_compact_ne_zero isCompact_univ g
      (fun _ _ _ => hg.continuousAt)
  have hzero : (0:ℝ) ∈ {t : ℝ | ∀ u ∈ (univ : Set K), g t u ≠ 0} := by
    intro u _ h
    have he : nonstationarySourceDefect (u.val:ℂ)=(86/625:ℂ) := by
      apply sub_eq_zero.mp
      simpa only [g,z,Complex.ofReal_zero,zero_mul,add_zero] using h
    have hgap := nonstationarySourceDefect_real_gap u.val u.property
    rw [he] at hgap
    norm_num at hgap
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  refine ⟨ε/2,by positivity,?_⟩
  intro w hw hi
  have ht : w.im ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    linarith
  have hne := hball ht (⟨w.re,hw⟩ : K) (mem_univ _)
  change nonstationarySourceDefect ((w.re:ℂ)+(w.im:ℂ)*Complex.I)-(86/625:ℂ) ≠ 0 at hne
  rw [Complex.re_add_im] at hne
  exact sub_ne_zero.mp hne

end
end RHTower.D4BMJointSource
