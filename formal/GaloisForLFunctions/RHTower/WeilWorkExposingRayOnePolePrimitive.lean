import GaloisForLFunctions.RHTower.WeilWorkExposingRayLogKernel
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarInverse
import GaloisForLFunctions.RHTower.ResolventDivisionDecay

/-!
# Actual compact first-order primitives for one-pole sources

Every compact complex C2 source with `paperFT f (s I) = 0` has an actual
compact C3 primitive satisfying `g' = s g + f`. Its full complex Fourier
multiplier is `paperFT f z = -(I z + s) paperFT g z`.

This uses the existing CCM exponential primitive and its support theorem,
with finite regularity supplied explicitly. It is a bridge for the
one-pole difference-quotient limit, not a claim of new ODE theory or a
completed WP02 energy estimate.

Paper: docs/reports/weil-work/results/02-exposing-ray/ONE-POLE-SUBLOG-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

private theorem compact_superExp {f : ℝ → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) : SuperExpDecay f := by
  refine ⟨hf,fun c => ?_⟩
  exact (hf.norm.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (c*|u|))).integrable_of_hasCompactSupport
    hs.norm.mul_right

private theorem contDiff_three_primitive {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (a : ℝ) :
    ContDiff ℝ 3 (fun x : ℝ => ∫ t in a..x, f t) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => ∫ t in a..y,f t) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable a x)
      (hf.continuous.stronglyMeasurableAtFilter _ _) hf.continuous.continuousAt
  have he : deriv (fun y : ℝ => ∫ t in a..y,f t) = f := by
    funext x
    exact (hd x).deriv
  change ContDiff ℝ (2+1) _
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt,?_,?_⟩
  · intro h
    norm_num at h
  · rw [he]
    exact hf

private theorem contDiff_three_exponentialPrimitive (s a : ℝ) (f : WeilTestFn) :
    ContDiff ℝ 3 (ccmPolarExponentialPrimitive s a f.1) := by
  have hp : ContDiff ℝ 3 (fun x : ℝ => (Real.exp (s*x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hm0 : ContDiff ℝ 2 (fun x : ℝ => (Real.exp (-s*x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hm : ContDiff ℝ 2 (fun x : ℝ => (Real.exp (-s*x) : ℂ)*f.1 x) :=
    hm0.mul f.2.1
  exact hp.mul (contDiff_three_primitive hm a)

private theorem paperFT_imaginary (s : ℝ) (f : ℝ → ℂ) :
    paperFT f ((s:ℂ)*I) = ∫ u : ℝ,(Real.exp (-s*u) : ℂ)*f u := by
  unfold paperFT
  apply integral_congr_ae
  filter_upwards [] with u
  have he : I*((s:ℂ)*I)*(u:ℂ) = ((-s*u:ℝ):ℂ) := by
    push_cast
    calc
      _ = (s:ℂ)*(u:ℂ)*(I*I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he,← Complex.ofReal_exp]
  ring

/-- Every compact C2 source with one imaginary zero has an actual compact
C3 first-order primitive. Its full complex Fourier multiplier is exact. -/
theorem exists_compact_onePole_primitive (s : ℝ) (f : WeilTestFn)
    (hzero : paperFT f.1 ((s:ℂ)*I) = 0) :
    ∃ g : WeilTestFn, ContDiff ℝ 3 g.1 ∧
      (∀ u : ℝ, HasDerivAt g.1 ((s:ℂ)*g.1 u+f.1 u) u) ∧
      ∀ z : ℂ, paperFT f.1 z = -(I*z+(s:ℂ))*paperFT g.1 z := by
  obtain ⟨R,hR,hvan⟩ := f.2.2.exists_pos_le_norm
  have hsource : ∀ u : ℝ, u ∉ Ioo (-R) R → f.1 u=0 := by
    intro u hu
    apply hvan
    rw [Real.norm_eq_abs]
    have hh : ¬ |u| < R := by simpa only [abs_lt,mem_Ioo] using hu
    exact le_of_not_gt hh
  have hm : (∫ u : ℝ,(Real.exp (-s*u) : ℂ)*f.1 u)=0 := by
    rw [← paperFT_imaginary]
    exact hzero
  let G := ccmPolarExponentialPrimitive s (-R) f.1
  have hG3 : ContDiff ℝ 3 G := contDiff_three_exponentialPrimitive s (-R) f
  have hGs : HasCompactSupport G := by
    have hs : tsupport G ⊆ Icc (-R) R := by
      apply closure_minimal _ isClosed_Icc
      intro u hu
      by_contra hh
      have hnot : u ∉ Ioo (-R) R := fun h => hh ⟨h.1.le,h.2.le⟩
      exact hu (ccmPolarExponentialPrimitive_eq_zero_outside hR s f.2.1.continuous hsource hm u hnot)
    exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hs
  let g : WeilTestFn := ⟨G,hG3.of_le (by norm_num),hGs⟩
  have hd (u : ℝ) : HasDerivAt G ((s:ℂ)*G u+f.1 u) u :=
    hasDerivAt_ccmPolarExponentialPrimitive s (-R) f.2.1.continuous u
  refine ⟨g,hG3,hd,fun z => ?_⟩
  have hg := compact_superExp hG3.continuous hGs
  have hf := compact_superExp f.2.1.continuous f.2.2
  have hg' : SuperExpDecay (fun u => (s:ℂ)*G u+f.1 u) := (hg.const_mul (s:ℂ)).add hf
  have hft := paperFT_deriv_of_superExpDecay hg hg' hd z
  have he : paperFT (fun u => (s:ℂ)*G u+f.1 u) z = (s:ℂ)*paperFT G z+paperFT f.1 z := by
    unfold paperFT
    have heq : (fun u : ℝ => ((s:ℂ)*G u+f.1 u)*cexp (I*z*u)) =
        fun u => (s:ℂ)*(G u*cexp (I*z*u))+f.1 u*cexp (I*z*u) := by
      funext u
      ring
    rw [heq,integral_add ((hg.integrable_mul_cexp z).const_mul _) (hf.integrable_mul_cexp z),
      integral_const_mul]
  rw [he] at hft
  change paperFT f.1 z = -(I*z+(s:ℂ))*paperFT G z
  linear_combination hft

end RHTower.ExposingRayTransfer
