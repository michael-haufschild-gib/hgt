import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalGradedCoefficient
import Mathlib.Algebra.Polynomial.Bivariate

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial Filter Topology

def gradedSurplusSlice (z : ℂ) (n : ℕ) : Polynomial ℂ :=
  (Bivariate.swap (gradedReducedRead z)).coeff n

theorem gradedSurplusSlice_eval (z : ℂ) (n : ℕ) (h : ℂ) :
    (gradedSurplusSlice z n).eval h=((gradedReducedRead z).eval (C h)).coeff n := by
  have he := congrArg (fun P : Polynomial ℂ => P.coeff n)
    (Bivariate.aveal_eq_map_swap (R:=ℂ) (A:=ℂ) h (gradedReducedRead z))
  simpa [coeff_mapAlgHom_apply,aeval_def,Polynomial.algebraMap_def,gradedSurplusSlice] using he.symm

theorem gradedSurplusSlice_zero (z : ℂ) (n : ℕ) :
    (gradedSurplusSlice z n).eval 0=((gradedReducedRead z).coeff 0).coeff n := by
  rw [gradedSurplusSlice_eval]
  simp only [map_zero,←coeff_zero_eq_eval_zero]

theorem gradedSurplusSlice_six_zero (z : ℂ) :
    (gradedSurplusSlice z 6).eval 0= -(8192/3)*189994*(12:ℂ)^18 := by
  rw [gradedSurplusSlice_zero,gradedReducedRead_zero_six]

theorem gradedSurplusSlice_six_source (z h : ℂ) (hh : h≠0) :
    (gradedSurplusSlice z 6).eval h=
      h^10*(flatSourceSurplus (inverseClockK h) z).coeff 6 := by
  rw [gradedSurplusSlice_eval,gradedReducedRead_six _ _ hh]

theorem flatSourceSurplus_six_eventually_neg (z : ℂ) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ((flatSourceSurplus (inverseClockK ((h:ℝ):ℂ)) z).coeff 6).re<0 := by
  have hc : Continuous (fun h : ℝ => ((gradedSurplusSlice z 6).eval (h:ℂ)).re) :=
    Complex.continuous_re.comp
      ((gradedSurplusSlice z 6).continuous.comp Complex.continuous_ofReal)
  have hz : ((gradedSurplusSlice z 6).eval 0).re<0 := by
    rw [gradedSurplusSlice_six_zero]
    norm_num
  have hn := hc.continuousAt.eventually_lt_const hz
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [gradedSurplusSlice_six_source _ _ hhC] at hn
  have hs : h^10*((flatSourceSurplus (inverseClockK ((h:ℝ):ℂ)) z).coeff 6).re<0 := by
    simpa only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using hn
  have hp : 0<h^10 := pow_pos hh _
  by_contra hq
  exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hq))) hs


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
