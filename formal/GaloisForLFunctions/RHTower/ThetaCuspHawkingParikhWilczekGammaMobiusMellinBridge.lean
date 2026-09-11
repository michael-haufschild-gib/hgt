import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusGlobalAdmission
import GaloisForLFunctions.RHTower.BurnolMoebiusLine
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# Literal Mellin transform of the complete Gamma/Möbius source

The original weighted atom integrals give Gamma(s+1/2) times the full
Möbius L-series at z+s. Their norm integral sum has the exact boundary
Re(z+s)>1, with Re(s)>-1/2. In that region the complete source integral
is Gamma(s+1/2)/zeta(z+s). No critical-strip continuation or Ward balance
is assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaRaySource_mellin_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ)^(s-1)*pwGammaRaySource x =
      (Real.exp (-x) : ℂ)*(x : ℂ)^((s+1/2)-1) := by
  rw [pwGammaRaySource_eq hx, Complex.ofReal_mul, Real.sqrt_eq_rpow,
    Complex.ofReal_cpow hx.le]
  rw [show (s+(1:ℂ)/2)-1 = (s-1)+(1/2 : ℝ) by push_cast; ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  ring

theorem pwGammaRaySource_mellinConvergent {s : ℂ} (hs : -(1/2:ℝ) < s.re) :
    MellinConvergent pwGammaRaySource s := by
  have hp : 0 < (s+(1:ℂ)/2).re := by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  apply IntegrableOn.congr_fun (Complex.GammaIntegral_convergent hp) _ measurableSet_Ioi
  intro x hx
  exact (pwGammaRaySource_mellin_integrand s hx).symm

theorem pwGammaRaySource_mellin {s : ℂ} (hs : -(1/2:ℝ) < s.re) :
    mellin pwGammaRaySource s = Complex.Gamma (s+1/2) := by
  have hp : 0 < (s+(1:ℂ)/2).re := by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  rw [Complex.Gamma_eq_integral hp]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaRaySource_mellin_integrand s hx)

def pwGammaMobiusMellinAtom (z s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)^(s-1)*pwGammaMobiusGlobalAtom z n x

theorem pwGammaMobiusMellinAtom_integrable (z : ℂ) {s : ℂ}
    (hs : -(1/2:ℝ) < s.re) (n : ℕ) :
    IntegrableOn (pwGammaMobiusMellinAtom z s n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : pwGammaMobiusMellinAtom z s 0 = 0 := by
      funext x
      simp [pwGammaMobiusMellinAtom, pwGammaMobiusGlobalAtom]
    rw [hz]
    exact integrable_zero ℝ ℂ (volume.restrict (Ioi (0:ℝ)))
  · have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hi := ((MellinConvergent.comp_mul_left hnr).mpr
      (pwGammaRaySource_mellinConvergent hs)).const_smul
        (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n:ℝ):ℂ)))
    change MellinConvergent (fun x => (((moebius n : ℤ):ℂ)*
      Complex.exp (-z*(Real.log (n:ℝ):ℂ))) • pwGammaRaySource ((n:ℝ)*x)) s
    exact hi

theorem pwGammaMobiusMellinAtom_integral (z : ℂ) {s : ℂ}
    (hs : -(1/2:ℝ) < s.re) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), pwGammaMobiusMellinAtom z s n x) =
      Complex.Gamma (s+1/2)*LSeries.term (fun m => ((moebius m : ℤ):ℂ)) (z+s) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusMellinAtom, pwGammaMobiusGlobalAtom]
  · have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    change mellin (fun x => (((moebius n : ℤ):ℂ)*Complex.exp (-z*(Real.log (n:ℝ):ℂ))) •
      pwGammaRaySource ((n:ℝ)*x)) s = _
    rw [mellin_const_smul, mellin_comp_mul_left _ _ hnr, pwGammaRaySource_mellin hs,
      smul_eq_mul, smul_eq_mul, LSeries.term_def₀ (by simp)]
    push_cast
    have he : Complex.exp (-z*Complex.log (n:ℂ)) = (n:ℂ)^(-z) := by
      rw [Complex.cpow_def_of_ne_zero hnc]
      congr 1
      ring
    rw [he, show -(z+s) = -z + -s by ring, Complex.cpow_add _ _ hnc]
    ring

private theorem pwGammaMobiusMellinAtom_norm_eq (z s : ℂ) {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    ‖pwGammaMobiusMellinAtom z s n x‖ =
      (‖((moebius n:ℤ):ℂ)‖*Real.exp (-z.re*Real.log (n:ℝ))*Real.sqrt (n:ℝ))*
        (x^((s.re+1/2)-1)*Real.exp (-((n:ℝ)*x))) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  rw [pwGammaMobiusMellinAtom, pwGammaMobiusGlobalAtom, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, pwGammaRaySource_eq (mul_pos hnr hx),
    Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp,
    Real.sqrt_mul hnr.le]
  simp only [Real.sqrt_eq_rpow]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show (s.re+(1:ℝ)/2)-1 = (s.re-1)+1/2 by ring, Real.rpow_add hx]
  ring

theorem pwGammaMobiusMellinAtom_norm_integral (z : ℂ) {s : ℂ}
    (hs : -(1/2:ℝ) < s.re) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), ‖pwGammaMobiusMellinAtom z s n x‖) =
      Real.Gamma (s.re+1/2)*‖LSeries.term (fun m => ((moebius m:ℤ):ℂ)) (z+s) n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusMellinAtom, pwGammaMobiusGlobalAtom]
  · have hnr : (0:ℝ) < n := by exact_mod_cast hn
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
      pwGammaMobiusMellinAtom_norm_eq z s hn hx), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < s.re+1/2) hnr,
      LSeries.norm_term_eq, if_neg hn.ne']
    have hp : Real.exp (-z.re*Real.log (n:ℝ))*Real.sqrt (n:ℝ)*
        (1/(n:ℝ))^(s.re+1/2) = 1/(n:ℝ)^(z+s).re := by
      rw [Real.sqrt_eq_rpow]
      simp only [one_div]
      rw [Real.inv_rpow hnr.le,
        ← Real.rpow_neg hnr.le]
      rw [show -z.re*Real.log (n:ℝ) = Real.log (n:ℝ)*(-z.re) by ring,
        ← Real.rpow_def_of_pos hnr]
      rw [← Real.rpow_add hnr, ← Real.rpow_add hnr]
      rw [show -z.re+(2:ℝ)⁻¹+ -(s.re+(2:ℝ)⁻¹) = -(z+s).re by
        simp only [Complex.add_re]
        ring]
      exact Real.rpow_neg hnr.le _
    calc
      _ = Real.Gamma (s.re+1/2)*‖((moebius n:ℤ):ℂ)‖*
          (Real.exp (-z.re*Real.log (n:ℝ))*Real.sqrt (n:ℝ)*(1/(n:ℝ))^(s.re+1/2)) := by ring
      _ = _ := by rw [hp]; ring

theorem pwGammaMobiusMellinAtom_absolute_admission (z : ℂ) {s : ℂ}
    (hs : -(1/2:ℝ) < s.re) :
    Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ), ‖pwGammaMobiusMellinAtom z s n x‖) ↔
      1 < (z+s).re := by
  simp_rw [pwGammaMobiusMellinAtom_norm_integral z hs]
  rw [summable_mul_left_iff (Real.Gamma_pos_of_pos (by linarith : 0 < s.re+1/2)).ne',
    summable_norm_iff]
  exact ArithmeticFunction.LSeriesSummable_moebius_iff

theorem pwGammaMobiusTilt_mellinConvergent {z s : ℂ}
    (hs : -(1/2:ℝ) < s.re) (hzs : 1 < (z+s).re) :
    MellinConvergent (pwGammaMobiusTilt z) s := by
  have hi := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusMellinAtom_integrable z hs)
    ((pwGammaMobiusMellinAtom_absolute_admission z hs).mpr hzs)
  change Integrable (fun x : ℝ => (x:ℂ)^(s-1)*pwGammaMobiusTilt z x)
    (volume.restrict (Ioi (0:ℝ)))
  simpa only [pwGammaMobiusMellinAtom, tsum_mul_left,
    ← pwGammaMobiusTilt_eq_global_atoms] using hi

theorem pwGammaMobiusTilt_mellin {z s : ℂ}
    (hs : -(1/2:ℝ) < s.re) (hzs : 1 < (z+s).re) :
    mellin (pwGammaMobiusTilt z) s = Complex.Gamma (s+1/2)*(riemannZeta (z+s))⁻¹ := by
  have he : ∀ x : ℝ, (x:ℂ)^(s-1)*pwGammaMobiusTilt z x =
      ∑' n, pwGammaMobiusMellinAtom z s n x := by
    intro x
    simp only [pwGammaMobiusMellinAtom, tsum_mul_left, ← pwGammaMobiusTilt_eq_global_atoms]
  simp only [mellin, smul_eq_mul, he]
  rw [← integral_tsum_of_summable_integral_norm (pwGammaMobiusMellinAtom_integrable z hs)
    ((pwGammaMobiusMellinAtom_absolute_admission z hs).mpr hzs)]
  simp only [pwGammaMobiusMellinAtom_integral z hs, tsum_mul_left,
    ← riemannZeta_inv_eq_tsum_term hzs]


end
end RHTower
