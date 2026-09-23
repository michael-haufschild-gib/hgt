import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaReciprocalEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceCurrent
import Mathlib.Analysis.Normed.Group.Tannery

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section

/-- Exact signed coefficient of the original nonzero reciprocal response modes. -/
def pwGammaMobiusReciprocalCoefficient (z : ℂ) (n : ℕ) : ℂ :=
  (((moebius (n+2) : ℤ) : ℂ)*Complex.exp (-z*(Real.log ((n+2 : ℕ) : ℝ) : ℂ)))*
    (Real.sqrt ((n+2 : ℕ) : ℝ) : ℂ)

def pwGammaMobiusReciprocalCurrentAtom (z : ℂ) (n : ℕ) (v : ℝ) : ℂ :=
  pwGammaMobiusReciprocalCoefficient z n*
    ((∫ h in Ioi (0 : ℝ), pwGammaReciprocalTranslationKernel ((n:ℝ)+1) v h : ℝ) : ℂ)

def pwGammaMobiusReciprocalEndpointAtom (z : ℂ) (n : ℕ) : ℂ :=
  pwGammaMobiusReciprocalCoefficient z n*
    ((∫ h in Ioi (0 : ℝ), pwGammaReciprocalEndpointKernel ((n:ℝ)+1) h : ℝ) : ℂ)

theorem pwGammaMobiusReciprocalCoefficient_norm_le {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N:ℝ)) (n : ℕ) :
    ‖pwGammaMobiusReciprocalCoefficient z n‖ ≤ ((n+2:ℕ):ℝ)^(N+1) := by
  have hn : (0:ℝ)<((n+2:ℕ):ℝ) := by positivity
  have hn1 : (1:ℝ)≤((n+2:ℕ):ℝ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hmu : ‖((moebius (n+2):ℤ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |moebius (n+2)| ≤ 1 from abs_moebius_le_one)
  have he : ‖Complex.exp (-z*(Real.log ((n+2:ℕ):ℝ):ℂ))‖ ≤ ((n+2:ℕ):ℝ)^N := by
    have hre : -z.re ≤ (N:ℝ) :=
      (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp ((N:ℝ)*Real.log ((n+2:ℕ):ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (Real.log_nonneg hn1))
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hn]
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  rw [pwGammaMobiusReciprocalCoefficient, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), pow_succ]
  calc
    _ ≤ (1*((n+2:ℕ):ℝ)^N)*((n+2:ℕ):ℝ) := by gcongr
    _ = _ := by ring

theorem pwGammaMobiusReciprocalCurrentAtom_tendsto_endpoint (z : ℂ) (n : ℕ) :
    Tendsto (pwGammaMobiusReciprocalCurrentAtom z n) (𝓝[>] (0:ℝ))
      (𝓝 (pwGammaMobiusReciprocalEndpointAtom z n)) := by
  unfold pwGammaMobiusReciprocalCurrentAtom pwGammaMobiusReciprocalEndpointAtom
  have ht := pwGammaReciprocalTranslationKernel_tendsto_endpoint_integral
    (show (0:ℝ)<(n:ℝ)+1 by positivity)
  simpa only [Function.comp_def] using
    ((Complex.continuous_ofReal.tendsto _).comp ht).const_mul (pwGammaMobiusReciprocalCoefficient z n)

theorem pwGammaMobiusReciprocalCurrentAtom_norm_le {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N:ℝ)) (n : ℕ) {v : ℝ} (hv : 0<v) (hv1 : v≤1) :
    ‖pwGammaMobiusReciprocalCurrentAtom z n v‖ ≤
      (2^(N+1)*((N+4).factorial:ℝ)*
        (∫ h in Ioi (0:ℝ), Real.exp (-h)*(1+h)^(N+2)))*(1/((n:ℝ)+1)^(2 : ℕ)) := by
  have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hI := (pwGammaReciprocalTranslationKernel_integral_pos ha hv).le
  have hJ : 0 ≤ ∫ h in Ioi (0:ℝ), Real.exp (-h)*(1+h)^(N+2) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro h hh
    have hh0 : 0<h := hh
    positivity
  rw [pwGammaMobiusReciprocalCurrentAtom, norm_mul, Complex.norm_real, Real.norm_of_nonneg hI]
  calc
    _ ≤ ((n+2:ℕ):ℝ)^(N+1)*
        ((((N+2+2).factorial:ℝ)/((n:ℝ)+1)^(N+2+1))*
          (∫ h in Ioi (0:ℝ), Real.exp (-h)*(1+h)^(N+2))) := by
      apply mul_le_mul (pwGammaMobiusReciprocalCoefficient_norm_le hz n)
        (pwGammaReciprocalTranslationKernel_integral_flat_bound (N+2) ha hv hv1) hI
      positivity
    _ ≤ (2*((n:ℝ)+1))^(N+1)*
        ((((N+4).factorial:ℝ)/((n:ℝ)+1)^(N+3))*
          (∫ h in Ioi (0:ℝ), Real.exp (-h)*(1+h)^(N+2))) := by
      gcongr
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    _ = _ := by
      rw [mul_pow, show N+3=(N+1)+2 by omega, pow_add]
      field_simp
      ring

private theorem pwGammaReciprocalSeries_bound_summable (N : ℕ) :
    Summable (fun n : ℕ =>
      (2^(N+1)*((N+4).factorial:ℝ)*
        (∫ h in Ioi (0:ℝ), Real.exp (-h)*(1+h)^(N+2)))*(1/((n:ℝ)+1)^(2 : ℕ))) := by
  have ht := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
  have hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^(2 : ℕ)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using ht
  exact hs.mul_left _

theorem pwGammaMobiusReciprocalEndpointAtom_summable (z : ℂ) :
    Summable (pwGammaMobiusReciprocalEndpointAtom z) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  apply (pwGammaReciprocalSeries_bound_summable N).of_norm_bounded
  intro n
  apply le_of_tendsto (pwGammaMobiusReciprocalCurrentAtom_tendsto_endpoint z n).norm
  filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ)<1 by positivity)] with v hv
  exact pwGammaMobiusReciprocalCurrentAtom_norm_le hN n hv.1 hv.2

theorem pwGammaMobiusReciprocalCurrentAtom_tsum_tendsto_endpoint (z : ℂ) :
    Tendsto (fun v : ℝ => ∑' n, pwGammaMobiusReciprocalCurrentAtom z n v)
      (𝓝[>] (0:ℝ)) (𝓝 (∑' n, pwGammaMobiusReciprocalEndpointAtom z n)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  apply tendsto_tsum_of_dominated_convergence (pwGammaReciprocalSeries_bound_summable N)
    (pwGammaMobiusReciprocalCurrentAtom_tendsto_endpoint z)
  filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ)<1 by positivity)] with v hv n
  exact pwGammaMobiusReciprocalCurrentAtom_norm_le hN n hv.1 hv.2

theorem pwGammaMobiusReciprocalCurrentAtom_source_eq (z : ℂ) (n : ℕ) {v : ℝ}
    (hv : 0<v) :
    (∫ h in Ioi (0:ℝ), pwGammaMobiusSameSourceAtom z (n+2) (h,v))/pwGammaRaySource v =
      pwGammaMobiusReciprocalCurrentAtom z n v := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh =>
    pwGammaMobiusSameSourceAtom_eq z (by omega : 0<n+2) hh.le hv)]
  simp only [integral_const_mul, integral_complex_ofReal]
  rw [pwGammaMobiusReciprocalCurrentAtom, pwGammaMobiusReciprocalCoefficient]
  have he : (((n+2:ℕ):ℝ)-1)=(n:ℝ)+1 := by push_cast; ring
  rw [he]
  field_simp [pwGammaRaySource_ne_zero]

theorem pwGammaMobiusSameSourceCurrent_normalized_eq_tsum (z : ℂ) {v : ℝ}
    (hv : 0<v) :
    pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v =
      ∑' n, pwGammaMobiusReciprocalCurrentAtom z n v := by
  have hs := (hasSum_integral_of_summable_integral_norm
    (fun n => pwGammaMobiusSameSourceAtom_integrable_section z n hv)
    (pwGammaMobiusSameSourceAtom_section_norm_integrals_summable z hv)).summable
  have htail := hs.sum_add_tsum_nat_add 2
  have h0 : (∫ h in Ioi (0:ℝ), pwGammaMobiusSameSourceAtom z 0 (h,v))=0 := by
    simp [pwGammaMobiusSameSourceAtom_zero]
  have h1 : (∫ h in Ioi (0:ℝ), pwGammaMobiusSameSourceAtom z 1 (h,v))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro h hh
    exact pwGammaMobiusSameSourceAtom_one z hh.le hv
  have ht : (∑' n, ∫ h in Ioi (0:ℝ), pwGammaMobiusSameSourceAtom z (n+2) (h,v))=
      ∑' n, ∫ h in Ioi (0:ℝ), pwGammaMobiusSameSourceAtom z n (h,v) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] using htail
  rw [pwGammaMobiusSameSourceCurrent_eq_tsum z hv, ← ht, ← tsum_div_const]
  exact tsum_congr (fun n => pwGammaMobiusReciprocalCurrentAtom_source_eq z n hv)

/-- Endpoint of the original complete signed arithmetic source current, for every z. -/
theorem pwGammaMobiusSameSourceCurrent_normalized_tendsto_endpoint (z : ℂ) :
    Tendsto (fun v : ℝ => pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v)
      (𝓝[>] (0:ℝ)) (𝓝 (∑' n, pwGammaMobiusReciprocalEndpointAtom z n)) := by
  apply (pwGammaMobiusReciprocalCurrentAtom_tsum_tendsto_endpoint z).congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (pwGammaMobiusSameSourceCurrent_normalized_eq_tsum z hv).symm

end
end RHTower
