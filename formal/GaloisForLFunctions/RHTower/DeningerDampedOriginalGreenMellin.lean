import GaloisForLFunctions.RHTower.DeningerWeightedOriginalGreenMellin
import GaloisForLFunctions.RHTower.DeningerDampedSourceMellinJets

/-!
# Actual damped source in the original prime Green domain

The literal future primitive is admitted by every positive weight in the source
strip. Its Mellin integral retains the original prime denominator. At damping
one the actual centered Xi response preserves every native zero order and
leading coefficient. No fixed physical-reader comparison is assumed.
-/

open Complex Filter Topology MeasureTheory
noncomputable section
namespace RHTower

private theorem mellinJet_zero_eq (s : ℂ) (f : ℝ → ℂ) :
    deningerMeyerStrongLogMellinJet 0 s f = (fun t : ℝ => Complex.exp (s * (t : ℂ)) * f t) := by
  funext t
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]

private theorem original_prime_log_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) :=
  Real.log_pos (by exact_mod_cast p.property.one_lt)

/-- Literal original, undamped, positive-translation Green primitive of the same source. -/
def deningerDampedOriginalPrimeGreen (a : {a : ℝ // 1/2 < a}) (p : Nat.Primes) : ℝ → ℂ :=
  deningerL1OriginalGreenSum (deningerDampedLogSource a) (Real.log (p : ℕ))

/-- The original prime period gives exactly the original prime power. -/
theorem deningerOriginalGreen_prime_weight (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℕ) : ℂ)) = (p : ℂ) ^ (-s) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by exact_mod_cast p.property.pos.le)]
  congr 1
  ring

/-- Admission is derived from the actual weighted source limit. -/
theorem deningerDampedOriginalPrimeGreen_weighted_integrable
    (a : {a : ℝ // 1/2 < a}) (p : Nat.Primes) (s : ℂ)
    (hs : 0 < s.re) (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    Integrable (deningerMeyerStrongLogMellinJet 0 s (deningerDampedOriginalPrimeGreen a p)) := by
  have hf : Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * deningerDampedLogSource a t) := by
    simpa only [mellinJet_zero_eq] using
      deningerDampedLogSource_mellin_integrable a s hs0 hs1
  simpa only [mellinJet_zero_eq, deningerDampedOriginalPrimeGreen]
    using deningerL1OriginalGreenSum_weighted_integrable (original_prime_log_pos p) hs hf

/-- Exact transform of the actual primitive, retaining the original prime factor. -/
theorem deningerDampedOriginalPrimeGreen_mellin (a : {a : ℝ // 1/2 < a})
    (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re)
    (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p) s =
      deningerMeyerStrongLogMellin (deningerDampedLogSource a) s / (1 - (p : ℂ) ^ (-s)) := by
  have hf : Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * deningerDampedLogSource a t) := by
    simpa only [mellinJet_zero_eq] using
      deningerDampedLogSource_mellin_integrable a s hs0 hs1
  simpa only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet, pow_zero, one_mul,
    deningerDampedOriginalPrimeGreen, deningerOriginalGreen_prime_weight] using
    deningerL1OriginalGreenSum_mellin (original_prime_log_pos p) hs hf

/-- No original prime denominator is zero in the admitted right half-plane. -/
theorem deningerOriginalGreen_prime_denominator_ne_zero (p : Nat.Primes)
    {s : ℂ} (hs : 0 < s.re) : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
  rw [← deningerOriginalGreen_prime_weight]
  exact deningerOriginalGreen_denominator_ne_zero (original_prime_log_pos p) hs

/-- The original Green transform retains the nonzero reading of the actual source. -/
theorem deningerDampedOriginalPrimeGreen_mellin_ne_zero (a : {a : ℝ // 1/2 < a})
    (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re)
    (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p) s ≠ 0 := by
  rw [deningerDampedOriginalPrimeGreen_mellin a p s hs hs0 hs1]
  exact div_ne_zero (deningerDampedLogSource_mellin_ne_zero a s hs0 hs1)
    (deningerOriginalGreen_prime_denominator_ne_zero p hs)

private theorem green_mellin_eventuallyEq (a : {a : ℝ // 1/2 < a})
    (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re)
    (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p) =ᶠ[𝓝 s]
      (fun z => deningerMeyerStrongLogMellin (deningerDampedLogSource a) z /
        (1 - Complex.exp (-z * (Real.log (p : ℕ) : ℂ)))) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ 1-a.val < z.re ∧ z.re < a.val} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
  filter_upwards [hopen.mem_nhds ⟨hs,hs0,hs1⟩] with z hz
  rw [deningerDampedOriginalPrimeGreen_mellin a p z hz.1 hz.2.1 hz.2.2,
    deningerOriginalGreen_prime_weight]

/-- Analyticity belongs to the literal integral, proved through its local admitted identity. -/
theorem deningerDampedOriginalPrimeGreen_mellin_analyticAt
    (a : {a : ℝ // 1/2 < a}) (p : Nat.Primes) (s : ℂ)
    (hs : 0 < s.re) (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    AnalyticAt ℂ (deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p)) s := by
  have hnum := analyticOnNhd_deningerDampedLogSource_mellin a s ⟨hs0,hs1⟩
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp (-z * (Real.log (p : ℕ) : ℂ))) s :=
    by fun_prop
  exact (hnum.div hden (deningerOriginalGreen_denominator_ne_zero (original_prime_log_pos p) hs)).congr
    (green_mellin_eventuallyEq a p s hs hs0 hs1).symm

/-- Every derivative of the literal Mellin integral is that of its original quotient. -/
theorem deningerDampedOriginalPrimeGreen_mellin_derivative
    (a : {a : ℝ // 1/2 < a}) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p)) s =
      iteratedDeriv k (fun z => deningerMeyerStrongLogMellin (deningerDampedLogSource a) z /
        (1 - Complex.exp (-z * (Real.log (p : ℕ) : ℂ)))) s :=
  (green_mellin_eventuallyEq a p s hs hs0 hs1).iteratedDeriv_eq k

private theorem green_xi_coordinate (rho : XiDivisorSupport) :
    (1/2 : ℂ) + xiSpectralPointSupport rho * I = (rho : ℂ) := by
  dsimp [xiSpectralPointSupport]
  rw [mul_assoc, neg_mul, I_mul_I, neg_neg, mul_one]
  ring

/-- Actual source admission at every native Xi point uses no critical-line assumption. -/
theorem deningerDampingOneOriginalPrimeGreen_xi_integrable (p : Nat.Primes)
    (rho : XiDivisorSupport) :
    Integrable (deningerMeyerStrongLogMellinJet 0 (rho : ℂ)
      (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p)) := by
  have h := xi_divisor_support_re_mem_open_unit rho
  exact deningerDampedOriginalPrimeGreen_weighted_integrable _ p rho h.1 (by simpa using h.1) h.2

private theorem green_xi_nonzero (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (rho : ℂ) ≠ 0 := by
  have h := xi_divisor_support_re_mem_open_unit rho
  exact deningerDampedOriginalPrimeGreen_mellin_ne_zero _ p rho h.1 (by simpa using h.1) h.2

private theorem green_xi_analytic (p : Nat.Primes) (rho : XiDivisorSupport) :
    AnalyticAt ℂ (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I)) (xiSpectralPointSupport rho) := by
  have h := xi_divisor_support_re_mem_open_unit rho
  have ha := deningerDampedOriginalPrimeGreen_mellin_analyticAt ⟨1,by norm_num⟩ p rho
    h.1 (by simpa using h.1) h.2
  rw [← green_xi_coordinate rho] at ha
  exact ha.comp (f := fun z : ℂ => 1/2+z*I) (x := xiSpectralPointSupport rho) (by fun_prop)

/-- The native Xi response of the literal original prime primitive. -/
def deningerDampingOneOriginalGreenXiResponse (p : Nat.Primes) (z : ℂ) : ℂ :=
  XiC z * deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I)

/-- The original primitive retains the exact native Xi order. -/
theorem deningerDampingOneOriginalGreenXiResponse_native_order (p : Nat.Primes)
    (rho : XiDivisorSupport) :
    analyticOrderAt (deningerDampingOneOriginalGreenXiResponse p) (xiSpectralPointSupport rho) =
      analyticOrderAt XiC (xiSpectralPointSupport rho) := by
  change analyticOrderAt (XiC * (fun z : ℂ => deningerMeyerStrongLogMellin
    (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I))) _ = _
  rw [analyticOrderAt_mul (XiC_analytic _ (Set.mem_univ _)) (green_xi_analytic p rho)]
  have hn : deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p)
      (1/2+xiSpectralPointSupport rho*I) ≠ 0 := by
    rw [green_xi_coordinate]
    exact green_xi_nonzero p rho
  have ho : analyticOrderAt (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I)) (xiSpectralPointSupport rho) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hn)
  rw [ho, add_zero]

/-- Every lower native derivative vanishes with its original multiplicity unchanged. -/
theorem deningerDampingOneOriginalGreenXiResponse_lower_jets (p : Nat.Primes)
    (rho : XiDivisorSupport) {k : ℕ} (hk : k < xiSupportMultiplicity rho) :
    iteratedDeriv k (deningerDampingOneOriginalGreenXiResponse p) (xiSpectralPointSupport rho) = 0 := by
  change iteratedDeriv k (XiC * (fun z : ℂ => deningerMeyerStrongLogMellin
    (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I))) _ = 0
  rw [iteratedDeriv_mul (XiC_analytic _ (Set.mem_univ _)).contDiffAt (green_xi_analytic p rho).contDiffAt]
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho (hjk.trans_lt hk)]
  simp

/-- The exact leading coefficient contains the original source and original prime denominator. -/
theorem deningerDampingOneOriginalGreenXiResponse_leading_jet (p : Nat.Primes)
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (deningerDampingOneOriginalGreenXiResponse p)
        (xiSpectralPointSupport rho) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
        (deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (rho : ℂ) /
          (1 - (p : ℂ) ^ (-(rho : ℂ)))) := by
  change iteratedDeriv (xiSupportMultiplicity rho) (XiC * (fun z : ℂ =>
    deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) (1/2+z*I))) _ = _
  rw [iteratedDeriv_mul (XiC_analytic _ (Set.mem_univ _)).contDiffAt (green_xi_analytic p rho).contDiffAt]
  rw [Finset.sum_eq_single (xiSupportMultiplicity rho)]
  · simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, iteratedDeriv_zero,
      one_mul, green_xi_coordinate]
    rw [deningerDampedOriginalPrimeGreen_mellin _ p rho
      (xi_divisor_support_re_mem_open_unit rho).1
      (by simpa using (xi_divisor_support_re_mem_open_unit rho).1)
      (xi_divisor_support_re_mem_open_unit rho).2]
  · intro j hj hjm
    have hj' : j < xiSupportMultiplicity rho := by
      rw [Finset.mem_range] at hj
      omega
    rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hj']
    simp
  · simp

/-- No actual native leading coefficient is lost in the original Green transform. -/
theorem deningerDampingOneOriginalGreenXiResponse_leading_jet_ne_zero (p : Nat.Primes)
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (deningerDampingOneOriginalGreenXiResponse p)
      (xiSpectralPointSupport rho) ≠ 0 := by
  rw [deningerDampingOneOriginalGreenXiResponse_leading_jet]
  exact mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (div_ne_zero (deningerDampingOne_source_xi_ne_zero rho)
      (deningerOriginalGreen_prime_denominator_ne_zero p (xi_divisor_support_re_mem_open_unit rho).1))

end RHTower
