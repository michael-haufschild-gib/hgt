import GaloisForLFunctions.RHTower.BurnolGraphActionFiltration
import GaloisForLFunctions.RHTower.PoissonPrimeClockCommutator
import GaloisForLFunctions.HTGeometry.GramDominatedSynthesis
import GaloisForLFunctions.HTGeometry.TranslationFrameOperators

/-!
# Native first-clock jets of the literal Burnol base source

The first native clock derivative has columns `λ_(p,e) f_(p,e)`. Its zero-depth Gram is
the bounded prime Poisson matrix multiplied by a normalized Cauchy correlation and divided
by four. Entrywise absolute domination therefore admits the complete prime coefficient
space. Positive-depth columns are square summable.
-/

open Complex Set MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- The literal first native clock jet, with no change to the source amplitude. -/
def burnolBaseFirstJetField (pe : RoutePPrimitiveIndex) : routePBurnolHalfLineL2 :=
  (xiGammaEulerPrimitiveLogFrequency pe : ℂ) • routePPrimitiveBurnolBaseField pe

theorem inner_routePPrimitiveBurnolBaseField (pe tau : RoutePPrimitiveIndex) :
    ⟪routePPrimitiveBurnolBaseField pe, routePPrimitiveBurnolBaseField tau⟫_ℂ =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1 (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency tau) 0 *
        star (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat tau)) := by
  unfold routePPrimitiveBurnolBaseField routePPrimitiveBurnolWindowFeatureLp
    routePBurnolHalfLineL2Of
  rw [inner_toLp_routePBurnolHalfLine_eq_pairing]
  simpa only [routePBurnolHalfLinePairing, sub_self] using
    integral_star_routePPrimitiveBurnolWindowFeature_mul pe tau 0 0

/-- The normalized Cauchy correlation of two positive prime clocks. -/
def burnolPrimeClockCorrelation (p q : Nat.Primes) : ℝ :=
  2 * Real.sqrt (stcClock p) * Real.sqrt (stcClock q) / (stcClock p + stcClock q)

theorem burnolPrimeClockCorrelation_pos (p q : Nat.Primes) :
    0 < burnolPrimeClockCorrelation p q := by
  unfold burnolPrimeClockCorrelation
  have hp := stcClock_pos' p
  have hq := stcClock_pos' q
  positivity

theorem burnolPrimeClockCorrelation_le_one (p q : Nat.Primes) :
    burnolPrimeClockCorrelation p q ≤ 1 := by
  rw [burnolPrimeClockCorrelation, div_le_one (add_pos (stcClock_pos' p) (stcClock_pos' q))]
  nlinarith [sq_nonneg (Real.sqrt (stcClock p) - Real.sqrt (stcClock q)),
    Real.sq_sqrt (stcClock_pos' p).le, Real.sq_sqrt (stcClock_pos' q).le]

/-- The exact real Gram matrix of the zero-depth first jet. -/
def burnolBaseFirstJetPrimeKernel (p q : Nat.Primes) : ℝ :=
  stcPrimePoissonKernel p q * burnolPrimeClockCorrelation p q / 4

theorem burnolBaseFirstJetPrimeKernel_nonneg (p q : Nat.Primes) :
    0 ≤ burnolBaseFirstJetPrimeKernel p q := by
  unfold burnolBaseFirstJetPrimeKernel stcPrimePoissonKernel
  have hp := stcClock_pos' p
  have hq := stcClock_pos' q
  have hr := burnolPrimeClockCorrelation_pos p q
  positivity

theorem inner_burnolBaseFirstJetField_prime (p q : Nat.Primes) :
    ⟪burnolBaseFirstJetField (p, 0), burnolBaseFirstJetField (q, 0)⟫_ℂ =
      (burnolBaseFirstJetPrimeKernel p q : ℂ) := by
  rw [burnolBaseFirstJetField, burnolBaseFirstJetField, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_routePPrimitiveBurnolBaseField]
  simp only [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat,
    zero_add, pow_one, finiteVonMangoldtDepthOneAmplitude,
    ArithmeticFunction.vonMangoldt_apply_prime p.property,
    ArithmeticFunction.vonMangoldt_apply_prime q.property,
    Complex.star_def, Complex.conj_ofReal,
    routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
  unfold burnolBaseFirstJetPrimeKernel stcPrimePoissonKernel burnolPrimeClockCorrelation stcClock
  rw [Real.sqrt_div (Real.log_pos (by exact_mod_cast p.property.one_lt)).le,
    Real.sqrt_div (Real.log_pos (by exact_mod_cast q.property.one_lt)).le]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, one_mul, one_pow, zero_mul, add_zero]
  ring

theorem norm_inner_burnolBaseFirstJetField_prime_le (p q : Nat.Primes) :
    ‖⟪burnolBaseFirstJetField (p, 0), burnolBaseFirstJetField (q, 0)⟫_ℂ‖ ≤
      stcPrimePoissonKernel p q := by
  rw [inner_burnolBaseFirstJetField_prime, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (burnolBaseFirstJetPrimeKernel_nonneg p q)]
  have hK : 0 ≤ stcPrimePoissonKernel p q := by
    unfold stcPrimePoissonKernel
    have hp := stcClock_pos' p
    have hq := stcClock_pos' q
    positivity
  have hr := burnolPrimeClockCorrelation_le_one p q
  have hmul := mul_le_mul_of_nonneg_left hr hK
  unfold burnolBaseFirstJetPrimeKernel
  nlinarith

/-- Bounded synthesis of every zero-depth prime first jet. -/
def burnolBaseFirstJetPrimeSynthesis :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] routePBurnolHalfLineL2 :=
  finiteGramSynthesis (fun p => burnolBaseFirstJetField (p, 0))

/-- Admission retains each original prime coefficient, including its phase. -/
theorem burnolBaseFirstJetPrimeSynthesis_single (p : Nat.Primes) (z : ℂ) :
    burnolBaseFirstJetPrimeSynthesis (lp.single 2 p z) = z • burnolBaseFirstJetField (p, 0) :=
  finiteGramSynthesis_single_of_majorant hasLpMatrix_poissonPrimeOp
    norm_inner_burnolBaseFirstJetField_prime_le p z

/-- Exact first-jet column energy at every prime and depth. -/
theorem norm_sq_burnolBaseFirstJetField (pe : RoutePPrimitiveIndex) :
    ‖burnolBaseFirstJetField pe‖ ^ 2 =
      (1 / 4 : ℝ) * (1 / (pe.1 : ℝ)) * ((pe.1 : ℝ)⁻¹) ^ pe.2 *
        ((pe.2 : ℝ) + 1)⁻¹ := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  have hk : (pe.2 : ℝ) + 1 ≠ 0 := by positivity
  have hfrequency : xiGammaEulerPrimitiveLogFrequency pe =
      ((pe.2 : ℝ) + 1) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat,
      Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [burnolBaseFirstJetField, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, norm_sq_routePPrimitiveBurnolBaseField,
    routePPrimitiveBaseCauchyCubicWeight, xiGammaEulerPrimitiveCubicLogMomentWeight,
    invNatLogSq, hfrequency]
  field_simp [hp.ne', hlog, hk]
  ring

/-- The critical prime slice has precisely the divergent reciprocal-prime energy. -/
theorem norm_sq_burnolBaseFirstJetField_prime (p : Nat.Primes) :
    ‖burnolBaseFirstJetField (p, 0)‖ ^ 2 = 1 / (4 * (p : ℝ)) := by
  rw [norm_sq_burnolBaseFirstJetField]
  simp
  ring

private theorem norm_sq_burnolBaseFirstJetField_succ_le (pe : RoutePPrimitiveIndex) :
    ‖burnolBaseFirstJetField (pe.1, pe.2 + 1)‖ ^ 2 ≤
      (1 / 4 : ℝ) * (1 / (pe.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pe.2 := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hp2 : (2 : ℝ) ≤ (pe.1 : ℝ) := by exact_mod_cast pe.1.property.two_le
  have hpInv : (pe.1 : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa using (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hpPow := pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hpInv pe.2
  have hkpos : 0 < (pe.2 : ℝ) + 2 := by positivity
  have hkInv : ((pe.2 : ℝ) + 2)⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hkpos zero_lt_one).2
      (by have := Nat.cast_nonneg (α := ℝ) pe.2; linarith)
  have heq : ‖burnolBaseFirstJetField (pe.1, pe.2 + 1)‖ ^ 2 =
      ((1 / 4 : ℝ) * (1 / (pe.1 : ℝ) ^ 2)) * ((pe.1 : ℝ)⁻¹) ^ pe.2 *
        ((pe.2 : ℝ) + 2)⁻¹ := by
    rw [norm_sq_burnolBaseFirstJetField]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [heq]
  calc
    _ ≤ ((1 / 4 : ℝ) * (1 / (pe.1 : ℝ) ^ 2)) * (1 / 2 : ℝ) ^ pe.2 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpPow (by positivity)) hkInv
        (inv_nonneg.mpr hkpos.le) (by positivity)
    _ = _ := mul_one _

/-- Every positive depth belongs to the square-summable part of the first jet. -/
theorem summable_norm_sq_burnolBaseFirstJetField_succ :
    Summable (fun pe : RoutePPrimitiveIndex =>
      ‖burnolBaseFirstJetField (pe.1, pe.2 + 1)‖ ^ 2) := by
  let major : RoutePPrimitiveIndex → ℝ := fun pe =>
    (1 / 4 : ℝ) * (1 / (pe.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pe.2
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg (show 0 ≤ major from fun pe => by dsimp [major]; positivity)]
    constructor
    · intro p
      change Summable (fun e : ℕ => (1 / 4 : ℝ) * (1 / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ e)
      exact (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num)).mul_left ((1 / 4 : ℝ) * (1 / (p : ℝ) ^ 2))
    · apply (burnolSummable_prime_one_div_sq.mul_left (1 / 2 : ℝ)).congr
      intro p
      dsimp [major]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  exact Summable.of_nonneg_of_le (fun pe => sq_nonneg _)
    norm_sq_burnolBaseFirstJetField_succ_le hmajor

private theorem isBesselFamily_burnolBaseFirstJet_prime :
    IsBesselFamily (fun p => burnolBaseFirstJetField (p, 0))
      (‖burnolBaseFirstJetPrimeSynthesis.adjoint‖ ^ 2) := by
  intro x
  have hcoeff (p : Nat.Primes) :
      (burnolBaseFirstJetPrimeSynthesis.adjoint x : Nat.Primes → ℂ) p =
        ⟪burnolBaseFirstJetField (p, 0), x⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right burnolBaseFirstJetPrimeSynthesis
      (lp.single 2 p 1) x
    rw [burnolBaseFirstJetPrimeSynthesis_single, one_smul, lp.inner_single_left,
      RCLike.inner_apply] at h
    simpa using h
  constructor
  · exact (summable_norm_sq_lp (burnolBaseFirstJetPrimeSynthesis.adjoint x)).congr
      (fun p => by rw [hcoeff])
  · simp only [← hcoeff, ← HilbertSchmidt.lp_norm_sq_eq]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (burnolBaseFirstJetPrimeSynthesis.adjoint.le_opNorm x) 2

/-- The complete literal prime-depth first jet is Bessel without a Hilbert–Schmidt premise. -/
theorem isBesselFamily_burnolBaseFirstJet :
    IsBesselFamily burnolBaseFirstJetField
      (‖burnolBaseFirstJetPrimeSynthesis.adjoint‖ ^ 2 +
        ∑' pe : RoutePPrimitiveIndex, ‖burnolBaseFirstJetField (pe.1, pe.2 + 1)‖ ^ 2) := by
  intro x
  have hzero := isBesselFamily_burnolBaseFirstJet_prime x
  have hplus := isBesselFamily_of_summable_sq summable_norm_sq_burnolBaseFirstJetField_succ x
  have hsplit := (summable_prod_of_nonneg (fun pe => sq_nonneg
    ‖⟪burnolBaseFirstJetField (pe.1, pe.2 + 1), x⟫_ℂ‖)).mp hplus.1
  have hrow (p : Nat.Primes) :
      Summable (fun n : ℕ => ‖⟪burnolBaseFirstJetField (p, n), x⟫_ℂ‖ ^ 2) :=
    (summable_nat_add_iff 1).mp (hsplit.1 p)
  have hrow_eq (p : Nat.Primes) :
      ∑' n : ℕ, ‖⟪burnolBaseFirstJetField (p, n), x⟫_ℂ‖ ^ 2 =
        ‖⟪burnolBaseFirstJetField (p, 0), x⟫_ℂ‖ ^ 2 +
          ∑' n : ℕ, ‖⟪burnolBaseFirstJetField (p, n + 1), x⟫_ℂ‖ ^ 2 :=
    tsum_eq_zero_add' (hsplit.1 p)
  have hsum : Summable (fun pe : RoutePPrimitiveIndex =>
      ‖⟪burnolBaseFirstJetField pe, x⟫_ℂ‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun pe => sq_nonneg _)).mpr
    refine ⟨hrow, ?_⟩
    exact (hzero.1.add hsplit.2).congr (fun p => (hrow_eq p).symm)
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod]
  simp only [hrow_eq]
  rw [hzero.1.tsum_add hsplit.2, ← hplus.1.tsum_prod, add_mul]
  exact add_le_add hzero.2 hplus.2

/-- Bounded first-jet synthesis on the entire original coefficient Hilbert space. -/
def burnolBaseFirstJetSynthesis :
    lp (fun _ : RoutePPrimitiveIndex => ℂ) 2 →L[ℂ] routePBurnolHalfLineL2 :=
  (besselAnalysis burnolBaseFirstJetField isBesselFamily_burnolBaseFirstJet).adjoint

theorem burnolBaseFirstJetSynthesis_single (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolBaseFirstJetSynthesis (lp.single 2 pe z) = z • burnolBaseFirstJetField pe :=
  besselSynthesis_single isBesselFamily_burnolBaseFirstJet pe z

end
end RHTower
