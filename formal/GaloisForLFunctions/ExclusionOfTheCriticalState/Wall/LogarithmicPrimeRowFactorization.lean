import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LogarithmicTranslationsAgainstACausalKernel
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# The alternating prime row on the logarithmic axis

Finite divisor convolution becomes a translation sum at critical weight.
Testing the centred Mangoldt wave against an alternating row therefore
transfers the whole arithmetic convolution to the kernel of the state.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ExceptionalLayerTheory

/-- Dilation kernel normalized at the critical exponent. -/
def logDilationKernel (a : ArithmeticFunction ℝ) (w : ℝ → ℂ) (v : ℝ) : ℂ :=
  (Real.exp (-v/2):ℂ)*arithmeticKernel a w (Real.exp v)

/-- No positive divisor occurs before the logarithmic origin. -/
theorem logDilationKernel_of_neg (a : ArithmeticFunction ℝ) (w : ℝ → ℂ) {v : ℝ} (hv : v < 0) :
    logDilationKernel a w v = 0 := by
  simp [logDilationKernel,arithmeticKernel,Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hv)]

/-- The infinite translation sum at a real cutoff is finite pointwise. -/
theorem logDilationKernel_mul (a c : ArithmeticFunction ℝ) (w : ℝ → ℂ) (v : ℝ) :
    logDilationKernel (c*a) w v =
      ∑' n : ℕ, ((c n / Real.sqrt n:ℝ):ℂ)*logDilationKernel a w (v-Real.log n) := by
  let N := ⌊Real.exp v⌋₊
  rw [tsum_eq_sum (s := Icc 1 N) (fun n hn => ?_)]
  · rw [logDilationKernel,arithmeticKernel_mul,arithmeticKernel,Finset.mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hp : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    have hroot : Real.sqrt n = Real.exp (Real.log n/2) := by rw [Real.exp_half,Real.exp_log hp]
    have hnexp : Real.exp (v-Real.log n) = Real.exp v/n := by rw [Real.exp_sub,Real.exp_log hp]
    have he : Real.exp (-(v-Real.log n)/2) = Real.exp (-v/2)*Real.exp (Real.log n/2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [logDilationKernel,hnexp,hroot,he,Complex.ofReal_mul,Complex.ofReal_div,Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne']
  · rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    have hN : N < n := lt_of_not_ge fun hN => hn (mem_Icc.mpr ⟨h,hN⟩)
    have hnr : Real.exp v < (n:ℝ) := (Nat.floor_lt (Real.exp_pos v).le).1 hN
    rw [logDilationKernel_of_neg _ _ (sub_neg.2 ((Real.exp_lt_exp).1 (by rwa [Real.exp_log (by exact_mod_cast h : (0:ℝ) < n)]))),
      mul_zero]

/-- Von Mangoldt coefficients after subtracting one unit at each positive integer. -/
def centredMangoldtCoefficients : ArithmeticFunction ℝ := vonMangoldt - (zeta : ArithmeticFunction ℝ)

private theorem abs_centredMangoldtCoefficients {n : ℕ} (hn : 0 < n) :
    |centredMangoldtCoefficients n| ≤ Real.log n+1 := by
  have hz : (zeta : ArithmeticFunction ℝ) n = 1 := by
    simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply,hn.ne']
  rw [centredMangoldtCoefficients,ArithmeticFunction.sub_apply,hz]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,abs_one]
                                exact add_le_add ArithmeticFunction.vonMangoldt_le_log le_rfl)

private theorem centred_inverse_square_summable :
    Summable (fun n : ℕ => |centredMangoldtCoefficients n / Real.sqrt n|/(n:ℝ)^2) := by
  have hs := GaloisForLFunctions.summable_log_nat_div_sq.add
    ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hroot : 1 ≤ Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  change _ ≤ Real.log n/(n:ℝ)^2+1/(n:ℝ)^2
  rw [← add_div]
  exact div_le_div_of_nonneg_right ((div_le_self (abs_nonneg _) hroot).trans (abs_centredMangoldtCoefficients hn)) (sq_nonneg _)

/-- The centered row grows no faster than every exponential of rate above
one half and at most two. The same bound controls its negative-time tail. -/
theorem centredMangoldtWave_exponential_bound {Φ : ℝ → ℝ} {C σ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (hs : ∀ u, 0 ≤ u → Φ u=0)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 2) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ t| ≤ D*Real.exp (σ*t) := by
  let m := fun n : ℕ => (Real.log n+1)*(n:ℝ)^(-(σ+1/2))
  have hτ : 1 < σ+1/2 := by linarith
  have hm : Summable m := by
    have h := (_root_.RHTower.summable_log_natCast_pow_mul_rpow_neg 1 hτ).add
      (Real.summable_nat_rpow.2 (by linarith only [hτ] : -(σ+1/2) < -1))
    simpa only [m,add_mul,one_mul,pow_one,Pi.add_apply] using h
  have hpos (n : ℕ) : 0 ≤ m n :=
    mul_nonneg (by linarith only [Real.log_natCast_nonneg n]) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C*∑' n, m n,mul_nonneg hC (tsum_nonneg hpos),fun t => ?_⟩
  have hΦ (u : ℝ) : |Φ u| ≤ C*Real.exp (σ*u) := by
    by_cases hu : 0 ≤ u
    · rw [hs _ hu,abs_zero]; positivity
    · exact (hb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonpos_right hσ' (le_of_not_ge hu))) hC)
  let a := fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n*Φ (t-Real.log n)
  have hpoint (n : ℕ) : |a n| ≤ (C*Real.exp (σ*t))*m n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a,m]
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
    have he : Real.exp (σ*(t-Real.log n)) = Real.exp (σ*t)*(n:ℝ)^(-σ) := by
      rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
      congr 1; ring
    simp only [a,abs_mul,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (mul_le_mul (div_le_div_of_nonneg_right (abs_centredMangoldtCoefficients hn) (Real.sqrt_nonneg _))
      (hΦ _) (abs_nonneg _) (by positivity : 0 ≤ (Real.log n+1)/Real.sqrt n)).trans_eq
    rw [he,Real.sqrt_eq_rpow]
    have hr : (n:ℝ)^(-(σ+1/2))=(n:ℝ)^(-σ)*((n:ℝ)^(1/2:ℝ))⁻¹ := by
      rw [show -(σ+1/2)=-σ+-(1/2) by ring,Real.rpow_add hn0,Real.rpow_neg hn0.le (1/2:ℝ)]
    dsimp only [m]; rw [hr]; ring
  have hsum := hm.mul_left (C*Real.exp (σ*t))
  have ha : Summable a := Summable.of_norm_bounded hsum fun n => (Real.norm_eq_abs _).trans_le (hpoint n)
  change |∑' n, a n| ≤ _
  calc _ ≤ ∑' n, |a n| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ha.norm
    _ ≤ ∑' n : ℕ, (C*Real.exp (σ*t))*m n := ha.abs.tsum_le_tsum hpoint hsum
    _ = _ := by rw [tsum_mul_left]; ring

/-- The centred prime row tested by a bounded causal divisor kernel is exactly
the alternating prime-excess kernel tested by the confined state. -/
theorem integral_centredMangoldtWave_mul_alternating {Φ : ℝ → ℝ} (hm : Measurable Φ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (w : ℝ → ℂ)
    (hK : Measurable (logDilationKernel alternatingDivisorCoeff w)) {B : ℝ}
    (hb : ∀ v, ‖logDilationKernel alternatingDivisorCoeff w v‖ ≤ B) (T : ℝ) :
    let V := logShiftWave (fun n : ℕ => centredMangoldtCoefficients n / Real.sqrt n) Φ
    let g := fun t : ℝ => (V t:ℂ)*logDilationKernel alternatingDivisorCoeff w (T-t)
    let q := fun u : ℝ => (Φ u:ℂ)*logDilationKernel alternatingPrimeExcess w (T-u)
    Integrable g ∧ Integrable q ∧ (∫ t, g t) = ∫ u, q u := by
  have he : alternatingPrimeExcess = centredMangoldtCoefficients * alternatingDivisorCoeff :=
    mul_comm alternatingDivisorCoeff centredMangoldtCoefficients
  dsimp only
  simp only [he,logDilationKernel_mul]
  exact integral_logShiftWave_mul_causal (by simp) centred_inverse_square_summable hm hC hc hK
    (fun _ h => logDilationKernel_of_neg _ _ h) hb T

#print axioms integral_centredMangoldtWave_mul_alternating

end GaloisForLFunctions.ExclusionOfTheCriticalState
