import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCumulantConvolution
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockRegularity
/-!
# Exact actual-source clock Volterra identity

The full source response `t S(t²/16)` has its literal odd factorial expansion. Compact source
factorial envelopes justify the Cauchy product and the interval-integral interchange. The
normalized divided-power Beta convolution reduces each integrated coefficient to the actual
all-order theta cumulant recurrence, giving the exact weighted Borel kernel.
-/

open MeasureTheory Set intervalIntegral
namespace RHTower
noncomputable section

private def dividedPower (n : ℕ) (t : ℝ) : ℝ := t^n/(n.factorial:ℝ)
@[fun_prop] private theorem continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop
private theorem dividedPower_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (dividedPower (n+1)) (dividedPower n t) t := by
  have h := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert h using 1 <;> try rfl
  simp only [dividedPower, id_eq, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp
private theorem integral_dividedPower_convolution (p q : ℕ) (t : ℝ) :
    ∫ s in 0..t, dividedPower p s * dividedPower q (t-s) =
      dividedPower (p+q+1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=t) (fun x _ => dividedPower_deriv p x)
      (by exact (by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simpa [dividedPower] using h
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => dividedPower (q+1) (t-s))
        (-dividedPower q (t-x)) x := by
      intro x
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (dividedPower_deriv q (t-x)).comp x
          ((hasDerivAt_const x t).sub (hasDerivAt_id x))
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a:=0) (b:=t)
      (u:=fun s => dividedPower (q+1) (t-s)) (v:=dividedPower (p+1))
      (u':=fun s => -dividedPower q (t-s)) (v':=dividedPower p)
      (by fun_prop) (by fun_prop) (fun x _ => hu x)
      (fun x _ => dividedPower_deriv p x)
      ((by fun_prop : Continuous fun s => -dividedPower q (t-s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simp only [dividedPower, sub_self, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_mul, mul_zero, sub_zero, zero_sub] at h
    have hn : (fun x : ℝ => -(dividedPower q (t-x)) * dividedPower (p+1) x) =
        (fun x => -(dividedPower q (t-x) * dividedPower (p+1) x)) := by
      funext x
      ring
    change (∫x in 0..t, dividedPower (q+1) (t-x)*dividedPower p x) =
      -(∫x in 0..t, -(dividedPower q (t-x))*dividedPower (p+1) x) at h
    rw [hn, intervalIntegral.integral_neg, neg_neg] at h
    calc
      (∫s in 0..t, dividedPower p s * dividedPower (q+1) (t-s)) =
          ∫s in 0..t, dividedPower (q+1) (t-s)*dividedPower p s := by
        congr 1
        funext s
        ring
      _ = ∫s in 0..t, dividedPower q (t-s)*dividedPower (p+1) s := h
      _ = ∫s in 0..t, dividedPower (p+1) s * dividedPower q (t-s) := by
        congr 1
        funext s
        ring
      _ = dividedPower (p+q+1+1) t := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p+1)

/-- Response with the exact source-clock normalization. -/
def liEvenCrossActualClockResponse (t : ℝ) : ℝ :=
  t * liEvenCrossActualCurrentClockSeries (t^2/16)

/-- The source coefficient in the odd factorial response expansion. -/
def liEvenCrossActualClockResponseTerm (t : ℝ) (j : ℕ) : ℝ :=
  (-1:ℝ)^j * normalizedPrimeArchMoment j * t^(2*j+1) /
    ((2*j+1).factorial:ℝ)

private theorem responseTerm_eq_mul_clockTerm (t : ℝ) (j : ℕ) :
    liEvenCrossActualClockResponseTerm t j = t *
      ((-1:ℝ)^j * (16*(t^2/16))^j * normalizedPrimeArchMoment j /
        ((2*j+1).factorial:ℝ)) := by
  unfold liEvenCrossActualClockResponseTerm
  rw [show 16*(t^2/16)=t^2 by ring, ← pow_mul, pow_succ]
  ring

/-- Absolute convergence of the complete odd source response expansion. -/
theorem summable_liEvenCrossActualClockResponseTerm (t : ℝ) :
    Summable (liEvenCrossActualClockResponseTerm t) := by
  change Summable (fun j : ℕ => liEvenCrossActualClockResponseTerm t j)
  simp_rw [responseTerm_eq_mul_clockTerm]
  exact (summable_liEvenCrossActualCurrentClockSeries (t^2/16)).mul_left t

/-- The entire response is literally its full factorial source series. -/
theorem liEvenCrossActualClockResponse_eq_tsum (t : ℝ) :
    liEvenCrossActualClockResponse t = ∑' j : ℕ, liEvenCrossActualClockResponseTerm t j := by
  unfold liEvenCrossActualClockResponse liEvenCrossActualCurrentClockSeries
  simp_rw [responseTerm_eq_mul_clockTerm]
  exact (tsum_mul_left).symm

/-- Compact intervals admit one complete absolute source envelope. -/
theorem norm_liEvenCrossActualClockResponseTerm_le {t T : ℝ} (ht : |t| ≤ T) (j : ℕ) :
    ‖liEvenCrossActualClockResponseTerm t j‖ ≤ xiShiftAbsoluteMass 0 * T *
      ((T^2/150)^j / ((2*j+1).factorial:ℝ)) := by
  have hT : 0 ≤ T := le_trans (abs_nonneg t) ht
  have hw : |t^2/16| ≤ T^2/16 := by
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hbound := norm_liEvenCrossActualCurrentClockSeriesTerm_le_of_abs_le hw j
  rw [responseTerm_eq_mul_clockTerm, norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ T * (xiShiftAbsoluteMass 0 * ((16*(T^2/16)/150)^j /
      ((2*j+1).factorial:ℝ))) := by gcongr
    _ = _ := by
      rw [show 16*(T^2/16)=T^2 by ring]
      ring

/-- Response continuity uses the complete-source factorial envelope. -/
theorem continuous_liEvenCrossActualClockResponse : Continuous liEvenCrossActualClockResponse := by
  unfold liEvenCrossActualClockResponse
  exact continuous_id.mul (continuous_liEvenCrossActualCurrentClockSeries.comp (by fun_prop))
private theorem integral_responseTerm_mul_borelTerm (j k : ℕ) (t : ℝ) :
    ∫s in 0..t, liEvenCrossActualClockResponseTerm s j *
        liEvenCrossActualClockBorelTerm (t-s) k =
      ((-1:ℝ)^j * normalizedPrimeArchMoment j * thetaCuspNormalizedEvenMoment k /
        ((2*k).factorial:ℝ)) * dividedPower (2*j+1+2*k+1) t := by
  have heq : (fun s : ℝ => liEvenCrossActualClockResponseTerm s j *
        liEvenCrossActualClockBorelTerm (t-s) k) =
      (fun s => ((-1:ℝ)^j * normalizedPrimeArchMoment j * thetaCuspNormalizedEvenMoment k /
        ((2*k).factorial:ℝ)) *
          (dividedPower (2*j+1) s * dividedPower (2*k) (t-s))) := by
    funext s
    dsimp [liEvenCrossActualClockResponseTerm, liEvenCrossActualClockBorelTerm, dividedPower]
    field_simp
  rw [heq, intervalIntegral.integral_const_mul, integral_dividedPower_convolution]

private def responseKernelBlock (t s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), liEvenCrossActualClockResponseTerm s j *
    liEvenCrossActualClockBorelTerm (t-s) (n-j)

private theorem responseKernelBlock_hasSum (t s : ℝ) :
    HasSum (responseKernelBlock t s)
      (liEvenCrossActualClockResponse s * liEvenCrossActualClockBorelKernel (t-s)) := by
  rw [liEvenCrossActualClockResponse_eq_tsum, liEvenCrossActualClockBorelKernel]
  exact hasSum_sum_range_mul_of_summable_norm
    (summable_liEvenCrossActualClockResponseTerm s).norm
    (summable_liEvenCrossActualClockBorelTerm (t-s)).norm

private theorem integral_responseKernelBlock (n : ℕ) (t : ℝ) :
    ∫s in 0..t, responseKernelBlock t s n =
      (2*(n+1):ℝ)*liEvenCrossActualClockBorelTerm t (n+1) := by
  unfold responseKernelBlock
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by unfold liEvenCrossActualClockResponseTerm liEvenCrossActualClockBorelTerm
        fun_prop : Continuous (fun s => liEvenCrossActualClockResponseTerm s j *
          liEvenCrossActualClockBorelTerm (t-s) (n-j))).intervalIntegrable 0 t)]
  calc
    (∑j ∈ Finset.range (n+1), ∫s in 0..t, liEvenCrossActualClockResponseTerm s j *
        liEvenCrossActualClockBorelTerm (t-s) (n-j)) =
      (∑j ∈ Finset.range (n+1), (-1:ℝ)^j * normalizedPrimeArchMoment j *
        thetaCuspNormalizedEvenMoment (n-j) / ((2*(n-j)).factorial:ℝ)) *
          dividedPower (2*n+2) t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      rw [integral_responseTerm_mul_borelTerm,
        show 2*j+1+2*(n-j)+1=2*n+2 by omega]
    _ = ((2*n+2:ℝ) * thetaCuspNormalizedEvenMoment (n+1) /
        ((2*n+2).factorial:ℝ)) * dividedPower (2*n+2) t := by
      rw [liEvenCrossActualClock_signedCumulantConvolution]
    _ = _ := by
      unfold dividedPower liEvenCrossActualClockBorelTerm
      rw [show 2*(n+1)=2*n+2 by omega]
      field_simp

/-- The complete actual source response and Borel kernel satisfy the exact Volterra equation. -/
theorem liEvenCrossActualClockResponse_volterra {t : ℝ} (ht : 0 ≤ t) :
    ∫s in 0..t, liEvenCrossActualClockResponse s * liEvenCrossActualClockBorelKernel (t-s) =
      liEvenCrossActualClockBorelWeighted t := by
  have hA := xiShiftAbsoluteMass_nonneg 0
  let E : ℕ → ℝ := fun j => xiShiftAbsoluteMass 0 * t *
    ((t^2/150)^j / ((2*j+1).factorial:ℝ))
  let H : ℕ → ℝ := fun j => ((32/303:ℝ)*t^2)^j / (j.factorial:ℝ)
  let Q : ℕ → ℝ := fun n => ∑j ∈ Finset.range (n+1), E j * H (n-j)
  have hE : Summable E :=
    (summable_liEvenCrossActualCurrentClockFactorialEnvelope (t^2/150)
      (by positivity)).mul_left (xiShiftAbsoluteMass 0*t)
  have hH : Summable H := Real.summable_pow_div_factorial _
  have hQ : Summable Q := summable_sum_mul_range_of_summable_mul
    (hE.mul_of_nonneg hH (fun j => by dsimp [E]; positivity)
      (fun j => by dsimp [H]; positivity))
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Set.uIoc 0 t) :
      ‖responseKernelBlock t s n‖ ≤ Q n := by
    rw [Set.uIoc_of_le ht] at hs
    have hsabs : |s| ≤ t := by rw [abs_of_pos hs.1]; exact hs.2
    have htsabs : |t-s| ≤ t := by
      rw [abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]
    unfold responseKernelBlock Q
    calc
      _ ≤ ∑j ∈ Finset.range (n+1), ‖liEvenCrossActualClockResponseTerm s j *
          liEvenCrossActualClockBorelTerm (t-s) (n-j)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul (norm_liEvenCrossActualClockResponseTerm_le hsabs j)
          (norm_liEvenCrossActualClockBorelTerm_le htsabs (n-j))
          (norm_nonneg _) (by dsimp [E]; positivity)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:=0) (b:=t) (μ:=volume) (F:=fun n s => responseKernelBlock t s n)
    (f:=fun s => liEvenCrossActualClockResponse s * liEvenCrossActualClockBorelKernel (t-s))
    (fun n _ => Q n)
    (fun n => (by unfold responseKernelBlock liEvenCrossActualClockResponseTerm
                             liEvenCrossActualClockBorelTerm
                  fun_prop : Continuous (fun s => responseKernelBlock t s n)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun s hs => hbound n s hs))
    (Filter.Eventually.of_forall (fun s hs => hQ))
    (by exact intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun s _ => responseKernelBlock_hasSum t s))
  calc
    _ = ∑'n : ℕ, ∫s in 0..t, responseKernelBlock t s n := hsum.tsum_eq.symm
    _ = ∑'n : ℕ, (2*(n+1):ℝ)*liEvenCrossActualClockBorelTerm t (n+1) := by
      apply tsum_congr
      intro n
      exact integral_responseKernelBlock n t
    _ = _ := by
      simpa [liEvenCrossActualClockBorelWeighted] using
        (summable_liEvenCrossActualClockBorelWeightedTerm t).tsum_eq_zero_add.symm

/-- The weighted-series Volterra identity is exactly the source-kernel logarithmic derivative. -/
theorem liEvenCrossActualClockResponse_volterra_eq_mul_deriv {t : ℝ} (ht : 0 ≤ t) :
    ∫s in 0..t, liEvenCrossActualClockResponse s * liEvenCrossActualClockBorelKernel (t-s) =
      t * deriv liEvenCrossActualClockBorelKernel t := by
  rw [liEvenCrossActualClockResponse_volterra ht, liEvenCrossActualClockBorel_mul_deriv]
end
end RHTower
