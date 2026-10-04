import GaloisForLFunctions.HTGeometry.BorelSeriesConvolution
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The actual theta generator, its reciprocal germ and the causal resolvent

Let `ν_j = R_j/R_0` be the normalized actual theta moments and `c_j = ν_j/(2j)!`.  Then
`c_0 = 1`, `0 < c_j ≤ (32/303)^j/j!`, and the ordinary generator

```text
Φ(z) = Σ_j c_j z^{2j} = XiC(-i z)/XiC(0)
```

is the normalized actual Xi function.  The reciprocal coefficients `a_0 = 1`,
`a_n = -Σ_{k=1}^n c_k a_{n-k}` satisfy `|a_n| ≤ 2^{-n}` and `Φ(z) A(z) = 1` for `|z|² < 2`, where
`A(z) = Σ a_n z^{2n}` is the reciprocal germ.

On real clocks the literal Borel kernel is `B = Σ c_j t^{2j}/(2j)!` and `K = B' =
Σ_m c_{m+1} t^{2m+1}/(2m+1)!`.  The entire odd function `u(t) = Σ a_n t^{2n+1}/(2n+1)!` solves the
causal equation `u + u⋆K = t` exactly (Borel coefficients multiply as the germ identity
`Φ·A = 1`), and the resolvent `r = -u''` solves `r + r⋆K = K` with `r(0) = 0`, `r'(0) = ν_1/2`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Generator coefficients -/

/-- `c_j = ν_j/(2j)!`. -/
def liClockThetaGeneratorCoeff (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment j / ((2 * j).factorial : ℝ)

theorem liClockThetaGeneratorCoeff_zero : liClockThetaGeneratorCoeff 0 = 1 := by
  simp [liClockThetaGeneratorCoeff, thetaCuspNormalizedEvenMoment_zero]

theorem liClockThetaGeneratorCoeff_pos (j : ℕ) : 0 < liClockThetaGeneratorCoeff j :=
  div_pos (thetaCuspNormalizedEvenMoment_pos j) (by exact_mod_cast Nat.factorial_pos _)

theorem liClockThetaGeneratorCoeff_one :
    liClockThetaGeneratorCoeff 1 = thetaCuspNormalizedEvenMoment 1 / 2 := by
  simp [liClockThetaGeneratorCoeff]

theorem liClockThetaGeneratorCoeff_le (j : ℕ) :
    liClockThetaGeneratorCoeff j ≤ (32 / 303 : ℝ) ^ j / (j.factorial : ℝ) := by
  have hν := thetaCuspNormalizedEvenMoment_le_score_factorial j
  have hf : (j.factorial : ℝ) * (j.factorial : ℝ) ≤ ((2 * j).factorial : ℝ) := by
    have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add j j)
    rw [← two_mul] at this
    exact_mod_cast this
  have hj : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  unfold liClockThetaGeneratorCoeff
  rw [div_le_div_iff₀ (by exact_mod_cast Nat.factorial_pos _) hj]
  calc thetaCuspNormalizedEvenMoment j * (j.factorial : ℝ) ≤
      (32 / 303 : ℝ) ^ j * (j.factorial : ℝ) * (j.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hν hj.le
    _ ≤ (32 / 303 : ℝ) ^ j * ((2 * j).factorial : ℝ) := by
        rw [mul_assoc]; gcongr

theorem geometricCoeffBound_liClockThetaGeneratorCoeff :
    GeometricCoeffBound liClockThetaGeneratorCoeff 1 (32 / 303) := by
  intro j
  rw [abs_of_pos (liClockThetaGeneratorCoeff_pos j), one_mul]
  refine (liClockThetaGeneratorCoeff_le j).trans ?_
  exact div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos j))

/-! ## Reciprocal coefficients -/

/-- The reciprocal coefficients `a_0 = 1`, `a_{n+1} = -Σ_{k ≤ n} c_{k+1} a_{n-k}`. -/
def liClockThetaReciprocalCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 => -∑ k : Fin (n + 1), liClockThetaGeneratorCoeff (k + 1) * liClockThetaReciprocalCoeff (n - k)
decreasing_by all_goals simp_wf

@[simp] theorem liClockThetaReciprocalCoeff_zero : liClockThetaReciprocalCoeff 0 = 1 := by
  rw [liClockThetaReciprocalCoeff]

theorem liClockThetaReciprocalCoeff_succ (n : ℕ) :
    liClockThetaReciprocalCoeff (n + 1) =
      -∑ k ∈ Finset.range (n + 1),
        liClockThetaGeneratorCoeff (k + 1) * liClockThetaReciprocalCoeff (n - k) := by
  rw [liClockThetaReciprocalCoeff, Fin.sum_univ_eq_sum_range
    (fun k => liClockThetaGeneratorCoeff (k + 1) * liClockThetaReciprocalCoeff (n - k))]

/-- **Germ identity.**  `Σ_{k ≤ n} c_k a_{n-k} = δ_{n0}`. -/
theorem liClockThetaReciprocalCoeff_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), liClockThetaGeneratorCoeff k * liClockThetaReciprocalCoeff (n - k) =
      if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp [liClockThetaGeneratorCoeff_zero]
  · rw [Finset.sum_range_succ', liClockThetaGeneratorCoeff_zero, one_mul, Nat.sub_zero,
      liClockThetaReciprocalCoeff_succ]
    simp only [Nat.add_sub_add_right, if_neg (Nat.succ_ne_zero n)]
    ring

theorem liClockThetaReciprocalCoeff_one :
    liClockThetaReciprocalCoeff 1 = -(thetaCuspNormalizedEvenMoment 1 / 2) := by
  rw [liClockThetaReciprocalCoeff_succ]
  simp [liClockThetaGeneratorCoeff_one]

private theorem exp_sixtyFour_lt_two : Real.exp (64 / 303) < 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 64 / 303) (by norm_num) (by norm_num)
  calc Real.exp (64 / 303) < 1 / (1 - 64 / 303) := h
    _ < 2 := by norm_num

/-- **Geometric reciprocal bound.**  `|a_n| ≤ 2^{-n}`. -/
theorem abs_liClockThetaReciprocalCoeff_le (n : ℕ) :
    |liClockThetaReciprocalCoeff n| ≤ (1 / 2 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp
    · rw [liClockThetaReciprocalCoeff_succ, abs_neg]
      have hterm : ∀ k ∈ Finset.range (n + 1),
          |liClockThetaGeneratorCoeff (k + 1) * liClockThetaReciprocalCoeff (n - k)| ≤
            (1 / 2 : ℝ) ^ (n + 1) * ((64 / 303 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [abs_mul, abs_of_pos (liClockThetaGeneratorCoeff_pos _)]
        have h1 := liClockThetaGeneratorCoeff_le (k + 1)
        have h2 := ih (n - k) (by omega)
        have hsplit : (1 / 2 : ℝ) ^ (n + 1) * ((64 / 303 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) =
            (32 / 303 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) * (1 / 2) ^ (n - k) := by
          have : n + 1 = (n - k) + (k + 1) := by omega
          have h64 : (1 / 2 : ℝ) ^ (k + 1) * (64 / 303) ^ (k + 1) = (32 / 303) ^ (k + 1) := by
            rw [← mul_pow]; norm_num
          rw [this, pow_add, ← h64]
          ring
        rw [hsplit]
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      calc |∑ k ∈ Finset.range (n + 1),
            liClockThetaGeneratorCoeff (k + 1) * liClockThetaReciprocalCoeff (n - k)| ≤
          ∑ k ∈ Finset.range (n + 1), |liClockThetaGeneratorCoeff (k + 1) *
            liClockThetaReciprocalCoeff (n - k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (n + 1),
            (1 / 2 : ℝ) ^ (n + 1) * ((64 / 303 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = (1 / 2 : ℝ) ^ (n + 1) * ∑ k ∈ Finset.range (n + 1),
            (64 / 303 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) := by rw [Finset.mul_sum]
        _ ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 := by
            gcongr
            have hexp := Real.sum_le_exp_of_nonneg (x := 64 / 303) (by norm_num) (n + 2)
            rw [Finset.sum_range_succ'] at hexp
            simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hexp
            linarith [exp_sixtyFour_lt_two]
        _ = (1 / 2 : ℝ) ^ (n + 1) := mul_one _

theorem geometricCoeffBound_liClockThetaReciprocalCoeff :
    GeometricCoeffBound liClockThetaReciprocalCoeff 1 (1 / 2) := fun n => by
  rw [one_mul]; exact abs_liClockThetaReciprocalCoeff_le n

/-! ## The generator and the reciprocal germ -/

/-- The ordinary actual generator `Φ(z) = Σ c_j z^{2j}`. -/
def liClockThetaGenerator (z : ℂ) : ℂ := ∑' j : ℕ, (liClockThetaGeneratorCoeff j : ℂ) * z ^ (2 * j)

/-- The reciprocal germ `A(z) = Σ a_n z^{2n}`. -/
def liClockThetaReciprocalGerm (z : ℂ) : ℂ :=
  ∑' n : ℕ, (liClockThetaReciprocalCoeff n : ℂ) * z ^ (2 * n)

theorem summable_norm_liClockThetaGeneratorTerm (z : ℂ) :
    Summable (fun j : ℕ => ‖(liClockThetaGeneratorCoeff j : ℂ) * z ^ (2 * j)‖) := by
  refine (Real.summable_pow_div_factorial ((32 / 303) * ‖z‖ ^ 2)).of_nonneg_of_le
    (fun j => norm_nonneg _) fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (liClockThetaGeneratorCoeff_pos j).le,
    norm_pow, pow_mul, mul_pow, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (liClockThetaGeneratorCoeff_le j) (by positivity)

theorem summable_norm_liClockThetaReciprocalTerm {z : ℂ} (hz : ‖z‖ ^ 2 < 2) :
    Summable (fun n : ℕ => ‖(liClockThetaReciprocalCoeff n : ℂ) * z ^ (2 * n)‖) := by
  refine (summable_geometric_of_lt_one (r := ‖z‖ ^ 2 / 2) (by positivity)
    (by rw [div_lt_one (by norm_num)]; exact hz)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, pow_mul]
  calc |liClockThetaReciprocalCoeff n| * (‖z‖ ^ 2) ^ n ≤ (1 / 2 : ℝ) ^ n * (‖z‖ ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right (abs_liClockThetaReciprocalCoeff_le n) (by positivity)
    _ = (‖z‖ ^ 2 / 2) ^ n := by rw [← mul_pow]; ring

/-- **Reciprocal germ.**  `Φ(z) A(z) = 1` for `|z|² < 2`. -/
theorem liClockThetaGenerator_mul_reciprocalGerm {z : ℂ} (hz : ‖z‖ ^ 2 < 2) :
    liClockThetaGenerator z * liClockThetaReciprocalGerm z = 1 := by
  unfold liClockThetaGenerator liClockThetaReciprocalGerm
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_liClockThetaGeneratorTerm z) (summable_norm_liClockThetaReciprocalTerm hz)]
  have hn : ∀ n : ℕ, (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (liClockThetaGeneratorCoeff kl.1 : ℂ) * z ^ (2 * kl.1) *
        ((liClockThetaReciprocalCoeff kl.2 : ℂ) * z ^ (2 * kl.2))) =
      if n = 0 then 1 else 0 := by
    intro n
    have hconv := liClockThetaReciprocalCoeff_convolution n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => (liClockThetaGeneratorCoeff k : ℂ) * z ^ (2 * k) *
        ((liClockThetaReciprocalCoeff l : ℂ) * z ^ (2 * l))) n]
    have hpow : ∀ k ∈ Finset.range n.succ,
        (liClockThetaGeneratorCoeff k : ℂ) * z ^ (2 * k) *
          ((liClockThetaReciprocalCoeff (n - k) : ℂ) * z ^ (2 * (n - k))) =
        ((liClockThetaGeneratorCoeff k * liClockThetaReciprocalCoeff (n - k) : ℝ) : ℂ) *
          z ^ (2 * n) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have : 2 * n = 2 * k + 2 * (n - k) := by omega
      rw [this, pow_add]; push_cast; ring
    rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul, ← Complex.ofReal_sum, hconv]
    split_ifs with h <;> simp [h]
  simp_rw [hn]
  rw [tsum_eq_single 0 (fun n hn => if_neg hn)]
  simp

theorem liClockThetaGenerator_zero : liClockThetaGenerator 0 = 1 := by
  unfold liClockThetaGenerator
  rw [tsum_eq_single 0]
  · simp [liClockThetaGeneratorCoeff_zero]
  · intro j hj; simp [hj]

/-- `Φ(z) ≠ 0` on the reciprocal disk `|z|² < 2`. -/
theorem liClockThetaGenerator_ne_zero {z : ℂ} (hz : ‖z‖ ^ 2 < 2) : liClockThetaGenerator z ≠ 0 := by
  intro h
  have := liClockThetaGenerator_mul_reciprocalGerm hz
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- **Normalized actual Xi.**  `Φ(z) = XiC(-i z)/XiC(0)`. -/
theorem liClockThetaGenerator_eq_XiC (z : ℂ) :
    liClockThetaGenerator z = XiC (-I * z) / XiC 0 := by
  have hX0 : XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) := by
    simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  have hR0 : (thetaCuspRawEvenMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast thetaCuspRawEvenMoment_zero_pos.ne'
  have htaylor := Complex.taylorSeries_eq_of_entire' (c := 0) (z := -I * z) XiC_differentiable
  set f : ℕ → ℂ := fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n XiC 0 * (-I * z - 0) ^ n
  have hhas : HasSum f (XiC (-I * z)) := by
    have h := Complex.hasSum_taylorSeries_of_entire XiC_differentiable 0 (-I * z)
    refine h.congr_fun fun n => ?_
    simp only [f, smul_eq_mul]; ring
  have hodd : ∀ k, f (2 * k + 1) = 0 := by
    intro k
    simp only [f]
    rw [iteratedDeriv_XiC_odd_zero ⟨k, rfl⟩]; ring
  have heven : ∀ k, f (2 * k) =
      (thetaCuspRawEvenMoment 0 : ℂ) * ((liClockThetaGeneratorCoeff k : ℂ) * z ^ (2 * k)) := by
    intro k
    simp only [f, liClockThetaGeneratorCoeff, thetaCuspNormalizedEvenMoment]
    rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment k, sub_zero, mul_pow, pow_mul, pow_mul]
    have hI : (-I) ^ 2 = (-1 : ℂ) := by rw [neg_sq, I_sq]
    rw [hI]
    push_cast
    field_simp
    ring_nf
    rw [Even.neg_one_pow ⟨k, by ring⟩, mul_one]
  have hsumm := hhas.summable
  have hse : Summable fun k => f (2 * k) := hsumm.comp_injective (fun a b h => by omega)
  have hso : Summable fun k => f (2 * k + 1) := hsumm.comp_injective (fun a b h => by omega)
  have htot := tsum_even_add_odd hse hso
  rw [hhas.tsum_eq] at htot
  simp_rw [hodd, heven, tsum_zero, add_zero] at htot
  rw [tsum_mul_left] at htot
  rw [hX0, ← htot]
  unfold liClockThetaGenerator
  field_simp

/-- The zeros of `Φ` are exactly the rotated spectral points `z = i·α_q`. -/
theorem liClockThetaGenerator_eq_zero_iff (z : ℂ) :
    liClockThetaGenerator z = 0 ↔ ∃ q : XiZeroCopy, xiSpectralPoint q = -I * z := by
  have hX0 : XiC 0 ≠ 0 := by
    have : XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) := by
      simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
    rw [this]; exact_mod_cast thetaCuspRawEvenMoment_zero_pos.ne'
  rw [liClockThetaGenerator_eq_XiC, div_eq_zero_iff, or_iff_left hX0,
    XiC_eq_zero_iff_exists_xiZeroCopy]

/-! ## The literal kernel and the causal inverse -/

/-- The literal Borel kernel is the even factorial series of the generator coefficients. -/
theorem liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries (t : ℝ) :
    liEvenCrossActualClockBorelKernel t = evenFactorialSeries liClockThetaGeneratorCoeff t := by
  unfold liEvenCrossActualClockBorelKernel evenFactorialSeries liEvenCrossActualClockBorelTerm
  refine tsum_congr fun j => ?_
  unfold liClockThetaGeneratorCoeff
  have : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- The literal kernel `K = B' = Σ_m c_{m+1} t^{2m+1}/(2m+1)!`. -/
def liClockThetaKernel (t : ℝ) : ℝ :=
  oddFactorialSeries (fun m => liClockThetaGeneratorCoeff (m + 1)) t

theorem geometricCoeffBound_liClockThetaKernelCoeff :
    GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1)) (32 / 303) (32 / 303) := by
  have h := geometricCoeffBound_liClockThetaGeneratorCoeff.shift
  simpa using h

theorem hasDerivAt_liEvenCrossActualClockBorelKernel_eq (t : ℝ) :
    HasDerivAt liEvenCrossActualClockBorelKernel (liClockThetaKernel t) t := by
  have hB : liEvenCrossActualClockBorelKernel = evenFactorialSeries liClockThetaGeneratorCoeff :=
    funext liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries
  rw [hB]
  exact hasDerivAt_evenFactorialSeries (by norm_num) geometricCoeffBound_liClockThetaGeneratorCoeff t

theorem deriv_liEvenCrossActualClockBorelKernel_eq (t : ℝ) :
    deriv liEvenCrossActualClockBorelKernel t = liClockThetaKernel t :=
  (hasDerivAt_liEvenCrossActualClockBorelKernel_eq t).deriv

/-- The odd entire causal inverse `u(t) = Σ a_n t^{2n+1}/(2n+1)!`. -/
def liClockThetaCausalInverse (t : ℝ) : ℝ := oddFactorialSeries liClockThetaReciprocalCoeff t

private theorem oddFactorialSeries_single_zero (t : ℝ) :
    oddFactorialSeries (fun m => if m = 0 then (1 : ℝ) else 0) t = t := by
  unfold oddFactorialSeries
  rw [tsum_eq_single 0]
  · simp
  · intro m hm; simp [hm]

private theorem oddFactorialSeries_add {a b : ℕ → ℝ} {M R M' R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R') (t : ℝ) :
    oddFactorialSeries a t + oddFactorialSeries b t = oddFactorialSeries (a + b) t := by
  unfold oddFactorialSeries
  rw [← Summable.tsum_add (summable_oddFactorialSeries_term hR ha t)
    (summable_oddFactorialSeries_term hR' hb t)]
  refine tsum_congr fun j => ?_
  simp only [Pi.add_apply]; ring

/-- **Exact causal inverse.**  `u + u⋆K = t` at every real clock. -/
theorem liClockThetaCausalInverse_volterra (t : ℝ) :
    liClockThetaCausalInverse t + volterraConv liClockThetaCausalInverse liClockThetaKernel t = t := by
  have ha := geometricCoeffBound_liClockThetaReciprocalCoeff
  have hc := geometricCoeffBound_liClockThetaKernelCoeff
  have ha' : GeometricCoeffBound liClockThetaReciprocalCoeff 1 (32 / 303 + 1 / 2) := fun n =>
    (ha n).trans (by gcongr; norm_num)
  have hc' : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1)) (32 / 303)
      (32 / 303 + 1 / 2) := fun n => (hc n).trans (by gcongr; norm_num)
  have hconv := volterraConv_oddFactorialSeries ha' hc' (by norm_num) t
  unfold liClockThetaCausalInverse liClockThetaKernel
  rw [hconv]
  have hcb : GeometricCoeffBound (oddConvCoeff liClockThetaReciprocalCoeff
      (fun m => liClockThetaGeneratorCoeff (m + 1))) (1 * (32 / 303) / (2 * (32 / 303 + 1 / 2)))
      (2 * (32 / 303 + 1 / 2)) := by
    intro m
    rw [oddConvCoeff_eq_borelConvCoeff]
    exact geometricCoeffBound_borelConvCoeff ha' hc' (by norm_num) m
  rw [oddFactorialSeries_add (by norm_num) (by norm_num) ha hcb]
  have hcoeff : (liClockThetaReciprocalCoeff + oddConvCoeff liClockThetaReciprocalCoeff
      (fun m => liClockThetaGeneratorCoeff (m + 1))) = fun m => if m = 0 then (1 : ℝ) else 0 := by
    funext m
    rcases m with _ | m
    · simp [oddConvCoeff]
    · simp only [Pi.add_apply, oddConvCoeff, if_neg (Nat.succ_ne_zero m)]
      have hid := liClockThetaReciprocalCoeff_convolution (m + 1)
      rw [if_neg (Nat.succ_ne_zero m), Finset.sum_range_succ', liClockThetaGeneratorCoeff_zero,
        one_mul, Nat.sub_zero] at hid
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun p q => liClockThetaReciprocalCoeff p * liClockThetaGeneratorCoeff (q + 1)) m]
      have hrefl := Finset.sum_range_reflect
        (fun k => liClockThetaReciprocalCoeff k * liClockThetaGeneratorCoeff (m - k + 1)) (m + 1)
      have hrw : ∀ j ∈ Finset.range (m + 1),
          liClockThetaReciprocalCoeff (m + 1 - 1 - j) *
            liClockThetaGeneratorCoeff (m - (m + 1 - 1 - j) + 1) =
          liClockThetaGeneratorCoeff (j + 1) * liClockThetaReciprocalCoeff (m + 1 - (j + 1)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show m + 1 - 1 - j = m + 1 - (j + 1) by omega,
          show m - (m + 1 - (j + 1)) + 1 = j + 1 by omega]
        ring
      rw [Finset.sum_congr rfl hrw] at hrefl
      simp only [Nat.succ_eq_add_one] at hrefl ⊢
      linarith
  rw [hcoeff, oddFactorialSeries_single_zero]

/-- The causal resolvent `r = -u''`. -/
def liClockThetaResolvent (t : ℝ) : ℝ :=
  oddFactorialSeries (fun m => -liClockThetaReciprocalCoeff (m + 1)) t

theorem iteratedDeriv_two_liClockThetaCausalInverse (t : ℝ) :
    iteratedDeriv 2 liClockThetaCausalInverse t = -liClockThetaResolvent t := by
  unfold liClockThetaCausalInverse liClockThetaResolvent
  rw [iteratedDeriv_two_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockThetaReciprocalCoeff]
  unfold oddFactorialSeries
  rw [← tsum_neg]
  refine tsum_congr fun j => ?_
  ring

/-- **Causal resolvent.**  `r + r⋆K = K` at every real clock. -/
theorem liClockThetaResolvent_volterra (t : ℝ) :
    liClockThetaResolvent t + volterraConv liClockThetaResolvent liClockThetaKernel t =
      liClockThetaKernel t := by
  have ha := geometricCoeffBound_liClockThetaReciprocalCoeff
  have hρ : GeometricCoeffBound (fun m => -liClockThetaReciprocalCoeff (m + 1)) (1 / 2)
      (32 / 303 + 1 / 2) := by
    intro m
    rw [abs_neg]
    refine (abs_liClockThetaReciprocalCoeff_le (m + 1)).trans ?_
    rw [pow_succ']
    gcongr; norm_num
  have hc := geometricCoeffBound_liClockThetaKernelCoeff
  have hc' : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1)) (32 / 303)
      (32 / 303 + 1 / 2) := fun n => (hc n).trans (by gcongr; norm_num)
  have hconv := volterraConv_oddFactorialSeries hρ hc' (by norm_num) t
  unfold liClockThetaResolvent liClockThetaKernel
  rw [hconv]
  have hcb : GeometricCoeffBound (oddConvCoeff (fun m => -liClockThetaReciprocalCoeff (m + 1))
      (fun m => liClockThetaGeneratorCoeff (m + 1)))
      (1 / 2 * (32 / 303) / (2 * (32 / 303 + 1 / 2))) (2 * (32 / 303 + 1 / 2)) := by
    intro m
    rw [oddConvCoeff_eq_borelConvCoeff]
    exact geometricCoeffBound_borelConvCoeff hρ hc' (by norm_num) m
  rw [oddFactorialSeries_add (by norm_num) (by norm_num) hρ hcb]
  congr 1
  funext m
  rcases m with _ | m
  · simp only [Pi.add_apply, oddConvCoeff, add_zero, zero_add, liClockThetaReciprocalCoeff_one,
      liClockThetaGeneratorCoeff_one, neg_neg]
  · simp only [Pi.add_apply, oddConvCoeff]
    have hid := liClockThetaReciprocalCoeff_convolution (m + 2)
    rw [if_neg (by omega), Finset.sum_range_succ', Finset.sum_range_succ,
      liClockThetaGeneratorCoeff_zero, one_mul, Nat.sub_zero, Nat.sub_self] at hid
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => -liClockThetaReciprocalCoeff (p + 1) * liClockThetaGeneratorCoeff (q + 1)) m]
    have hrefl := Finset.sum_range_reflect
      (fun k => liClockThetaReciprocalCoeff (k + 1) * liClockThetaGeneratorCoeff (m - k + 1)) (m + 1)
    have hrw : ∀ j ∈ Finset.range (m + 1),
        liClockThetaReciprocalCoeff (m + 1 - 1 - j + 1) *
          liClockThetaGeneratorCoeff (m - (m + 1 - 1 - j) + 1) =
        liClockThetaGeneratorCoeff (j + 1) * liClockThetaReciprocalCoeff (m + 2 - (j + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show m + 1 - 1 - j + 1 = m + 2 - (j + 1) by omega,
        show m - (m + 1 - 1 - j) + 1 = j + 1 by omega]
      ring
    rw [Finset.sum_congr rfl hrw] at hrefl
    have hneg : (∑ k ∈ Finset.range (m + 1),
        -liClockThetaReciprocalCoeff (k + 1) * liClockThetaGeneratorCoeff (m - k + 1)) =
        -∑ k ∈ Finset.range (m + 1),
          liClockThetaReciprocalCoeff (k + 1) * liClockThetaGeneratorCoeff (m - k + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hneg]
    rw [liClockThetaReciprocalCoeff_zero, mul_one] at hid
    rw [show m + 1 + 1 = m + 2 by ring]
    linarith

theorem liClockThetaResolvent_zero : liClockThetaResolvent 0 = 0 := by
  unfold liClockThetaResolvent oddFactorialSeries
  simp

theorem hasDerivAt_liClockThetaResolvent_zero :
    HasDerivAt liClockThetaResolvent (thetaCuspNormalizedEvenMoment 1 / 2) 0 := by
  have hρ : GeometricCoeffBound (fun m => -liClockThetaReciprocalCoeff (m + 1)) (1 / 2) (1 / 2) := by
    intro m
    rw [abs_neg]
    refine (abs_liClockThetaReciprocalCoeff_le (m + 1)).trans_eq ?_
    rw [pow_succ']
  have h := hasDerivAt_oddFactorialSeries (by norm_num) hρ 0
  have hv : evenFactorialSeries (fun m => -liClockThetaReciprocalCoeff (m + 1)) 0 =
      thetaCuspNormalizedEvenMoment 1 / 2 := by
    unfold evenFactorialSeries
    rw [tsum_eq_single 0]
    · simp [liClockThetaReciprocalCoeff_one]
    · intro m hm; simp [hm]
  rw [hv] at h
  exact h

theorem continuous_liClockThetaKernel : Continuous liClockThetaKernel :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockThetaKernelCoeff t).continuousAt

theorem continuous_liClockThetaResolvent : Continuous liClockThetaResolvent := by
  have hρ : GeometricCoeffBound (fun m => -liClockThetaReciprocalCoeff (m + 1)) (1 / 2) (1 / 2) := by
    intro m
    rw [abs_neg]
    refine (abs_liClockThetaReciprocalCoeff_le (m + 1)).trans_eq ?_
    rw [pow_succ']
  exact continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_oddFactorialSeries (by norm_num) hρ t).continuousAt

end RHTower
