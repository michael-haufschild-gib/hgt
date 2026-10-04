import GaloisForLFunctions.RHTower.LiClockThetaResolventSignedMass
import GaloisForLFunctions.HTGeometry.BorelSeriesSmoothRatio

/-!
# The causal inverse of the theta kernel and its growth class

For every continuous input `h`, the function `h - r ⋆ h` is the unique continuous solution of
`y + y ⋆ K = h` (`r` the theta resolvent).  If `h` is smooth with every positive exponential type,
then every fixed derivative of `h - r ⋆ h` is `O(e^{δ|t|})` for one `δ < 1/300`: the resolvent
carries such a rate, `(r ⋆ h)^{(m)} = Σ_{j<m} r^{(j)}(0) h^{(m-1-j)} + r^{(m)} ⋆ h`, and the
compact convolution costs one factor `|t|`, absorbed by a slightly larger rate.

The literal kernel `K`, its clock companion `h = K + tK'` and the derivative forcing `g` are odd
factorial series whose coefficients beat every geometric rate, so all have every positive
exponential type.  The clock response satisfies `F + F ⋆ K = K + tK'` (differentiate
`F ⋆ B = tK`), hence `F = h - r ⋆ h`, and `-S = g - r ⋆ g`; both lie in the strict sub-`1/300`
class.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

/-! ## Growth classes -/

/-- Every fixed derivative is `O(e^{ε|t|})` for every `ε > 0`. -/
def LiClockEveryExpType (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv m f t| ≤ C * Real.exp (ε * |t|)

/-- Every fixed derivative is `O(e^{δ|t|})` for one `0 < δ < 1/300`. -/
def LiClockSubGammaClass (f : ℝ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 300 ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ t : ℝ,
    |iteratedDeriv m f t| ≤ C * Real.exp (δ * |t|)

theorem liClockEveryExpType_borelSeries {b : ℕ → ℝ}
    (hb : ∀ R : ℝ, 0 < R → ∃ M, GeometricCoeffBound b M R) : LiClockEveryExpType (borelSeries b) := by
  intro ε hε m
  obtain ⟨M, hM⟩ := hb ε hε
  rw [iteratedDeriv_borelSeries hM]
  exact ⟨M * ε ^ m, fun t => abs_borelSeries_le (geometricCoeffBound_shift_add hM m) t⟩

theorem natCast_succ_le_four_pow (m : ℕ) : ((m : ℝ) + 1) ≤ 4 ^ m := by
  have h : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h' : (2 : ℝ) ^ m ≤ 4 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have : ((m : ℝ) + 1) ≤ (2 : ℝ) ^ m := by exact_mod_cast h
  linarith

theorem geometricCoeffBound_oddSpread_of_le {a : ℕ → ℝ} {M ρ : ℝ} (hρ : 0 < ρ)
    (ha : ∀ k, |a k| ≤ M * ρ ^ (2 * k)) : GeometricCoeffBound (oddSpread a) (M / ρ) ρ := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  intro N
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · rw [hk, oddSpread_two_mul, abs_zero]; positivity
  · rw [hk, oddSpread_two_mul_add_one]
    refine (ha k).trans (le_of_eq ?_)
    rw [pow_succ]; field_simp

theorem geometricCoeffBound_evenSpread_of_le {a : ℕ → ℝ} {M ρ : ℝ} (hρ : 0 < ρ)
    (ha : ∀ k, |a k| ≤ M * ρ ^ (2 * k)) : GeometricCoeffBound (evenSpread a) M ρ := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  intro N
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · rw [hk, evenSpread_two_mul]; exact ha k
  · rw [hk, evenSpread_two_mul_add_one, abs_zero]; positivity

/-! ## Smoothness of the theta functions -/

theorem contDiff_liClockThetaResolvent : ContDiff ℝ ∞ liClockThetaResolvent := by
  rw [liClockThetaResolvent_eq_borelSeries]
  exact contDiff_borelSeries (a := fun n => -liClockThetaInverseBorelCoeff (n + 2)) (M := 1) (R := 1)
    fun n => by rw [abs_neg]; simpa using geometricCoeffBound_liClockThetaInverseBorelCoeff (n + 2)

theorem contDiff_liClockThetaKernel : ContDiff ℝ ∞ liClockThetaKernel :=
  contDiff_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockThetaGeneratorCoeff.shift

/-! ## Every positive exponential type -/

theorem liClockEveryExpType_liClockThetaKernel : LiClockEveryExpType liClockThetaKernel := by
  rw [liClockThetaKernel_eq_borelSeries]
  exact liClockEveryExpType_borelSeries fun R hR =>
    ⟨_, geometricCoeffBound_oddSpread_liClockThetaKernelCoeff hR⟩

/-- The clock companion `h = K + tK'`, whose odd coefficients are `(2m+2) c_{m+1}`. -/
def liClockThetaClockInput (t : ℝ) : ℝ :=
  liClockThetaKernel t + t * liClockThetaKernelDeriv t

theorem liClockThetaClockInput_eq_oddFactorialSeries :
    liClockThetaClockInput =
      oddFactorialSeries fun m => (2 * m + 2) * liClockThetaGeneratorCoeff (m + 1) := by
  funext t
  have hc1 := geometricCoeffBound_liClockThetaGeneratorCoeff.shift
  have h1 := (summable_oddFactorialSeries_term (by norm_num) hc1 t).hasSum
  have h2 := ((summable_evenFactorialSeries_term (by norm_num) hc1 t).hasSum).mul_left t
  unfold liClockThetaClockInput liClockThetaKernel liClockThetaKernelDeriv oddFactorialSeries
    evenFactorialSeries
  rw [← (h1.add h2).tsum_eq]
  refine tsum_congr fun m => ?_
  have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem abs_kernelClockCoeff_le_pow {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    |(2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1)| ≤
      2 * ρ ^ 2 * Real.exp (32 / (303 * ρ ^ 2)) * (2 * ρ) ^ (2 * m) := by
  have hc := liClockThetaGeneratorCoeff_le_pow hρ (m + 1)
  have h4 := natCast_succ_le_four_pow m
  rw [abs_of_pos (by have := liClockThetaGeneratorCoeff_pos (m + 1); positivity)]
  have e : (2 * ρ) ^ (2 * m) = 4 ^ m * ρ ^ (2 * m) := by
    rw [mul_pow, pow_mul]; norm_num
  rw [e]
  calc (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1) ≤
      (2 * (m : ℝ) + 2) * (Real.exp (32 / (303 * ρ ^ 2)) * ρ ^ (2 * (m + 1))) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2 * ρ ^ 2 * Real.exp (32 / (303 * ρ ^ 2)) * (((m : ℝ) + 1) * ρ ^ (2 * m)) := by
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]; ring
    _ ≤ 2 * ρ ^ 2 * Real.exp (32 / (303 * ρ ^ 2)) * (4 ^ m * ρ ^ (2 * m)) := by
        gcongr

theorem liClockEveryExpType_liClockThetaClockInput : LiClockEveryExpType liClockThetaClockInput := by
  have hb : GeometricCoeffBound (fun m => (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1))
      (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2))) 1 := fun m => by
    have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
    simpa using this
  rw [liClockThetaClockInput_eq_oddFactorialSeries, oddFactorialSeries_eq_borelSeries (by norm_num) hb]
  refine liClockEveryExpType_borelSeries fun R hR => ⟨_, geometricCoeffBound_oddSpread_of_le
    (M := 2 * (R / 2) ^ 2 * Real.exp (32 / (303 * (R / 2) ^ 2))) hR fun k => ?_⟩
  have := abs_kernelClockCoeff_le_pow (ρ := R / 2) (by positivity) k
  rw [show 2 * (R / 2) = R by ring] at this
  exact this

theorem contDiff_liClockThetaClockInput : ContDiff ℝ ∞ liClockThetaClockInput := by
  rw [liClockThetaClockInput_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (M := 2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)))
    (R := 1) (by norm_num) fun m => by
      have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
      simpa using this

theorem abs_liClockThetaForcingTaylorCoeff_le_pow {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    |liClockThetaForcingTaylorCoeff k| ≤
      Real.exp (32 / (303 * ρ ^ 2)) * (2 * ρ ^ 2 + 2 * liEvenCrossActualClockGreenRate ^ 2 +
        normalizedPrimeArchMoment 0) * (2 * ρ) ^ (2 * k) := by
  rw [liClockThetaForcingTaylorCoeff_eq]
  have hM0 : 0 < normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact thetaCuspNormalizedEvenMoment_pos 1
  have hω : 0 ≤ liEvenCrossActualClockGreenRate ^ 2 := sq_nonneg _
  have h1 := abs_kernelClockCoeff_le_pow hρ k
  have hck := liClockThetaGeneratorCoeff_le_pow hρ k
  have hc0 := (liClockThetaGeneratorCoeff_pos k).le
  have h4 := natCast_succ_le_four_pow k
  set E := Real.exp (32 / (303 * ρ ^ 2))
  have hE : 0 < E := Real.exp_pos _
  have e : (2 * ρ) ^ (2 * k) = 4 ^ k * ρ ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
  have hρk : 0 ≤ ρ ^ (2 * k) := by positivity
  have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  rw [abs_of_nonneg (by have := liClockThetaGeneratorCoeff_pos (k + 1); positivity), e] at h1
  have h2 : (2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
      liClockThetaGeneratorCoeff k ≤
        (2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * E *
          (4 ^ k * ρ ^ (2 * k)) := by
    have hk : (k : ℝ) ≤ 4 ^ k := by linarith
    calc (2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
          liClockThetaGeneratorCoeff k ≤
        (2 * 4 ^ k * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0 * 4 ^ k) *
          (E * ρ ^ (2 * k)) := by
          gcongr
          · nlinarith
      _ = _ := by ring
  have hX : 0 ≤ (2 * (k : ℝ) + 2) * liClockThetaGeneratorCoeff (k + 1) := by
    have := liClockThetaGeneratorCoeff_pos (k + 1); positivity
  have hY : 0 ≤ (2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
      liClockThetaGeneratorCoeff k := by positivity
  rw [e]
  calc |(2 * (k : ℝ) + 2) * liClockThetaGeneratorCoeff (k + 1) -
        (2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
          liClockThetaGeneratorCoeff k| ≤
      |(2 * (k : ℝ) + 2) * liClockThetaGeneratorCoeff (k + 1)| +
        |(2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
          liClockThetaGeneratorCoeff k| := abs_sub _ _
    _ = (2 * (k : ℝ) + 2) * liClockThetaGeneratorCoeff (k + 1) +
        (2 * (k : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
          liClockThetaGeneratorCoeff k := by rw [abs_of_nonneg hX, abs_of_nonneg hY]
    _ ≤ 2 * ρ ^ 2 * E * (4 ^ k * ρ ^ (2 * k)) +
        (2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * E *
          (4 ^ k * ρ ^ (2 * k)) := add_le_add h1 h2
    _ = _ := by ring

theorem liClockEveryExpType_liClockThetaForcingInput :
    LiClockEveryExpType liClockThetaForcingInput := by
  have hb : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
      ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
    fun m => by rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m
  unfold liClockThetaForcingInput
  rw [show (oddFactorialSeries fun m => -liClockThetaForcingTaylorCoeff (m + 1)) =
    borelSeries _ from oddFactorialSeries_eq_borelSeries (by norm_num) hb]
  refine liClockEveryExpType_borelSeries fun R hR => ⟨_, geometricCoeffBound_oddSpread_of_le hR
    (M := Real.exp (32 / (303 * (R / 2) ^ 2)) * (2 * (R / 2) ^ 2 +
      2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * R ^ 2)
    fun k => ?_⟩
  rw [abs_neg]
  have := abs_liClockThetaForcingTaylorCoeff_le_pow (ρ := R / 2) (by positivity) (k + 1)
  rw [show 2 * (R / 2) = R by ring, show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc |liClockThetaForcingTaylorCoeff (k + 1)| ≤ _ := this
    _ = _ := by ring

theorem contDiff_liClockThetaForcingInput : ContDiff ℝ ∞ liClockThetaForcingInput :=
  contDiff_oddFactorialSeries (R := 1) (by norm_num) fun m => by
    rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m

/-! ## The general causal inverse -/

/-- The causal inverse `h - r ⋆ h` of an input `h`. -/
def liClockThetaInverse (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  h t - volterraConv liClockThetaResolvent h t

/-- `y = h - r ⋆ h` solves `y + y ⋆ K = h`. -/
theorem liClockThetaInverse_volterra {h : ℝ → ℝ} (hh : Continuous h) (t : ℝ) :
    liClockThetaInverse h t + volterraConv (liClockThetaInverse h) liClockThetaKernel t = h t := by
  have hr := continuous_liClockThetaResolvent
  have hK := continuous_liClockThetaKernel
  have hrh : Continuous (volterraConv liClockThetaResolvent h) := continuous_volterraConv hr hh
  have hres : ∀ u, volterraConv liClockThetaKernel liClockThetaResolvent u =
      liClockThetaKernel u - liClockThetaResolvent u := fun u => by
    have := liClockThetaResolvent_volterra u
    rw [volterraConv_comm] at this
    linarith
  have h1 : volterraConv (liClockThetaInverse h) liClockThetaKernel t =
      volterraConv liClockThetaKernel h t -
        volterraConv liClockThetaKernel (volterraConv liClockThetaResolvent h) t := by
    rw [volterraConv_comm]
    exact volterraConv_sub_right hK hh hrh t
  have h2 : volterraConv liClockThetaKernel (volterraConv liClockThetaResolvent h) t =
      volterraConv (volterraConv liClockThetaKernel liClockThetaResolvent) h t :=
    (volterraConv_assoc hK hr hh t).symm
  have h3 : volterraConv (volterraConv liClockThetaKernel liClockThetaResolvent) h t =
      volterraConv liClockThetaKernel h t - volterraConv liClockThetaResolvent h t := by
    rw [show volterraConv liClockThetaKernel liClockThetaResolvent =
      fun u => liClockThetaKernel u - liClockThetaResolvent u from funext hres,
      volterraConv_comm, volterraConv_sub_right hh hK hr, volterraConv_comm h,
      volterraConv_comm h]
  rw [h1, h2, h3]
  unfold liClockThetaInverse
  ring

/-- **Uniqueness.**  Every continuous solution of `y + y ⋆ K = h` is `h - r ⋆ h`. -/
theorem eq_liClockThetaInverse {h y : ℝ → ℝ} (hh : Continuous h) (hy : Continuous y)
    (hyh : ∀ t, y t + volterraConv y liClockThetaKernel t = h t) : y = liClockThetaInverse h := by
  have hK := continuous_liClockThetaKernel
  have hX : Continuous (liClockThetaInverse h) :=
    hh.sub (continuous_volterraConv continuous_liClockThetaResolvent hh)
  have hD : Continuous fun s => y s - liClockThetaInverse h s := hy.sub hX
  have hzero := eq_zero_of_mul_eq_volterraConv (k := fun u => -liClockThetaKernel u) (c := 1)
    one_ne_zero hK.neg hD fun t => by
      rw [volterraConv_neg_left, one_mul, volterraConv_sub_right hK hy hX,
        volterraConv_comm liClockThetaKernel y, volterraConv_comm liClockThetaKernel]
      linarith [hyh t, liClockThetaInverse_volterra hh t]
  funext t
  have := congrFun hzero t
  simp only [Pi.zero_apply] at this
  linarith

private theorem abs_volterraConv_le_exp {f g : ℝ → ℝ} {Cf Cg a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ t, |f t| ≤ Cf * Real.exp (a * |t|)) (hgb : ∀ t, |g t| ≤ Cg * Real.exp (b * |t|))
    (t : ℝ) : |volterraConv f g t| ≤ Cf * Cg * Real.exp ((a + b) * |t|) * |t| := by
  unfold volterraConv
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := Cf * Cg * Real.exp ((a + b) * |t|)) (f := fun s => f (t - s) * g s) (fun s hs => by
      have hs' : s ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hs
      have h1 : |t - s| ≤ |t| := by
        rcases le_total 0 t with h0 | h0
        · rw [Set.uIcc_of_le h0] at hs'
          rw [abs_le, abs_of_nonneg h0]; constructor <;> linarith [hs'.1, hs'.2]
        · rw [Set.uIcc_of_ge h0] at hs'
          rw [abs_le, abs_of_nonpos h0]; constructor <;> linarith [hs'.1, hs'.2]
      have h2 : |s| ≤ |t| := by
        rcases le_total 0 t with h0 | h0
        · rw [Set.uIcc_of_le h0] at hs'
          rw [abs_le, abs_of_nonneg h0]; constructor <;> linarith [hs'.1, hs'.2]
        · rw [Set.uIcc_of_ge h0] at hs'
          rw [abs_le, abs_of_nonpos h0]; constructor <;> linarith [hs'.1, hs'.2]
      rw [Real.norm_eq_abs, abs_mul]
      calc |f (t - s)| * |g s| ≤ (Cf * Real.exp (a * |t|)) * (Cg * Real.exp (b * |t|)) := by
            refine mul_le_mul ((hfb _).trans ?_) ((hgb _).trans ?_) (abs_nonneg _) (by positivity)
            · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
                (mul_le_mul_of_nonneg_left h1 ha)) hCf
            · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
                (mul_le_mul_of_nonneg_left h2 hb)) hCg
        _ = Cf * Cg * Real.exp ((a + b) * |t|) := by
            rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf)
  rw [Real.norm_eq_abs, sub_zero] at h
  exact h

private theorem contDiff_volterraConv_resolvent {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (volterraConv liClockThetaResolvent h) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_volterraConv contDiff_liClockThetaResolvent hh m]
  have hd : ∀ k, Differentiable ℝ (iteratedDeriv k h) := fun k =>
    hh.differentiable_iteratedDeriv k (natCast_lt_infty k)
  refine Differentiable.add ?_ ?_
  · exact Differentiable.fun_sum fun j _ => (hd _).const_mul _
  · intro t
    exact (hasDerivAt_volterraConv (f := iteratedDeriv m liClockThetaResolvent)
      (f' := iteratedDeriv (m + 1) liClockThetaResolvent) (g := h)
      (fun s => by
        rw [iteratedDeriv_succ]
        exact ((contDiff_liClockThetaResolvent.differentiable_iteratedDeriv m
          (natCast_lt_infty m)) s).hasDerivAt)
      (contDiff_liClockThetaResolvent.continuous_iteratedDeriv (m + 1) (natCast_lt_infty _).le)
      hh.continuous t).differentiableAt

/-- **Growth propagation.**  A smooth input of every positive exponential type has its causal
inverse in the strict sub-`1/300` class. -/
theorem liClockSubGammaClass_liClockThetaInverse {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hexp : LiClockEveryExpType h) : LiClockSubGammaClass (liClockThetaInverse h) := by
  obtain ⟨δ0, hδ0, hδ0', hr⟩ := exists_liClockThetaResolvent_iteratedDeriv_growth
  set ε := (1 / 300 - δ0) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨δ0 + 2 * ε, by positivity, by rw [hεdef]; linarith, fun m => ?_⟩
  choose Ch hCh using hexp ε hε
  have hCh0 : ∀ k, 0 ≤ Ch k := fun k => by
    have := (abs_nonneg _).trans (hCh k 0); simpa using this
  obtain ⟨Cr, hCr⟩ := hr m
  have hCr0 : 0 ≤ Cr := by have := (abs_nonneg _).trans (hCr 0); simpa using this
  set A := ∑ j ∈ Finset.range m, |iteratedDeriv j liClockThetaResolvent 0| * Ch (m - 1 - j)
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hCh0 _)
  refine ⟨Ch m + A + Cr * Ch 0 / ε, fun t => ?_⟩
  have hconv := contDiff_volterraConv_resolvent hh
  have hfun : liClockThetaInverse h = h - volterraConv liClockThetaResolvent h := rfl
  rw [hfun, iteratedDeriv_sub (hh.contDiffAt.of_le (natCast_lt_infty m).le)
    (hconv.contDiffAt.of_le (natCast_lt_infty m).le),
    iteratedDeriv_volterraConv contDiff_liClockThetaResolvent hh m]
  have hE1 : Real.exp (ε * |t|) ≤ Real.exp ((δ0 + 2 * ε) * |t|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t))
  have hsum : |∑ j ∈ Finset.range m, iteratedDeriv j liClockThetaResolvent 0 *
      iteratedDeriv (m - 1 - j) h t| ≤ A * Real.exp (ε * |t|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCh _ t) (abs_nonneg _)
  have hvc := abs_volterraConv_le_exp (f := iteratedDeriv m liClockThetaResolvent) (g := h)
    hδ0.le hε.le hCr0 (hCh0 0)
    (fun s => hCr s) (fun s => by simpa using hCh 0 s) t
  have htexp : |t| ≤ Real.exp (ε * |t|) / ε := by
    rw [le_div_iff₀ hε]
    have := Real.add_one_le_exp (ε * |t|)
    nlinarith [abs_nonneg t]
  have hvc' : |volterraConv (iteratedDeriv m liClockThetaResolvent) h t| ≤
      Cr * Ch 0 / ε * Real.exp ((δ0 + 2 * ε) * |t|) := by
    refine hvc.trans ?_
    calc Cr * Ch 0 * Real.exp ((δ0 + ε) * |t|) * |t| ≤
        Cr * Ch 0 * Real.exp ((δ0 + ε) * |t|) * (Real.exp (ε * |t|) / ε) :=
          mul_le_mul_of_nonneg_left htexp
            (mul_nonneg (mul_nonneg hCr0 (hCh0 0)) (Real.exp_pos _).le)
      _ = Cr * Ch 0 / ε * Real.exp ((δ0 + 2 * ε) * |t|) := by
          rw [mul_div_assoc', mul_assoc, ← Real.exp_add]; ring_nf
  have hhm := (hCh m t).trans (mul_le_mul_of_nonneg_left hE1 (hCh0 m))
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hE1 hA)
  calc |iteratedDeriv m h t - (∑ j ∈ Finset.range m, iteratedDeriv j liClockThetaResolvent 0 *
        iteratedDeriv (m - 1 - j) h t + volterraConv (iteratedDeriv m liClockThetaResolvent) h t)|
      ≤ |iteratedDeriv m h t| + (|∑ j ∈ Finset.range m, iteratedDeriv j liClockThetaResolvent 0 *
        iteratedDeriv (m - 1 - j) h t| +
          |volterraConv (iteratedDeriv m liClockThetaResolvent) h t|) :=
        (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ Ch m * Real.exp ((δ0 + 2 * ε) * |t|) + (A * Real.exp ((δ0 + 2 * ε) * |t|) +
          Cr * Ch 0 / ε * Real.exp ((δ0 + 2 * ε) * |t|)) := by
        gcongr
    _ = (Ch m + A + Cr * Ch 0 / ε) * Real.exp ((δ0 + 2 * ε) * |t|) := by ring

/-! ## The clock response and the massive source as causal inverses -/

/-- **Clock causal equation.**  `F + F ⋆ K = K + tK'` at every real clock. -/
theorem liEvenCrossActualClockResponse_volterra_kernel (t : ℝ) :
    liEvenCrossActualClockResponse t +
        volterraConv liEvenCrossActualClockResponse liClockThetaKernel t =
      liClockThetaClockInput t := by
  have hF : Continuous liEvenCrossActualClockResponse := continuous_liEvenCrossActualClockResponse
  have h1 := hasDerivAt_volterraConv (f := liEvenCrossActualClockBorelKernel)
    (f' := liClockThetaKernel) (g := liEvenCrossActualClockResponse)
    hasDerivAt_liEvenCrossActualClockBorelKernel_eq continuous_liClockThetaKernel hF t
  rw [liEvenCrossActualClockBorelKernel_zero, one_mul] at h1
  have hV : volterraConv liEvenCrossActualClockBorelKernel liEvenCrossActualClockResponse =
      fun s => s * liClockThetaKernel s := by
    funext s
    rw [volterraConv_comm]
    exact volterraConv_liEvenCrossActualClockResponse_borelKernel s
  rw [hV] at h1
  have h2 := (hasDerivAt_id t).mul (hasDerivAt_liClockThetaKernel t)
  simp only [id, one_mul] at h2
  have h3 := h1.unique h2
  rw [volterraConv_comm] at h3
  unfold liClockThetaClockInput
  exact h3

theorem liEvenCrossActualClockResponse_eq_inverse :
    liEvenCrossActualClockResponse = liClockThetaInverse liClockThetaClockInput :=
  eq_liClockThetaInverse contDiff_liClockThetaClockInput.continuous
    continuous_liEvenCrossActualClockResponse liEvenCrossActualClockResponse_volterra_kernel

/-- **The clock response lies in the strict sub-`1/300` class.** -/
theorem liClockSubGammaClass_liEvenCrossActualClockResponse :
    LiClockSubGammaClass liEvenCrossActualClockResponse := by
  rw [liEvenCrossActualClockResponse_eq_inverse]
  exact liClockSubGammaClass_liClockThetaInverse contDiff_liClockThetaClockInput
    liClockEveryExpType_liClockThetaClockInput

theorem neg_liEvenCrossActualClockMassiveSource_eq_inverse :
    (fun t => -liEvenCrossActualClockMassiveSource t) =
      liClockThetaInverse liClockThetaForcingInput := by
  funext t
  exact neg_liEvenCrossActualClockMassiveSource_eq t

/-- **The massive response `-S` lies in the strict sub-`1/300` class.** -/
theorem liClockSubGammaClass_neg_liEvenCrossActualClockMassiveSource :
    LiClockSubGammaClass fun t => -liEvenCrossActualClockMassiveSource t := by
  rw [neg_liEvenCrossActualClockMassiveSource_eq_inverse]
  exact liClockSubGammaClass_liClockThetaInverse contDiff_liClockThetaForcingInput
    liClockEveryExpType_liClockThetaForcingInput

end RHTower
