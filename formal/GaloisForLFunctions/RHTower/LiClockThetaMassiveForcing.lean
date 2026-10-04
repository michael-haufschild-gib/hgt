import GaloisForLFunctions.RHTower.LiClockMassiveCompletionComparison
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import GaloisForLFunctions.RHTower.LiClockThetaInverseContourGrowth
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus
import GaloisForLFunctions.HTGeometry.BorelSeriesParityLaplace

/-!
# The literal massive theta forcing and its causal resolvent decomposition

Let `F` be the actual clock response, `S = F'' - ω² F` the massive source, `B` the literal theta
Borel kernel and `K = B'`.  From the Volterra law `F ⋆ B = t B'`, `F(0) = 0`, `F'(0) = M₀ = ν₁`,
two Leibniz differentiations give the transformed forcing

`J_S := S ⋆ B = t B''' + 2 B'' - ω² t B' - M₀ B = Σ_j q_j t^{2j}/((2j)!)²`,
`q_j = ν_{j+1}/(2j+1) - (2jω² + M₀) ν_j`.

Here `q_0 = 0` and the all-order score recurrence `303 ν_{j+1} ≤ (32j+17) ν_j` gives
`q_j ≤ -η ν_j` for `j ≥ 1`, `η = 2ω² + M₀ - 49/909 > 1/4`.  Hence `J_S ≤ -η(B - 1) < 0` off the
origin, every derivative `J_S^{(m)} ≤ -η B^{(m)} < 0` on `t > 0` (`m ≥ 1`), and
`g := -J_S' ≥ η K` coefficientwise.  Differentiating `J_S = B ⋆ S` gives the causal equation
`S + K ⋆ S = -g`, and with the resolvent `r + r ⋆ K = K` the exact decomposition `-S = g - r ⋆ g`.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The response and the massive source as odd factorial series -/

/-- The odd coefficients `f_j = (-1)^j M_j` of the response. -/
def liClockResponseCoeff (j : ℕ) : ℝ := (-1) ^ j * normalizedPrimeArchMoment j

theorem abs_normalizedPrimeArchMoment_le_shiftMass_mul_pow (j : ℕ) :
    |normalizedPrimeArchMoment j| ≤ xiShiftAbsoluteMass 0 * (1 / 150) ^ j := by
  have h := norm_liEvenCrossActualClockResponseTerm_le (t := 1) (T := 1) (by norm_num) j
  have hf : (0 : ℝ) < ((2 * j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hl : ‖liEvenCrossActualClockResponseTerm 1 j‖ =
      |normalizedPrimeArchMoment j| / ((2 * j + 1).factorial : ℝ) := by
    rw [liEvenCrossActualClockResponseTerm, Real.norm_eq_abs, one_pow, mul_one, abs_div,
      abs_of_pos hf, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hl, div_le_iff₀ hf] at h
  calc |normalizedPrimeArchMoment j| ≤ xiShiftAbsoluteMass 0 * 1 *
        ((1 ^ 2 / 150) ^ j / ((2 * j + 1).factorial : ℝ)) * ((2 * j + 1).factorial : ℝ) := h
    _ = xiShiftAbsoluteMass 0 * (1 / 150) ^ j := by field_simp

theorem geometricCoeffBound_liClockResponseCoeff :
    GeometricCoeffBound liClockResponseCoeff (xiShiftAbsoluteMass 0) (1 / 150) := fun j => by
  rw [liClockResponseCoeff, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_normalizedPrimeArchMoment_le_shiftMass_mul_pow j

theorem liEvenCrossActualClockResponse_eq_oddFactorialSeries :
    liEvenCrossActualClockResponse = oddFactorialSeries liClockResponseCoeff := by
  funext t
  rw [liEvenCrossActualClockResponse_eq_tsum]
  rfl

/-- The odd coefficients `f_{j+1} - ω² f_j` of the massive source. -/
def liClockMassiveSourceCoeff (j : ℕ) : ℝ :=
  liClockResponseCoeff (j + 1) - liEvenCrossActualClockGreenRate ^ 2 * liClockResponseCoeff j

theorem geometricCoeffBound_liClockMassiveSourceCoeff :
    GeometricCoeffBound liClockMassiveSourceCoeff
      (xiShiftAbsoluteMass 0 * (1 / 150) + liEvenCrossActualClockGreenRate ^ 2 *
        xiShiftAbsoluteMass 0) (1 / 150) := fun j => by
  have h1 := geometricCoeffBound_liClockResponseCoeff.shift j
  have h2 := geometricCoeffBound_liClockResponseCoeff j
  unfold liClockMassiveSourceCoeff
  calc |liClockResponseCoeff (j + 1) - liEvenCrossActualClockGreenRate ^ 2 * liClockResponseCoeff j|
      ≤ |liClockResponseCoeff (j + 1)| + liEvenCrossActualClockGreenRate ^ 2 *
          |liClockResponseCoeff j| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg liEvenCrossActualClockGreenRate)]
    _ ≤ xiShiftAbsoluteMass 0 * (1 / 150) * (1 / 150) ^ j +
          liEvenCrossActualClockGreenRate ^ 2 * (xiShiftAbsoluteMass 0 * (1 / 150) ^ j) := by
        gcongr
    _ = _ := by ring

theorem liEvenCrossActualClockMassiveSource_eq_oddFactorialSeries :
    liEvenCrossActualClockMassiveSource = oddFactorialSeries liClockMassiveSourceCoeff := by
  funext t
  have hf := geometricCoeffBound_liClockResponseCoeff
  unfold liEvenCrossActualClockMassiveSource
  rw [liEvenCrossActualClockResponse_eq_oddFactorialSeries,
    iteratedDeriv_two_oddFactorialSeries (by norm_num) hf]
  unfold oddFactorialSeries
  rw [← tsum_mul_left, ← Summable.tsum_sub (summable_oddFactorialSeries_term (by norm_num) hf.shift t)
    ((summable_oddFactorialSeries_term (by norm_num) hf t).mul_left _)]
  exact tsum_congr fun j => by unfold liClockMassiveSourceCoeff; ring

theorem continuous_liEvenCrossActualClockMassiveSource :
    Continuous liEvenCrossActualClockMassiveSource := by
  rw [liEvenCrossActualClockMassiveSource_eq_oddFactorialSeries]
  exact continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockMassiveSourceCoeff
      t).continuousAt

theorem liEvenCrossActualClockMassiveSource_zero : liEvenCrossActualClockMassiveSource 0 = 0 := by
  rw [liEvenCrossActualClockMassiveSource_eq_oddFactorialSeries, oddFactorialSeries_zero]

/-! ## The theta kernel calculus -/

private theorem hc : GeometricCoeffBound liClockThetaGeneratorCoeff 1 (32 / 303) :=
  geometricCoeffBound_liClockThetaGeneratorCoeff

private theorem hc1 : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) (32 / 303) := hc.shift

private theorem hc2 : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1 + 1))
    (1 * (32 / 303) * (32 / 303)) (32 / 303) := hc1.shift

/-- `K' = Σ_m c_{m+1} t^{2m}/(2m)!`. -/
def liClockThetaKernelDeriv (t : ℝ) : ℝ :=
  evenFactorialSeries (fun m => liClockThetaGeneratorCoeff (m + 1)) t

theorem hasDerivAt_liClockThetaKernel (t : ℝ) :
    HasDerivAt liClockThetaKernel (liClockThetaKernelDeriv t) t :=
  hasDerivAt_oddFactorialSeries (by norm_num) hc1 t

theorem hasDerivAt_liClockThetaKernelDeriv (t : ℝ) :
    HasDerivAt liClockThetaKernelDeriv
      (oddFactorialSeries (fun m => liClockThetaGeneratorCoeff (m + 1 + 1)) t) t :=
  hasDerivAt_evenFactorialSeries (by norm_num) hc1 t

theorem liClockThetaKernel_neg (t : ℝ) : liClockThetaKernel (-t) = -liClockThetaKernel t :=
  oddFactorialSeries_neg_arg _ t

/-- Every odd Taylor coefficient of `K` is strictly positive, so `K > 0` on `t > 0`. -/
theorem liClockThetaKernel_pos {t : ℝ} (ht : 0 < t) : 0 < liClockThetaKernel t := by
  have h := oddFactorialSeries_lt_of_le_of_lt (a := fun _ => (0 : ℝ))
    (b := fun m => liClockThetaGeneratorCoeff (m + 1)) (M := 0) (R := 0) le_rfl (by norm_num)
    (fun j => by simp) hc1 (fun j => (liClockThetaGeneratorCoeff_pos _).le)
    (i := 0) (liClockThetaGeneratorCoeff_pos _) ht
  have h0 : oddFactorialSeries (fun _ => (0 : ℝ)) t = 0 := by simp [oddFactorialSeries]
  rw [h0] at h
  exact h

theorem liClockThetaKernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ liClockThetaKernel t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [liClockThetaKernel, oddFactorialSeries_zero]
  · exact (liClockThetaKernel_pos ht).le

/-! ## The Volterra law at every real clock -/

/-- `F ⋆ B = t K` at every real clock. -/
theorem volterraConv_liEvenCrossActualClockResponse_borelKernel (t : ℝ) :
    volterraConv liEvenCrossActualClockResponse liEvenCrossActualClockBorelKernel t =
      t * liClockThetaKernel t := by
  have hpos : ∀ t : ℝ, 0 ≤ t → volterraConv liEvenCrossActualClockResponse
      liEvenCrossActualClockBorelKernel t = t * liClockThetaKernel t := by
    intro t ht
    rw [volterraConv_comm, volterraConv, ← deriv_liEvenCrossActualClockBorelKernel_eq,
      ← liEvenCrossActualClockResponse_volterra_eq_mul_deriv ht]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  rcases le_total 0 t with ht | ht
  · exact hpos t ht
  · obtain ⟨u, rfl⟩ : ∃ u, t = -u := ⟨-t, by ring⟩
    have hu : 0 ≤ u := by linarith
    have hFodd : (fun s => liEvenCrossActualClockResponse (-s)) =
        fun s => -liEvenCrossActualClockResponse s := by
      funext s
      rw [liEvenCrossActualClockResponse_eq_oddFactorialSeries, oddFactorialSeries_neg_arg]
    have hBeven : (fun s => liEvenCrossActualClockBorelKernel (-s)) =
        liEvenCrossActualClockBorelKernel := by
      funext s
      rw [liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries,
        liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries, evenFactorialSeries_neg_arg]
    rw [volterraConv_neg, hFodd, hBeven, volterraConv_neg_left, neg_neg, hpos u hu,
      liClockThetaKernel_neg]
    ring

/-! ## The transformed forcing -/

/-- The literal transformed massive forcing `J_S = S ⋆ B`. -/
def liClockThetaMassiveForcing (t : ℝ) : ℝ :=
  volterraConv liEvenCrossActualClockMassiveSource liEvenCrossActualClockBorelKernel t

private theorem volterraConv_sub_smul_left {f h k : ℝ → ℝ} (hf : Continuous f)
    (hh : Continuous h) (hk : Continuous k) (c : ℝ) (t : ℝ) :
    volterraConv (fun s => f s - c * h s) k t = volterraConv f k t - c * volterraConv h k t := by
  rw [volterraConv_comm, volterraConv_sub_right hk hf (hh.const_mul c), volterraConv_smul_right,
    volterraConv_comm k f, volterraConv_comm k h]

/-- **Endpoint-exact forcing identity.**
`J_S = 2K' + tK'' - M₀ B - ω² t K` at every real clock (`K' = B''`, `K'' = B'''`). -/
theorem liClockThetaMassiveForcing_eq (t : ℝ) :
    liClockThetaMassiveForcing t =
      2 * liClockThetaKernelDeriv t +
        t * oddFactorialSeries (fun m => liClockThetaGeneratorCoeff (m + 1 + 1)) t -
        normalizedPrimeArchMoment 0 * liEvenCrossActualClockBorelKernel t -
        liEvenCrossActualClockGreenRate ^ 2 * (t * liClockThetaKernel t) := by
  have hf := geometricCoeffBound_liClockResponseCoeff
  set F := liEvenCrossActualClockResponse
  set B := liEvenCrossActualClockBorelKernel
  have hF : F = oddFactorialSeries liClockResponseCoeff :=
    liEvenCrossActualClockResponse_eq_oddFactorialSeries
  have hB : Continuous B := continuous_liEvenCrossActualClockBorelKernel
  have hE : Continuous (evenFactorialSeries liClockResponseCoeff) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_evenFactorialSeries (by norm_num) hf s).continuousAt
  have hO1 : Continuous (oddFactorialSeries fun j => liClockResponseCoeff (j + 1)) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_oddFactorialSeries (by norm_num) hf.shift s).continuousAt
  have hO : Continuous (oddFactorialSeries liClockResponseCoeff) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_oddFactorialSeries (by norm_num) hf s).continuousAt
  have hV : volterraConv F B = fun s => s * liClockThetaKernel s :=
    funext volterraConv_liEvenCrossActualClockResponse_borelKernel
  -- first derivative
  have hV1 : ∀ s, volterraConv (evenFactorialSeries liClockResponseCoeff) B s =
      liClockThetaKernel s + s * liClockThetaKernelDeriv s := by
    intro s
    have h1 := hasDerivAt_volterraConv (f := F) (f' := evenFactorialSeries liClockResponseCoeff)
      (g := B) (fun x => by rw [hF]; exact hasDerivAt_oddFactorialSeries (by norm_num) hf x) hE hB s
    rw [hV, hF, oddFactorialSeries_zero, zero_mul, zero_add] at h1
    have h2 := (hasDerivAt_id s).mul (hasDerivAt_liClockThetaKernel s)
    simp only [id, one_mul] at h2
    exact h1.unique h2
  -- second derivative
  have hV2 : volterraConv (oddFactorialSeries fun j => liClockResponseCoeff (j + 1)) B t =
      2 * liClockThetaKernelDeriv t +
        t * oddFactorialSeries (fun m => liClockThetaGeneratorCoeff (m + 1 + 1)) t -
        normalizedPrimeArchMoment 0 * B t := by
    have h1 := hasDerivAt_volterraConv (f := evenFactorialSeries liClockResponseCoeff)
      (f' := oddFactorialSeries fun j => liClockResponseCoeff (j + 1)) (g := B)
      (fun x => hasDerivAt_evenFactorialSeries (by norm_num) hf x) hO1 hB t
    rw [funext hV1, evenFactorialSeries_zero] at h1
    have h2 := (hasDerivAt_liClockThetaKernel t).add
      ((hasDerivAt_id t).mul (hasDerivAt_liClockThetaKernelDeriv t))
    simp only [id, one_mul] at h2
    have h3 := h1.unique h2
    have hf0 : liClockResponseCoeff 0 = normalizedPrimeArchMoment 0 := by
      simp [liClockResponseCoeff]
    rw [hf0] at h3
    linarith
  have hS : liEvenCrossActualClockMassiveSource = fun s =>
      oddFactorialSeries (fun j => liClockResponseCoeff (j + 1)) s -
        liEvenCrossActualClockGreenRate ^ 2 * oddFactorialSeries liClockResponseCoeff s := by
    funext s
    unfold liEvenCrossActualClockMassiveSource
    rw [liEvenCrossActualClockResponse_eq_oddFactorialSeries,
      iteratedDeriv_two_oddFactorialSeries (by norm_num) hf]
  unfold liClockThetaMassiveForcing
  rw [hS, volterraConv_sub_smul_left hO1 hO hB, hV2, ← hF,
    volterraConv_liEvenCrossActualClockResponse_borelKernel]

/-- The forcing coefficients `q_j = ν_{j+1}/(2j+1) - (2jω² + M₀) ν_j`. -/
def liClockThetaForcingCoeff (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment (j + 1) / (2 * j + 1) -
    (2 * j * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
      thetaCuspNormalizedEvenMoment j

private theorem fac_two_succ (k : ℕ) :
    ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * (2 * k + 1) * ((2 * k).factorial : ℝ) := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast; ring

/-- **Exact forcing series.**  `J_S(t) = Σ_j q_j t^{2j}/((2j)!)²`. -/
theorem hasSum_liClockThetaMassiveForcing (t : ℝ) :
    HasSum (fun j : ℕ => liClockThetaForcingCoeff j * t ^ (2 * j) / ((2 * j).factorial : ℝ) ^ 2)
      (liClockThetaMassiveForcing t) := by
  have hK' := (summable_evenFactorialSeries_term (by norm_num) hc1 t).hasSum
  have htK'' := hasSum_id_mul_oddFactorialSeries (by norm_num) hc2 t
  have hB := (summable_evenFactorialSeries_term (by norm_num) hc t).hasSum
  have htK := hasSum_id_mul_oddFactorialSeries (by norm_num) hc1 t
  have hsum := (((hK'.mul_left 2).add htK'').sub (hB.mul_left (normalizedPrimeArchMoment 0))).sub
    (htK.mul_left (liEvenCrossActualClockGreenRate ^ 2))
  rw [liClockThetaMassiveForcing_eq, liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries]
  refine hsum.congr_fun fun k => ?_
  have hM0 := normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment
  have hf0 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold liClockThetaForcingCoeff liClockThetaGeneratorCoeff
  rcases k with _ | k
  · simp only [Nat.zero_sub, mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one,
      CharP.cast_eq_zero, zero_mul, zero_add, sub_zero, mul_one, one_pow,
      thetaCuspNormalizedEvenMoment_zero]
    norm_num
    ring
  · simp only [Nat.add_sub_cancel]
    rw [fac_two_succ (k + 1), show k + 1 + 1 = (k + 1) + 1 by rfl]
    have hk2 : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

/-- `J_S` as an even factorial series with coefficients `e_j = q_j/(2j)!`. -/
def liClockThetaForcingTaylorCoeff (j : ℕ) : ℝ :=
  liClockThetaForcingCoeff j / ((2 * j).factorial : ℝ)

theorem liClockThetaMassiveForcing_eq_evenFactorialSeries :
    liClockThetaMassiveForcing = evenFactorialSeries liClockThetaForcingTaylorCoeff := by
  funext t
  rw [← (hasSum_liClockThetaMassiveForcing t).tsum_eq]
  unfold evenFactorialSeries liClockThetaForcingTaylorCoeff
  exact tsum_congr fun j => by ring

/-- `e_j = (2j+2) c_{j+1} - (2jω² + M₀) c_j`. -/
theorem liClockThetaForcingTaylorCoeff_eq (j : ℕ) :
    liClockThetaForcingTaylorCoeff j = (2 * j + 2) * liClockThetaGeneratorCoeff (j + 1) -
      (2 * j * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) *
        liClockThetaGeneratorCoeff j := by
  unfold liClockThetaForcingTaylorCoeff liClockThetaForcingCoeff liClockThetaGeneratorCoeff
  rw [fac_two_succ j]
  have hf0 : (0 : ℝ) < ((2 * j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hj : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  field_simp

private theorem nat_mul_inv_factorial_le_one (k : ℕ) : (k : ℝ) * ((k.factorial : ℝ))⁻¹ ≤ 1 := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [← div_eq_mul_inv, div_le_one hk]
  exact_mod_cast Nat.self_le_factorial k

private theorem generatorCoeff_le_inv_factorial (k : ℕ) :
    liClockThetaGeneratorCoeff k ≤ ((k.factorial : ℝ))⁻¹ := by
  refine (liClockThetaGeneratorCoeff_le k).trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem geometricCoeffBound_liClockThetaForcingTaylorCoeff :
    GeometricCoeffBound liClockThetaForcingTaylorCoeff
      (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) 1 := by
  intro j
  rw [one_pow, mul_one, liClockThetaForcingTaylorCoeff_eq]
  have hM0 : 0 < normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact thetaCuspNormalizedEvenMoment_pos 1
  have hω : 0 ≤ liEvenCrossActualClockGreenRate ^ 2 := sq_nonneg _
  have hc0 := (liClockThetaGeneratorCoeff_pos j).le
  have hc1' := (liClockThetaGeneratorCoeff_pos (j + 1)).le
  have h1 : (2 * (j : ℝ) + 2) * liClockThetaGeneratorCoeff (j + 1) ≤ 2 := by
    have := mul_le_mul_of_nonneg_left (generatorCoeff_le_inv_factorial (j + 1))
      (by positivity : (0 : ℝ) ≤ 2 * (j : ℝ) + 2)
    have h' := nat_mul_inv_factorial_le_one (j + 1)
    push_cast at h'
    nlinarith
  have h2 : (j : ℝ) * liClockThetaGeneratorCoeff j ≤ 1 :=
    (mul_le_mul_of_nonneg_left (generatorCoeff_le_inv_factorial j) (by positivity)).trans
      (nat_mul_inv_factorial_le_one j)
  have h3 : liClockThetaGeneratorCoeff j ≤ 1 :=
    (generatorCoeff_le_inv_factorial j).trans (inv_le_one_of_one_le₀ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hω hc0, mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hc0]

/-! ## Signs -/

/-- The sign margin `η = 2ω² + M₀ - 49/909`. -/
def liClockThetaForcingMargin : ℝ :=
  2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0 - 49 / 909

theorem one_quarter_lt_liClockThetaForcingMargin : 1 / 4 < liClockThetaForcingMargin := by
  have hω := liEvenCrossActualClockGreenRate_sq_gt
  have hM0 : 0 < normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact thetaCuspNormalizedEvenMoment_pos 1
  unfold liClockThetaForcingMargin
  linarith

theorem liClockThetaForcingCoeff_zero : liClockThetaForcingCoeff 0 = 0 := by
  unfold liClockThetaForcingCoeff
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    thetaCuspNormalizedEvenMoment_zero]
  simp

/-- **All-order coefficient margin.**  `q_j ≤ -η ν_j` for every `j ≥ 1`. -/
theorem liClockThetaForcingCoeff_le {j : ℕ} (hj : 1 ≤ j) :
    liClockThetaForcingCoeff j ≤ -liClockThetaForcingMargin * thetaCuspNormalizedEvenMoment j := by
  have hscore := thetaCuspNormalizedEvenMoment_succ_le_score j
  have hν := (thetaCuspNormalizedEvenMoment_pos j).le
  have hν1 := (thetaCuspNormalizedEvenMoment_pos (j + 1)).le
  have hω : 0 ≤ liEvenCrossActualClockGreenRate ^ 2 := sq_nonneg _
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : (0 : ℝ) < 2 * j + 1 := by positivity
  have hratio : thetaCuspNormalizedEvenMoment (j + 1) / (2 * j + 1) ≤
      49 / 909 * thetaCuspNormalizedEvenMoment j := by
    rw [div_le_iff₀ hpos]
    nlinarith
  unfold liClockThetaForcingCoeff liClockThetaForcingMargin
  nlinarith [mul_nonneg hω hν, mul_nonneg (mul_nonneg hω hν) (by linarith : (0 : ℝ) ≤ j - 1)]

theorem liClockThetaForcingTaylorCoeff_le {j : ℕ} (hj : 1 ≤ j) :
    liClockThetaForcingTaylorCoeff j ≤ -liClockThetaForcingMargin * liClockThetaGeneratorCoeff j := by
  have hf0 : (0 : ℝ) < ((2 * j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold liClockThetaForcingTaylorCoeff liClockThetaGeneratorCoeff
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hf0]
  exact liClockThetaForcingCoeff_le hj

theorem liClockThetaForcingTaylorCoeff_zero : liClockThetaForcingTaylorCoeff 0 = 0 := by
  simp [liClockThetaForcingTaylorCoeff, liClockThetaForcingCoeff_zero]

/-- **Negative forcing at every clock.**  `J_S(t) ≤ -η (B(t) - 1)`. -/
theorem liClockThetaMassiveForcing_le (t : ℝ) :
    liClockThetaMassiveForcing t ≤
      -liClockThetaForcingMargin * (liEvenCrossActualClockBorelKernel t - 1) := by
  have hη := one_quarter_lt_liClockThetaForcingMargin
  have hJ : HasSum (fun j => liClockThetaForcingTaylorCoeff j * t ^ (2 * j) /
      ((2 * j).factorial : ℝ)) (liClockThetaMassiveForcing t) := by
    rw [liClockThetaMassiveForcing_eq_evenFactorialSeries]
    exact (summable_evenFactorialSeries_term (by norm_num)
      geometricCoeffBound_liClockThetaForcingTaylorCoeff t).hasSum
  have hB : HasSum (fun j => liClockThetaGeneratorCoeff j * t ^ (2 * j) /
      ((2 * j).factorial : ℝ)) (liEvenCrossActualClockBorelKernel t) := by
    rw [liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries]
    exact (summable_evenFactorialSeries_term (by norm_num) hc t).hasSum
  have hsum := hJ.add (hB.mul_left liClockThetaForcingMargin)
  have hle : liClockThetaMassiveForcing t + liClockThetaForcingMargin *
      liEvenCrossActualClockBorelKernel t ≤ liClockThetaForcingMargin := by
    rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
    simp only [liClockThetaForcingTaylorCoeff_zero, liClockThetaGeneratorCoeff_zero, mul_zero,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, mul_one]
    have : ∑' k : ℕ, (liClockThetaForcingTaylorCoeff (k + 1) * t ^ (2 * (k + 1)) /
        ((2 * (k + 1)).factorial : ℝ) + liClockThetaForcingMargin *
          (liClockThetaGeneratorCoeff (k + 1) * t ^ (2 * (k + 1)) /
            ((2 * (k + 1)).factorial : ℝ))) ≤ 0 := by
      refine tsum_nonpos fun k => ?_
      have hk := liClockThetaForcingTaylorCoeff_le (j := k + 1) (by omega)
      have hX : 0 ≤ t ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) := by
        rw [pow_mul]; positivity
      have e : liClockThetaForcingTaylorCoeff (k + 1) * t ^ (2 * (k + 1)) /
          ((2 * (k + 1)).factorial : ℝ) + liClockThetaForcingMargin *
            (liClockThetaGeneratorCoeff (k + 1) * t ^ (2 * (k + 1)) /
              ((2 * (k + 1)).factorial : ℝ)) =
          (liClockThetaForcingTaylorCoeff (k + 1) + liClockThetaForcingMargin *
            liClockThetaGeneratorCoeff (k + 1)) * (t ^ (2 * (k + 1)) /
              ((2 * (k + 1)).factorial : ℝ)) := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hX
    linarith
  linarith

theorem one_lt_liEvenCrossActualClockBorelKernel {t : ℝ} (ht : t ≠ 0) :
    1 < liEvenCrossActualClockBorelKernel t := by
  have hB := (summable_evenFactorialSeries_term (by norm_num) hc t)
  rw [liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries, evenFactorialSeries,
    hB.tsum_eq_zero_add]
  simp only [liClockThetaGeneratorCoeff_zero, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one]
  have hpos : 0 < ∑' k : ℕ, liClockThetaGeneratorCoeff (k + 1) * t ^ (2 * (k + 1)) /
      ((2 * (k + 1)).factorial : ℝ) := by
    refine ((summable_nat_add_iff 1).2 hB).tsum_pos (fun k => ?_) 0 ?_
    · have := (liClockThetaGeneratorCoeff_pos (k + 1)).le
      rw [pow_mul]; positivity
    · have := liClockThetaGeneratorCoeff_pos 1
      have ht2 : 0 < t ^ 2 := by positivity
      simp only [zero_add, mul_one]
      positivity
  linarith

/-- **Strict negativity.**  `J_S(t) < -(B(t) - 1)/4 < 0` for `t ≠ 0`. -/
theorem liClockThetaMassiveForcing_lt {t : ℝ} (ht : t ≠ 0) :
    liClockThetaMassiveForcing t < -(liEvenCrossActualClockBorelKernel t - 1) / 4 ∧
      -(liEvenCrossActualClockBorelKernel t - 1) / 4 < 0 := by
  have h := liClockThetaMassiveForcing_le t
  have hη := one_quarter_lt_liClockThetaForcingMargin
  have hB := one_lt_liEvenCrossActualClockBorelKernel ht
  constructor <;> nlinarith

/-! ## The derivative forcing `g` and every higher derivative -/

/-- `g = -J_S' = Σ_m (-e_{m+1}) t^{2m+1}/(2m+1)!`. -/
def liClockThetaForcingInput (t : ℝ) : ℝ :=
  oddFactorialSeries (fun m => -liClockThetaForcingTaylorCoeff (m + 1)) t

private theorem he : GeometricCoeffBound liClockThetaForcingTaylorCoeff
    (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) 1 :=
  geometricCoeffBound_liClockThetaForcingTaylorCoeff

private theorem hg : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
    ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
  fun m => by rw [abs_neg]; exact he.shift m

theorem hasDerivAt_liClockThetaMassiveForcing (t : ℝ) :
    HasDerivAt liClockThetaMassiveForcing (-liClockThetaForcingInput t) t := by
  rw [liClockThetaMassiveForcing_eq_evenFactorialSeries]
  have h := hasDerivAt_evenFactorialSeries (by norm_num) he t
  have e : oddFactorialSeries (fun j => liClockThetaForcingTaylorCoeff (j + 1)) t =
      -liClockThetaForcingInput t := by
    unfold liClockThetaForcingInput oddFactorialSeries
    rw [← tsum_neg]
    exact tsum_congr fun j => by ring
  rwa [e] at h

theorem continuous_liClockThetaForcingInput : Continuous liClockThetaForcingInput :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_oddFactorialSeries (by norm_num) hg t).continuousAt

/-- **Coefficient floor.**  Every odd coefficient of `g` dominates `η` times that of `K`. -/
theorem liClockThetaForcingInput_coeff_ge (m : ℕ) :
    liClockThetaForcingMargin * liClockThetaGeneratorCoeff (m + 1) ≤
      -liClockThetaForcingTaylorCoeff (m + 1) := by
  have := liClockThetaForcingTaylorCoeff_le (j := m + 1) (by omega)
  linarith

/-- **Exact coefficient ratio.**  `[t^{2j-1}] g / [t^{2j-1}] K = 2jω² + M₀ - ν_{j+1}/((2j+1)ν_j)`. -/
theorem liClockThetaForcingInput_coeff_ratio {j : ℕ} (_hj : 1 ≤ j) :
    -liClockThetaForcingTaylorCoeff j / liClockThetaGeneratorCoeff j =
      2 * j * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0 -
        thetaCuspNormalizedEvenMoment (j + 1) / ((2 * j + 1) * thetaCuspNormalizedEvenMoment j) := by
  have hν := (thetaCuspNormalizedEvenMoment_pos j).ne'
  have hf0 : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hj1 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  unfold liClockThetaForcingTaylorCoeff liClockThetaGeneratorCoeff liClockThetaForcingCoeff
  field_simp
  ring

/-- `g ≥ η K > K/4` on nonnegative clocks, strictly on positive clocks. -/
theorem liClockThetaForcingInput_ge {t : ℝ} (ht : 0 ≤ t) :
    liClockThetaForcingMargin * liClockThetaKernel t ≤ liClockThetaForcingInput t := by
  have hη := one_quarter_lt_liClockThetaForcingMargin
  have hcb : GeometricCoeffBound (fun m => liClockThetaForcingMargin *
      liClockThetaGeneratorCoeff (m + 1)) (liClockThetaForcingMargin * (1 * (32 / 303)))
        (32 / 303) := fun m => by
    rw [abs_mul, abs_of_pos (by linarith), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hc1 m) (by linarith)
  have h := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) hcb hg
    liClockThetaForcingInput_coeff_ge ht
  have e : oddFactorialSeries (fun m => liClockThetaForcingMargin *
      liClockThetaGeneratorCoeff (m + 1)) t = liClockThetaForcingMargin * liClockThetaKernel t := by
    unfold liClockThetaKernel oddFactorialSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [e] at h
  exact h

theorem liClockThetaForcingInput_gt {t : ℝ} (ht : 0 < t) :
    liClockThetaKernel t / 4 < liClockThetaForcingInput t := by
  have h := liClockThetaForcingInput_ge ht.le
  have hK := liClockThetaKernel_pos ht
  have hη := one_quarter_lt_liClockThetaForcingMargin
  nlinarith

/-- `J_S' ≤ -η K < -K/4 < 0` on positive clocks. -/
theorem deriv_liClockThetaMassiveForcing_lt {t : ℝ} (ht : 0 < t) :
    deriv liClockThetaMassiveForcing t ≤ -liClockThetaForcingMargin * liClockThetaKernel t ∧
      -liClockThetaForcingMargin * liClockThetaKernel t < -liClockThetaKernel t / 4 ∧
      -liClockThetaKernel t / 4 < 0 := by
  rw [(hasDerivAt_liClockThetaMassiveForcing t).deriv]
  have h := liClockThetaForcingInput_ge ht.le
  have hK := liClockThetaKernel_pos ht
  have hη := one_quarter_lt_liClockThetaForcingMargin
  refine ⟨by linarith, by nlinarith, by linarith⟩

/-- **Every fixed derivative.**  For `m ≥ 1` and `t > 0`,
`J_S^{(m)}(t) ≤ -η B^{(m)}(t) < 0`. -/
theorem iteratedDeriv_liClockThetaMassiveForcing_le {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv m liClockThetaMassiveForcing t ≤
        -liClockThetaForcingMargin * iteratedDeriv m liEvenCrossActualClockBorelKernel t ∧
      -liClockThetaForcingMargin * iteratedDeriv m liEvenCrossActualClockBorelKernel t < 0 := by
  have hη := one_quarter_lt_liClockThetaForcingMargin
  have heS := he.evenSpread (by norm_num)
  have hcS := hc.evenSpread (by norm_num)
  rw [liClockThetaMassiveForcing_eq_evenFactorialSeries,
    evenFactorialSeries_eq_borelSeries (by norm_num) he,
    iteratedDeriv_borelSeries heS, funext liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries,
    evenFactorialSeries_eq_borelSeries (by norm_num) hc, iteratedDeriv_borelSeries hcS]
  have hcoef : ∀ N, evenSpread liClockThetaForcingTaylorCoeff (N + m) ≤
      -liClockThetaForcingMargin * evenSpread liClockThetaGeneratorCoeff (N + m) := by
    intro N
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N + m)
    · rw [hk, evenSpread_two_mul, evenSpread_two_mul]
      exact liClockThetaForcingTaylorCoeff_le (by omega)
    · rw [hk, evenSpread_two_mul_add_one, evenSpread_two_mul_add_one, mul_zero]
  have hle := borelSeries_le_borelSeries (geometricCoeffBound_shift_add heS m)
    (fun N => by
      have := geometricCoeffBound_shift_add hcS m N
      rw [abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < liClockThetaForcingMargin)]
      calc liClockThetaForcingMargin * |evenSpread liClockThetaGeneratorCoeff (N + m)| ≤
          liClockThetaForcingMargin * (1 * max (32 / 303) 1 ^ m * max (32 / 303) 1 ^ N) :=
            mul_le_mul_of_nonneg_left this (by linarith)
        _ = liClockThetaForcingMargin * (1 * max (32 / 303) 1 ^ m) * max (32 / 303) 1 ^ N := by
            ring)
    hcoef ht.le
  rw [borelSeries_const_mul] at hle
  refine ⟨hle, ?_⟩
  have hpos : 0 < borelSeries (fun n => evenSpread liClockThetaGeneratorCoeff (n + m)) t := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
    · refine borelSeries_pos (geometricCoeffBound_shift_add hcS m) (fun n => ?_) (i := 0) ?_ ht
      · obtain ⟨l, hl | hl⟩ := Nat.even_or_odd' (n + m)
        · rw [hl, evenSpread_two_mul]; exact (liClockThetaGeneratorCoeff_pos l).le
        · rw [hl, evenSpread_two_mul_add_one]
      · rw [zero_add, hk, evenSpread_two_mul]; exact liClockThetaGeneratorCoeff_pos k
    · refine borelSeries_pos (geometricCoeffBound_shift_add hcS m) (fun n => ?_) (i := 1) ?_ ht
      · obtain ⟨l, hl | hl⟩ := Nat.even_or_odd' (n + m)
        · rw [hl, evenSpread_two_mul]; exact (liClockThetaGeneratorCoeff_pos l).le
        · rw [hl, evenSpread_two_mul_add_one]
      · rw [hk, show 1 + (2 * k + 1) = 2 * (k + 1) by ring, evenSpread_two_mul]
        exact liClockThetaGeneratorCoeff_pos (k + 1)
  nlinarith

/-! ## The causal equation and the resolvent decomposition -/

/-- **Causal equation.**  `S + K ⋆ S = J_S' = -g` at every real clock, with `S(0) = 0`. -/
theorem liEvenCrossActualClockMassiveSource_volterra (t : ℝ) :
    liEvenCrossActualClockMassiveSource t +
        volterraConv liClockThetaKernel liEvenCrossActualClockMassiveSource t =
      -liClockThetaForcingInput t := by
  have h1 := hasDerivAt_volterraConv (f := liEvenCrossActualClockBorelKernel)
    (f' := liClockThetaKernel) (g := liEvenCrossActualClockMassiveSource)
    hasDerivAt_liEvenCrossActualClockBorelKernel_eq continuous_liClockThetaKernel
    continuous_liEvenCrossActualClockMassiveSource t
  rw [liEvenCrossActualClockBorelKernel_zero, one_mul] at h1
  have h2 := hasDerivAt_liClockThetaMassiveForcing t
  have e : liClockThetaMassiveForcing = volterraConv liEvenCrossActualClockBorelKernel
      liEvenCrossActualClockMassiveSource := by
    funext s; exact volterraConv_comm _ _ s
  rw [e] at h2
  exact h1.unique h2

private theorem volterraConv_sub_left' {f h k : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hk : Continuous k) (t : ℝ) :
    volterraConv (fun s => f s - h s) k t = volterraConv f k t - volterraConv h k t := by
  rw [volterraConv_comm, volterraConv_sub_right hk hf hh, volterraConv_comm k f,
    volterraConv_comm k h]

/-- **Exact resolvent decomposition.**  `-S = g - r ⋆ g` at every real clock. -/
theorem neg_liEvenCrossActualClockMassiveSource_eq (t : ℝ) :
    -liEvenCrossActualClockMassiveSource t =
      liClockThetaForcingInput t - volterraConv liClockThetaResolvent liClockThetaForcingInput t := by
  set S := liEvenCrossActualClockMassiveSource
  set g := liClockThetaForcingInput
  set r := liClockThetaResolvent
  set K := liClockThetaKernel
  have hS : Continuous S := continuous_liEvenCrossActualClockMassiveSource
  have hgc : Continuous g := continuous_liClockThetaForcingInput
  have hr : Continuous r := continuous_liClockThetaResolvent
  have hK : Continuous K := continuous_liClockThetaKernel
  have hrg : Continuous (volterraConv r g) := continuous_volterraConv hr hgc
  set X : ℝ → ℝ := fun s => volterraConv r g s - g s with hXdef
  have hX : Continuous X := hrg.sub hgc
  -- `X + K ⋆ X = -g`
  have hXeq : ∀ s, X s + volterraConv K X s = -g s := by
    intro s
    have hres : ∀ u, volterraConv K r u = K u - r u := fun u => by
      have := liClockThetaResolvent_volterra u
      rw [volterraConv_comm] at this
      linarith
    have h1 : volterraConv K X s = volterraConv K (volterraConv r g) s - volterraConv K g s :=
      volterraConv_sub_right hK hrg hgc s
    have h2 : volterraConv K (volterraConv r g) s = volterraConv (volterraConv K r) g s :=
      (volterraConv_assoc hK hr hgc s).symm
    have h3 : volterraConv (volterraConv K r) g s = volterraConv K g s - volterraConv r g s := by
      rw [show volterraConv K r = fun u => K u - r u from funext hres]
      exact volterraConv_sub_left' hK hr hgc s
    rw [h1, h2, h3]
    simp only [hXdef]
    ring
  -- the difference solves the homogeneous equation
  set D : ℝ → ℝ := fun s => S s - X s with hDdef
  have hD : Continuous D := hS.sub hX
  have hhom : ∀ s, 1 * D s = volterraConv (fun u => -K u) D s := by
    intro s
    rw [volterraConv_neg_left, one_mul]
    have hSv := liEvenCrossActualClockMassiveSource_volterra s
    have hlin : volterraConv K D s = volterraConv K S s - volterraConv K X s :=
      volterraConv_sub_right hK hS hX s
    have hx := hXeq s
    simp only [hDdef]
    rw [hlin]
    linarith
  have hzero := eq_zero_of_mul_eq_volterraConv one_ne_zero hK.neg hD hhom
  have hDt : D t = 0 := congrFun hzero t
  simp only [hDdef, hXdef] at hDt
  linarith

/-- **Exact signed comparison.**  `S(t) ≤ 0` iff `(r ⋆ g)(t) ≤ g(t)`. -/
theorem liEvenCrossActualClockMassiveSource_nonpos_iff (t : ℝ) :
    liEvenCrossActualClockMassiveSource t ≤ 0 ↔
      volterraConv liClockThetaResolvent liClockThetaForcingInput t ≤ liClockThetaForcingInput t := by
  have h := neg_liEvenCrossActualClockMassiveSource_eq t
  constructor <;> intro h' <;> linarith

/-! ## Uniqueness of the causal inverse and of the resolvent -/

private theorem eq_of_volterra_kernel {v w f : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w)
    (hvf : ∀ t, v t + volterraConv v liClockThetaKernel t = f t)
    (hwf : ∀ t, w t + volterraConv w liClockThetaKernel t = f t) : v = w := by
  have hK := continuous_liClockThetaKernel
  have hD : Continuous fun s => v s - w s := hv.sub hw
  have hzero := eq_zero_of_mul_eq_volterraConv (k := fun u => -liClockThetaKernel u) (c := 1)
    one_ne_zero hK.neg hD fun t => by
      rw [volterraConv_neg_left, one_mul, volterraConv_sub_right hK hv hw,
        volterraConv_comm liClockThetaKernel v, volterraConv_comm liClockThetaKernel w]
      linarith [hvf t, hwf t]
  funext t
  have := congrFun hzero t
  simp only [Pi.zero_apply] at this
  linarith

/-- **Unique causal inverse.**  Every continuous solution of `v + v ⋆ K = t` is `u`. -/
theorem eq_liClockThetaCausalInverse_of_volterra {v : ℝ → ℝ} (hv : Continuous v)
    (hvt : ∀ t, v t + volterraConv v liClockThetaKernel t = t) : v = liClockThetaCausalInverse :=
  eq_of_volterra_kernel hv (by
    rw [liClockThetaCausalInverse_eq_borelSeries]
    exact continuous_borelSeries geometricCoeffBound_liClockThetaInverseBorelCoeff) hvt
    liClockThetaCausalInverse_volterra

/-- **Unique resolvent.**  Every continuous solution of `v + v ⋆ K = K` is `r`. -/
theorem eq_liClockThetaResolvent_of_volterra {v : ℝ → ℝ} (hv : Continuous v)
    (hvK : ∀ t, v t + volterraConv v liClockThetaKernel t = liClockThetaKernel t) :
    v = liClockThetaResolvent :=
  eq_of_volterra_kernel hv continuous_liClockThetaResolvent hvK liClockThetaResolvent_volterra

/-- The sign margin exceeds `6047/22725`. -/
theorem liClockThetaForcingMargin_gt : (6047 / 22725 : ℝ) < liClockThetaForcingMargin := by
  have hω := liEvenCrossActualClockGreenRate_sq_gt
  have hM0 : 0 < normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact thetaCuspNormalizedEvenMoment_pos 1
  unfold liClockThetaForcingMargin
  linarith

end RHTower
