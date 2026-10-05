import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryRetention
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCausalHistoryFlattening
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCausalHistoryOrigin
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth
import GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSourceCorrelationEnvelope

/-!
# Moving-history retention and age escape of the actual clock

For the actual kernel `K = B' = Σ_N a_N t^N/N!` (odd degrees only, `a_N ≥ 0`), its degree posterior
`p_t(N) = a_N t^N/(N! K(t))` and the mean degree `m(t) = tK'(t)/K(t)`:

* (M3, M4) `d³ ≤ (9/2) d(d-1)(d-2) + 1` for odd `d`, cubic Jensen, and
  `0 < m³/t² ≤ (9/2) tK'''/K + 1/t² → 0`; also `m ≥ 1`, `m → ∞`, `m' = Var_{p_t}/t ≥ 0` and
  `(K'/K)' = (Var - m)/t²`;
* (M5) `ℓ = K/(4K') = t/(4m)` satisfies `0 < ℓ < t/4`, `ℓ/t → 0`, `ℓ³/t → ∞`, `ℓ → ∞` and
  `ℓ/t^{1/3} → ∞`;
* (M6, M7) for `0 ≤ s ≤ ℓ`: `K(t-s) ≥ K(t) - sK'(t)`, `K'(t-s) ≤ K'(t)` and
  `K(t-s) - sK'(t-s) ≥ K(t)/2`; `∫_0^ℓ s^q K(t-s) ≥ K(t)ℓ^{q+1}/(2(q+1))`;
* (M8–M12) the age law `Q_t` is the complete Beta(1,2j) mixture, `P(t) = tK(t) - A(t) E_{Q_t} P`,
  `Q_t[0,R] → 0`, `Q_t[εt,t] → 0`, `Q_t(R,εt) → 1`, `E S^q → ∞` and `E (S/t)^q → 0`;
* (M14) at clocks with `D ≥ 0` on `[0,ℓ]`,
  `tD'(t) ≥ tK(t) + (K(t)/2)∫_0^ℓ D - ∫_ℓ^t D J_t`, and `J_t = -∂_s(sK(t-s))` conserves mass.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => liClockThetaKernel
local notation "K'" => liClockThetaKernelDeriv
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "J" => liClockHistoryCrossingKernel
local notation "A" => liEvenCrossActualClockHistoryExcess
local notation "ℓ" => liEvenCrossActualClockHistoryScale
local notation "Q" => liEvenCrossActualClockHistoryAgeMeasure
local notation "ν" => thetaCuspNormalizedEvenMoment

/-! ## Bridges between the Borel kernel and its derivatives -/

theorem deriv_liEvenCrossActualClockBorelKernel_fun : deriv B = K :=
  funext deriv_liEvenCrossActualClockBorelKernel_eq

theorem deriv_liClockThetaKernel_fun : deriv K = K' :=
  funext fun t => (hasDerivAt_liClockThetaKernel t).deriv

theorem iteratedDeriv_one_liClockThetaKernel : iteratedDeriv 1 K = K' := by
  rw [iteratedDeriv_one, deriv_liClockThetaKernel_fun]

theorem iteratedDeriv_succ_liEvenCrossActualClockBorelKernel (n : ℕ) :
    iteratedDeriv (n + 1) B = iteratedDeriv n K := by
  rw [iteratedDeriv_succ', deriv_liEvenCrossActualClockBorelKernel_fun]

theorem hasDerivAt_iteratedDeriv_liClockThetaKernel (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n K) (iteratedDeriv (n + 1) K t) t := by
  have hc : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) K :=
    contDiff_liClockThetaKernel.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_succ]
  exact ((hc.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)) t).hasDerivAt

theorem liEvenCrossActualClockHistoryScale_eq (t : ℝ) : ℓ t = K t / (4 * K' t) := by
  unfold liEvenCrossActualClockHistoryScale
  rw [deriv_liEvenCrossActualClockBorelKernel_fun, deriv_liClockThetaKernel_fun]

theorem liClockThetaKernelDeriv_pos (t : ℝ) : 0 < K' t :=
  liClockThetaKernelDeriv_zero_pos.trans_le (liClockThetaKernelDeriv_zero_le t)

/-! ## The degree posterior -/

/-- The degree coefficients `a_N` of `K = Σ_N a_N t^N/N!`: `a_{2m+1} = c_{m+1}`, `a_{2m} = 0`. -/
def liClockThetaKernelDegreeCoeff (N : ℕ) : ℝ :=
  oddSpread (fun m => liClockThetaGeneratorCoeff (m + 1)) N

/-- The degree weights `w_t(N) = a_N t^N/N!`. -/
def liEvenCrossActualClockDegreeWeight (t : ℝ) (N : ℕ) : ℝ :=
  liClockThetaKernelDegreeCoeff N * dividedPowerFn N t

/-- The degree posterior `p_t(N) = a_N t^N/(N! K(t))`. -/
def liEvenCrossActualClockDegreePosterior (t : ℝ) (N : ℕ) : ℝ :=
  liEvenCrossActualClockDegreeWeight t N / K t

/-- The mean degree `m(t) = tK'(t)/K(t)`. -/
def liEvenCrossActualClockMeanDegree (t : ℝ) : ℝ := t * K' t / K t

/-- The posterior degree variance `(t²K'' + tK')/K - m²`. -/
def liEvenCrossActualClockDegreeVariance (t : ℝ) : ℝ :=
  (t ^ 2 * iteratedDeriv 2 K t + t * K' t) / K t - liEvenCrossActualClockMeanDegree t ^ 2

local notation "w" => liEvenCrossActualClockDegreeWeight
local notation "pp" => liEvenCrossActualClockDegreePosterior
local notation "m" => liEvenCrossActualClockMeanDegree
local notation "Var" => liEvenCrossActualClockDegreeVariance

theorem liClockThetaKernelDegreeCoeff_nonneg (N : ℕ) : 0 ≤ liClockThetaKernelDegreeCoeff N := by
  unfold liClockThetaKernelDegreeCoeff oddSpread
  split_ifs
  · exact (liClockThetaGeneratorCoeff_pos _).le
  · exact le_rfl

theorem liClockThetaKernelDegreeCoeff_of_even {N : ℕ} (hN : N % 2 = 0) :
    liClockThetaKernelDegreeCoeff N = 0 := by
  unfold liClockThetaKernelDegreeCoeff oddSpread
  rw [if_neg (by omega)]

theorem liEvenCrossActualClockDegreeWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (N : ℕ) : 0 ≤ w t N :=
  mul_nonneg (liClockThetaKernelDegreeCoeff_nonneg N) (dividedPowerFn_nonneg ht N)

/-- `Σ_N N^{\underline n} w_t(N) = t^n K^{(n)}(t)`: every falling-factorial degree moment. -/
theorem hasSum_descFactorial_mul_degreeWeight (n : ℕ) (t : ℝ) :
    HasSum (fun N => (N.descFactorial n : ℝ) * w t N) (t ^ n * iteratedDeriv n K t) := by
  have hb := geometricCoeffBound_oddSpread_liClockThetaKernelCoeff (R := 1) one_pos
  have hK : iteratedDeriv n K = borelSeries (fun N => liClockThetaKernelDegreeCoeff (N + n)) := by
    rw [liClockThetaKernel_eq_borelSeries, iteratedDeriv_borelSeries hb]
    rfl
  have hs : HasSum (fun N => liClockThetaKernelDegreeCoeff (N + n) * dividedPowerFn N t)
      (iteratedDeriv n K t) := by
    rw [hK]
    exact (summable_borelTerm (geometricCoeffBound_shift_add hb n) t).hasSum
  have hs' := hs.mul_left (t ^ n)
  refine (hasSum_nat_add_iff' n).1 ?_
  have hzero : ∑ i ∈ Finset.range n, (i.descFactorial n : ℝ) * w t i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hi), Nat.cast_zero, zero_mul]
  rw [hzero, sub_zero]
  have e : ∀ N : ℕ, ((N + n).descFactorial n : ℝ) * w t (N + n) =
      t ^ n * (liClockThetaKernelDegreeCoeff (N + n) * dividedPowerFn N t) := fun N => by
    unfold liEvenCrossActualClockDegreeWeight dividedPowerFn
    have hf := Nat.factorial_mul_descFactorial (show n ≤ N + n by omega)
    rw [show N + n - n = N by omega] at hf
    have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hNn : ((N + n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← hf, Nat.cast_mul, pow_add]
    field_simp
  simp only [e]
  exact hs'

theorem hasSum_degreeWeight (t : ℝ) : HasSum (w t) (K t) := by
  simpa using hasSum_descFactorial_mul_degreeWeight 0 t

theorem hasSum_mul_degreeWeight (t : ℝ) : HasSum (fun N : ℕ => (N : ℝ) * w t N) (t * K' t) := by
  simpa [deriv_liClockThetaKernel_fun] using hasSum_descFactorial_mul_degreeWeight 1 t

private theorem descFactorial_two (N : ℕ) : (N.descFactorial 2 : ℝ) = N * (N - 1) := by
  rcases N with _ | _ | N
  · simp
  · simp
  · simp [Nat.descFactorial_succ]; ring

private theorem descFactorial_three (N : ℕ) : (N.descFactorial 3 : ℝ) = N * (N - 1) * (N - 2) := by
  rcases N with _ | _ | _ | N
  · simp
  · simp
  · simp [Nat.descFactorial_succ]
  · simp [Nat.descFactorial_succ]; ring

/-- `Σ N² w = t²K'' + tK'`. -/
theorem hasSum_sq_mul_degreeWeight (t : ℝ) :
    HasSum (fun N : ℕ => (N : ℝ) ^ 2 * w t N) (t ^ 2 * iteratedDeriv 2 K t + t * K' t) := by
  have h := (hasSum_descFactorial_mul_degreeWeight 2 t).add (hasSum_mul_degreeWeight t)
  convert h using 1
  funext N
  rw [descFactorial_two]; ring

/-- `Σ N³ w = t³K''' + 3t²K'' + tK'`. -/
theorem hasSum_cube_mul_degreeWeight (t : ℝ) :
    HasSum (fun N : ℕ => (N : ℝ) ^ 3 * w t N)
      (t ^ 3 * iteratedDeriv 3 K t + 3 * (t ^ 2 * iteratedDeriv 2 K t) + t * K' t) := by
  have h := ((hasSum_descFactorial_mul_degreeWeight 3 t).add
    ((hasSum_descFactorial_mul_degreeWeight 2 t).mul_left 3)).add (hasSum_mul_degreeWeight t)
  convert h using 1
  funext N
  rw [descFactorial_three, descFactorial_two]; ring

/-- **(M4 input)** `p_t` is a probability on the degrees, carried by odd degrees. -/
theorem liEvenCrossActualClockDegreePosterior_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (pp t) 1 ∧ (∀ N, 0 ≤ pp t N) ∧ (∀ N, N % 2 = 0 → pp t N = 0) := by
  have hK := liClockThetaKernel_pos ht
  refine ⟨?_, fun N => div_nonneg (liEvenCrossActualClockDegreeWeight_nonneg ht.le N) hK.le,
    fun N hN => by
      simp [liEvenCrossActualClockDegreePosterior, liEvenCrossActualClockDegreeWeight,
        liClockThetaKernelDegreeCoeff_of_even hN]⟩
  have h := (hasSum_degreeWeight t).div_const (K t)
  rwa [div_self hK.ne'] at h

/-- **(M4 input)** The posterior moments: `E d = m`, `E d² = (t²K''+tK')/K`,
`E d³ = (t³K'''+3t²K''+tK')/K`, and `E d(d-1)(d-2) = t³K'''/K`. -/
theorem liEvenCrossActualClockDegreePosterior_moments (t : ℝ) :
    HasSum (fun N : ℕ => (N : ℝ) * pp t N) (m t) ∧
      HasSum (fun N : ℕ => (N : ℝ) ^ 2 * pp t N) ((t ^ 2 * iteratedDeriv 2 K t + t * K' t) / K t) ∧
      HasSum (fun N : ℕ => (N : ℝ) ^ 3 * pp t N)
        ((t ^ 3 * iteratedDeriv 3 K t + 3 * (t ^ 2 * iteratedDeriv 2 K t) + t * K' t) / K t) ∧
      HasSum (fun N : ℕ => (N : ℝ) * (N - 1) * (N - 2) * pp t N) (t ^ 3 * iteratedDeriv 3 K t / K t) := by
  unfold liEvenCrossActualClockDegreePosterior liEvenCrossActualClockMeanDegree
  simp only [← mul_div_assoc]
  refine ⟨(hasSum_mul_degreeWeight t).div_const _, (hasSum_sq_mul_degreeWeight t).div_const _,
    (hasSum_cube_mul_degreeWeight t).div_const _, ?_⟩
  have h := (hasSum_descFactorial_mul_degreeWeight 3 t).div_const (K t)
  simp only [descFactorial_three] at h
  exact h

/-- **(M4 input)** `m(t) ≥ 1` for `t > 0`. -/
theorem one_le_liEvenCrossActualClockMeanDegree {t : ℝ} (ht : 0 < t) : 1 ≤ m t := by
  obtain ⟨h1, hnn, hodd⟩ := liEvenCrossActualClockDegreePosterior_hasSum ht
  refine hasSum_le (fun N => ?_) h1 (liEvenCrossActualClockDegreePosterior_moments t).1
  rcases Nat.even_or_odd N with hN | hN
  · rw [hodd N (Nat.even_iff.1 hN), mul_zero]
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN.pos
    nlinarith [hnn N]

/-! ## (M3, M4) Arithmetic cubic control of the mean degree -/

/-- **(M3)** `d³ ≤ (9/2) d(d-1)(d-2) + 1` for every odd `d`. -/
theorem cube_le_descFactorial_of_odd {d : ℕ} (hd : Odd d) :
    (d : ℝ) ^ 3 ≤ 9 / 2 * ((d : ℝ) * (d - 1) * (d - 2)) + 1 := by
  obtain ⟨k, rfl⟩ := hd
  push_cast
  rcases k with _ | k
  · norm_num
  · push_cast
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith [pow_nonneg hk 3, sq_nonneg (k : ℝ)]

/-- **(M4)** Cubic Jensen for the degree posterior: `m³ ≤ E d³ = (t³K''' + 3t²K'' + tK')/K`. -/
theorem liEvenCrossActualClockMeanDegree_cube_le {t : ℝ} (ht : 0 < t) :
    m t ^ 3 ≤ (t ^ 3 * iteratedDeriv 3 K t + 3 * (t ^ 2 * iteratedDeriv 2 K t) + t * K' t) / K t := by
  obtain ⟨h1, hnn, -⟩ := liEvenCrossActualClockDegreePosterior_hasSum ht
  obtain ⟨hm1, -, hm3, -⟩ := liEvenCrossActualClockDegreePosterior_moments t
  have hm := one_le_liEvenCrossActualClockMeanDegree ht
  have hf := (hm1.mul_left (3 * m t ^ 2)).sub (h1.mul_left (2 * m t ^ 3))
  have key := hasSum_le (fun N => ?_) hf hm3
  · nlinarith [key]
  · have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have := mul_nonneg (mul_nonneg (sq_nonneg ((N : ℝ) - m t)) (by linarith : (0 : ℝ) ≤ N + 2 * m t))
      (hnn N)
    nlinarith [this]

/-- **(M4)** `0 < m³/t² ≤ (9/2) tK'''/K + 1/t²`. -/
theorem liEvenCrossActualClockMeanDegree_cube_div_sq_le {t : ℝ} (ht : 0 < t) :
    0 < m t ^ 3 / t ^ 2 ∧ m t ^ 3 / t ^ 2 ≤ 9 / 2 * (t * iteratedDeriv 3 K t / K t) + 1 / t ^ 2 := by
  obtain ⟨h1, hnn, hodd⟩ := liEvenCrossActualClockDegreePosterior_hasSum ht
  obtain ⟨-, -, hm3, hd3⟩ := liEvenCrossActualClockDegreePosterior_moments t
  have hm := one_le_liEvenCrossActualClockMeanDegree ht
  have hK := liClockThetaKernel_pos ht
  have hg := (hd3.mul_left (9 / 2)).add h1
  have hle := hasSum_le (fun N => ?_) hm3 hg
  · have hJ := liEvenCrossActualClockMeanDegree_cube_le ht
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have e : (9 / 2 * (t * iteratedDeriv 3 K t / K t) + 1 / t ^ 2) * t ^ 2 =
        9 / 2 * (t ^ 3 * iteratedDeriv 3 K t / K t) + 1 := by
      field_simp
    rw [e]
    linarith
  · rcases Nat.even_or_odd N with hN | hN
    · rw [hodd N (Nat.even_iff.1 hN)]; simp
    · have h := mul_le_mul_of_nonneg_right (cube_le_descFactorial_of_odd hN) (hnn N)
      nlinarith [h]

theorem iteratedDeriv_two_liEvenCrossActualClockBorelKernel : iteratedDeriv 2 B = K' := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ_liEvenCrossActualClockBorelKernel,
    iteratedDeriv_one_liClockThetaKernel]

theorem iteratedDeriv_four_liEvenCrossActualClockBorelKernel :
    iteratedDeriv 4 B = iteratedDeriv 3 K :=
  iteratedDeriv_succ_liEvenCrossActualClockBorelKernel 3

/-- `m(t) → ∞`. -/
theorem tendsto_liEvenCrossActualClockMeanDegree_atTop : Tendsto m atTop atTop := by
  have h := tendsto_liEvenCrossActualClockBorel_deriv_logarithmicDegree_atTop
  rw [iteratedDeriv_two_liEvenCrossActualClockBorelKernel,
    deriv_liEvenCrossActualClockBorelKernel_fun] at h
  exact h

/-- The arithmetic Ward control `tK'''/K → 0`. -/
theorem tendsto_mul_iteratedDeriv_three_liClockThetaKernel_div :
    Tendsto (fun t => t * iteratedDeriv 3 K t / K t) atTop (𝓝 0) := by
  have h := tendsto_liEvenCrossActualClockBorel_clock_fourth_div_deriv_zero
  rw [iteratedDeriv_four_liEvenCrossActualClockBorelKernel,
    deriv_liEvenCrossActualClockBorelKernel_fun] at h
  exact h

/-- **(M4)** `m³/t² → 0`. -/
theorem tendsto_liEvenCrossActualClockMeanDegree_cube_div_sq :
    Tendsto (fun t => m t ^ 3 / t ^ 2) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => 9 / 2 * (t * iteratedDeriv 3 K t / K t) + 1 / t ^ 2) atTop
      (𝓝 0) := by
    have h1 := tendsto_mul_iteratedDeriv_three_liClockThetaKernel_div.const_mul (9 / 2)
    have h2 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero) :
        Tendsto (fun t : ℝ => t ^ 2) atTop atTop)
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact (liEvenCrossActualClockMeanDegree_cube_div_sq_le ht).1.le
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact (liEvenCrossActualClockMeanDegree_cube_div_sq_le ht).2

/-! ## The posterior variance and the monotone mean degree -/

/-- `Var_{p_t}(d) = Σ (d - m)² p_t(d) ≥ 0`. -/
theorem liEvenCrossActualClockDegreeVariance_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun N : ℕ => ((N : ℝ) - m t) ^ 2 * pp t N) (Var t) ∧ 0 ≤ Var t := by
  obtain ⟨h1, hnn, -⟩ := liEvenCrossActualClockDegreePosterior_hasSum ht
  obtain ⟨hm1, hm2, -, -⟩ := liEvenCrossActualClockDegreePosterior_moments t
  have h := (hm2.sub (hm1.mul_left (2 * m t))).add (h1.mul_left (m t ^ 2))
  have e : ∀ N : ℕ, (N : ℝ) ^ 2 * pp t N - 2 * m t * ((N : ℝ) * pp t N) + m t ^ 2 * pp t N =
      ((N : ℝ) - m t) ^ 2 * pp t N := fun N => by ring
  simp only [e] at h
  have hv : (t ^ 2 * iteratedDeriv 2 K t + t * K' t) / K t - 2 * m t * m t + m t ^ 2 * 1 = Var t := by
    unfold liEvenCrossActualClockDegreeVariance; ring
  rw [hv] at h
  exact ⟨h, h.nonneg fun N => mul_nonneg (sq_nonneg _) (hnn N)⟩

private theorem hasDerivAt_liClockThetaKernelDeriv' (t : ℝ) :
    HasDerivAt K' (iteratedDeriv 2 K t) t := by
  have h := hasDerivAt_iteratedDeriv_liClockThetaKernel 1 t
  rwa [iteratedDeriv_one_liClockThetaKernel] at h

/-- **Monotone mean degree.**  `m'(t) = Var_{p_t}(d)/t ≥ 0`. -/
theorem hasDerivAt_liEvenCrossActualClockMeanDegree {t : ℝ} (ht : 0 < t) :
    HasDerivAt m (Var t / t) t := by
  have hK := liClockThetaKernel_pos ht
  have h := ((hasDerivAt_id t).mul (hasDerivAt_liClockThetaKernelDeriv' t)).div
    (hasDerivAt_liClockThetaKernel t) hK.ne'
  have e : ((1 * K' t + id t * iteratedDeriv 2 K t) * K t - ((id : ℝ → ℝ) * K') t * K' t) / K t ^ 2 =
      Var t / t := by
    unfold liEvenCrossActualClockDegreeVariance liEvenCrossActualClockMeanDegree
    simp only [Pi.mul_apply, id]
    field_simp
    ring
  rw [e] at h
  exact h

/-- `(K'/K)' = (Var_{p_t}(d) - m)/t²`. -/
theorem hasDerivAt_liClockThetaKernel_logDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => K' t / K t) ((Var t - m t) / t ^ 2) t := by
  have hK := liClockThetaKernel_pos ht
  have h := (hasDerivAt_liClockThetaKernelDeriv' t).div (hasDerivAt_liClockThetaKernel t) hK.ne'
  have e : (iteratedDeriv 2 K t * K t - K' t * K' t) / K t ^ 2 = (Var t - m t) / t ^ 2 := by
    unfold liEvenCrossActualClockDegreeVariance liEvenCrossActualClockMeanDegree
    field_simp
    ring
  rw [e] at h
  exact h

/-! ## (M5) The actual source scale -/

/-- **(M5)** `ℓ = K/(4K') = t/(4m)` and `0 < ℓ < t/4`. -/
theorem liEvenCrossActualClockHistoryScale_eq_div_meanDegree {t : ℝ} (ht : 0 < t) :
    ℓ t = t / (4 * m t) ∧ 0 < ℓ t ∧ ℓ t < t / 4 := by
  have hK := liClockThetaKernel_pos ht
  have hK' := liClockThetaKernelDeriv_pos t
  have hg := liEvenCrossActualClockHistory_geometry ht
  refine ⟨?_, hg.2.2.1, hg.2.2.2⟩
  rw [liEvenCrossActualClockHistoryScale_eq, liEvenCrossActualClockMeanDegree]
  field_simp

/-- **(M5)** `ℓ(t)/t → 0`. -/
theorem tendsto_liEvenCrossActualClockHistoryScale_div_atTop :
    Tendsto (fun t => ℓ t / t) atTop (𝓝 0) := by
  have h : Tendsto (fun t => (4 * m t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_liEvenCrossActualClockMeanDegree_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 4))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [(liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht).1]
  have := one_le_liEvenCrossActualClockMeanDegree ht
  field_simp

/-- **(M5)** `ℓ(t)³/t = t²/(64 m³) → ∞`. -/
theorem tendsto_liEvenCrossActualClockHistoryScale_cube_div_atTop :
    Tendsto (fun t => ℓ t ^ 3 / t) atTop atTop := by
  have h0 : Tendsto (fun t => m t ^ 3 / t ^ 2) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_liEvenCrossActualClockMeanDegree_cube_div_sq,
      (eventually_gt_atTop 0).mono fun t ht => (liEvenCrossActualClockMeanDegree_cube_div_sq_le ht).1⟩
  have h := (tendsto_inv_nhdsGT_zero.comp h0).atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 64)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [(liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht).1]
  have := one_le_liEvenCrossActualClockMeanDegree ht
  simp only [Function.comp]
  field_simp
  ring

private theorem tendsto_atTop_of_cube {f : ℝ → ℝ} (hpos : ∀ᶠ t in atTop, 0 < f t)
    (h : Tendsto (fun t => f t ^ 3) atTop atTop) : Tendsto f atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [hpos, tendsto_atTop.1 h (max M 0 ^ 3 + 1)] with t ht hM
  by_contra hlt
  rw [not_le] at hlt
  have h1 : f t ≤ max M 0 := hlt.le.trans (le_max_left _ _)
  have h2 : f t ^ 3 ≤ max M 0 ^ 3 := pow_le_pow_left₀ ht.le h1 3
  linarith

/-- **(M5)** `ℓ(t)/t^{1/3} → ∞`. -/
theorem tendsto_liEvenCrossActualClockHistoryScale_div_cbrt_atTop :
    Tendsto (fun t => ℓ t / t ^ (1 / 3 : ℝ)) atTop atTop := by
  refine tendsto_atTop_of_cube ?_ (tendsto_liEvenCrossActualClockHistoryScale_cube_div_atTop.congr' ?_)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact div_pos (liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht).2.1
      (Real.rpow_pos_of_pos ht _)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [div_pow, ← Real.rpow_natCast (t ^ (1 / 3 : ℝ)), ← Real.rpow_mul ht.le]
    norm_num

/-! ## (M6, M7) The favorable retention window -/

theorem monotoneOn_liClockThetaKernelDeriv : MonotoneOn K' (Ici 0) := by
  have h := liEvenCrossActualClockHistory_source_curvature.2
  rwa [deriv_liEvenCrossActualClockBorelKernel_fun, deriv_liClockThetaKernel_fun] at h

/-- **(M6)** For `t > 0` and `0 ≤ s ≤ ℓ(t)`: `K(t-s) ≥ K(t) - sK'(t)`, `K'(t-s) ≤ K'(t)` and the full
favorable history coefficient obeys `K(t-s) - sK'(t-s) ≥ K(t) - 2sK'(t) ≥ K(t)/2 > 0`. -/
theorem liClockThetaKernel_retention {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (hsl : s ≤ ℓ t) :
    K t - s * K' t ≤ K (t - s) ∧ K' (t - s) ≤ K' t ∧
      K t - 2 * s * K' t ≤ K (t - s) - s * K' (t - s) ∧ K t / 2 ≤ K t - 2 * s * K' t ∧
      0 < K t / 2 := by
  obtain ⟨he, hl0, hlt⟩ := liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht
  have hK := liClockThetaKernel_pos ht
  have hK' := liClockThetaKernelDeriv_pos t
  have hts : 0 ≤ t - s := by linarith
  have hmono : K' (t - s) ≤ K' t :=
    monotoneOn_liClockThetaKernelDeriv (mem_Ici.2 hts) (mem_Ici.2 ht.le) (by linarith)
  have htan : K t - s * K' t ≤ K (t - s) := by
    rcases hs.eq_or_lt with rfl | hs'
    · simp
    · obtain ⟨c, hc, hcK⟩ := exists_hasDerivAt_eq_slope K K' (by linarith : t - s < t)
        continuous_liClockThetaKernel.continuousOn fun x _ => hasDerivAt_liClockThetaKernel x
      have hcle : K' c ≤ K' t := monotoneOn_liClockThetaKernelDeriv
        (mem_Ici.2 (by linarith [hc.1])) (mem_Ici.2 ht.le) hc.2.le
      rw [show t - (t - s) = s by ring, eq_div_iff hs'.ne'] at hcK
      nlinarith
  have hsK : s * K' t ≤ K t / 4 := by
    have : ℓ t * K' t = K t / 4 := by
      rw [liEvenCrossActualClockHistoryScale_eq]; field_simp
    nlinarith
  refine ⟨htan, hmono, by nlinarith, by linarith, by linarith⟩

/-- **(M6)** The crossing kernel is uniformly favorable on the window: `J_t(s) ≤ -K(t)/2`. -/
theorem liClockHistoryCrossingKernel_le_of_le_scale {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hsl : s ≤ ℓ t) : J t s ≤ -(K t / 2) := by
  obtain ⟨-, -, h3, h4, -⟩ := liClockThetaKernel_retention ht hs hsl
  unfold liClockHistoryCrossingKernel
  linarith

/-- **(M7)** `∫_0^ℓ s^q K(t-s) ds ≥ K(t) ℓ^{q+1}/(2(q+1))`. -/
theorem integral_pow_mul_liClockThetaKernel_scale_ge {t : ℝ} (ht : 0 < t) (q : ℕ) :
    K t * ℓ t ^ (q + 1) / (2 * (q + 1)) ≤ ∫ s in (0 : ℝ)..ℓ t, s ^ q * K (t - s) := by
  have hl := (liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht).2.1
  have hK := liClockThetaKernel_pos ht
  have hlow : ∀ s ∈ Icc (0 : ℝ) (ℓ t), s ^ q * (K t / 2) ≤ s ^ q * K (t - s) := fun s hs => by
    obtain ⟨h1, -, -, -, -⟩ := liClockThetaKernel_retention ht hs.1 hs.2
    have hsK : s * K' t ≤ K t / 2 := by
      obtain ⟨-, -, -, h4, -⟩ := liClockThetaKernel_retention ht hs.1 hs.2
      nlinarith [liClockThetaKernelDeriv_pos t, hs.1]
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hs.1 q)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hl.le
    ((by fun_prop : Continuous fun s : ℝ => s ^ q * (K t / 2)).intervalIntegrable _ _)
    (((continuous_pow q).mul (continuous_liClockThetaKernel.comp
      (continuous_const.sub continuous_id))).intervalIntegrable _ _) hlow
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_mul_const, integral_pow]
  field_simp
  ring

/-- **(M7)** `∫_0^t s² K(t-s) ds/(tK(t)) ≥ ℓ³/(6t)`, hence `→ ∞`: quadratic norm replacement fails. -/
theorem integral_sq_mul_liClockThetaKernel_div_ge {t : ℝ} (ht : 0 < t) :
    ℓ t ^ 3 / (6 * t) ≤ (∫ s in (0 : ℝ)..t, s ^ 2 * K (t - s)) / (t * K t) := by
  obtain ⟨-, hl, hlt⟩ := liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht
  have hK := liClockThetaKernel_pos ht
  have hc : Continuous fun s => s ^ 2 * K (t - s) :=
    (continuous_pow 2).mul (continuous_liClockThetaKernel.comp (continuous_const.sub continuous_id))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (ℓ t)) (hc.intervalIntegrable (μ := volume) (ℓ t) t)
  have hrest : 0 ≤ ∫ s in ℓ t..t, s ^ 2 * K (t - s) :=
    intervalIntegral.integral_nonneg (by linarith) fun s hs =>
      mul_nonneg (sq_nonneg s) (liClockThetaKernel_nonneg (by linarith [hs.2]))
  have h2 := integral_pow_mul_liClockThetaKernel_scale_ge ht 2
  rw [le_div_iff₀ (by positivity)]
  have e : ℓ t ^ 3 / (6 * t) * (t * K t) = K t * ℓ t ^ (2 + 1) / (2 * ((2 : ℕ) + 1)) := by
    push_cast; field_simp; ring
  rw [e, ← hsplit]
  linarith

theorem tendsto_integral_sq_mul_liClockThetaKernel_div_atTop :
    Tendsto (fun t => (∫ s in (0 : ℝ)..t, s ^ 2 * K (t - s)) / (t * K t)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_liEvenCrossActualClockHistoryScale_cube_div_atTop.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 6))
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h := integral_sq_mul_liClockThetaKernel_div_ge ht
  have e : ℓ t ^ 3 / t * (1 / 6) = ℓ t ^ 3 / (6 * t) := by field_simp
  rw [e]
  exact h

/-! ## (M8–M10) The complete age law -/

/-- **(M9)** The primitive equation retains the entire age history:
`P(t) = tK(t) - A(t) E_{Q_t}[P(S)]`. -/
theorem liEvenCrossActualClockPrimitive_eq_ageMean {t : ℝ} (ht : 0 < t) :
    P t = t * K t - A t * ∫ s, P s ∂Q t := by
  have hv := liEvenCrossActualClockPrimitive_volterra ht.le
  obtain ⟨-, hE⟩ := liEvenCrossActualClockHistoryAge_integral ht P
    continuous_liEvenCrossActualClockPrimitive
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  rw [hE, mul_div_cancel₀ _ hA.ne']
  rw [deriv_liEvenCrossActualClockBorelKernel_fun] at hv ⊢
  have e : ∫ s in (0 : ℝ)..t, K (t - s) * P s = ∫ s in (0 : ℝ)..t, P s * K (t - s) :=
    intervalIntegral.integral_congr fun s _ => mul_comm _ _
  rw [e]
  linarith

private theorem hasSum_liClockThetaKernel_odd (x : ℝ) :
    HasSum (fun j : ℕ => liClockThetaGeneratorCoeff (j + 1) * x ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℝ)) (K x) := by
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b hab => by simpa using hab
  have hzero : ∀ N ∉ Set.range (fun j : ℕ => 2 * j + 1), w x N = 0 := fun N hN => by
    have hN2 : N % 2 = 0 := by
      by_contra h
      exact hN ⟨N / 2, show 2 * (N / 2) + 1 = N by omega⟩
    simp [liEvenCrossActualClockDegreeWeight, liClockThetaKernelDegreeCoeff_of_even hN2]
  have h := (hinj.hasSum_iff hzero).2 (hasSum_degreeWeight x)
  have e : (w x ∘ fun j : ℕ => 2 * j + 1) = fun j : ℕ => liClockThetaGeneratorCoeff (j + 1) *
      x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := funext fun j => by
    simp only [Function.comp, liEvenCrossActualClockDegreeWeight, liClockThetaKernelDegreeCoeff,
      oddSpread, dividedPowerFn]
    rw [if_pos (by omega), show (2 * j + 1) / 2 = j by omega]
    ring
  rwa [e] at h

/-- **(M10)** The Beta weights `π_j(t) = ν_j t^{2j}/(((2j)!)² A(t))`, `j ≥ 1`, form a probability. -/
theorem hasSum_liEvenCrossActualClockHistoryAge_betaWeight {t : ℝ} (ht : 0 < t) :
    HasSum (fun j : ℕ => liEvenCrossActualClockBorelTerm t (j + 1) / A t) 1 := by
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  have h := (hasSum_nat_add_iff' 1).2 (summable_liEvenCrossActualClockBorelTerm t).hasSum
  have h0 : ∑ i ∈ Finset.range 1, liEvenCrossActualClockBorelTerm t i = 1 := by
    simp [liEvenCrossActualClockBorelTerm]
  rw [h0] at h
  have h' := h.div_const (A t)
  rwa [show (∑' j, liEvenCrossActualClockBorelTerm t j) - 1 = A t from rfl, div_self hA.ne'] at h'

/-- **(M10)** `Q_t` is the complete mixture of the Beta(1,2j) laws of `S/t`:
`K(t-s)/A(t) = Σ_{j≥1} π_j(t) (2j/t)(1 - s/t)^{2j-1}` for every `s`. -/
theorem hasSum_liEvenCrossActualClockHistoryAge_betaDensity {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasSum (fun j : ℕ => liEvenCrossActualClockBorelTerm t (j + 1) / A t *
      (2 * ((j + 1 : ℕ) : ℝ) / t * (1 - s / t) ^ (2 * (j + 1) - 1))) (K (t - s) / A t) := by
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  have h := (hasSum_liClockThetaKernel_odd (t - s)).div_const (A t)
  have e : ∀ j : ℕ, liClockThetaGeneratorCoeff (j + 1) * (t - s) ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℝ) / A t = liEvenCrossActualClockBorelTerm t (j + 1) / A t *
        (2 * ((j + 1 : ℕ) : ℝ) / t * (1 - s / t) ^ (2 * (j + 1) - 1)) := fun j => by
    have hf : ((2 * (j + 1)).factorial : ℝ) = (2 * j + 2) * ((2 * j + 1).factorial : ℝ) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hf1 : ((2 * j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, one_sub_div ht.ne', div_pow]
    unfold liEvenCrossActualClockBorelTerm liClockThetaGeneratorCoeff
    rw [hf]
    push_cast
    field_simp
    ring
  simp only [e] at h
  exact h

/-! ## (M11, M12) Two-scale escape of the age law -/

theorem tendsto_liEvenCrossActualClockBorelKernel_atTop : Tendsto B atTop atTop := by
  have h1 := thetaCuspNormalizedEvenMoment_pos 1
  refine tendsto_atTop_mono (fun t => liEvenCrossActualClockBorelTerm_le_kernel t 1) ?_
  have e : (fun t => liEvenCrossActualClockBorelTerm t 1) = fun t => ν 1 / 4 * t ^ 2 := by
    funext t; simp [liEvenCrossActualClockBorelTerm]; ring
  rw [e]
  exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)

private theorem tendsto_borel_div_excess : Tendsto (fun t => B t / A t) atTop (𝓝 1) := by
  have h : Tendsto (fun t => (1 - (B t)⁻¹)⁻¹) atTop (𝓝 1) := by
    have := ((tendsto_inv_atTop_zero.comp tendsto_liEvenCrossActualClockBorelKernel_atTop).const_sub
      1).inv₀ (by norm_num)
    simpa using this
  refine h.congr' ?_
  filter_upwards [tendsto_liEvenCrossActualClockBorelKernel_atTop.eventually_gt_atTop 1] with t ht
  unfold liEvenCrossActualClockHistoryExcess
  have : B t - 1 ≠ 0 := by linarith
  field_simp

/-- `K(t)/A(t) → 0`. -/
theorem tendsto_liClockThetaKernel_div_excess : Tendsto (fun t => K t / A t) atTop (𝓝 0) := by
  have h1 := tendsto_liEvenCrossActualClockBorel_deriv_div_kernel_zero
  rw [deriv_liEvenCrossActualClockBorelKernel_fun] at h1
  have h := h1.mul tendsto_borel_div_excess
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [tendsto_liEvenCrossActualClockBorelKernel_atTop.eventually_gt_atTop 1] with t ht
  have : B t ≠ 0 := by linarith
  field_simp

theorem strictMono_liClockThetaKernel : StrictMono K :=
  strictMono_of_hasDerivAt_pos hasDerivAt_liClockThetaKernel liClockThetaKernelDeriv_pos

/-- **(M11)** Every fixed age interval is escaped: `Q_t[0,R] → 0`. -/
theorem tendsto_liEvenCrossActualClockHistoryAge_Icc_zero {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun t => (Q t).real (Icc 0 R)) atTop (𝓝 0) := by
  have hKA := tendsto_liClockThetaKernel_div_excess.const_mul R
  rw [mul_zero] at hKA
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKA
    (Eventually.of_forall fun t => measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop R, eventually_gt_atTop 0] with t htR ht
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  rw [liEvenCrossActualClockHistoryAge_Icc_zero ht hR, min_eq_left htR.le, div_le_iff₀ hA,
    show R * (K t / A t) * A t = R * K t by field_simp]
  unfold liEvenCrossActualClockHistoryExcess
  rcases hR.eq_or_lt with rfl | hR'
  · simp
  · obtain ⟨c, hc, hcK⟩ := exists_hasDerivAt_eq_slope B K (by linarith : t - R < t)
      continuous_liEvenCrossActualClockBorelKernel.continuousOn
      fun x _ => hasDerivAt_liEvenCrossActualClockBorelKernel_eq x
    have hc' : K c ≤ K t := strictMono_liClockThetaKernel.monotone hc.2.le
    rw [show t - (t - R) = R by ring, eq_div_iff hR'.ne'] at hcK
    nlinarith

/-- `B(at) ≤ Prefix_J(t) + a^{2J} B(t)` for `0 ≤ a ≤ 1`: every term retained. -/
theorem liEvenCrossActualClockBorelKernel_mul_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (t : ℝ) : B (a * t) ≤ liEvenCrossActualClockBorelPrefix n t + a ^ (2 * n) * B t := by
  have hterm : ∀ j, liEvenCrossActualClockBorelTerm (a * t) j =
      a ^ (2 * j) * liEvenCrossActualClockBorelTerm t j := fun j => by
    unfold liEvenCrossActualClockBorelTerm; rw [mul_pow]; ring
  have hs := summable_liEvenCrossActualClockBorelTerm t
  have hsa := summable_liEvenCrossActualClockBorelTerm (a * t)
  have hnn := liEvenCrossActualClockBorelTerm_nonneg t
  have hB : B (a * t) = ∑ j ∈ Finset.range n, liEvenCrossActualClockBorelTerm (a * t) j +
      ∑' j, liEvenCrossActualClockBorelTerm (a * t) (j + n) := (hsa.sum_add_tsum_nat_add n).symm
  have hBt : B t = ∑ j ∈ Finset.range n, liEvenCrossActualClockBorelTerm t j +
      ∑' j, liEvenCrossActualClockBorelTerm t (j + n) := (hs.sum_add_tsum_nat_add n).symm
  have hpre : ∑ j ∈ Finset.range n, liEvenCrossActualClockBorelTerm (a * t) j ≤
      liEvenCrossActualClockBorelPrefix n t := Finset.sum_le_sum fun j _ => by
    rw [hterm]
    exact mul_le_of_le_one_left (hnn j) (pow_le_one₀ ha ha1)
  have htail : ∑' j, liEvenCrossActualClockBorelTerm (a * t) (j + n) ≤
      a ^ (2 * n) * ∑' j, liEvenCrossActualClockBorelTerm t (j + n) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) ((summable_nat_add_iff n).2 hsa)
      (((summable_nat_add_iff n).2 hs).mul_left _)
    rw [hterm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha ha1 (by omega)) (hnn _)
  have hpre_nn : 0 ≤ ∑ j ∈ Finset.range n, liEvenCrossActualClockBorelTerm t j :=
    Finset.sum_nonneg fun j _ => hnn j
  have haJ : 0 ≤ a ^ (2 * n) := pow_nonneg ha _
  have htB : ∑' j, liEvenCrossActualClockBorelTerm t (j + n) ≤ B t := by linarith
  have hm := mul_le_mul_of_nonneg_left htB haJ
  rw [hB]
  linarith

/-- `B(at)/B(t) → 0` for every fixed `0 ≤ a < 1`. -/
theorem tendsto_liEvenCrossActualClockBorelKernel_mul_div {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun t => B (a * t) / B t) atTop (𝓝 0) := by
  have hpos : ∀ t, 0 < B t := fun t => one_pos.trans_le (one_le_liEvenCrossActualClockBorelKernel t)
  refine tendsto_order.2 ⟨fun η hη => Eventually.of_forall fun t =>
    lt_of_lt_of_le hη (div_nonneg (hpos _).le (hpos _).le), fun η hη => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη) (by nlinarith : a ^ 2 < 1)
  filter_upwards [(tendsto_order.1 (liEvenCrossActualClockBorelPrefix_div_kernel_tendsto n)).2 _
    (half_pos hη)] with t ht
  have h := liEvenCrossActualClockBorelKernel_mul_le ha ha1.le n t
  rw [div_lt_iff₀ (hpos t)]
  rw [div_lt_iff₀ (hpos t)] at ht
  rw [pow_mul] at h
  nlinarith [hpos t]

/-- `A(at)/A(t) → 0` for every fixed `0 ≤ a < 1`. -/
theorem tendsto_liEvenCrossActualClockHistoryExcess_mul_div {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun t => A (a * t) / A t) atTop (𝓝 0) := by
  have h := (tendsto_liEvenCrossActualClockBorelKernel_mul_div ha ha1).mul tendsto_borel_div_excess
  rw [zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact div_nonneg (sub_nonneg.2 (one_le_liEvenCrossActualClockBorelKernel _))
      (liEvenCrossActualClockHistory_geometry ht).1.le
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hA := (liEvenCrossActualClockHistory_geometry ht).1
    have hB : 0 < B t := one_pos.trans_le (one_le_liEvenCrossActualClockBorelKernel t)
    rw [div_mul_div_comm, mul_comm (B t), ← div_mul_div_comm, div_self hB.ne', mul_one]
    exact div_le_div_of_nonneg_right (by unfold liEvenCrossActualClockHistoryExcess; linarith) hA.le

theorem liEvenCrossActualClockHistoryAge_singleton (t x : ℝ) : Q t {x} = 0 := by
  have hac : Q t ≪ volume := (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact hac (Real.volume_singleton)

theorem liEvenCrossActualClockHistoryAge_Icc_self {t : ℝ} (ht : 0 < t) :
    (Q t).real (Icc 0 t) = 1 := by
  rw [liEvenCrossActualClockHistoryAge_Icc_zero ht ht.le, min_self, sub_self]
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  have h0 : A 0 = 0 := by simp [liEvenCrossActualClockHistoryExcess]
  rw [h0, sub_zero, div_self hA.ne']

/-- **(M11)** `Q_t[εt, t] ≤ A((1-ε)t)/A(t)`. -/
theorem liEvenCrossActualClockHistoryAge_Icc_frac_le {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) : (Q t).real (Icc (ε * t) t) ≤ A ((1 - ε) * t) / A t := by
  haveI := (liEvenCrossActualClockHistoryAge_admission ht).1
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  have hεt : ε * t ≤ t := mul_le_of_le_one_left ht.le hε1
  have hεt0 : 0 ≤ ε * t := mul_nonneg hε ht.le
  have hsplit : (Q t).real (Icc 0 (ε * t)) + (Q t).real (Ioc (ε * t) t) = 1 := by
    rw [← measureReal_union (Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx'.1)
      measurableSet_Ioc, Icc_union_Ioc_eq_Icc hεt0 hεt, liEvenCrossActualClockHistoryAge_Icc_self ht]
  have hcut := liEvenCrossActualClockHistoryAge_Icc_zero ht hεt0
  rw [min_eq_left hεt] at hcut
  have hle : (Q t).real (Icc (ε * t) t) ≤ (Q t).real (Ioc (ε * t) t) := by
    have h0 : (Q t).real {ε * t} = 0 := by
      rw [measureReal_def, liEvenCrossActualClockHistoryAge_singleton, ENNReal.toReal_zero]
    rw [← Ioc_insert_left hεt, Set.insert_eq]
    refine (measureReal_union_le _ _).trans ?_
    rw [h0, zero_add]
  rw [show (1 - ε) * t = t - ε * t by ring]
  have : (A t - A (t - ε * t)) / A t + A (t - ε * t) / A t = 1 := by
    rw [← add_div, sub_add_cancel, div_self hA.ne']
  linarith

/-- **(M11)** Concentration below every fixed clock fraction: `Q_t[εt, t] → 0` for `0 < ε < 1`. -/
theorem tendsto_liEvenCrossActualClockHistoryAge_Icc_frac {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun t => (Q t).real (Icc (ε * t) t)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_liEvenCrossActualClockHistoryExcess_mul_div (a := 1 - ε) (by linarith) (by linarith))
    (Eventually.of_forall fun t => measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact liEvenCrossActualClockHistoryAge_Icc_frac_le ht hε.le hε1.le

/-- **(M11)** The age law concentrates on `(R, εt)`: `Q_t(R, εt) → 1`. -/
theorem tendsto_liEvenCrossActualClockHistoryAge_Ioo {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hε1 : ε < 1) : Tendsto (fun t => (Q t).real (Ioo R (ε * t))) atTop (𝓝 1) := by
  have h := ((tendsto_liEvenCrossActualClockHistoryAge_Icc_zero hR).add
    (tendsto_liEvenCrossActualClockHistoryAge_Icc_frac hε hε1)).const_sub 1
  rw [add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (R / ε), eventually_gt_atTop 0] with t htR ht
  haveI := (liEvenCrossActualClockHistoryAge_admission ht).1
  have hRt : R < ε * t := by rwa [div_lt_iff₀ hε, mul_comm] at htR
  have hεt : ε * t ≤ t := mul_le_of_le_one_left ht.le hε1.le
  have hunion : Icc 0 t = (Icc 0 R ∪ Ioo R (ε * t)) ∪ Icc (ε * t) t := by
    ext x
    simp only [mem_Icc, mem_union, mem_Ioo]
    constructor
    · rintro ⟨h0, h1⟩
      by_cases hxR : x ≤ R
      · exact Or.inl (Or.inl ⟨h0, hxR⟩)
      · by_cases hxe : x < ε * t
        · exact Or.inl (Or.inr ⟨not_le.1 hxR, hxe⟩)
        · exact Or.inr ⟨not_lt.1 hxe, h1⟩
    · rintro ((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩)
      · exact ⟨h0, h1.trans (by linarith)⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, h1⟩
  have h1 := liEvenCrossActualClockHistoryAge_Icc_self ht
  rw [hunion, measureReal_union (Set.disjoint_left.2 fun x hx hx' => by
      rcases hx with hx | hx
      · linarith [hx.2, hx'.1]
      · linarith [hx.2, hx'.1]) measurableSet_Icc,
    measureReal_union (Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1])
      measurableSet_Ioo] at h1
  linarith

/-- **(M12)** `E_{Q_t} S^q → ∞` for every fixed `q ≥ 1`. -/
theorem tendsto_liEvenCrossActualClockHistoryAge_moment_atTop {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun t => ∫ s, s ^ q ∂Q t) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  set R := max 1 (2 * M) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRq : 2 * M ≤ R ^ q := (le_max_right _ _).trans (le_self_pow₀ hR1 (by omega))
  filter_upwards [(tendsto_order.1 (tendsto_liEvenCrossActualClockHistoryAge_Ioo
    (by linarith : (0 : ℝ) ≤ R) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num))).1 (1 / 2)
      (by norm_num), eventually_gt_atTop 0] with t hQ ht
  obtain ⟨hprob, hsupp, hint⟩ := liEvenCrossActualClockHistoryAge_admission ht
  haveI := hprob
  have hlow : ∫ s, (Ioo R (1 / 2 * t)).indicator (fun _ => R ^ q) s ∂Q t ≤ ∫ s, s ^ q ∂Q t := by
    refine integral_mono_ae ((integrable_const _).indicator measurableSet_Ioo) (hint q) ?_
    filter_upwards [hsupp] with s hs
    by_cases hs' : s ∈ Ioo R (1 / 2 * t)
    · rw [indicator_of_mem hs']
      exact pow_le_pow_left₀ (by linarith) hs'.1.le q
    · rw [indicator_of_notMem hs']
      exact pow_nonneg hs.1 q
  rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul] at hlow
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ R) q]

/-- **(M12)** `E_{Q_t} (S/t)^q → 0` for every fixed `q ≥ 1`. -/
theorem tendsto_liEvenCrossActualClockHistoryAge_scaled_moment {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun t => ∫ s, (s / t) ^ q ∂Q t) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun η hη => ?_, fun η hη => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht
    obtain ⟨hprob, hsupp, -⟩ := liEvenCrossActualClockHistoryAge_admission ht
    refine lt_of_lt_of_le hη (integral_nonneg_of_ae ?_)
    filter_upwards [hsupp] with s hs
    exact pow_nonneg (div_nonneg hs.1 ht.le) q
  · obtain ⟨ε, hε, hε1, hεq⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε ^ q < η / 2 := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη) (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨(1 / 2) ^ n / 2 + 0, by positivity, ?_, ?_⟩
      · have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      · have hb : (1 / 2 : ℝ) ^ n / 2 + 0 < 1 := by
          have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          linarith
        calc ((1 / 2 : ℝ) ^ n / 2 + 0) ^ q ≤ (1 / 2 : ℝ) ^ n / 2 + 0 :=
              pow_le_of_le_one (by positivity) hb.le (by omega)
          _ < η / 2 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    filter_upwards [(tendsto_order.1 (tendsto_liEvenCrossActualClockHistoryAge_Icc_frac hε hε1)).2
      (η / 2) (half_pos hη), eventually_gt_atTop 0] with t hQ ht
    obtain ⟨hprob, hsupp, -⟩ := liEvenCrossActualClockHistoryAge_admission ht
    haveI := hprob
    have hcont : Continuous fun s : ℝ => (s / t) ^ q := by fun_prop
    have hup : ∫ s, (s / t) ^ q ∂Q t ≤
        ∫ s, (ε ^ q + (Icc (ε * t) t).indicator (fun _ => (1 : ℝ)) s) ∂Q t := by
      refine integral_mono_ae (liEvenCrossActualClockHistoryAge_integral ht _ hcont).1
        ((integrable_const _).add ((integrable_const _).indicator measurableSet_Icc)) ?_
      filter_upwards [hsupp] with s hs
      have h0 : 0 ≤ s / t := div_nonneg hs.1 ht.le
      have h1 : s / t ≤ 1 := (div_le_one ht).2 hs.2
      by_cases hs' : s ∈ Icc (ε * t) t
      · rw [indicator_of_mem hs']
        linarith [pow_le_one₀ h0 h1 (n := q), pow_nonneg hε.le q]
      · rw [indicator_of_notMem hs', add_zero]
        have hlt : s < ε * t := by
          by_contra hge
          exact hs' ⟨not_lt.1 hge, hs.2⟩
        exact pow_le_pow_left₀ h0 (by rw [div_le_iff₀ ht]; linarith) q
    rw [integral_add (integrable_const _) ((integrable_const _).indicator measurableSet_Icc),
      integral_const, integral_indicator_const _ measurableSet_Icc, probReal_univ, one_smul,
      smul_eq_mul, mul_one] at hup
    linarith

/-! ## (M14) The favorable window in the crossing law, and conservation of `J_t` -/

theorem continuous_liEvenCrossActualClockLogHistory : Continuous D := by
  have e : D = liEvenCrossActualClockDampedCutoff 0 :=
    funext liEvenCrossActualClockLogHistory_eq_dampedCutoff_zero
  rw [e]
  exact continuous_liEvenCrossActualClockDampedCutoff 0

/-- **(M14)** At every clock with `D ≥ 0` on `[0, ℓ(t)]`,
`tD'(t) ≥ tK(t) + (K(t)/2) ∫_0^ℓ D - ∫_ℓ^t D J_t`. -/
theorem liEvenCrossActualClockLogHistory_crossing_ge {t : ℝ} (ht : 0 < t)
    (hD : ∀ s ∈ Icc 0 (ℓ t), 0 ≤ D s) :
    t * K t + K t / 2 * (∫ s in (0 : ℝ)..ℓ t, D s) - ∫ s in ℓ t..t, D s * J t s ≤
      t * deriv D t := by
  obtain ⟨-, hl, hlt⟩ := liEvenCrossActualClockHistoryScale_eq_div_meanDegree ht
  have hc : Continuous fun s => D s * J t s :=
    continuous_liEvenCrossActualClockLogHistory.mul (continuous_liClockHistoryCrossingKernel t)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (ℓ t)) (hc.intervalIntegrable (μ := volume) (ℓ t) t)
  have hwin : ∫ s in (0 : ℝ)..ℓ t, D s * J t s ≤ ∫ s in (0 : ℝ)..ℓ t, D s * -(K t / 2) :=
    intervalIntegral.integral_mono_on hl.le (hc.intervalIntegrable _ _)
      ((continuous_liEvenCrossActualClockLogHistory.mul continuous_const).intervalIntegrable _ _)
      fun s hs => mul_le_mul_of_nonneg_left
        (liClockHistoryCrossingKernel_le_of_le_scale ht hs.1 hs.2) (hD s hs)
  rw [intervalIntegral.integral_mul_const] at hwin
  rw [liEvenCrossActualClockLogHistory_crossing_eq ht.le, ← hsplit]
  nlinarith [hwin]

/-- **(M15 ⇒ slope)** If `D ≥ 0` on `[0, ℓ(t)]` and the outside correlation obeys
`∫_ℓ^t D J_t ≤ tK(t) + (K(t)/2) ∫_0^ℓ D`, then `D'(t) ≥ 0`. -/
theorem deriv_liEvenCrossActualClockLogHistory_nonneg_of_outside {t : ℝ} (ht : 0 < t)
    (hD : ∀ s ∈ Icc 0 (ℓ t), 0 ≤ D s)
    (hout : ∫ s in ℓ t..t, D s * J t s ≤ t * K t + K t / 2 * (∫ s in (0 : ℝ)..ℓ t, D s)) :
    0 ≤ deriv D t := by
  have h := liEvenCrossActualClockLogHistory_crossing_ge ht hD
  have : 0 ≤ t * deriv D t := by linarith
  exact nonneg_of_mul_nonneg_right (by linarith) ht

/-- `J_t(s) = -∂_s (s K(t-s))`. -/
theorem hasDerivAt_mul_liClockThetaKernel_sub (t s : ℝ) :
    HasDerivAt (fun s => s * K (t - s)) (-J t s) s := by
  have hK : HasDerivAt (fun s => K (t - s)) (K' (t - s) * -1) s :=
    (hasDerivAt_liClockThetaKernel (t - s)).comp s ((hasDerivAt_id s).const_sub t)
  have h := (hasDerivAt_id' s).mul hK
  refine h.congr_deriv ?_
  unfold liClockHistoryCrossingKernel
  ring

private theorem hasDerivAt_neg_mul_liClockThetaKernel_sub (t s : ℝ) :
    HasDerivAt (fun s => -(s * K (t - s))) (J t s) s := by
  have h := (hasDerivAt_mul_liClockThetaKernel_sub t s).neg
  rwa [neg_neg] at h

/-- `∫_0^x J_t = -x K(t-x)`. -/
theorem integral_liClockHistoryCrossingKernel (t x : ℝ) :
    ∫ s in (0 : ℝ)..x, J t s = -(x * K (t - x)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_neg_mul_liClockThetaKernel_sub t s)
    ((continuous_liClockHistoryCrossingKernel t).intervalIntegrable 0 x)]
  simp

/-- `∫_0^x J_t ≤ 0` for `0 ≤ x ≤ t`. -/
theorem integral_liClockHistoryCrossingKernel_nonpos {t x : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) :
    ∫ s in (0 : ℝ)..x, J t s ≤ 0 := by
  rw [integral_liClockHistoryCrossingKernel, neg_nonpos]
  exact mul_nonneg hx (liClockThetaKernel_nonneg (by linarith))

/-- `∫_0^t J_t = 0`. -/
theorem integral_liClockHistoryCrossingKernel_self (t : ℝ) : ∫ s in (0 : ℝ)..t, J t s = 0 := by
  rw [integral_liClockHistoryCrossingKernel, sub_self, liClockThetaKernel_zero, mul_zero, neg_zero]

/-- For every `C¹` test `φ`: `∫_0^t φ J_t = ∫_0^t φ'(s) s K(t-s) ds`. -/
theorem integral_mul_liClockHistoryCrossingKernel {φ φ' : ℝ → ℝ}
    (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hφ' : Continuous φ') (t : ℝ) :
    ∫ s in (0 : ℝ)..t, φ s * J t s = ∫ s in (0 : ℝ)..t, φ' s * (s * K (t - s)) := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := t)
    (fun s _ => hφ s) (fun s _ => hasDerivAt_neg_mul_liClockThetaKernel_sub t s)
    (hφ'.intervalIntegrable _ _) ((continuous_liClockHistoryCrossingKernel t).intervalIntegrable _ _)]
  simp only [sub_self, liClockThetaKernel_zero, mul_zero, zero_mul, neg_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

end RHTower
