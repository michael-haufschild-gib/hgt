import GaloisForLFunctions.HTGeometry.SmoothPlateau
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDIOverHeight
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# The smoothed unit block and its Fourier transform

The unit block `U_N(t) = ∑_{N < n ≤ N'} n^{-1-it}` is the sum over the integers of
`f_t(x) = φ(x) x^{-1} e^{-it log x}`, where `φ` is the smooth plateau that is `0` off
`(N + ¼, N' + ¾)` and `1` on `[N + ¾, N' + ¼]`: the window takes the value `1[N < n ≤ N']` at
every integer `n` (`tsum_ubKernel_eq`).

The Fourier transform of `f_t` at `−k` is the oscillatory integral

`ubFreq N N' t k = ∫_N^{N'+1} φ(x) x^{-1} e^{i(2πkx − t log x)} dx`

(`fourier_ubKernel_neg`), whose phase `Θ_k(x) = 2πkx − t log x` has `Θ_k' = 2πk − t/x` and
`Θ_k'' = t/x² ≥ 0`.  The frequency `k` is stationary exactly when `t/(2πk)` lies in the support.
-/

open Complex Set MeasureTheory intervalIntegral Filter Asymptotics
open GaloisForLFunctions.HTGeometry
open scoped Real FourierTransform

namespace RHTower.Sieve

noncomputable section

/-- The smooth window of the unit block `(N, N']`. -/
def ubWindow (N N' : ℕ) (x : ℝ) : ℝ := smoothPlateau ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x

/-- The real amplitude `φ(x)/x`. -/
def ubAmp (N N' : ℕ) (x : ℝ) : ℝ := ubWindow N N' x / x

/-- The smoothed summand `f_t(x) = φ(x) x^{-1} e^{-it log x}`. -/
def ubKernel (N N' : ℕ) (t x : ℝ) : ℂ :=
  (ubAmp N N' x : ℂ) * Complex.exp (((-(t * Real.log x) : ℝ) : ℂ) * I)

/-- The phase `Θ_k(x) = 2πkx − t log x` of the `(−k)`-th Fourier coefficient. -/
def ubPhase (t : ℝ) (k : ℤ) (x : ℝ) : ℝ := 2 * π * k * x - t * Real.log x

/-- The `(−k)`-th Fourier coefficient of the smoothed summand. -/
def ubFreq (N N' : ℕ) (t : ℝ) (k : ℤ) : ℂ :=
  ∫ x in (N : ℝ)..((N' : ℝ) + 1), (ubAmp N N' x : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I)

variable {N N' : ℕ}

theorem ubWindow_eq_zero_of_le {x : ℝ} (hx : x ≤ (N : ℝ) + 1 / 4) : ubWindow N N' x = 0 :=
  smoothPlateau_eq_zero_of_le (by norm_num) hx

theorem ubWindow_eq_zero_of_ge {x : ℝ} (hx : (N' : ℝ) + 3 / 4 ≤ x) : ubWindow N N' x = 0 :=
  smoothPlateau_eq_zero_of_ge (by norm_num) hx

theorem ubWindow_eq_one {x : ℝ} (h1 : (N : ℝ) + 3 / 4 ≤ x) (h2 : x ≤ (N' : ℝ) + 1 / 4) :
    ubWindow N N' x = 1 :=
  smoothPlateau_eq_one (by norm_num) (by linarith) (by linarith)

theorem ubAmp_eq_zero_of_le {x : ℝ} (hx : x ≤ (N : ℝ) + 1 / 4) : ubAmp N N' x = 0 := by
  rw [ubAmp, ubWindow_eq_zero_of_le hx, zero_div]

theorem ubAmp_eq_zero_of_ge {x : ℝ} (hx : (N' : ℝ) + 3 / 4 ≤ x) : ubAmp N N' x = 0 := by
  rw [ubAmp, ubWindow_eq_zero_of_ge hx, zero_div]

theorem ubKernel_eq_zero_of_not_mem {t x : ℝ}
    (hx : x ∉ Ioo ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4)) : ubKernel N N' t x = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · rw [ubKernel, ubAmp_eq_zero_of_le hx]; simp
  · rw [ubKernel, ubAmp_eq_zero_of_ge hx]; simp

/-- At a positive integer the smoothed summand is the sharp block summand. -/
theorem ubKernel_natCast (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ubKernel N N' t n = if N < n ∧ n ≤ N' then (n : ℂ) ^ (-(1 : ℂ) - I * (t : ℂ)) else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h : N < n ∧ n ≤ N'
  · rw [if_pos h]
    have h1 : (N : ℝ) + 3 / 4 ≤ n := by
      have : N + 1 ≤ n := h.1
      have : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have h2 : (n : ℝ) ≤ (N' : ℝ) + 1 / 4 := by
      have : (n : ℝ) ≤ N' := by exact_mod_cast h.2
      linarith
    rw [ubKernel, ubAmp, ubWindow_eq_one h1 h2, Complex.cpow_def_of_ne_zero
      (by exact_mod_cast hn0.ne'), ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    rw [show ((Real.log n : ℝ) : ℂ) * (-(1 : ℂ) - I * (t : ℂ)) =
        ((-Real.log n : ℝ) : ℂ) + ((-(t * Real.log n) : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn0, one_div]
  · rw [if_neg h]
    refine ubKernel_eq_zero_of_not_mem fun hx => h ⟨?_, ?_⟩
    · have : (N : ℝ) < n := by linarith [hx.1]
      exact_mod_cast this
    · have : (n : ℝ) < (N' : ℝ) + 1 := by linarith [hx.2]
      have : n < N' + 1 := by exact_mod_cast this
      omega

/-- **The sum of the smoothed summand over the integers is the unit block.** -/
theorem tsum_ubKernel_eq (hN : 1 ≤ N) (t : ℝ) :
    ∑' n : ℤ, ubKernel N N' t n = mtWattUnitBlock N N' t := by
  classical
  rw [mtWattUnitBlock_eq_sum_Ico]
  have hsupp : ∀ n : ℤ, n ∉ (Finset.Ico (N + 1) (N' + 1)).map Nat.castEmbedding →
      ubKernel N N' t n = 0 := by
    intro n hn
    by_cases hpos : 1 ≤ n
    · lift n to ℕ using (by omega)
      have hn1 : 1 ≤ n := by exact_mod_cast hpos
      rw [show ((n : ℤ) : ℝ) = (n : ℝ) by push_cast; rfl, ubKernel_natCast t hn1, if_neg]
      rintro ⟨h1, h2⟩
      exact hn (Finset.mem_map.2 ⟨n, Finset.mem_Ico.2 ⟨h1, by omega⟩, rfl⟩)
    · refine ubKernel_eq_zero_of_not_mem fun hx => ?_
      have : (n : ℝ) ≤ 0 := by exact_mod_cast (by omega : n ≤ 0)
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith [hx.1]
  rw [tsum_eq_sum hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
  simp only [Nat.castEmbedding_apply]
  rw [show (((n : ℤ) : ℝ)) = (n : ℝ) by push_cast; rfl, ubKernel_natCast t (by omega),
    if_pos ⟨by omega, by omega⟩]

theorem continuous_ubWindow : Continuous (ubWindow N N') := continuous_smoothPlateau

/-- The smoothed summand is continuous: it vanishes near every point left of the window. -/
theorem continuous_ubKernel (t : ℝ) : Continuous (ubKernel N N' t) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_or_ge x ((N : ℝ) + 1 / 4) with hx | hx
  · have hev : ubKernel N N' t =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact ubKernel_eq_zero_of_not_mem fun h => absurd h.1 (not_lt.2 (le_of_lt hy))
    exact (continuousAt_congr hev).2 continuousAt_const
  · have hx0 : x ≠ 0 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      intro h; rw [h] at hx; linarith
    unfold ubKernel ubAmp
    refine (Complex.continuous_ofReal.continuousAt.comp
      ((continuous_ubWindow.continuousAt).div continuousAt_id hx0)).mul ?_
    refine Complex.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    exact (continuousAt_const.mul (Real.continuousAt_log hx0)).neg

/-- The smoothed summand has compact support, hence decays at every rate. -/
theorem ubKernel_isBigO_cocompact (t b : ℝ) :
    (ubKernel N N' t) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b) := by
  have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[cocompact ℝ] ubKernel N N' t := by
    filter_upwards [(isCompact_Icc (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)).compl_mem_cocompact]
      with x hx
    exact (ubKernel_eq_zero_of_not_mem fun h => hx (Ioo_subset_Icc_self h)).symm
  exact (isBigO_zero _ _).congr' hev EventuallyEq.rfl

/-- **The Fourier coefficient at `−k` is the oscillatory integral `ubFreq`.** -/
theorem fourier_ubKernel_neg (hNN' : N ≤ N') (t : ℝ) (k : ℤ) :
    𝓕 (ubKernel N N' t) (-(k : ℝ)) = ubFreq N N' t k := by
  have hle : (N : ℝ) ≤ N' + 1 := by
    have : (N : ℝ) ≤ N' := by exact_mod_cast hNN'
    linarith
  rw [Real.fourier_real_eq_integral_exp_smul, ubFreq, intervalIntegral.integral_of_le hle]
  have hpt : ∀ v : ℝ, Complex.exp (((-2 * π * v * -(k : ℝ)) : ℝ) * I) • ubKernel N N' t v =
      (ubAmp N N' v : ℂ) * Complex.exp ((ubPhase t k v : ℂ) * I) := by
    intro v
    rw [smul_eq_mul, ubKernel, ubPhase, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [hpt]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
  have : ubAmp N N' v = 0 := by
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hv
    rcases hv with hv | hv
    · exact ubAmp_eq_zero_of_le (by linarith)
    · exact ubAmp_eq_zero_of_ge (by linarith)
  rw [this]; simp

end

end RHTower.Sieve
