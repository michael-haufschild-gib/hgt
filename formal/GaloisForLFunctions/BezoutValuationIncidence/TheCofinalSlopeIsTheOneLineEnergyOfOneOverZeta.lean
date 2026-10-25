import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalSlopeIsASumOfCoprimeEnergies
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The cofinal Möbius slope is the one-line energy of `1/ζ`

The coprime profile `g_δ(v) = T_δ(⌊e^v⌋₊)` is a sum of steps `w(a) 1_{v ≥ log a}` over `a`
prime to `δ`, so its Laplace transform is a Dirichlet series:

  `∫ g_δ(v) e^{−sv} dv = L(c_δ, s)/s`,  `Re s > 0`,  `c_δ = w·1_{(·,δ)=1}`
  (`coprimeLaplace_eq_LSeries_div`).

The kernel identity `c_δ = β_δ ⋆ (μ/id)`, `β_δ(n) = n^{−1} ∏_{p ∣ n, p ∤ δ} (p+1)^{−1}`, gives
`L(c_δ, s) = L(β_δ, s)/ζ(1+s)`, and `L(β_δ, ·)` converges absolutely on `Re s ≥ 0`. Dominated
convergence as `Re s ↓ 0`, continuity of `ζ` at `1 + it` and `ζ(1+it) ≠ 0` give the boundary value

  `ĝ_δ(t) = L(β_δ, it) / (it ζ(1+it))`,  `t ≠ 0`  (`coprimeLaplace_imaginary`),

and Plancherel turns the coprime energy into a one-line integral. With the signed energy sum of
`TheCofinalSlopeIsASumOfCoprimeEnergies`:

  `κ = (ρ/2π) ∫_ℝ (Σ_{δ ≥ 1} μ(δ) w(δ)² |L(β_δ, it)|²) / |t ζ(1+it)|² dt`
  (`cofinalMobiusSlope_eq_integral_one_line`).

The cofinal slope of the Möbius energy profile reads `1/ζ` on the line `Re s = 1`, weighted by an
absolutely convergent arithmetic factor.
-/

open MeasureTheory Set Filter ArithmeticFunction Complex Topology

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ### The profile as a sum of steps -/

theorem coprimeMoebiusSigmaSum_eq_sum (δ Y : ℕ) :
    coprimeMoebiusSigmaSum δ Y = ∑ a ∈ Finset.Icc 1 Y, coprimeMoebiusSigma δ a := rfl

/-- `g_δ(v) = Σ_a w(a+1) 1_{(a+1,δ)=1} 1_{v ≥ log(a+1)}`. -/
theorem coprimeProfile_eq_tsum (δ : ℕ) (v : ℝ) :
    coprimeProfile δ v = ∑' a : ℕ, (Ici (Real.log ((a : ℝ) + 1))).indicator
      (fun _ => coprimeMoebiusSigma δ (a + 1)) v := by
  set X := ⌊Real.exp v⌋₊ with hX
  have hmem : ∀ a : ℕ, v ∈ Ici (Real.log ((a : ℝ) + 1)) ↔ a < X := by
    intro a
    rw [Set.mem_Ici, Real.log_le_iff_le_exp (by positivity), hX, Nat.lt_iff_add_one_le,
      Nat.le_floor_iff (Real.exp_pos v).le]
    push_cast; rfl
  rw [tsum_eq_sum (s := Finset.range X) (fun a ha => by
    rw [Finset.mem_range, not_lt] at ha
    exact Set.indicator_of_notMem (fun h => absurd ((hmem a).mp h) (not_lt.mpr ha)) _)]
  rw [coprimeProfile, coprimeMoebiusSigmaSum_eq_sum, ← hX]
  rw [Finset.sum_congr rfl fun a ha => Set.indicator_of_mem ((hmem a).mpr (Finset.mem_range.mp ha))
    (fun _ => coprimeMoebiusSigma δ (a + 1))]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun a => coprimeMoebiusSigma δ a) 0 X 1]
  rfl

/-! ### The Laplace transform -/

/-- The Laplace transform `ĝ_δ(s) = ∫ g_δ(v) e^{−sv} dv`. -/
def coprimeLaplace (δ : ℕ) (s : ℂ) : ℂ := ∫ v : ℝ, (coprimeProfile δ v : ℂ) * Complex.exp (-s * v)

/-- The coefficients `c_δ(n) = w(n) 1_{(n,δ)=1}` as a complex sequence. -/
def coprimeCoeff (δ : ℕ) (n : ℕ) : ℂ := (coprimeMoebiusSigma δ n : ℂ)

theorem abs_coprimeMoebiusSigma_le (δ n : ℕ) : |coprimeMoebiusSigma δ n| ≤ (n : ℝ)⁻¹ := by
  rw [coprimeMoebiusSigma_apply]
  split_ifs
  · exact abs_moebiusSigma_le n
  · rw [abs_zero]; positivity

theorem cexp_neg_mul_log (s : ℂ) (a : ℕ) :
    Complex.exp (-s * (Real.log ((a : ℝ) + 1) : ℝ)) = (((a + 1 : ℕ) : ℂ) ^ s)⁻¹ := by
  have hpos : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
  have hne : ((a + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
  rw [Complex.ofReal_log hpos, cpow_def_of_ne_zero hne, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- One step: `∫ 1_{v ≥ log(a+1)} c e^{−sv} dv = c (a+1)^{−s}/s` for `Re s > 0`. -/
theorem integral_indicator_step {s : ℂ} (hs : 0 < s.re) (a : ℕ) (c : ℝ) :
    ∫ v : ℝ, ((Ici (Real.log ((a : ℝ) + 1))).indicator (fun _ => c) v : ℂ) *
      Complex.exp (-s * v) = c * (((a + 1 : ℕ) : ℂ) ^ s)⁻¹ / s := by
  have hre : (-s).re < 0 := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have h1 : (fun v : ℝ => ((Ici (Real.log ((a : ℝ) + 1))).indicator (fun _ => c) v : ℂ) *
      Complex.exp (-s * v)) = (Ici (Real.log ((a : ℝ) + 1))).indicator
        (fun v => (c : ℂ) * Complex.exp (-s * v)) := by
    funext v
    by_cases hv : v ∈ Ici (Real.log ((a : ℝ) + 1))
    · simp [Set.indicator_of_mem hv]
    · simp [Set.indicator_of_notMem hv]
  rw [h1, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_complex_Ioi hre, cexp_neg_mul_log]
  field_simp

theorem norm_indicator_step (s : ℂ) (a : ℕ) (c : ℝ) (v : ℝ) :
    ‖((Ici (Real.log ((a : ℝ) + 1))).indicator (fun _ => c) v : ℂ) * Complex.exp (-s * v)‖ =
      (Ici (Real.log ((a : ℝ) + 1))).indicator (fun v => |c| * Real.exp (-s.re * v)) v := by
  by_cases hv : v ∈ Ici (Real.log ((a : ℝ) + 1))
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs]
    simp
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; simp

/-- **The Laplace transform is a Dirichlet series.** `ĝ_δ(s) = L(c_δ, s)/s` for `Re s > 0`. -/
theorem coprimeLaplace_eq_LSeries_div (δ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    coprimeLaplace δ s = LSeries (coprimeCoeff δ) s / s := by
  set F : ℕ → ℝ → ℂ := fun a v =>
    ((Ici (Real.log ((a : ℝ) + 1))).indicator (fun _ => coprimeMoebiusSigma δ (a + 1)) v : ℂ) *
      Complex.exp (-s * v) with hF
  have hre : -s.re < 0 := by linarith
  -- integrals of the norms
  have hnormInt : ∀ a : ℕ, ∫ v, ‖F a v‖ =
      |coprimeMoebiusSigma δ (a + 1)| * Real.exp (-s.re * Real.log ((a : ℝ) + 1)) / s.re := by
    intro a
    simp only [hF, norm_indicator_step]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_exp_mul_Ioi hre]
    field_simp
  have hint : ∀ a : ℕ, Integrable (F a) := by
    intro a
    have h := ((integrableOn_exp_mul_complex_Ioi (a := -s) (by simp [hs])
      (Real.log ((a : ℝ) + 1))).const_mul (coprimeMoebiusSigma δ (a + 1) : ℂ))
    have h' : IntegrableOn (fun v : ℝ => (coprimeMoebiusSigma δ (a + 1) : ℂ) * Complex.exp (-s * v))
        (Ici (Real.log ((a : ℝ) + 1))) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h
    refine (h'.integrable_indicator measurableSet_Ici).congr (Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ Ici (Real.log ((a : ℝ) + 1))
    · simp [hF, Set.indicator_of_mem hv]
    · simp [hF, Set.indicator_of_notMem hv]
  have hsum : Summable fun a : ℕ => ∫ v, ‖F a v‖ := by
    simp_rw [hnormInt]
    have hp : Summable fun a : ℕ => ((a : ℝ) + 1) ^ (-(1 + s.re)) := by
      have := (Real.summable_nat_rpow.mpr (show -(1 + s.re) < -1 by linarith))
      exact (summable_nat_add_iff 1).mpr this |>.congr fun a => by push_cast; rfl
    refine (hp.div_const s.re).of_nonneg_of_le (fun a => by positivity) fun a => ?_
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hc := abs_coprimeMoebiusSigma_le δ (a + 1)
    push_cast at hc
    rw [show Real.exp (-s.re * Real.log ((a : ℝ) + 1)) = ((a : ℝ) + 1) ^ (-s.re) by
      rw [Real.rpow_def_of_pos hpos]; ring_nf]
    have : |coprimeMoebiusSigma δ (a + 1)| * ((a : ℝ) + 1) ^ (-s.re) ≤
        ((a : ℝ) + 1) ^ (-(1 + s.re)) := by
      rw [show -(1 + s.re) = -1 + -s.re by ring, Real.rpow_add hpos, Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    exact div_le_div_of_nonneg_right this hs.le
  have hsplit : (fun v : ℝ => (coprimeProfile δ v : ℂ) * Complex.exp (-s * v)) =
      fun v => ∑' a, F a v := by
    funext v
    rw [coprimeProfile_eq_tsum, Complex.ofReal_tsum, ← tsum_mul_right]
    refine tsum_congr fun a => ?_
    by_cases hv : v ∈ Ici (Real.log ((a : ℝ) + 1))
    · simp [hF, Set.indicator_of_mem hv]
    · simp [hF, Set.indicator_of_notMem hv]
  have hLS : LSeriesSummable (coprimeCoeff δ) s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 0) hs ⟨1, fun n hn => ?_⟩
    rw [coprimeCoeff, Complex.norm_real, Real.norm_eq_abs, zero_sub, Real.rpow_neg_one, one_mul]
    exact abs_coprimeMoebiusSigma_le δ n
  rw [coprimeLaplace, hsplit, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hF, integral_indicator_step hs]
  rw [LSeries, hLS.tsum_eq_zero_add, tsum_div_const, LSeries.term_zero, zero_add]
  refine congrArg (· / s) (tsum_congr fun a => ?_)
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero a), coprimeCoeff, div_eq_mul_inv]

/-! ### The factorization through `ζ(1+s)` -/

/-- The kernel `β_δ(n) = n^{−1} ∏_{p ∣ n, p ∤ δ} (p+1)^{−1}` as a complex sequence. -/
def kernelCoeff (δ : ℕ) (n : ℕ) : ℂ := (coprimeSigmaKernel δ n : ℂ)

/-- `μ(n)/n` as a complex sequence. -/
def harmonicCoeff (n : ℕ) : ℂ := (moebiusHarmonicKernel n : ℂ)

/-- `c_δ = β_δ ⋆ (μ/id)` for `δ ≠ 0`. -/
theorem coprimeCoeff_eq_convolution {δ : ℕ} (hδ : δ ≠ 0) :
    coprimeCoeff δ = LSeries.convolution (kernelCoeff δ) harmonicCoeff := by
  funext n
  rw [LSeries.convolution_def, coprimeCoeff, ← coprimeSigmaKernel_mul_moebiusHarmonicKernel hδ,
    ArithmeticFunction.mul_apply]
  push_cast
  rfl

theorem norm_coprimeSigmaKernel_le (δ n : ℕ) : ‖(coprimeSigmaKernel δ n : ℂ)‖ ≤ (n : ℝ)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coprimeSigmaKernel_nonneg δ n),
    coprimeSigmaKernel_apply]
  have hp : ∏ p ∈ n.primeFactors \ δ.primeFactors, ((p : ℝ) + 1)⁻¹ ≤ 1 :=
    Finset.prod_le_one (fun p _ => by positivity) fun p _ =>
      inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  calc (n : ℝ)⁻¹ * ∏ p ∈ n.primeFactors \ δ.primeFactors, ((p : ℝ) + 1)⁻¹ ≤ (n : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (n : ℝ)⁻¹ := mul_one _

theorem LSeriesSummable_of_le_inv {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ (n : ℝ)⁻¹) {s : ℂ}
    (hs : 0 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 0) hs ⟨1, fun n _ => by
    rw [zero_sub, Real.rpow_neg_one, one_mul]; exact hf n⟩

/-- `L(μ/id, s) = ζ(s+1)^{−1}` for `Re s > 0`. -/
theorem LSeries_harmonicCoeff {s : ℂ} (hs : 0 < s.re) :
    LSeries harmonicCoeff s = (riemannZeta (s + 1))⁻¹ := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have hshift : LSeries harmonicCoeff s = LSeries (fun n => ((moebius n : ℤ) : ℂ)) (s + 1) := by
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, harmonicCoeff,
        moebiusHarmonicKernel_apply, cpow_add _ _ (by exact_mod_cast hn), cpow_one]
      push_cast
      field_simp
  rw [hshift, ← LSeries_one_eq_riemannZeta hs1]
  exact (eq_inv_of_mul_eq_one_right (LSeries_one_mul_Lseries_moebius hs1))

/-- **Factorization.** `L(c_δ, s) = L(β_δ, s) ζ(s+1)^{−1}` for `Re s > 0`, `δ ≠ 0`. -/
theorem LSeries_coprimeCoeff {δ : ℕ} (hδ : δ ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    LSeries (coprimeCoeff δ) s = LSeries (kernelCoeff δ) s * (riemannZeta (s + 1))⁻¹ := by
  rw [coprimeCoeff_eq_convolution hδ, LSeries_convolution'
    (LSeriesSummable_of_le_inv (f := kernelCoeff δ) (norm_coprimeSigmaKernel_le δ) hs)
    (LSeriesSummable_of_le_inv (f := harmonicCoeff) (fun n => ?_) hs), LSeries_harmonicCoeff hs]
  rw [harmonicCoeff, Complex.norm_real, moebiusHarmonicKernel_apply, Real.norm_eq_abs, abs_div,
    Nat.abs_cast, div_eq_mul_inv]
  have : |((moebius n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  calc |((moebius n : ℤ) : ℝ)| * (n : ℝ)⁻¹ ≤ 1 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = (n : ℝ)⁻¹ := one_mul _

/-- The kernel is absolutely summable: `Σ_n β_δ(n) < ∞` (Rankin). -/
theorem summable_coprimeSigmaKernel {δ : ℕ} (hδ : δ ≠ 0) :
    Summable fun n => coprimeSigmaKernel δ n := by
  refine summable_of_sum_range_le (c := kernelRankinConstant * (δ : ℝ) ^ (1 / 4 : ℝ))
    (coprimeSigmaKernel_nonneg δ) fun N => ?_
  have hrank := sum_Icc_coprimeSigmaKernelRankin_le hδ N
  have h0 : coprimeSigmaKernel δ 0 = 0 := by simp
  have hle : ∑ n ∈ Finset.range N, coprimeSigmaKernel δ n ≤
      ∑ n ∈ Finset.Icc 1 N, coprimeSigmaKernelRankin δ n := by
    have hsub : ∑ n ∈ Finset.range N, coprimeSigmaKernel δ n ≤
        ∑ n ∈ Finset.range (N + 1), coprimeSigmaKernel δ n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ N))
        fun n _ _ => coprimeSigmaKernel_nonneg δ n
    refine hsub.trans ?_
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), h0, zero_add]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    rw [coprimeSigmaKernelRankin_apply]
    have : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
    nlinarith [coprimeSigmaKernel_nonneg δ n]
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
  rw [hIcc] at hrank
  exact hle.trans hrank

/-- `L(β_δ, ·)` is continuous on the closed half-plane `Re s ≥ 0`. -/
theorem continuousOn_LSeries_kernelCoeff {δ : ℕ} (hδ : δ ≠ 0) :
    ContinuousOn (LSeries (kernelCoeff δ)) {s : ℂ | 0 ≤ s.re} := by
  refine continuousOn_tsum (u := fun n => coprimeSigmaKernel δ n) (fun n => ?_)
    (summable_coprimeSigmaKernel hδ) fun n s hs => ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]; exact continuousOn_const
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hc : Continuous fun s : ℂ => (n : ℂ) ^ s :=
        continuous_iff_continuousAt.mpr fun b => continuousAt_const_cpow hn'
      have hc' : Continuous fun s : ℂ => kernelCoeff δ n / (n : ℂ) ^ s :=
        continuous_const.div hc fun s => by
          rw [cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _
      exact hc'.continuousOn.congr fun s _ => LSeries.term_of_ne_zero hn _ _
  · rw [LSeries.norm_term_eq]
    split_ifs with hn
    · exact coprimeSigmaKernel_nonneg δ n
    · rw [kernelCoeff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coprimeSigmaKernel_nonneg δ n)]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs
      exact div_le_self (coprimeSigmaKernel_nonneg δ n) h1

/-! ### The boundary value on the imaginary axis -/

/-- The profile is integrable. -/
theorem integrable_coprimeProfile {δ : ℕ} (hδ : δ ≠ 0) : Integrable (coprimeProfile δ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_coprimeProfile_le
  have hmeas := (measurable_coprimeProfile δ).aestronglyMeasurable (μ := volume.restrict (Ioi 0))
  have hOn : IntegrableOn (coprimeProfile δ) (Ioi 0) :=
    (integrableOn_inv_one_add_sq.const_mul (C * (δ : ℝ) ^ (1 / 4 : ℝ))).mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs]; exact hC δ hδ v (le_of_lt hv)))
  rw [← integrableOn_univ, ← Ioi_union_Iic (a := (0 : ℝ))]
  refine hOn.union ?_
  have hae : coprimeProfile δ =ᵐ[volume.restrict (Iic 0)] 0 := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Iic]
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with v hv hv'
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp only [Set.mem_Iic] at hv'
    simp [coprimeProfile_of_neg δ (lt_of_le_of_ne hv' hv)]
  exact (integrable_zero _ _ _).congr hae.symm

theorem norm_profile_mul_cexp_le (δ : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (t v : ℝ) :
    ‖(coprimeProfile δ v : ℂ) * Complex.exp (-((σ : ℂ) + t * I) * v)‖ ≤ |coprimeProfile δ v| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  rcases lt_or_ge v 0 with hv | hv
  · rw [coprimeProfile_of_neg δ hv]; simp
  · have : Real.exp (-((σ : ℂ) + t * I) * v).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]
      nlinarith
    calc |coprimeProfile δ v| * Real.exp (-((σ : ℂ) + t * I) * v).re ≤ |coprimeProfile δ v| * 1 :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |coprimeProfile δ v| := mul_one _

/-- **Dominated convergence at the axis.** `ĝ_δ(σ + it) → ĝ_δ(it)` as `σ ↓ 0`. -/
theorem tendsto_coprimeLaplace {δ : ℕ} (hδ : δ ≠ 0) (t : ℝ) :
    Tendsto (fun σ : ℝ => coprimeLaplace δ (σ + t * I)) (𝓝[>] 0)
      (𝓝 (coprimeLaplace δ (t * I))) := by
  have hint := integrable_coprimeProfile hδ
  refine tendsto_integral_filter_of_dominated_convergence (fun v => |coprimeProfile δ v|) ?_ ?_
    hint.abs ?_
  · refine Eventually.of_forall fun σ => ?_
    exact ((measurable_coprimeProfile δ).complex_ofReal.aestronglyMeasurable).mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact Eventually.of_forall fun v => norm_profile_mul_cexp_le δ (le_of_lt hσ) t v
  · refine Eventually.of_forall fun v => ?_
    have hc : Continuous fun σ : ℝ => (coprimeProfile δ v : ℂ) * Complex.exp (-((σ : ℂ) + t * I) * v) :=
      by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this

/-- **The boundary value.** For `t ≠ 0`, `ĝ_δ(it) = L(β_δ, it) / (it ζ(1+it))`. -/
theorem coprimeLaplace_imaginary {δ : ℕ} (hδ : δ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    coprimeLaplace δ (t * I) =
      LSeries (kernelCoeff δ) (t * I) * (riemannZeta (t * I + 1))⁻¹ / (t * I) := by
  have htI : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  have hζ : riemannZeta (t * I + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hne1 : (t : ℂ) * I + 1 ≠ 1 := by simpa using htI
  -- the right-hand side as a limit
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + t * I) (𝓝[>] 0) (𝓝 (t * I)) := by
    have : Continuous fun σ : ℝ => (σ : ℂ) + t * I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpathW : Tendsto (fun σ : ℝ => (σ : ℂ) + t * I) (𝓝[>] 0)
      (𝓝[{s : ℂ | 0 ≤ s.re}] (t * I)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath
      (by filter_upwards [self_mem_nhdsWithin] with σ hσ; simp [le_of_lt (Set.mem_Ioi.mp hσ)])
  have hL : Tendsto (fun σ : ℝ => LSeries (kernelCoeff δ) ((σ : ℂ) + t * I)) (𝓝[>] 0)
      (𝓝 (LSeries (kernelCoeff δ) (t * I))) :=
    ((continuousOn_LSeries_kernelCoeff hδ) (t * I) (by simp)).tendsto.comp hpathW
  have hZ : Tendsto (fun σ : ℝ => riemannZeta ((σ : ℂ) + t * I + 1)) (𝓝[>] 0)
      (𝓝 (riemannZeta (t * I + 1))) := by
    have hpath1 : Tendsto (fun σ : ℝ => (σ : ℂ) + t * I + 1) (𝓝[>] 0) (𝓝 (t * I + 1)) :=
      hpath.add_const 1
    exact ((differentiableAt_riemannZeta hne1).continuousAt.tendsto).comp hpath1
  have hR : Tendsto (fun σ : ℝ => LSeries (kernelCoeff δ) ((σ : ℂ) + t * I) *
      (riemannZeta ((σ : ℂ) + t * I + 1))⁻¹ / ((σ : ℂ) + t * I)) (𝓝[>] 0)
      (𝓝 (LSeries (kernelCoeff δ) (t * I) * (riemannZeta (t * I + 1))⁻¹ / (t * I))) :=
    (hL.mul (hZ.inv₀ hζ)).div hpath htI
  -- the left-hand side agrees on `σ > 0`
  have heq : ∀ᶠ σ : ℝ in 𝓝[>] 0, coprimeLaplace δ ((σ : ℂ) + t * I) =
      LSeries (kernelCoeff δ) ((σ : ℂ) + t * I) * (riemannZeta ((σ : ℂ) + t * I + 1))⁻¹ /
        ((σ : ℂ) + t * I) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hre : 0 < ((σ : ℂ) + t * I).re := by simpa using hσ
    rw [coprimeLaplace_eq_LSeries_div δ hre, LSeries_coprimeCoeff hδ hre]
  exact tendsto_nhds_unique (tendsto_coprimeLaplace hδ t) (hR.congr' (heq.mono fun σ h => h.symm))

/-! ### Plancherel -/

/-- The Fourier transform of the profile is its Laplace transform on the imaginary axis. -/
theorem fourier_coprimeProfile (δ : ℕ) (ξ : ℝ) :
    FourierTransform.fourier (fun v => (coprimeProfile δ v : ℂ)) ξ =
      coprimeLaplace δ ((2 * Real.pi * ξ : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, coprimeLaplace]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- **The coprime energy is a one-line integral of the Laplace transform.**
`∫ g_δ² = (2π)^{−1} ∫ |ĝ_δ(it)|² dt`. -/
theorem coprimeEnergy_eq_integral_laplace {δ : ℕ} (hδ : δ ≠ 0) :
    coprimeEnergy δ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖coprimeLaplace δ (t * I)‖ ^ 2 := by
  obtain ⟨K, -, hK⟩ := exists_integrable_coprimeProfile_sq
  have hφ : Integrable (fun v => (coprimeProfile δ v : ℂ)) := (integrable_coprimeProfile hδ).ofReal
  have hφ2 : MemLp (fun v => (coprimeProfile δ v : ℂ)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable]
    refine (hK δ hδ).1.congr (Eventually.of_forall fun v => ?_)
    simp [Complex.norm_real, sq_abs]
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hφ hφ2
  simp_rw [fourier_coprimeProfile] at hP
  have hrhs : ∫ v, ‖(coprimeProfile δ v : ℂ)‖ ^ 2 = coprimeEnergy δ := by
    rw [coprimeEnergy]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [Complex.norm_real, sq_abs]
  have hscale := Measure.integral_comp_mul_left
    (fun t : ℝ => ‖coprimeLaplace δ (t * I)‖ ^ 2) (2 * Real.pi)
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [abs_inv, abs_of_pos h2π, smul_eq_mul] at hscale
  rw [← hrhs, ← hP]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hscale

/-- **The coprime energy as a one-line integral of `1/ζ`.** For `δ ≠ 0`,
`∫ g_δ² = (2π)^{−1} ∫ |L(β_δ, it)|² / |it ζ(1+it)|² dt`. -/
theorem coprimeEnergy_eq_integral_zeta {δ : ℕ} (hδ : δ ≠ 0) :
    coprimeEnergy δ = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖LSeries (kernelCoeff δ) (t * I)‖ ^ 2 / ‖(t : ℂ) * I * riemannZeta (t * I + 1)‖ ^ 2 := by
  rw [coprimeEnergy_eq_integral_laplace hδ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  rw [coprimeLaplace_imaginary hδ ht]
  simp only [norm_div, norm_mul, norm_inv, div_pow, mul_pow, inv_pow]
  ring

/-! ### The closed form of the cofinal slope -/

/-- Plancherel also gives square integrability of the Fourier transform. -/
theorem integrable_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    Integrable fun ξ => ‖FourierTransform.fourier φ ξ‖ ^ 2 := by
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφ2.toLp φ with hu
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] φ := hφ2.coeFn_toLp
  have hint : Integrable (u : ℝ → ℂ) := hφ.congr hcoe.symm
  have hF : ((FourierTransform.fourier u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourier φ := by
    refine (GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral u hint).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have hmem : MemLp (FourierTransform.fourier φ) 2 := (Lp.memLp _).ae_eq hF
  exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem

/-- `t ↦ |ĝ_δ(it)|²` is integrable. -/
theorem integrable_norm_sq_coprimeLaplace {δ : ℕ} (hδ : δ ≠ 0) :
    Integrable fun t : ℝ => ‖coprimeLaplace δ (t * I)‖ ^ 2 := by
  obtain ⟨K, -, hK⟩ := exists_integrable_coprimeProfile_sq
  have hφ : Integrable (fun v => (coprimeProfile δ v : ℂ)) := (integrable_coprimeProfile hδ).ofReal
  have hφ2 : MemLp (fun v => (coprimeProfile δ v : ℂ)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable]
    refine (hK δ hδ).1.congr (Eventually.of_forall fun v => ?_)
    simp [Complex.norm_real, sq_abs]
  have h := (integrable_norm_sq_fourier hφ hφ2).comp_mul_left' (R := (2 * Real.pi)⁻¹)
    (inv_ne_zero (by positivity))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [fourier_coprimeProfile]
  congr 3
  push_cast
  field_simp

theorem norm_sq_coprimeLaplace_imaginary {δ : ℕ} (hδ : δ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    ‖coprimeLaplace δ (t * I)‖ ^ 2 =
      ‖LSeries (kernelCoeff δ) (t * I)‖ ^ 2 / ‖(t : ℂ) * I * riemannZeta (t * I + 1)‖ ^ 2 := by
  rw [coprimeLaplace_imaginary hδ ht]
  simp only [norm_div, norm_mul, norm_inv, div_pow, mul_pow, inv_pow]
  ring

/-- The arithmetic weight `H(t) = Σ_{δ ≥ 1} μ(δ) w(δ)² |L(β_δ, it)|²`. -/
def oneLineWeight (t : ℝ) : ℝ :=
  ∑' δ : ℕ, if δ = 0 then 0 else
    (moebius δ : ℝ) * moebiusSigma δ ^ 2 * ‖LSeries (kernelCoeff δ) (t * I)‖ ^ 2

/-- **The cofinal Möbius slope is the one-line energy of `1/ζ`.**

  `κ = (ρ/2π) ∫_ℝ H(t) / |t ζ(1+it)|² dt`,   `H(t) = Σ_{δ ≥ 1} μ(δ) w(δ)² |L(β_δ, it)|²`,

with `w = μ/σ`, `β_δ(n) = n^{−1} ∏_{p ∣ n, p ∤ δ} (p+1)^{−1}` and `ρ = 6/π²`. -/
theorem cofinalMobiusSlope_eq_integral_one_line :
    cofinalMobiusSlope = RHTower.Sieve.squarefreeDensity * (2 * Real.pi)⁻¹ *
      ∫ t : ℝ, oneLineWeight t / ‖(t : ℂ) * I * riemannZeta (t * I + 1)‖ ^ 2 := by
  obtain ⟨hsumE, hκ⟩ := cofinalMobiusSlope_eq_tsum_coprimeEnergy
  set G : ℕ → ℝ → ℝ := fun δ t => if δ = 0 then 0 else
    (moebius δ : ℝ) * moebiusSigma δ ^ 2 * ‖coprimeLaplace δ (t * I)‖ ^ 2 with hG
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  -- each energy term is a one-line integral
  have hterm : ∀ δ : ℕ, (if δ = 0 then 0 else
      (moebius δ : ℝ) * moebiusSigma δ ^ 2 * coprimeEnergy δ) = (2 * Real.pi)⁻¹ * ∫ t, G δ t := by
    intro δ
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp [hG]
    · simp only [hG, if_neg hδ]
      rw [integral_const_mul, coprimeEnergy_eq_integral_laplace hδ]
      ring
  have hint : ∀ δ : ℕ, Integrable (G δ) := by
    intro δ
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp only [hG]; exact integrable_zero _ _ _
    · simp only [hG, if_neg hδ]
      exact (integrable_norm_sq_coprimeLaplace hδ).const_mul _
  have hnorm : ∀ δ : ℕ, ∫ t, ‖G δ t‖ ≤ 2 * Real.pi * |moebiusSigma δ ^ 2 * coprimeEnergy δ| := by
    intro δ
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp only [hG, if_pos rfl, norm_zero, integral_zero]; positivity
    · have hpt : ∀ t, ‖G δ t‖ = |(moebius δ : ℝ)| * moebiusSigma δ ^ 2 *
          ‖coprimeLaplace δ (t * I)‖ ^ 2 := by
        intro t
        simp only [hG, if_neg hδ, Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
      simp_rw [hpt]
      rw [integral_const_mul]
      have hE := coprimeEnergy_eq_integral_laplace hδ
      have hI : ∫ t : ℝ, ‖coprimeLaplace δ (t * I)‖ ^ 2 = 2 * Real.pi * coprimeEnergy δ := by
        rw [hE, ← mul_assoc, mul_inv_cancel₀ h2π.ne', one_mul]
      rw [hI]
      have hμ : |(moebius δ : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hE0 : 0 ≤ coprimeEnergy δ := integral_nonneg fun v => sq_nonneg _
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hE0)]
      have : 0 ≤ moebiusSigma δ ^ 2 * (2 * Real.pi * coprimeEnergy δ) := by positivity
      nlinarith [abs_nonneg (moebius δ : ℝ)]
  have hsum : Summable fun δ => ∫ t, ‖G δ t‖ :=
    (hsumE.mul_left (2 * Real.pi)).of_nonneg_of_le (fun δ => integral_nonneg fun _ => norm_nonneg _)
      hnorm
  rw [hκ, tsum_congr hterm, tsum_mul_left, integral_tsum_of_summable_integral_norm hint hsum,
    ← mul_assoc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  rw [oneLineWeight, ← tsum_div_const]
  refine tsum_congr fun δ => ?_
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp [hG]
  · simp only [hG, if_neg hδ]
    rw [norm_sq_coprimeLaplace_imaginary hδ ht]
    ring

/-! ### The Euler product of the weight -/

/-- The squarefree kernel `R_δ = ∏_{p ∣ δ} p`. -/
def primeKernel (δ : ℕ) : ℕ := ∏ p ∈ δ.primeFactors, p

theorem primeFactors_primeKernel (δ : ℕ) : (primeKernel δ).primeFactors = δ.primeFactors :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors hp

theorem primeKernel_ne_zero (δ : ℕ) : primeKernel δ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem squarefree_primeKernel (δ : ℕ) : Squarefree (primeKernel δ) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq)

/-- The local corrections `γ_δ = w·1_{(·) ∣ R_δ}`. -/
def primeSupportedMoebiusSigma (δ : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∣ primeKernel δ then moebiusSigma n else 0, by
    simp [moebiusSigma]⟩

theorem primeSupportedMoebiusSigma_apply (δ n : ℕ) :
    primeSupportedMoebiusSigma δ n = if n ∣ primeKernel δ then moebiusSigma n else 0 := rfl

theorem isMultiplicative_primeSupportedMoebiusSigma (δ : ℕ) :
    (primeSupportedMoebiusSigma δ).IsMultiplicative := by
  refine ⟨by simp [primeSupportedMoebiusSigma_apply, moebiusSigma], fun {m n} h => ?_⟩
  simp only [primeSupportedMoebiusSigma_apply]
  by_cases hm : m ∣ primeKernel δ <;> by_cases hn : n ∣ primeKernel δ
  · rw [if_pos (h.mul_dvd_of_dvd_of_dvd hm hn), if_pos hm, if_pos hn, moebiusSigma_mul h]
  · rw [if_neg (fun hc => hn (dvd_trans (dvd_mul_left n m) hc)), if_neg hn, mul_zero]
  · rw [if_neg (fun hc => hm (dvd_trans (dvd_mul_right m n) hc)), if_neg hm, zero_mul]
  · rw [if_neg (fun hc => hm (dvd_trans (dvd_mul_right m n) hc)), if_neg hm, zero_mul]

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : (ArithmeticFunction.sigma 1 p : ℝ) = p + 1 := by
  have h1 := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at h1
  rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

theorem moebiusSigma_prime {p : ℕ} (hp : p.Prime) : moebiusSigma p = -((p : ℝ) + 1)⁻¹ := by
  unfold moebiusSigma
  rw [moebius_apply_prime hp, sigma_one_prime hp]
  push_cast
  ring

theorem moebiusSigma_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    moebiusSigma (p ^ k) = 0 := by
  unfold moebiusSigma
  rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  simp

theorem prime_dvd_primeKernel_iff {δ p : ℕ} (hp : p.Prime) :
    p ∣ primeKernel δ ↔ p ∈ δ.primeFactors := by
  rw [← primeFactors_primeKernel δ, Nat.mem_primeFactors]
  simp [hp, primeKernel_ne_zero]

theorem primeSupportedMoebiusSigma_prime_pow (δ : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeSupportedMoebiusSigma δ (p ^ k) =
      if k = 0 then 1 else if k = 1 then (if p ∈ δ.primeFactors then -((p : ℝ) + 1)⁻¹ else 0)
      else 0 := by
  rw [primeSupportedMoebiusSigma_apply]
  rcases Nat.lt_trichotomy k 1 with hk | rfl | hk
  · obtain rfl : k = 0 := by omega
    simp [moebiusSigma]
  · simp only [pow_one, one_ne_zero, if_false, if_true]
    by_cases h : p ∈ δ.primeFactors
    · rw [if_pos ((prime_dvd_primeKernel_iff hp).mpr h), if_pos h, moebiusSigma_prime hp]
    · rw [if_neg (mt (prime_dvd_primeKernel_iff hp).mp h), if_neg h]
  · rw [moebiusSigma_prime_pow hp (by omega)]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega]

/-- **Removing the primes of `δ`.** `β_1 = β_δ ⋆ γ_δ` for `δ ≠ 0`. -/
theorem coprimeSigmaKernel_one_eq_mul (δ : ℕ) :
    coprimeSigmaKernel 1 = coprimeSigmaKernel δ * primeSupportedMoebiusSigma δ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_coprimeSigmaKernel 1) _
    ((isMultiplicative_coprimeSigmaKernel δ).mul
      (isMultiplicative_primeSupportedMoebiusSigma δ))).mpr ?_
  intro p k hp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => coprimeSigmaKernel δ x *
    primeSupportedMoebiusSigma δ y), Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ j ∈ Finset.range (k + 1), p ^ k / p ^ j = p ^ (k - j) := fun j hj =>
    Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos
  rw [Finset.sum_congr rfl fun j hj => by rw [hdiv j hj]]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [primeSupportedMoebiusSigma_apply, moebiusSigma, coprimeSigmaKernel_apply]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ j ∈ Finset.range k, coprimeSigmaKernel δ (p ^ j) *
      primeSupportedMoebiusSigma δ (p ^ (k + 1 - j)) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj := Finset.mem_range.mp hj
      rw [primeSupportedMoebiusSigma_prime_pow δ hp, if_neg (by omega), if_neg (by omega), mul_zero]
  rw [hzero, zero_add, show k + 1 - k = 1 by omega, Nat.sub_self,
    primeSupportedMoebiusSigma_prime_pow δ hp, primeSupportedMoebiusSigma_prime_pow δ hp,
    if_neg one_ne_zero, if_pos rfl, if_pos rfl, mul_one,
    coprimeSigmaKernel_prime_pow 1 hp (Nat.succ_ne_zero k),
    coprimeSigmaKernel_prime_pow δ hp (Nat.succ_ne_zero k)]
  have hp1 : p ∉ (1 : ℕ).primeFactors := by simp
  rw [if_neg hp1]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [pow_one, pow_zero]
    have h1 : coprimeSigmaKernel δ 1 = 1 := by simp [coprimeSigmaKernel_apply]
    rw [h1]
    by_cases h : p ∈ δ.primeFactors
    · simp only [if_pos h]; field_simp; ring
    · simp only [if_neg h]; ring
  · rw [coprimeSigmaKernel_prime_pow δ hp hk1.ne']
    by_cases h : p ∈ δ.primeFactors
    · simp only [if_pos h, pow_succ]; field_simp; ring
    · simp only [if_neg h]; ring

/-- `γ_δ(n) n^{−s}` as a multiplicative arithmetic function. -/
def twistedPrimeSupported (δ : ℕ) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (primeSupportedMoebiusSigma δ n : ℂ) * (n : ℂ) ^ (-s), if_pos rfl⟩

theorem twistedPrimeSupported_apply {δ : ℕ} {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    twistedPrimeSupported δ s n = (primeSupportedMoebiusSigma δ n : ℂ) * (n : ℂ) ^ (-s) :=
  if_neg hn

theorem isMultiplicative_twistedPrimeSupported (δ : ℕ) (s : ℂ) :
    (twistedPrimeSupported δ s).IsMultiplicative := by
  have hγ := isMultiplicative_primeSupportedMoebiusSigma δ
  refine ⟨?_, fun {m n} h => ?_⟩
  · rw [twistedPrimeSupported_apply one_ne_zero, hγ.map_one]; simp
  · rcases eq_or_ne m 0 with rfl | hm
    · simp [twistedPrimeSupported]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [twistedPrimeSupported]
    rw [twistedPrimeSupported_apply (mul_ne_zero hm hn), twistedPrimeSupported_apply hm,
      twistedPrimeSupported_apply hn, hγ.map_mul_of_coprime h, Nat.cast_mul,
      natCast_mul_natCast_cpow]
    push_cast
    ring

/-- **The finite Euler product of the corrections.**
`L(γ_δ, s) = ∏_{p ∣ δ} (1 + w(p) p^{−s})`. -/
theorem LSeries_primeSupported (δ : ℕ) (s : ℂ) :
    LSeries (fun n => (primeSupportedMoebiusSigma δ n : ℂ)) s =
      ∏ p ∈ δ.primeFactors, (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-s)) := by
  have hterm : ∀ n, LSeries.term (fun n => (primeSupportedMoebiusSigma δ n : ℂ)) s n =
      twistedPrimeSupported δ s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [twistedPrimeSupported]
    · rw [LSeries.term_of_ne_zero hn, twistedPrimeSupported_apply hn, cpow_neg, div_eq_mul_inv]
  rw [LSeries, tsum_congr hterm, tsum_eq_sum (s := (primeKernel δ).divisors) fun n hn => ?_]
  · rw [← (isMultiplicative_twistedPrimeSupported δ s).prodPrimeFactors_one_add_of_squarefree
      (squarefree_primeKernel δ), primeFactors_primeKernel]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [twistedPrimeSupported_apply hpp.ne_zero, primeSupportedMoebiusSigma_apply,
      if_pos ((prime_dvd_primeKernel_iff hpp).mpr hp)]
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp [twistedPrimeSupported]
    · rw [twistedPrimeSupported_apply hn0, primeSupportedMoebiusSigma_apply, if_neg]
      · simp
      · intro hd
        exact hn (Nat.mem_divisors.mpr ⟨hd, primeKernel_ne_zero δ⟩)

theorem norm_term_kernelCoeff_le (δ n : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖LSeries.term (kernelCoeff δ) s n‖ ≤ coprimeSigmaKernel δ n := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact coprimeSigmaKernel_nonneg δ n
  · rw [kernelCoeff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coprimeSigmaKernel_nonneg δ n)]
    exact div_le_self (coprimeSigmaKernel_nonneg δ n)
      (Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs)

/-- **Removing the primes of `δ` from the kernel series.** `L(β_1, s) = L(β_δ, s) L(γ_δ, s)` on
`Re s ≥ 0`, `δ ≠ 0`. -/
theorem LSeries_kernelCoeff_one {δ : ℕ} (hδ : δ ≠ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    LSeries (kernelCoeff 1) s = LSeries (kernelCoeff δ) s *
      ∏ p ∈ δ.primeFactors, (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-s)) := by
  have hconv : kernelCoeff 1 = LSeries.convolution (kernelCoeff δ)
      (fun n => (primeSupportedMoebiusSigma δ n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def, kernelCoeff, coprimeSigmaKernel_one_eq_mul δ,
      ArithmeticFunction.mul_apply]
    push_cast
    rfl
  have hβ : LSeriesSummable (kernelCoeff δ) s :=
    (summable_coprimeSigmaKernel hδ).of_norm_bounded fun n => norm_term_kernelCoeff_le δ n hs
  have hγ : LSeriesSummable (fun n => (primeSupportedMoebiusSigma δ n : ℂ)) s := by
    refine summable_of_ne_finset_zero (s := (primeKernel δ).divisors) fun n hn => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [LSeries.term_of_ne_zero hn0, primeSupportedMoebiusSigma_apply, if_neg]
      · simp
      · intro hd; exact hn (Nat.mem_divisors.mpr ⟨hd, primeKernel_ne_zero δ⟩)
  rw [hconv, LSeries_convolution' hβ hγ, LSeries_primeSupported]

theorem norm_one_add_moebiusSigma_mul_cpow_ge {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (p : ℝ) / (p + 1) ≤ ‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnorm : ‖(moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ = ((p : ℝ) + 1)⁻¹ := by
    have hre : (-((t : ℂ) * I)).re = 0 := by simp
    rw [norm_mul, Complex.norm_real, norm_natCast_cpow_of_pos hp.pos, moebiusSigma_prime hp, hre,
      Real.rpow_zero, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have h := norm_sub_norm_le (1 : ℂ) (-((moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))))
  rw [sub_neg_eq_add, norm_neg, hnorm, norm_one] at h
  have : (p : ℝ) / (p + 1) = 1 - ((p : ℝ) + 1)⁻¹ := by field_simp; ring
  linarith

/-- `(p+1)|1 + w(p) p^{−it}| = |p + 1 − p^{−it}|`. -/
theorem norm_succ_sub_cpow (p : ℕ) (hp : p.Prime) (t : ℝ) :
    ((p : ℝ) + 1) * ‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ =
      ‖(p : ℂ) + 1 - (p : ℂ) ^ (-((t : ℂ) * I))‖ := by
  have hq : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hn1 : ‖((p : ℂ) + 1)‖ = (p : ℝ) + 1 := by
    rw [show ((p : ℂ) + 1) = ((p + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  calc ((p : ℝ) + 1) * ‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖
      = ‖((p : ℂ) + 1)‖ * ‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ := by rw [hn1]
    _ = ‖((p : ℂ) + 1) * (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I)))‖ :=
        (norm_mul _ _).symm
    _ = ‖(p : ℂ) + 1 - (p : ℂ) ^ (-((t : ℂ) * I))‖ := by
        congr 1
        rw [moebiusSigma_prime hp]
        have hq' : ((p : ℂ) + 1) ≠ 0 := by exact_mod_cast hq.ne'
        push_cast
        field_simp
        ring

/-- The Euler-product weight `F(δ) = μ(δ) w(δ)² ∏_{p ∣ δ} |1 + w(p) p^{−it}|^{−2}`. -/
def oneLineEulerWeight (t : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun δ => if δ = 0 then 0 else (moebius δ : ℝ) * moebiusSigma δ ^ 2 *
    ∏ p ∈ δ.primeFactors, (‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹,
    if_pos rfl⟩

theorem oneLineEulerWeight_apply {t : ℝ} {δ : ℕ} (hδ : δ ≠ 0) :
    oneLineEulerWeight t δ = (moebius δ : ℝ) * moebiusSigma δ ^ 2 *
      ∏ p ∈ δ.primeFactors, (‖1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹ :=
  if_neg hδ

theorem isMultiplicative_oneLineEulerWeight (t : ℝ) : (oneLineEulerWeight t).IsMultiplicative := by
  refine ⟨?_, fun {m n} h => ?_⟩
  · rw [oneLineEulerWeight_apply one_ne_zero]; simp [moebiusSigma]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp [oneLineEulerWeight]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [oneLineEulerWeight]
    rw [oneLineEulerWeight_apply (mul_ne_zero hm hn), oneLineEulerWeight_apply hm,
      oneLineEulerWeight_apply hn, isMultiplicative_moebius.map_mul_of_coprime h,
      moebiusSigma_mul h, Nat.primeFactors_mul hm hn,
      Finset.prod_union h.disjoint_primeFactors]
    push_cast
    ring

theorem oneLineEulerWeight_prime {t : ℝ} {p : ℕ} (hp : p.Prime) :
    oneLineEulerWeight t p = -(‖(p : ℂ) + 1 - (p : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹ := by
  rw [oneLineEulerWeight_apply hp.ne_zero, Nat.Prime.primeFactors hp, Finset.prod_singleton,
    moebius_apply_prime hp, ← norm_succ_sub_cpow p hp t, moebiusSigma_prime hp]
  push_cast
  have hq : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  field_simp

theorem oneLineEulerWeight_prime_pow {t : ℝ} {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 2 ≤ e) :
    oneLineEulerWeight t (p ^ e) = 0 := by
  rw [oneLineEulerWeight_apply (pow_ne_zero _ hp.ne_zero), moebius_apply_prime_pow hp (by omega),
    if_neg (by omega)]
  simp

theorem abs_oneLineEulerWeight_le (t : ℝ) (δ : ℕ) :
    |oneLineEulerWeight t δ| ≤ ((δ : ℝ) ^ 2)⁻¹ := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp [oneLineEulerWeight]
  by_cases hsq : Squarefree δ
  · have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hF : oneLineEulerWeight t δ = ∏ p ∈ δ.primeFactors, oneLineEulerWeight t p := by
      conv_lhs => rw [← hprod]
      exact (isMultiplicative_oneLineEulerWeight t).map_prod_of_prime _
        fun p hp => Nat.prime_of_mem_primeFactors hp
    rw [hF, Finset.abs_prod]
    conv_rhs => rw [← hprod]
    push_cast
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p _ => abs_nonneg _) fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [oneLineEulerWeight_prime hpp, abs_neg, abs_of_nonneg (by positivity)]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hge : (p : ℝ) ≤ ‖(p : ℂ) + 1 - (p : ℂ) ^ (-((t : ℂ) * I))‖ := by
      rw [← norm_succ_sub_cpow p hpp t]
      have h := norm_one_add_moebiusSigma_mul_cpow_ge hpp t
      have hq : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      calc (p : ℝ) = ((p : ℝ) + 1) * ((p : ℝ) / (p + 1)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h hq.le
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpR.le hge 2)
  · rw [oneLineEulerWeight_apply hδ, moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- **The Euler product of the one-line weight.**
`H(t) = |L(β_1, it)|² ∏_p (1 − |p + 1 − p^{−it}|^{−2})`. -/
theorem oneLineWeight_eq_eulerProduct (t : ℝ) :
    oneLineWeight t = ‖LSeries (kernelCoeff 1) (t * I)‖ ^ 2 *
      ∏' p : Nat.Primes, (1 - (‖((p : ℕ) : ℂ) + 1 - ((p : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹) := by
  have hsumF : Summable fun δ => ‖oneLineEulerWeight t δ‖ :=
    (Real.summable_nat_pow_inv.mpr one_lt_two).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun δ => by rw [Real.norm_eq_abs]; exact abs_oneLineEulerWeight_le t δ
  have hE := (isMultiplicative_oneLineEulerWeight t).eulerProduct_tprod hsumF
  have hloc : ∀ p : Nat.Primes, ∑' e, oneLineEulerWeight t ((p : ℕ) ^ e) =
      1 - (‖((p : ℕ) : ℂ) + 1 - ((p : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹ := by
    intro p
    rw [tsum_eq_sum (s := Finset.range 2) fun e he => by
      rw [Finset.mem_range, not_lt] at he
      exact oneLineEulerWeight_prime_pow p.prop he]
    simp [Finset.sum_range_succ, (isMultiplicative_oneLineEulerWeight t).map_one,
      oneLineEulerWeight_prime p.prop, sub_eq_add_neg]
  simp_rw [hloc] at hE
  rw [hE, ← tsum_mul_left, oneLineWeight]
  refine tsum_congr fun δ => ?_
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp [oneLineEulerWeight]
  rw [if_neg hδ, oneLineEulerWeight_apply hδ]
  have hA : ∀ p ∈ δ.primeFactors, (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))) ≠ 0 := by
    intro p hp
    have h := norm_one_add_moebiusSigma_mul_cpow_ge (Nat.prime_of_mem_primeFactors hp) t
    have hpos : (0 : ℝ) < (p : ℝ) / (p + 1) := by
      have := (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    exact norm_pos_iff.mp (lt_of_lt_of_le hpos h)
  have hL := LSeries_kernelCoeff_one hδ (s := (t : ℂ) * I) (by simp)
  have hprod0 : ∏ p ∈ δ.primeFactors, (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hA
  have hLδ : LSeries (kernelCoeff δ) (t * I) = LSeries (kernelCoeff 1) (t * I) /
      ∏ p ∈ δ.primeFactors, (1 + (moebiusSigma p : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I))) := by
    rw [hL, mul_div_cancel_right₀ _ hprod0]
  rw [hLδ, norm_div, div_pow, norm_prod, ← Finset.prod_pow, Finset.prod_inv_distrib]
  ring

/-- **The closed form of the cofinal Möbius slope.**

  `κ = (ρ/2π) ∫_ℝ |L(β_1, it)|² ∏_p (1 − |p + 1 − p^{−it}|^{−2}) / |t ζ(1+it)|² dt`,

with `L(β_1, s) = Σ_n n^{−1−s} ∏_{p ∣ n} (p+1)^{−1}` absolutely convergent on `Re s ≥ 0`. -/
theorem cofinalMobiusSlope_eq_integral_eulerProduct :
    cofinalMobiusSlope = RHTower.Sieve.squarefreeDensity * (2 * Real.pi)⁻¹ *
      ∫ t : ℝ, ‖LSeries (kernelCoeff 1) (t * I)‖ ^ 2 *
        (∏' p : Nat.Primes, (1 - (‖((p : ℕ) : ℂ) + 1 - ((p : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2)⁻¹)) /
        ‖(t : ℂ) * I * riemannZeta (t * I + 1)‖ ^ 2 := by
  rw [cofinalMobiusSlope_eq_integral_one_line]
  simp_rw [oneLineWeight_eq_eulerProduct]

end GaloisForLFunctions.BezoutValuationIncidence
