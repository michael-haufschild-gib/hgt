import GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

/-!
# Positive self-dual measures with a gap are Dirac combs

The Fejér tent `Λ(x) = max(0, 1 − |x|)` is supported in `[−1, 1]` and has nonnegative transform
`𝓕Λ(ξ) = sinc(πξ)²`, which vanishes exactly on `ℤ ∖ {0}`. Pairing a Poisson identity with tents
is the spectral gap identity of this programme.

**Poisson rigidity** (`tentSelfDual_iff_eq_smul_diracComb`). Let `μ ≥ 0` be a locally finite
measure on `ℝ` with a gap, `μ((−1, 1) ∖ {0}) = 0`. Then `μ` is self-dual against the integer
translates of the tent, `∫ 𝓕Λ(· − n) dμ = ∫ Λ(· − n) dμ` for all `n ∈ ℤ`, iff
`μ = μ{0} · Σ_{n ∈ ℤ} δ_n`.

*Proof.* At `n = 0` the gap leaves only the atom at `0` on the tent side, and the transform side is
`μ{0} + ∫_{ξ ≠ 0} sinc(πξ)² dμ`. So `sinc(πξ)² = 0` for `μ`-almost every `ξ ≠ 0`: `μ` lives on `ℤ`.
On `ℤ` the transform of `Λ(· − n)` is `δ_{0}` and `Λ(· − n)` is `δ_{n}`, so `μ{n} = μ{0}`.

* **The gap is at most one** (`eq_zero_of_wide_gap`): a positive tent-self-dual measure with a
  gap `(−a, a) ∖ {0}`, `a > 1`, is zero.
* **One-sided pairs** (`integral_sincSq_shift_eq`, `measure_Icc_le_of_poissonPair`). If only the
  dual side `ν` has the gap and `μ` is positive, the identity says `μ ⋆ sinc(π·)² ≡ ν{0}`:
  `μ` has uniform local mass, `μ[s − ½, s + ½] ≤ (π²/4) ν{0}`. It forces no lattice.

Rigidity needs positivity and the gap on opposite sides of a self-dual pair. The theta law of
`PositiveMeasureHamburgerRigidity` is the same mechanism tested on Gaussians instead of tents. On
the Weil pair the prime side carries both the positivity and the prime-free gap, so only the
density statement has an analogue there.
-/

open MeasureTheory Set Complex Real
open GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### Tents and their transforms -/

/-- The tent centred at `c`, complex-valued. -/
def tentAt (c x : ℝ) : ℂ := (triangle (x - c) : ℂ)

/-- The modulated tent `e^{2πisx} Λ(x)`. -/
def modTent (s x : ℝ) : ℂ := cexp (((2 * π * s * x : ℝ) : ℂ) * I) * (triangle x : ℂ)

theorem fourier_triangle' (ξ : ℝ) :
    ∫ v : ℝ, cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) * (triangle v : ℂ) = (sincSq ξ : ℂ) := by
  rw [← fourier_triangle ξ, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

/-- **The tent translate has transform `e^{−2πicξ} sinc(πξ)²`.** -/
theorem fourier_tentAt (c ξ : ℝ) :
    FourierTransform.fourier (tentAt c) ξ =
      cexp (((-2 * π * c * ξ : ℝ) : ℂ) * I) * (sincSq ξ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← fourier_triangle', ← integral_const_mul,
    ← integral_add_right_eq_self _ c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [tentAt, smul_eq_mul, add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The modulated tent has transform `sinc(π(ξ − s))²`.** -/
theorem fourier_modTent (s ξ : ℝ) :
    FourierTransform.fourier (modTent s) ξ = (sincSq (ξ - s) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← fourier_triangle']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [modTent, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `sinc(πm)² = 0` at every nonzero integer. -/
theorem sincSq_int_eq_zero {m : ℤ} (hm : m ≠ 0) : sincSq m = 0 := by
  have hx : Real.pi * m ≠ 0 := mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hm)
  rw [sincSq, Real.sinc_of_ne_zero hx, mul_comm, Real.sin_int_mul_pi]
  simp

/-- `sinc(πξ)² = 0` only at nonzero integers. -/
theorem exists_int_of_sincSq_eq_zero {ξ : ℝ} (h : sincSq ξ = 0) : ∃ m : ℤ, (m : ℝ) = ξ := by
  by_cases hξ : ξ = 0
  · exact ⟨0, by simp [hξ]⟩
  have hx : Real.pi * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
  rw [sincSq, Real.sinc_of_ne_zero hx, sq_eq_zero_iff, div_eq_zero_iff] at h
  rcases h with h | h
  · obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
    exact ⟨m, by
      have := mul_right_cancel₀ Real.pi_ne_zero (hm.trans (mul_comm _ _))
      exact this⟩
  · exact absurd h hx

/-! ### Measures on the integers -/

/-- A measure concentrated on `ℤ ⊂ ℝ`. -/
def IsIntSupported (μ : Measure ℝ) : Prop := μ (range ((↑) : ℤ → ℝ))ᶜ = 0

theorem ae_int_of_isIntSupported {μ : Measure ℝ} (h : IsIntSupported μ) :
    ∀ᵐ x ∂μ, ∃ m : ℤ, (m : ℝ) = x := by
  rw [ae_iff]
  simpa [IsIntSupported, compl_def] using h

/-- On an integer-supported measure, a function equal to `δ_k` on `ℤ` integrates to `μ{k}`. -/
theorem integral_eq_of_isIntSupported {μ : Measure ℝ} (h : IsIntSupported μ) {f : ℝ → ℂ}
    {k : ℤ} (hk : f k = 1) (hf : ∀ m : ℤ, m ≠ k → f m = 0) :
    ∫ x, f x ∂μ = (μ.real {(k : ℝ)} : ℂ) := by
  have hae : f =ᵐ[μ] ({(k : ℝ)} : Set ℝ).indicator fun _ => (1 : ℂ) := by
    filter_upwards [ae_int_of_isIntSupported h] with x hx
    obtain ⟨m, rfl⟩ := hx
    by_cases hm : m = k
    · subst hm; simp [hk]
    · rw [hf m hm, indicator_of_notMem]
      simp only [mem_singleton_iff, Int.cast_inj]
      exact hm
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_singleton _)]
  simp

/-- The Dirac comb `Σ_{n ∈ ℤ} δ_n`. -/
def diracComb : Measure ℝ := Measure.sum fun n : ℤ => Measure.dirac (n : ℝ)

theorem measurableSet_range_intCast : MeasurableSet (range ((↑) : ℤ → ℝ)) :=
  (countable_range _).measurableSet

theorem diracComb_isIntSupported : IsIntSupported diracComb := by
  unfold IsIntSupported diracComb
  rw [Measure.sum_apply _ measurableSet_range_intCast.compl]
  refine ENNReal.tsum_eq_zero.mpr fun n => ?_
  rw [Measure.dirac_apply' _ measurableSet_range_intCast.compl, indicator_of_notMem]
  simp

theorem diracComb_singleton (n : ℤ) : diracComb {(n : ℝ)} = 1 := by
  unfold diracComb
  rw [Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single n]
  · simp
  · intro m hm
    rw [Measure.dirac_apply' _ (measurableSet_singleton _), indicator_of_notMem]
    simp only [mem_singleton_iff, Int.cast_inj]
    exact hm

/-- An integer-supported measure with equal atoms is a multiple of the Dirac comb. -/
theorem eq_smul_diracComb {μ : Measure ℝ} (h : IsIntSupported μ)
    (hconst : ∀ n : ℤ, μ {(n : ℝ)} = μ {0}) : μ = μ {0} • diracComb := by
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, diracComb, Measure.sum_apply _ hs,
    ← ENNReal.tsum_mul_left, ← measure_inter_conull (s := s) h]
  have hU : s ∩ range ((↑) : ℤ → ℝ) = ⋃ n : ℤ, s ∩ {(n : ℝ)} := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_iUnion, mem_singleton_iff]
    constructor
    · rintro ⟨hx, m, rfl⟩
      exact ⟨m, hx, rfl⟩
    · rintro ⟨m, hx, rfl⟩
      exact ⟨hx, m, rfl⟩
  rw [hU, measure_iUnion]
  · refine tsum_congr fun n => ?_
    rw [Measure.dirac_apply' _ hs]
    by_cases hn : (n : ℝ) ∈ s
    · rw [inter_eq_right.mpr (singleton_subset_iff.mpr hn), hconst, indicator_of_mem hn]
      simp
    · rw [inter_singleton_eq_empty.mpr hn, measure_empty, indicator_of_notMem hn]
      simp
  · intro m n hmn
    refine Disjoint.mono inter_subset_right inter_subset_right ?_
    rw [disjoint_singleton]
    exact_mod_cast hmn
  · exact fun n => hs.inter (measurableSet_singleton _)

/-- With the gap `(−1, 1) ∖ {0}`, a function vanishing for `|x| ≥ 1` integrates to `f(0) μ{0}`. -/
theorem integral_eq_of_gap {μ : Measure ℝ} (hgap : μ (Ioo (-1) 1 \ {0}) = 0) {f : ℝ → ℂ}
    (hf : ∀ x, 1 ≤ |x| → f x = 0) : ∫ x, f x ∂μ = f 0 * (μ.real {0} : ℂ) := by
  have hae : f =ᵐ[μ] ({0} : Set ℝ).indicator fun _ => f 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hgap] with x hx
    by_cases h0 : x = 0
    · subst h0
      simp
    · rw [indicator_of_notMem (by simpa using h0)]
      apply hf
      by_contra hlt
      push Not at hlt
      exact hx ⟨⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩, h0⟩
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_singleton _)]
  simp [mul_comm]

/-! ### Poisson rigidity -/

/-- `μ` is self-dual against the integer translates of the tent: the pairing converges and
`∫ 𝓕Λ(· − n) dμ = ∫ Λ(· − n) dμ` for every `n ∈ ℤ`. -/
def IsTentSelfDual (μ : Measure ℝ) : Prop :=
  Integrable sincSq μ ∧
    ∀ n : ℤ, ∫ ξ, FourierTransform.fourier (tentAt n) ξ ∂μ = ∫ x, tentAt n x ∂μ

theorem tentAt_self (c : ℝ) : tentAt c c = 1 := by simp [tentAt, triangle_zero]

theorem tentAt_eq_zero {c x : ℝ} (h : 1 ≤ |x - c|) : tentAt c x = 0 := by
  simp [tentAt, triangle_eq_zero h]

/-- **The tent identity puts a gapped self-dual measure on `ℤ`.** -/
theorem isIntSupported_of_tentSelfDual {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hgap : μ (Ioo (-1) 1 \ {0}) = 0) (hμ : IsTentSelfDual μ) : IsIntSupported μ := by
  obtain ⟨hint, hdual⟩ := hμ
  have h0 := hdual 0
  simp only [fourier_tentAt, Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, one_mul] at h0
  rw [integral_eq_of_gap hgap (f := tentAt 0) (fun x hx => tentAt_eq_zero (by simpa using hx)),
    tentAt_self, one_mul, integral_complex_ofReal] at h0
  have hreal : ∫ ξ, sincSq ξ ∂μ = μ.real {0} := by exact_mod_cast h0
  have hfin : μ {0} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
  have hind : Integrable (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_indicator_iff (measurableSet_singleton 0)).mpr (integrableOn_const hfin)
  set g : ℝ → ℝ := fun ξ => sincSq ξ - ({0} : Set ℝ).indicator 1 ξ
  have hg0 : ∫ ξ, g ξ ∂μ = 0 := by
    rw [integral_sub hint hind, hreal, integral_indicator_one (measurableSet_singleton 0), sub_self]
  have hgnn : 0 ≤ g := fun ξ => by
    by_cases h : ξ = 0
    · simp [g, h, sincSq]
    · simp [g, h, sincSq_nonneg]
  have hae := (integral_eq_zero_iff_of_nonneg hgnn (hint.sub hind)).mp hg0
  have hint' : ∀ᵐ ξ ∂μ, ∃ m : ℤ, (m : ℝ) = ξ := by
    filter_upwards [hae] with ξ hξ
    by_cases h : ξ = 0
    · exact ⟨0, by simp [h]⟩
    · have : sincSq ξ = 0 := by simpa [g, h] using hξ
      exact exists_int_of_sincSq_eq_zero this
  rw [ae_iff] at hint'
  simpa [IsIntSupported, compl_def] using hint'

/-- **Equal atoms.** On `ℤ`, the tent identity at `n` reads `μ{0} = μ{n}`. -/
theorem measure_singleton_eq_of_tentSelfDual {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hgap : μ (Ioo (-1) 1 \ {0}) = 0) (hμ : IsTentSelfDual μ) (n : ℤ) :
    μ {(n : ℝ)} = μ {0} := by
  have hsupp := isIntSupported_of_tentSelfDual hgap hμ
  have h := hμ.2 n
  simp only [fourier_tentAt] at h
  rw [integral_eq_of_isIntSupported hsupp (k := 0) (by simp [sincSq]) (fun m hm => by
      simp [sincSq_int_eq_zero hm]),
    integral_eq_of_isIntSupported hsupp (k := n) (tentAt_self _) (fun m hm => tentAt_eq_zero (by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)))] at h
  have hr : μ.real {(n : ℝ)} = μ.real {0} := by
    have := (Complex.ofReal_injective h).symm
    simpa using this
  exact (ENNReal.toReal_eq_toReal_iff' isCompact_singleton.measure_lt_top.ne
    isCompact_singleton.measure_lt_top.ne).mp hr

theorem integrable_sincSq_diracComb : Integrable sincSq diracComb := by
  refine ⟨continuous_sincSq.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral diracComb
  rw [lintegral_sum_measure]
  simp only [lintegral_dirac]
  rw [tsum_eq_single 0]
  · simp [sincSq]
  · intro m hm
    simp [sincSq_int_eq_zero hm]

/-- **Poisson rigidity.** A locally finite positive measure with the gap `(−1, 1) ∖ {0}` is
self-dual against the integer translates of the tent iff it is `μ{0}` times the Dirac comb. -/
theorem tentSelfDual_iff_eq_smul_diracComb {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hgap : μ (Ioo (-1) 1 \ {0}) = 0) : IsTentSelfDual μ ↔ μ = μ {0} • diracComb := by
  constructor
  · intro hμ
    exact eq_smul_diracComb (isIntSupported_of_tentSelfDual hgap hμ)
      (measure_singleton_eq_of_tentSelfDual hgap hμ)
  · intro hμ
    have hfin : μ {0} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
    generalize hc : μ {0} = c at hμ hfin
    subst hμ
    have hsupp : IsIntSupported (c • diracComb) := by
      unfold IsIntSupported
      rw [Measure.smul_apply, diracComb_isIntSupported, smul_zero]
    have hat : ∀ n : ℤ, (c • diracComb).real {(n : ℝ)} = c.toReal := by
      intro n
      rw [Measure.real, Measure.smul_apply, diracComb_singleton, smul_eq_mul, mul_one]
    refine ⟨integrable_sincSq_diracComb.smul_measure hfin, fun n => ?_⟩
    simp only [fourier_tentAt]
    rw [integral_eq_of_isIntSupported hsupp (k := 0) (by simp [sincSq]) (fun m hm => by
        simp [sincSq_int_eq_zero hm]),
      integral_eq_of_isIntSupported hsupp (k := n) (tentAt_self _) (fun m hm => tentAt_eq_zero (by
        rw [← Int.cast_sub, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm))), hat, hat]

/-- **The gap of a positive self-dual measure is at most one.** -/
theorem eq_zero_of_wide_gap {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {a : ℝ} (ha : 1 < a)
    (hgap : μ (Ioo (-a) a \ {0}) = 0) (hμ : IsTentSelfDual μ) : μ = 0 := by
  have hgap1 : μ (Ioo (-1) 1 \ {0}) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left (Ioo_subset_Ioo (by linarith) ha.le)) hgap
  have h1 := measure_singleton_eq_of_tentSelfDual hgap1 hμ 1
  have h1z : μ {(1 : ℝ)} = 0 := measure_mono_null (by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨by linarith, ha⟩, by norm_num⟩) hgap
  have h0 : μ {0} = 0 := by
    rw [← h1]
    simpa using h1z
  rw [(tentSelfDual_iff_eq_smul_diracComb hgap1).mp hμ, h0, zero_smul]

/-! ### One-sided pairs: uniform density -/

/-- **The tent identity of a one-sided pair.** If `∫ 𝓕g dμ = ∫ g dν` for the modulated tents and
`ν` has the gap, then `∫ sinc(π(ξ − s))² dμ(ξ) = ν{0}` at every `s`. -/
theorem integral_sincSq_shift_eq {μ ν : Measure ℝ} (hgap : ν (Ioo (-1) 1 \ {0}) = 0)
    (hpair : ∀ s : ℝ, ∫ ξ, FourierTransform.fourier (modTent s) ξ ∂μ = ∫ x, modTent s x ∂ν)
    (s : ℝ) : ∫ ξ, (sincSq (ξ - s) : ℂ) ∂μ = (ν.real {0} : ℂ) := by
  have h := hpair s
  simp only [fourier_modTent] at h
  rw [h, integral_eq_of_gap hgap (fun x hx => by simp [modTent, triangle_eq_zero hx])]
  simp [modTent, triangle_zero]

/-- Jordan's inequality: `sinc(πy)² ≥ 4/π²` for `|y| ≤ ½`. -/
theorem four_div_pi_sq_le_sincSq {y : ℝ} (hy : |y| ≤ 1 / 2) : 4 / π ^ 2 ≤ sincSq y := by
  have hπ := Real.pi_pos
  have key : 2 / π ≤ Real.sinc (π * |y|) := by
    by_cases h0 : |y| = 0
    · rw [h0, mul_zero, Real.sinc_zero, div_le_one hπ]
      linarith [Real.pi_gt_three]
    · have hpos : 0 < π * |y| := mul_pos hπ (lt_of_le_of_ne (abs_nonneg y) (Ne.symm h0))
      rw [Real.sinc_of_ne_zero hpos.ne', le_div_iff₀ hpos]
      have := Real.mul_le_sin hpos.le (by nlinarith)
      calc 2 / π * (π * |y|) = 2 / π * (π * |y|) := rfl
        _ ≤ Real.sin (π * |y|) := this
  have hsym : Real.sinc (π * y) = Real.sinc (π * |y|) := by
    rcases abs_choice y with h | h <;> rw [h]
    rw [mul_neg, Real.sinc_neg]
  have h2 : 0 ≤ 2 / π := by positivity
  unfold sincSq
  rw [hsym, show (4 : ℝ) / π ^ 2 = (2 / π) ^ 2 by ring]
  exact pow_le_pow_left₀ h2 key 2

/-- **Uniform local mass.** In a one-sided pair with the gap on the dual side, every interval of
length one carries `μ`-mass at most `(π²/4) ν{0}`. -/
theorem measure_Icc_le_of_poissonPair {μ ν : Measure ℝ} (hgap : ν (Ioo (-1) 1 \ {0}) = 0)
    (hpair : ∀ s : ℝ, ∫ ξ, FourierTransform.fourier (modTent s) ξ ∂μ = ∫ x, modTent s x ∂ν)
    (hint : ∀ s : ℝ, Integrable (fun ξ => sincSq (ξ - s)) μ) (s : ℝ) :
    μ (Icc (s - 1 / 2) (s + 1 / 2)) < ⊤ ∧
      μ.real (Icc (s - 1 / 2) (s + 1 / 2)) ≤ π ^ 2 / 4 * ν.real {0} := by
  set I := Icc (s - 1 / 2) (s + 1 / 2)
  have hI := integral_sincSq_shift_eq hgap hpair s
  rw [integral_complex_ofReal] at hI
  have hreal : ∫ ξ, sincSq (ξ - s) ∂μ = ν.real {0} := by exact_mod_cast hI
  have hle : ∀ ξ, I.indicator (fun _ => 4 / π ^ 2) ξ ≤ sincSq (ξ - s) := by
    intro ξ
    by_cases hξ : ξ ∈ I
    · rw [indicator_of_mem hξ]
      apply four_div_pi_sq_le_sincSq
      rw [abs_le]
      constructor <;> linarith [hξ.1, hξ.2]
    · rw [indicator_of_notMem hξ]
      exact sincSq_nonneg _
  have hc : (0 : ℝ) < 4 / π ^ 2 := by positivity
  have hfin : μ I < ⊤ := by
    have hlt := ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ξ =>
      sincSq_nonneg (ξ - s))).mp (hint s).hasFiniteIntegral)
    have hmono : ENNReal.ofReal (4 / π ^ 2) * μ I ≤
        ∫⁻ ξ, ENNReal.ofReal (sincSq (ξ - s)) ∂μ := by
      rw [← lintegral_indicator_const measurableSet_Icc]
      refine lintegral_mono fun ξ => ?_
      by_cases hξ : ξ ∈ I
      · rw [indicator_of_mem hξ]
        have := hle ξ
        rw [indicator_of_mem hξ] at this
        exact ENNReal.ofReal_le_ofReal this
      · rw [indicator_of_notMem hξ]
        exact zero_le
    exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hmono hlt).ne
      (ENNReal.ofReal_pos.mpr hc).ne'
  refine ⟨hfin, ?_⟩
  have hind : Integrable (I.indicator fun _ => 4 / π ^ 2) μ :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hfin.ne)
  have hmono := integral_mono hind (hint s) hle
  rw [integral_indicator_const _ measurableSet_Icc, hreal, smul_eq_mul] at hmono
  have hπ2 : 0 < π ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have := mul_le_mul_of_nonneg_left hmono hπ2.le
  rw [show π ^ 2 * (μ.real I * (4 / π ^ 2)) = 4 * μ.real I by field_simp] at this
  linarith

end GaloisForLFunctions.ArithmeticPositiveDuality
