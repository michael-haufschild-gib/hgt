import GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity
import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing

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
* **The unit gap is sharp** (`exists_tentSelfDual_not_comb`). For `0 < a < 1` the two dual
  lattices `Σ_m δ_{am} + a⁻¹ Σ_k δ_{k/a}` form a locally finite positive tent-self-dual measure
  with gap `(−a, a) ∖ {0}` that is no multiple of the Dirac comb. Self-duality is Poisson
  summation on `aℤ` and on `a⁻¹ℤ` (`tsum_tentAt_lattice`).
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

/-! ### The unit gap is sharp: two dual lattices -/

open GaloisForLFunctions.HTGeometry (eventually_abs_ge_cocompact abs_sinc_le_inv)
open Asymptotics Filter
open scoped ENNReal

/-- The comb `Σ_m δ_{bm}` of the lattice `bℤ`. -/
def latticeComb (b : ℝ) : Measure ℝ := Measure.sum fun m : ℤ => (1 : ℝ≥0∞) • Measure.dirac (b * m)

/-- Two dual lattices: `Σ_m δ_{bm} + b⁻¹ Σ_k δ_{b⁻¹k}`. -/
def dualLatticePair (b : ℝ) : Measure ℝ := latticeComb b + ENNReal.ofReal b⁻¹ • latticeComb b⁻¹

theorem integral_latticeComb (b : ℝ) (f : ℝ → ℂ) :
    ∫ x, f x ∂latticeComb b = ∑' m : ℤ, f (b * m) := by
  rw [latticeComb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp

theorem one_div_sq_eq_abs_rpow (x : ℝ) : |x| ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
  rw [Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    sq_abs, one_div]

/-- A function bounded by `K/y²` off the origin is summable along `bℤ`. -/
theorem summable_lattice {b : ℝ} (hb : 0 < b) {f : ℝ → ℂ} {K : ℝ}
    (hf : ∀ y, y ≠ 0 → ‖f y‖ ≤ K / y ^ 2) : Summable fun m : ℤ => ‖f (b * m)‖ := by
  refine Summable.of_norm_bounded_eventually (g := fun m : ℤ => K / b ^ 2 * (1 / (m : ℝ) ^ 2))
    ((summable_one_div_int_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [eventually_cofinite_ne 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [norm_norm]
  calc ‖f (b * m)‖ ≤ K / (b * m) ^ 2 := hf _ (mul_ne_zero hb.ne' hm')
    _ = K / b ^ 2 * (1 / (m : ℝ) ^ 2) := by field_simp

theorem norm_fourier_tentAt (c ξ : ℝ) : ‖FourierTransform.fourier (tentAt c) ξ‖ = sincSq ξ := by
  rw [fourier_tentAt, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (sincSq_nonneg ξ)]

theorem sincSq_le_div_sq {y : ℝ} (hy : y ≠ 0) : sincSq y ≤ (1 / π ^ 2) / y ^ 2 := by
  have h := abs_sinc_le_inv (mul_ne_zero Real.pi_ne_zero hy)
  have hpos : 0 < |π * y| := abs_pos.mpr (mul_ne_zero Real.pi_ne_zero hy)
  unfold sincSq
  rw [← sq_abs]
  calc |Real.sinc (π * y)| ^ 2 ≤ (1 / |π * y|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (1 / π ^ 2) / y ^ 2 := by rw [div_pow, sq_abs]; field_simp

theorem norm_tentAt_le (c y : ℝ) : ‖tentAt c y‖ ≤ 1 := by
  rw [tentAt, Complex.norm_real, Real.norm_of_nonneg (by unfold triangle; positivity)]
  unfold triangle
  exact max_le zero_le_one (by linarith [abs_nonneg (y - c)])

theorem norm_tentAt_le_div_sq (c : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ‖tentAt c y‖ ≤ (|c| + 1) ^ 2 / y ^ 2 := by
  by_cases h : 1 ≤ |y - c|
  · rw [tentAt_eq_zero h, norm_zero]; positivity
  · push Not at h
    have hy2 : y ^ 2 ≤ (|c| + 1) ^ 2 := by
      rw [← sq_abs y]
      have : |y| ≤ |c| + 1 := by
        have := abs_sub_abs_le_abs_sub y c
        linarith
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [le_div_iff₀ (by positivity)]
    calc ‖tentAt c y‖ * y ^ 2 ≤ 1 * (|c| + 1) ^ 2 :=
          mul_le_mul (norm_tentAt_le c y) hy2 (by positivity) zero_le_one
      _ = (|c| + 1) ^ 2 := one_mul _

/-- The transform of a dilated tent: `𝓕[Λ(b · − c)](ξ) = b⁻¹ 𝓕[Λ(· − c)](ξ/b)`. -/
theorem fourier_tentAt_comp_mul {b : ℝ} (hb : 0 < b) (c ξ : ℝ) :
    FourierTransform.fourier (fun x => tentAt c (b * x)) ξ =
      ((b⁻¹ : ℝ) : ℂ) * FourierTransform.fourier (tentAt c) (ξ / b) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set G : ℝ → ℂ := fun y => cexp (((-2 * π * y * (ξ / b) : ℝ) : ℂ) * I) • tentAt c y
  have e : (fun v : ℝ => cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • tentAt c (b * v)) =
      fun v => G (b * v) := by
    funext v
    simp only [G]
    congr 3
    field_simp
  rw [e, Measure.integral_comp_mul_left G b, abs_inv, abs_of_pos hb, Complex.real_smul]

theorem continuous_tentAt_comp_mul (b c : ℝ) : Continuous fun x => tentAt c (b * x) := by
  unfold tentAt
  exact Complex.continuous_ofReal.comp
    (continuous_triangle.comp ((continuous_const.mul continuous_id).sub continuous_const))

/-- **Poisson summation on `bℤ` for a tent.** -/
theorem tsum_tentAt_lattice {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∑' m : ℤ, tentAt c (b * m) =
      ((b⁻¹ : ℝ) : ℂ) * ∑' k : ℤ, FourierTransform.fourier (tentAt c) (b⁻¹ * k) := by
  have h1 : (fun x => tentAt c (b * x)) =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_abs_ge_cocompact ((|c| + 1) / b)] with x hx
    have h : 1 ≤ |b * x - c| := by
      have h1 : |c| + 1 ≤ b * |x| := by rwa [div_le_iff₀ hb, mul_comm] at hx
      have h2 : b * |x| - |c| ≤ |b * x - c| := by
        have := abs_sub_abs_le_abs_sub (b * x) c
        rwa [abs_mul, abs_of_pos hb] at this
      linarith
    rw [tentAt_eq_zero h, norm_zero]
    positivity
  have h2 : FourierTransform.fourier (fun x => tentAt c (b * x)) =O[cocompact ℝ]
      (|·| ^ (-(2 : ℝ))) := by
    refine IsBigO.of_bound (b / π ^ 2) ?_
    filter_upwards [eventually_abs_ge_cocompact 1] with ξ hξ
    have hξ0 : ξ ≠ 0 := by
      intro h; rw [h, abs_zero] at hξ; linarith
    rw [fourier_tentAt_comp_mul hb, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hb.le), norm_fourier_tentAt, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), one_div_sq_eq_abs_rpow]
    have := sincSq_le_div_sq (div_ne_zero hξ0 hb.ne')
    calc b⁻¹ * sincSq (ξ / b) ≤ b⁻¹ * ((1 / π ^ 2) / (ξ / b) ^ 2) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hb.le)
      _ = b / π ^ 2 * (1 / ξ ^ 2) := by field_simp
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_tentAt_comp_mul b c)
    (by norm_num : (1 : ℝ) < 2) h1 h2 0
  simp only [zero_add, fourier_coe_apply, Complex.ofReal_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [fourier_tentAt_comp_mul hb]
  congr 2
  field_simp

theorem integrable_latticeComb {b : ℝ} (hb : 0 < b) {f : ℝ → ℂ} {K : ℝ}
    (hf : ∀ y, y ≠ 0 → ‖f y‖ ≤ K / y ^ 2) : Integrable f (latticeComb b) := by
  rw [latticeComb, integrable_sum_dirac_iff (fun _ => ENNReal.one_ne_top)]
  simpa using summable_lattice hb hf

theorem integral_dualLatticePair {b : ℝ} (hb : 0 < b) {f : ℝ → ℂ} {K : ℝ}
    (hf : ∀ y, y ≠ 0 → ‖f y‖ ≤ K / y ^ 2) :
    ∫ x, f x ∂dualLatticePair b =
      ∑' m : ℤ, f (b * m) + ((b⁻¹ : ℝ) : ℂ) * ∑' k : ℤ, f (b⁻¹ * k) := by
  rw [dualLatticePair, integral_add_measure (integrable_latticeComb hb hf)
    ((integrable_latticeComb (inv_pos.mpr hb) hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_latticeComb, integral_latticeComb,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hb.le), Complex.real_smul]

/-- **Two dual lattices are tent self-dual.** -/
theorem isTentSelfDual_dualLatticePair {b : ℝ} (hb : 0 < b) :
    IsTentSelfDual (dualLatticePair b) := by
  have hF : ∀ n : ℤ, ∀ y, y ≠ 0 → ‖FourierTransform.fourier (tentAt n) y‖ ≤ (1 / π ^ 2) / y ^ 2 :=
    fun n y hy => by rw [norm_fourier_tentAt]; exact sincSq_le_div_sq hy
  refine ⟨?_, fun n => ?_⟩
  · have hs : ∀ y, y ≠ 0 → ‖((sincSq y : ℝ) : ℂ)‖ ≤ (1 / π ^ 2) / y ^ 2 := fun y hy => by
      rw [Complex.norm_real, Real.norm_of_nonneg (sincSq_nonneg y)]; exact sincSq_le_div_sq hy
    have h1 := integrable_latticeComb hb hs
    have h2 := (integrable_latticeComb (inv_pos.mpr hb) hs).smul_measure
      (ENNReal.ofReal_ne_top (r := b⁻¹))
    exact (h1.add_measure h2).re.congr (Eventually.of_forall fun y => by simp)
  · rw [integral_dualLatticePair hb (hF n), integral_dualLatticePair hb
      (fun y hy => norm_tentAt_le_div_sq (n : ℝ) hy), tsum_tentAt_lattice hb,
      tsum_tentAt_lattice (inv_pos.mpr hb), inv_inv]
    have hb' : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
    ring

/-- The lattice comb puts no mass on `S` when no lattice point lies in `S`. -/
theorem latticeComb_eq_zero {b : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (h : ∀ m : ℤ, b * m ∉ S) : latticeComb b S = 0 := by
  rw [latticeComb, Measure.sum_apply _ hS]
  refine ENNReal.tsum_eq_zero.mpr fun m => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, indicator_of_notMem (h m), smul_zero]

theorem one_le_latticeComb {b : ℝ} {S : Set ℝ} (hS : MeasurableSet S) {m : ℤ} (hm : b * m ∈ S) :
    1 ≤ latticeComb b S := by
  rw [latticeComb, Measure.sum_apply _ hS]
  refine le_trans ?_ (ENNReal.le_tsum m)
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, indicator_of_mem hm]
  simp

theorem latticeComb_Icc_lt_top {b : ℝ} (hb : 0 < b) (x : ℝ) :
    latticeComb b (Icc (x - 1) (x + 1)) < ⊤ := by
  classical
  set F : Finset ℤ := Finset.Icc (⌊(x - 1) / b⌋) (⌈(x + 1) / b⌉)
  rw [latticeComb, Measure.sum_apply _ measurableSet_Icc, tsum_eq_sum (s := F)]
  · exact ENNReal.sum_lt_top.mpr fun m _ => by
      rw [Measure.smul_apply, one_smul]
      exact measure_lt_top _ _
  · intro m hm
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc, indicator_of_notMem, smul_zero]
    intro hmem
    apply hm
    rw [Finset.mem_Icc]
    constructor
    · exact Int.floor_le_iff.mpr (by
        have := hmem.1
        have h : (x - 1) / b ≤ m := by rw [div_le_iff₀ hb]; linarith
        linarith)
    · exact Int.le_ceil_iff.mpr (by
        have := hmem.2
        have h : (m : ℝ) ≤ (x + 1) / b := by rw [le_div_iff₀ hb]; linarith
        linarith)

instance isLocallyFiniteMeasure_dualLatticePair {b : ℝ} [Fact (0 < b)] :
    IsLocallyFiniteMeasure (dualLatticePair b) := by
  have hb : 0 < b := Fact.out
  refine ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  rw [dualLatticePair, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.add_lt_top.mpr ⟨latticeComb_Icc_lt_top hb x,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (latticeComb_Icc_lt_top (inv_pos.mpr hb) x)⟩

/-- **The unit gap is sharp.** For `0 < a < 1` the two dual lattices form a locally finite
positive tent-self-dual measure with gap `(−a, a) ∖ {0}` that is no multiple of the Dirac comb. -/
theorem exists_tentSelfDual_not_comb {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ μ : Measure ℝ, IsLocallyFiniteMeasure μ ∧ μ (Ioo (-a) a \ {0}) = 0 ∧ IsTentSelfDual μ ∧
      μ ≠ μ {0} • diracComb := by
  haveI : Fact (0 < a) := ⟨ha0⟩
  have hmeas : MeasurableSet (Ioo (-a) a \ {0}) := measurableSet_Ioo.diff (measurableSet_singleton 0)
  refine ⟨dualLatticePair a, inferInstance, ?_, isTentSelfDual_dualLatticePair ha0, ?_⟩
  · rw [dualLatticePair, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      latticeComb_eq_zero hmeas, latticeComb_eq_zero hmeas, mul_zero, add_zero]
    · intro m ⟨⟨h1, h2⟩, h0⟩
      have hm0 : m ≠ 0 := by rintro rfl; simp at h0
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
      have : a⁻¹ ≤ |a⁻¹ * m| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr ha0)]
        nlinarith [inv_pos.mpr ha0]
      have ha' : a < a⁻¹ := by
        rw [lt_inv_comm₀ ha0 ha0]
        calc a⁻¹ > 1 := one_lt_inv_iff₀.mpr ⟨ha0, ha1⟩
          _ > a := ha1
      cases abs_cases (a⁻¹ * m) <;> linarith
    · intro m ⟨⟨h1, h2⟩, h0⟩
      have hm0 : m ≠ 0 := by rintro rfl; simp at h0
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
      have : a ≤ |a * m| := by rw [abs_mul, abs_of_pos ha0]; nlinarith
      cases abs_cases (a * m) <;> linarith
  · intro h
    have h1 : 1 ≤ dualLatticePair a {a} := by
      rw [dualLatticePair, Measure.add_apply]
      exact le_add_right (one_le_latticeComb (measurableSet_singleton a) (m := 1) (by simp))
    have h2 : diracComb {a} = 0 := by
      unfold diracComb
      rw [Measure.sum_apply _ (measurableSet_singleton a)]
      refine ENNReal.tsum_eq_zero.mpr fun n => ?_
      rw [Measure.dirac_apply' _ (measurableSet_singleton a), indicator_of_notMem]
      rw [mem_singleton_iff]
      intro hn
      have hn0 : (0 : ℝ) < n := hn ▸ ha0
      have hn1 : (n : ℝ) < 1 := hn ▸ ha1
      have : (0 : ℤ) < n := by exact_mod_cast hn0
      have : n < (1 : ℤ) := by exact_mod_cast hn1
      omega
    rw [h, Measure.smul_apply, h2, smul_zero] at h1
    exact absurd h1 (by norm_num)

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_tentSelfDual_not_comb
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.tentSelfDual_iff_eq_smul_diracComb
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.measure_Icc_le_of_poissonPair
