import Mathlib

/-!
# The explicit counterexample to the `L²(ℓ¹)` Plancherel order swap

A band-limited profile modulated along an `ℓ² \ ℓ¹` amplitude sequence separates the two mixed
norms: with `ψ` a smooth bump supported in an interval of length `1/2` and `a_n = 1/(n+1)`, the
frequency family `ĉ_n(ξ) = a_n ψ(ξ - n)` has disjoint supports, so its pointwise `ℓ¹` norm has
square `∑_n a_n² ψ(ξ-n)²` and the `L²(ℓ¹)` norm is finite.  Coordinatewise inverse Fourier
transform turns each translate into a unimodular modulation of the fixed inverse profile
`φ = 𝓕⁻ψ`, so `∑_n ‖c_n(x)‖ = ‖φ(x)‖ ∑_n a_n = ∞` wherever `φ(x) ≠ 0` — a set of positive
measure.  Hence `L²_ξ(ℓ¹)` does not transport to `L²_x(ℓ¹)`: the general Plancherel order swap
is false, and only the coordinatewise (`ℓ¹(L²)`) order is legal.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory SchwartzMap Filter
open scoped ENNReal FourierTransform

/-- The band-limiting bump: supported in `ball 0 (1/4)`, equal to one on `ball 0 (1/8)`. -/
def swapBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The frequency profile: the bump as a complex Schwartz function. -/
def swapFreqProfile : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (swapBump.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp swapBump.contDiff)

theorem swapFreqProfile_apply (ξ : ℝ) : swapFreqProfile ξ = (swapBump ξ : ℂ) := rfl

theorem swapFreqProfile_zero : swapFreqProfile 0 = 1 := by
  rw [swapFreqProfile_apply]
  have h1 : swapBump (0 : ℝ) = 1 :=
    swapBump.one_of_mem_closedBall (by simp [swapBump])
  rw [h1]
  norm_num

/-- The profile vanishes outside `ball 0 (1/4)`. -/
theorem swapFreqProfile_eq_zero {ξ : ℝ} (hξ : (1 : ℝ) / 4 ≤ |ξ|) :
    swapFreqProfile ξ = 0 := by
  rw [swapFreqProfile_apply]
  have hmem : ξ ∉ Function.support (swapBump : ℝ → ℝ) := by
    rw [swapBump.support_eq]
    intro hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
    have : swapBump.rOut = 1 / 4 := rfl
    rw [this] at hball
    linarith
  have h0 : swapBump ξ = 0 := Function.notMem_support.mp hmem
  rw [h0]
  norm_num

/-- The position profile `φ = 𝓕⁻ ψ`, at the Schwartz level. -/
def swapPositionProfile : 𝓢(ℝ, ℂ) := 𝓕⁻ swapFreqProfile

theorem swapPositionProfile_ne_zero : swapPositionProfile ≠ 0 := by
  intro h
  have h0 : (FourierTransform.fourierEquiv ℂ 𝓢(ℝ, ℂ)).symm swapFreqProfile = 0 := h
  have h1 : swapFreqProfile = 0 :=
    (LinearEquiv.map_eq_zero_iff _).mp h0
  have h3 := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) h1
  simp only [swapFreqProfile_zero] at h3
  simp at h3

/-- The frequency family `ĉ_n(ξ) = (n+1)⁻¹ ψ(ξ - n)`. -/
def swapFreqFamily (n : ℕ) : ℝ → ℂ := fun ξ =>
  (((n : ℝ) + 1)⁻¹ : ℝ) • swapFreqProfile (ξ - n)

/-- **Disjoint supports**: two distinct translates never overlap. -/
theorem swapFreqFamily_disjoint {m n : ℕ} (hmn : m ≠ n) (ξ : ℝ) :
    swapFreqFamily m ξ = 0 ∨ swapFreqFamily n ξ = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hm, hn⟩ := hcon
  have hme : swapFreqProfile (ξ - m) ≠ 0 := by
    intro h0
    exact hm (by rw [swapFreqFamily, h0, smul_zero])
  have hne : swapFreqProfile (ξ - n) ≠ 0 := by
    intro h0
    exact hn (by rw [swapFreqFamily, h0, smul_zero])
  have hm4 : |ξ - (m : ℝ)| < 1 / 4 := by
    by_contra h4
    exact hme (swapFreqProfile_eq_zero (not_lt.mp h4))
  have hn4 : |ξ - (n : ℝ)| < 1 / 4 := by
    by_contra h4
    exact hne (swapFreqProfile_eq_zero (not_lt.mp h4))
  have hdist : |(m : ℝ) - n| < 1 / 2 := by
    calc |(m : ℝ) - n| = |(ξ - n) - (ξ - m)| := by ring_nf
      _ ≤ |ξ - (n : ℝ)| + |ξ - (m : ℝ)| := abs_sub _ _
      _ < 1 / 2 := by linarith
  have hge : (1 : ℝ) ≤ |(m : ℝ) - n| := by
    have hne : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast hmn
    have h1 : (1 : ℤ) ≤ |(m : ℤ) - n| := Int.one_le_abs (sub_ne_zero.mpr hne)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|(m : ℤ) - n| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |(m : ℝ) - n| := by push_cast; ring
  linarith

/-- A family with pairwise disjoint supports has `(∑ f)² = ∑ f²` pointwise. -/
theorem tsum_sq_of_pairwise_disjoint {f : ℕ → ℝ≥0∞}
    (h : ∀ m n, m ≠ n → f m = 0 ∨ f n = 0) :
    (∑' n, f n) ^ 2 = ∑' n, f n ^ 2 := by
  by_cases hex : ∃ n, f n ≠ 0
  · obtain ⟨n₀, hn₀⟩ := hex
    have hz : ∀ m, m ≠ n₀ → f m = 0 := fun m hm => (h m n₀ hm).resolve_right hn₀
    rw [tsum_eq_single n₀ hz, tsum_eq_single n₀ fun m hm => by
      rw [hz m hm, zero_pow (two_ne_zero)]]
  · push Not at hex
    simp only [hex, tsum_zero, zero_pow two_ne_zero]

/-! ## The frequency mixed norm is finite -/

theorem enorm_swapFreqFamily (n : ℕ) (ξ : ℝ) :
    ‖swapFreqFamily n ξ‖ₑ
      = ENNReal.ofReal (((n : ℝ) + 1)⁻¹) * ‖swapFreqProfile (ξ - n)‖ₑ := by
  rw [swapFreqFamily, enorm_smul]
  congr 1
  rw [Real.enorm_eq_ofReal (by positivity)]

theorem hasCompactSupport_swapFreqProfile :
    HasCompactSupport (swapFreqProfile : ℝ → ℂ) :=
  swapBump.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero

/-- The tail energy of the frequency profile is finite. -/
theorem lintegral_sq_swapFreqProfile_lt_top :
    (∫⁻ ξ, ‖swapFreqProfile ξ‖ₑ ^ 2) < ⊤ := by
  have hF : Continuous fun ξ : ℝ => ‖swapFreqProfile ξ‖ ^ 2 :=
    ((SchwartzMap.continuous swapFreqProfile).norm).pow 2
  have hFcs : HasCompactSupport fun ξ : ℝ => ‖swapFreqProfile ξ‖ ^ 2 :=
    (hasCompactSupport_swapFreqProfile.norm).comp_left (g := (· ^ 2)) (by norm_num)
  have hint : Integrable (fun ξ : ℝ => ‖swapFreqProfile ξ‖ ^ 2) volume :=
    hF.integrable_of_hasCompactSupport hFcs
  have hfin := hint.hasFiniteIntegral
  rw [HasFiniteIntegral] at hfin
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine lintegral_congr fun ξ => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ofReal_norm]
  congr 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **The `L²(ℓ¹)` frequency norm is finite** — the card's `(7)`: disjoint supports collapse the
square of the `ℓ¹` sum to the sum of squares, and translation invariance leaves the geometric
`∑ (n+1)⁻²`. -/
theorem lintegral_sq_tsum_swapFreqFamily :
    (∫⁻ ξ, (∑' n : ℕ, ‖swapFreqFamily n ξ‖ₑ) ^ 2) < ⊤ := by
  have hpt : ∀ ξ : ℝ, (∑' n : ℕ, ‖swapFreqFamily n ξ‖ₑ) ^ 2
      = ∑' n : ℕ, ‖swapFreqFamily n ξ‖ₑ ^ 2 := by
    intro ξ
    refine tsum_sq_of_pairwise_disjoint fun m n hmn => ?_
    rcases swapFreqFamily_disjoint hmn ξ with h | h
    · exact Or.inl (by rw [h, enorm_zero])
    · exact Or.inr (by rw [h, enorm_zero])
  simp_rw [hpt]
  have hmeas : ∀ n : ℕ, AEMeasurable (fun ξ => ‖swapFreqFamily n ξ‖ₑ ^ 2) volume := by
    intro n
    have hc : Continuous (swapFreqFamily n) := by
      have h1 : Continuous fun ξ : ℝ => ξ - (n : ℝ) := continuous_id.sub continuous_const
      have h2 : Continuous fun ξ : ℝ => swapFreqProfile (ξ - n) :=
        (SchwartzMap.continuous swapFreqProfile).comp h1
      exact h2.const_smul ((((n : ℝ) + 1)⁻¹ : ℝ))
    exact (hc.enorm.measurable.pow_const 2).aemeasurable
  rw [lintegral_tsum hmeas]
  have hterm : ∀ n : ℕ, (∫⁻ ξ, ‖swapFreqFamily n ξ‖ₑ ^ 2)
      = ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ^ 2
          * ∫⁻ ξ, ‖swapFreqProfile ξ‖ₑ ^ 2 := by
    intro n
    have h1 : ∀ ξ : ℝ, ‖swapFreqFamily n ξ‖ₑ ^ 2
        = ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ^ 2 * ‖swapFreqProfile (ξ - n)‖ₑ ^ 2 := by
      intro ξ
      rw [enorm_swapFreqFamily, mul_pow]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    congr 1
    have h2 : ∀ ξ : ℝ, ‖swapFreqProfile (ξ - n)‖ₑ ^ 2
        = (fun η => ‖swapFreqProfile η‖ₑ ^ 2) (ξ + -(n : ℝ)) := by
      intro ξ
      rw [← sub_eq_add_neg]
    simp_rw [h2]
    exact lintegral_add_right_eq_self (fun η => ‖swapFreqProfile η‖ₑ ^ 2) (-(n : ℝ))
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ lintegral_sq_swapFreqProfile_lt_top
  have hsummable : Summable fun n : ℕ => (((n : ℝ) + 1)⁻¹) ^ 2 := by
    have hp := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have hs := (summable_nat_add_iff 1).mpr hp
    refine hs.congr fun n => ?_
    rw [one_div, ← inv_pow]
    push_cast
    ring
  have hofreal : ∀ n : ℕ, ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ^ 2
      = ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) := fun n =>
    (ENNReal.ofReal_pow (by positivity) 2).symm
  simp_rw [hofreal]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
  exact ENNReal.ofReal_lt_top

/-! ## The position family diverges in `ℓ¹` on a set of positive measure -/

open scoped RealInnerProductSpace

/-- The position family: the coordinatewise inverse Fourier transform. -/
def swapPositionFamily (n : ℕ) : ℝ → ℂ := 𝓕⁻ (swapFreqFamily n)

/-- **Each position coordinate is a unimodular modulation of the fixed profile** — the card's
`(8)`: frequency translation contributes only a phase, so the norm is the amplitude times the
profile norm. -/
theorem norm_swapPositionFamily (n : ℕ) (x : ℝ) :
    ‖swapPositionFamily n x‖ = ((n : ℝ) + 1)⁻¹ * ‖swapPositionProfile x‖ := by
  rw [swapPositionFamily, Real.fourierInv_eq]
  have hshift : (∫ ξ, 𝐞 ⟪ξ, x⟫ • swapFreqFamily n ξ)
      = ∫ η, 𝐞 ⟪η + (n : ℝ), x⟫ • swapFreqFamily n (η + n) :=
    (integral_add_right_eq_self (fun ξ => 𝐞 ⟪ξ, x⟫ • swapFreqFamily n ξ) (n : ℝ)).symm
  rw [hshift]
  have hint : ∀ η : ℝ, 𝐞 ⟪η + (n : ℝ), x⟫ • swapFreqFamily n (η + n)
      = ((𝐞 ⟪(n : ℝ), x⟫ : Circle) : ℂ)
          * ((((n : ℝ) + 1)⁻¹ : ℝ) • (𝐞 ⟪η, x⟫ • swapFreqProfile η)) := by
    intro η
    rw [swapFreqFamily]
    have hadd : ⟪η + (n : ℝ), x⟫ = ⟪η, x⟫ + ⟪(n : ℝ), x⟫ := inner_add_left _ _ _
    rw [hadd, AddChar.map_add_eq_mul]
    have harg : η + (n : ℝ) - n = η := by ring
    rw [harg]
    simp only [Circle.smul_def, Circle.coe_mul, Complex.real_smul]
    ring
  simp_rw [hint]
  rw [integral_const_mul, norm_mul, Circle.norm_coe, one_mul, integral_smul, norm_smul]
  congr 1
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · have hcoe : (swapPositionProfile : ℝ → ℂ) x = 𝓕⁻ (swapFreqProfile : ℝ → ℂ) x := by
      rw [swapPositionProfile]
      exact congrFun (SchwartzMap.fourierInv_coe swapFreqProfile) x
    rw [hcoe, Real.fourierInv_eq]

/-- **The pointwise `ℓ¹` divergence** — the card's `(9)`: wherever the profile does not vanish,
the amplitudes sum to the harmonic series. -/
theorem not_summable_norm_swapPositionFamily {x : ℝ}
    (hx : swapPositionProfile x ≠ 0) :
    ¬ Summable fun n : ℕ => ‖swapPositionFamily n x‖ := by
  intro hsum
  have hc : ‖swapPositionProfile x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ‖swapPositionProfile x‖ :=
    hsum.congr fun n => norm_swapPositionFamily n x
  have h2 : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
    have h3 := h1.mul_right (‖swapPositionProfile x‖⁻¹)
    refine h3.congr fun n => ?_
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have h4 : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) := by
    refine h2.congr fun n => ?_
    rw [one_div]
    push_cast
    ring
  have h5 : Summable fun n : ℕ => 1 / (n : ℝ) := (summable_nat_add_iff 1).mp h4
  exact Real.not_summable_one_div_natCast h5

/-- The divergence set has positive measure. -/
theorem measurePos_not_summable_swapPositionFamily :
    0 < volume {x : ℝ | ¬ Summable fun n : ℕ => ‖swapPositionFamily n x‖} := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, swapPositionProfile x ≠ 0 := by
    by_contra hall
    push Not at hall
    refine swapPositionProfile_ne_zero ?_
    ext x
    simpa using hall x
  have hopen : IsOpen {x : ℝ | swapPositionProfile x ≠ 0} := by
    have h1 : {x : ℝ | swapPositionProfile x ≠ 0}
        = (swapPositionProfile : ℝ → ℂ) ⁻¹' ({0}ᶜ) := rfl
    rw [h1]
    exact (isOpen_compl_singleton).preimage (SchwartzMap.continuous _)
  have hsub : {x : ℝ | swapPositionProfile x ≠ 0}
      ⊆ {x : ℝ | ¬ Summable fun n : ℕ => ‖swapPositionFamily n x‖} :=
    fun x hx => not_summable_norm_swapPositionFamily hx
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨x₀, hx₀⟩) (measure_mono hsub)

/-- **The explicit counterexample to the `L²(ℓ¹)` order swap**: a frequency family with finite
`L²(ℓ¹)` mixed norm whose coordinatewise inverse Fourier transforms fail pointwise `ℓ¹`
summability on a set of positive measure.  Frequency-side `L²(ℓ¹)` control does not transport to
position space; only the `ℓ¹(L²)` order is legal. -/
theorem suzukiWiener_orderSwap_counterexample :
    (∫⁻ ξ, (∑' n : ℕ, ‖swapFreqFamily n ξ‖ₑ) ^ 2) < ⊤ ∧
      0 < volume {x : ℝ | ¬ Summable fun n : ℕ => ‖𝓕⁻ (swapFreqFamily n) x‖} :=
  ⟨lintegral_sq_tsum_swapFreqFamily, measurePos_not_summable_swapPositionFamily⟩

end GaloisForLFunctions.RHTower
