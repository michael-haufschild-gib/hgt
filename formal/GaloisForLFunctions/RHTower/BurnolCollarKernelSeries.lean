import GaloisForLFunctions.RHTower.BurnolGammaSteinMoments

/-!
# Normal convergence of the depth ladder and the crossing commutator

The depth kernels `κ_n(u) = 4 e^{-u/2} e^{-z_n} z_n (2z_n² - 7z_n + 3)`, `z_n = π 4ⁿ e^{-2u}`, decay
superexponentially in the depth: `e^{-z}(2z³+7z²+3z) ≤ 4608 e^{-z/2}` for every `z > 0`, and
`z_{n} ≥ n z_0`.  Hence the total kernel `κ₂ = ∑_{n ≥ 1} κ_n` converges normally on every compact
logarithmic interval.

The aperture commutator of a convolution operator is supported on the crossing region: for every
half-line projection `P_b`,

`([P_b, K] g)(u) = ∫ κ(u-v) (1_{u ≤ b} - 1_{v ≤ b}) g(v) dv`,

which vanishes unless `u` and `v` lie on opposite sides of `b`.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## The depth decay -/

theorem burnolCollarCubicExpBound {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) * (2 * z ^ 3 + 7 * z ^ 2 + 3 * z) ≤ 4608 * Real.exp (-z / 2) := by
  have hkey : Real.exp (-z / 2) * (2 * z ^ 3 + 7 * z ^ 2 + 3 * z) ≤ 4608 := by
    rcases le_or_gt z 1 with hle | hgt
    · have h1 : Real.exp (-z / 2) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      have h2 : 2 * z ^ 3 + 7 * z ^ 2 + 3 * z ≤ 12 := by nlinarith
      nlinarith [Real.exp_pos (-z / 2), h1, h2, hz]
    · have hexp : (z / 2) ^ 4 / (24 : ℝ) ≤ Real.exp (z / 2) := by
        have hnn : (0 : ℝ) ≤ z / 2 := by linarith
        have hsum := Real.sum_le_exp_of_nonneg hnn 5
        have hmem : (z / 2) ^ 4 / ((4 : ℕ).factorial : ℝ) ≤
            ∑ i ∈ Finset.range 5, (z / 2) ^ i / ((i.factorial : ℕ) : ℝ) :=
          Finset.single_le_sum (f := fun i : ℕ => (z / 2) ^ i / ((i.factorial : ℕ) : ℝ))
            (fun i _ => by positivity) (by decide)
        norm_num at hmem
        linarith
      have hE : (0 : ℝ) < Real.exp (z / 2) := Real.exp_pos _
      have hinv : Real.exp (-z / 2) = (Real.exp (z / 2))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        ring
      rw [hinv, inv_mul_eq_div, div_le_iff₀ hE]
      have hz2 : z ≤ z ^ 2 := by nlinarith
      have hz3 : z ^ 2 ≤ z ^ 3 := by nlinarith
      have hz4 : z ^ 3 ≤ z ^ 4 := by nlinarith
      have hz24 : z ^ 2 ≤ z ^ 4 := le_trans hz3 hz4
      have hz14 : z ≤ z ^ 4 := le_trans (le_trans hz2 hz3) hz4
      have hbig : 12 * z ^ 4 ≤ 4608 * Real.exp (z / 2) := by nlinarith [hexp]
      linarith [hz4, hz24, hz14, hbig]
  have hsplit : Real.exp (-z) = Real.exp (-z / 2) * Real.exp (-z / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  nlinarith [hkey, Real.exp_pos (-z / 2), Real.exp_nonneg (-z / 2)]

theorem burnolNatCast_le_four_pow (n : ℕ) : (n : ℝ) ≤ (4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ]
    linarith [ih, h1]

theorem burnolCollarZ_ge {n : ℕ} (u : ℝ) : (n : ℝ) * burnolCollarZ 0 u ≤ burnolCollarZ n u := by
  have hz0 : 0 < burnolCollarZ 0 u := burnolCollarZ_pos 0 u
  have hz : burnolCollarZ n u = (4 : ℝ) ^ n * burnolCollarZ 0 u := by
    rw [burnolCollarZ, burnolCollarZ]
    ring
  rw [hz]
  nlinarith [burnolNatCast_le_four_pow n, hz0]

/-- **Superexponential depth decay.** -/
theorem abs_burnolCollarKernel_le (n : ℕ) (u : ℝ) :
    |burnolCollarKernel n u| ≤
      18432 * Real.exp (-u / 2) * Real.exp (-((n : ℝ) * burnolCollarZ 0 u) / 2) := by
  have hz : 0 < burnolCollarZ n u := burnolCollarZ_pos n u
  have hz0 : 0 < burnolCollarZ 0 u := burnolCollarZ_pos 0 u
  have hEu : (0 : ℝ) < Real.exp (-u / 2) := Real.exp_pos _
  have hcubic := burnolCollarCubicExpBound hz
  have habs : |burnolCollarKernel n u| =
      4 * Real.exp (-u / 2) * Real.exp (-burnolCollarZ n u) * burnolCollarZ n u *
        |2 * burnolCollarZ n u ^ 2 - 7 * burnolCollarZ n u + 3| := by
    rw [burnolCollarKernel, abs_mul]
    congr 1
    rw [abs_of_pos (by positivity)]
  have hquad : |2 * burnolCollarZ n u ^ 2 - 7 * burnolCollarZ n u + 3| ≤
      2 * burnolCollarZ n u ^ 2 + 7 * burnolCollarZ n u + 3 := by
    rw [abs_le]
    constructor <;> nlinarith [hz, sq_nonneg (burnolCollarZ n u)]
  have hstep : |burnolCollarKernel n u| ≤
      4 * Real.exp (-u / 2) *
        (Real.exp (-burnolCollarZ n u) *
          (2 * burnolCollarZ n u ^ 3 + 7 * burnolCollarZ n u ^ 2 + 3 * burnolCollarZ n u)) := by
    rw [habs]
    nlinarith [hquad, hEu, Real.exp_pos (-burnolCollarZ n u), hz,
      mul_pos hEu (Real.exp_pos (-burnolCollarZ n u)),
      mul_pos (mul_pos hEu (Real.exp_pos (-burnolCollarZ n u))) hz]
  refine hstep.trans ?_
  have hmono : Real.exp (-burnolCollarZ n u / 2) ≤
      Real.exp (-((n : ℝ) * burnolCollarZ 0 u) / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have := burnolCollarZ_ge (n := n) u
    linarith
  nlinarith [hcubic, hmono, hEu, Real.exp_pos (-burnolCollarZ n u / 2),
    Real.exp_pos (-((n : ℝ) * burnolCollarZ 0 u) / 2)]

theorem burnolSummable_collarKernel (u : ℝ) :
    Summable (fun n : ℕ => burnolCollarKernel n u) := by
  have hz0 : 0 < burnolCollarZ 0 u := burnolCollarZ_pos 0 u
  set r : ℝ := Real.exp (-burnolCollarZ 0 u / 2) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => 18432 * Real.exp (-u / 2) * r ^ n) ?_ (fun n => ?_)
  · exact (summable_geometric_of_lt_one hrpos.le hrlt).mul_left _
  · have hb := abs_burnolCollarKernel_le n u
    have hpow : Real.exp (-((n : ℝ) * burnolCollarZ 0 u) / 2) = r ^ n := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [Real.norm_eq_abs, ← hpow]
    exact hb

/-- The total Gamma-sewn collar kernel `κ₂ = ∑_{n ≥ 1} κ_n`. -/
def burnolCollarKernelTotal (u : ℝ) : ℝ := ∑' n : ℕ, burnolCollarKernel (n + 1) u

theorem hasSum_burnolCollarKernelTotal (u : ℝ) :
    HasSum (fun n : ℕ => burnolCollarKernel (n + 1) u) (burnolCollarKernelTotal u) :=
  ((summable_nat_add_iff 1).mpr (burnolSummable_collarKernel u)).hasSum

/-- **Normal convergence on every compact logarithmic interval.** -/
theorem burnolCollarKernel_normal_convergence {a b : ℝ} :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ u ∈ Icc a b, ∀ n : ℕ, |burnolCollarKernel n u| ≤ C * r ^ n := by
  set c : ℝ := π * Real.exp (-2 * b) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨18432 * Real.exp (-a / 2), Real.exp (-c / 2), by positivity,
    (Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  intro u hu n
  have hz0 : burnolCollarZ 0 u = π * Real.exp (-2 * u) := burnolCollarZ_zero u
  have hzc : c ≤ burnolCollarZ 0 u := by
    rw [hz0, hc]
    have : Real.exp (-2 * b) ≤ Real.exp (-2 * u) :=
      Real.exp_le_exp.mpr (by linarith [hu.2])
    nlinarith [Real.pi_pos, this]
  have hb := abs_burnolCollarKernel_le n u
  refine hb.trans ?_
  have hpow : Real.exp (-((n : ℝ) * burnolCollarZ 0 u) / 2) ≤ Real.exp (-c / 2) ^ n := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hzc, hnn]
  have hexpu : Real.exp (-u / 2) ≤ Real.exp (-a / 2) :=
    Real.exp_le_exp.mpr (by linarith [hu.1])
  nlinarith [hpow, hexpu, Real.exp_pos (-u / 2), Real.exp_pos (-a / 2),
    pow_nonneg (Real.exp_pos (-c / 2)).le n,
    Real.exp_pos (-((n : ℝ) * burnolCollarZ 0 u) / 2)]

/-! ## The aperture crossing commutator -/

/-- Multiplication by the indicator of the closed half-line `(-∞, b]`. -/
def burnolHalfLineProjection (b : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => if u ≤ b then g u else 0

/-- Convolution by a real logarithmic kernel. -/
def burnolKernelConvolution (κ : ℝ → ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, ((κ (u - v) : ℝ) : ℂ) * g v

/-- **The aperture commutator is the cross-boundary operator.** -/
theorem burnolKernelConvolution_commutator (κ : ℝ → ℝ) (g : ℝ → ℂ) (b u : ℝ)
    (hint : Integrable (fun v : ℝ => ((κ (u - v) : ℝ) : ℂ) * g v)) :
    burnolHalfLineProjection b (burnolKernelConvolution κ g) u -
        burnolKernelConvolution κ (burnolHalfLineProjection b g) u =
      ∫ v : ℝ, ((κ (u - v) : ℝ) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v := by
  have hind : Integrable (fun v : ℝ =>
      ((κ (u - v) : ℝ) : ℂ) * (if v ≤ b then (1 : ℂ) else 0) * g v) := by
    have hset : (fun v : ℝ => ((κ (u - v) : ℝ) : ℂ) * (if v ≤ b then (1 : ℂ) else 0) * g v) =
        Set.indicator (Iic b) (fun v : ℝ => ((κ (u - v) : ℝ) : ℂ) * g v) := by
      funext v
      by_cases hv : v ≤ b
      · rw [if_pos hv, Set.indicator_of_mem (by exact hv)]
        ring
      · rw [if_neg hv, Set.indicator_of_notMem (by exact hv)]
        ring
    rw [hset]
    exact hint.indicator measurableSet_Iic
  have hconst : Integrable (fun v : ℝ =>
      ((κ (u - v) : ℝ) : ℂ) * (if u ≤ b then (1 : ℂ) else 0) * g v) := by
    by_cases hu : u ≤ b
    · simpa only [if_pos hu, mul_one] using hint
    · simp only [if_neg hu, mul_zero, zero_mul]
      exact integrable_zero _ _ _
  have hsplit : ∀ v : ℝ, ((κ (u - v) : ℝ) : ℂ) *
      ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v =
      ((κ (u - v) : ℝ) : ℂ) * (if u ≤ b then (1 : ℂ) else 0) * g v -
        ((κ (u - v) : ℝ) : ℂ) * (if v ≤ b then (1 : ℂ) else 0) * g v := by
    intro v
    ring
  rw [funext hsplit, integral_sub hconst hind]
  congr 1
  · rw [burnolHalfLineProjection, burnolKernelConvolution]
    by_cases hu : u ≤ b
    · simp only [if_pos hu, mul_one]
    · simp only [if_neg hu, mul_zero, zero_mul, integral_zero]
  · rw [burnolKernelConvolution]
    refine integral_congr_ae ?_
    filter_upwards with v
    rw [burnolHalfLineProjection]
    by_cases hv : v ≤ b
    · rw [if_pos hv, if_pos hv]
      ring
    · rw [if_neg hv, if_neg hv]
      ring

/-- The commutator integrand is supported on the crossing region. -/
theorem burnolCrossingSupport (κ : ℝ → ℝ) (g : ℝ → ℂ) (b u v : ℝ)
    (h : (u ≤ b ∧ v ≤ b) ∨ (¬ u ≤ b ∧ ¬ v ≤ b)) :
    ((κ (u - v) : ℝ) : ℂ) *
      ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v = 0 := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [if_pos hu, if_pos hv]
    ring
  · rw [if_neg hu, if_neg hv]
    ring

/-! ## The oriented aperture-crossing correlation and the depth pairing -/

/-- The oriented aperture-crossing correlation of a logarithmic source. -/
def burnolCrossingCorrelation (g : ℝ → ℂ) (b s : ℝ) : ℂ :=
  ∫ v : ℝ, (starRingEnd ℂ) (g (v + s)) *
    ((if v + s ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v

/-- **The depth pairing is one translated copy of the depth-zero pairing.** -/
theorem burnolDepthPairing_translate (n : ℕ) (W : ℝ → ℂ) :
    (∫ s : ℝ, ((burnolCollarKernel n s : ℝ) : ℂ) * W s) =
      (((2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) := by
  have hshift : (∫ s : ℝ, ((burnolCollarKernel 0 (s - (n : ℝ) * Real.log 2) : ℝ) : ℂ) * W s) =
      ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) := by
    have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun s : ℝ => ((burnolCollarKernel 0 (s - (n : ℝ) * Real.log 2) : ℝ) : ℂ) * W s)
      ((n : ℝ) * Real.log 2)
    rw [← h]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with r
    congr 2
    ring
  rw [← hshift, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with s
  rw [burnolCollarKernel_eq_translate n s]
  push_cast
  ring

/-- **Fubini form of the depth pairing.**  The commutator pairing is the kernel integrated against
the oriented crossing correlation. -/
theorem burnolDepthPairing_eq_crossingCorrelation (κ : ℝ → ℝ) (g : ℝ → ℂ) (b : ℝ)
    (hslice : ∀ u : ℝ, Integrable (fun v : ℝ => ((κ (u - v) : ℝ) : ℂ) * g v))
    (hjointUV : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (g p.1) *
      (((κ (p.1 - p.2) : ℝ)) : ℂ) *
        ((if p.1 ≤ b then (1 : ℂ) else 0) - (if p.2 ≤ b then (1 : ℂ) else 0)) * g p.2))
    (hjointVS : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (g (p.1 + p.2)) *
      (((κ p.2 : ℝ)) : ℂ) *
        ((if p.1 + p.2 ≤ b then (1 : ℂ) else 0) - (if p.1 ≤ b then (1 : ℂ) else 0)) * g p.1)) :
    (∫ u : ℝ, (starRingEnd ℂ) (g u) *
        (burnolHalfLineProjection b (burnolKernelConvolution κ g) u -
          burnolKernelConvolution κ (burnolHalfLineProjection b g) u)) =
      ∫ s : ℝ, ((κ s : ℝ) : ℂ) * burnolCrossingCorrelation g b s := by
  have hcomm : ∀ u : ℝ, (starRingEnd ℂ) (g u) *
      (burnolHalfLineProjection b (burnolKernelConvolution κ g) u -
        burnolKernelConvolution κ (burnolHalfLineProjection b g) u) =
      ∫ v : ℝ, (starRingEnd ℂ) (g u) * (((κ (u - v) : ℝ)) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v := by
    intro u
    rw [burnolKernelConvolution_commutator κ g b u (hslice u), ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with v
    ring
  rw [funext hcomm, MeasureTheory.integral_integral_swap hjointUV]
  have hshear : ∀ v : ℝ,
      (∫ u : ℝ, (starRingEnd ℂ) (g u) * (((κ (u - v) : ℝ)) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v) =
      ∫ s : ℝ, (starRingEnd ℂ) (g (v + s)) * (((κ s : ℝ)) : ℂ) *
        ((if v + s ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v := by
    intro v
    have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => (starRingEnd ℂ) (g u) * (((κ (u - v) : ℝ)) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v) v
    rw [← h]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [show v + x - v = x from by ring]
  rw [funext hshear, MeasureTheory.integral_integral_swap hjointVS]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with s
  rw [burnolCrossingCorrelation, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with v
  ring

/-! ## The scale-free collar plateau criterion -/

/-- **The plateau criterion forces the exact normalized limit.**  If the crossing correlation
becomes asymptotically constant across the fixed-width profile, the normalized depth pairing
converges to `-c Γ_ℝ(1/2)/16`. -/
theorem burnolCollarPlateauLimit {W : ℝ → ℂ} {a : ℕ → ℝ} {c : ℂ}
    (hkint : Integrable (fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ)))
    (hint : ∀ n : ℕ, Integrable (fun r : ℝ =>
      ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r)))
    (hplateau : Tendsto (fun n : ℕ => ∫ r : ℝ, |burnolCollarKernel 0 r| *
      ‖(((a n)⁻¹ : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) - c‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (((a n)⁻¹ : ℝ) : ℂ) *
        ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r))
      atTop (𝓝 (-(((burnolArchimedeanHalf / 16 : ℝ)) : ℂ) * c)) := by
  have hmass : (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ)) =
      ((-(burnolArchimedeanHalf / 16) : ℝ) : ℂ) := by
    have h0 : (∫ r : ℝ, burnolCollarKernel 0 r) = -(burnolArchimedeanHalf / 16) := by
      rw [integral_burnolCollarKernel_depth 0]
      norm_num
      ring
    calc (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ))
        = ((∫ r : ℝ, burnolCollarKernel 0 r : ℝ) : ℂ) := integral_complex_ofReal
      _ = ((-(burnolArchimedeanHalf / 16) : ℝ) : ℂ) := by rw [h0]
  have hbound : ∀ n : ℕ,
      ‖(((a n)⁻¹ : ℝ) : ℂ) *
          (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r)) -
        (-(((burnolArchimedeanHalf / 16 : ℝ)) : ℂ) * c)‖ ≤
      ∫ r : ℝ, |burnolCollarKernel 0 r| *
        ‖(((a n)⁻¹ : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) - c‖ := by
    intro n
    have hsplit : (((a n)⁻¹ : ℝ) : ℂ) *
          (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r)) -
        (-(((burnolArchimedeanHalf / 16 : ℝ)) : ℂ) * c) =
        ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
          ((((a n)⁻¹ : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) - c) := by
      have hexp : ∀ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
          ((((a n)⁻¹ : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r) - c) =
          (((a n)⁻¹ : ℝ) : ℂ) *
            (((burnolCollarKernel 0 r : ℝ) : ℂ) * W ((n : ℝ) * Real.log 2 + r)) -
            ((burnolCollarKernel 0 r : ℝ) : ℂ) * c := by
        intro r
        ring
      rw [funext hexp,
        MeasureTheory.integral_sub ((hint n).const_mul _) (hkint.mul_const c),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, hmass]
      push_cast
      ring
    rw [hsplit]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    refine le_of_eq (MeasureTheory.integral_congr_ae ?_)
    filter_upwards with r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbound hplateau)

/-- **Coefficient-faithful depth lift of the crossing integrand.**  Keeping the depth summands
before addition resolves the crossing operator into its labelled depth components. -/
theorem hasSum_burnolCollarCrossing_depth (g : ℝ → ℂ) (b u v : ℝ) :
    HasSum (fun n : ℕ => ((burnolCollarKernel (n + 1) (u - v) : ℝ) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v)
      (((burnolCollarKernelTotal (u - v) : ℝ) : ℂ) *
        ((if u ≤ b then (1 : ℂ) else 0) - (if v ≤ b then (1 : ℂ) else 0)) * g v) := by
  have hreal := hasSum_burnolCollarKernelTotal (u - v)
  have hcomplex : HasSum (fun n : ℕ => ((burnolCollarKernel (n + 1) (u - v) : ℝ) : ℂ))
      ((burnolCollarKernelTotal (u - v) : ℝ) : ℂ) :=
    Complex.ofRealCLM.hasSum hreal
  exact (hcomplex.mul_right _).mul_right _

end RHTower
