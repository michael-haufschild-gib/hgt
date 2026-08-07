import GaloisForLFunctions.RHTower.HedenmalmThetaIntervalTransform
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The two-prime normal frame of the Xi divisor

The centered prime windows transform to `ĉ_n = a_n Ξ_C`.  Because `a_2` and `a_3` have no common
zero, the pair of prime windows retains every zero of `Ξ_C` together with its exact analytic
order: at a zero `ζ` at least one multiplier is nonzero there, and multiplying by a unit does not
move the analytic order.

In the compact reciprocal coordinate `μ = -1/ζ` of the Grushin inverse the normal multiplier
becomes `A_n(μ) = 2 n^{-1/2} μ sin(L_n/(2μ))`, which has an essential singularity at the compact
spectral boundary `μ = 0` yet reproduces `a_n(ζ)` on every root block.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

/-! ### The centered multiplier in closed trigonometric form -/

theorem centeredMultiplier_eq_sin (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplier n z
      = 2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
        * Complex.sin (z * ((Real.log n / 2 : ℝ) : ℂ)) / z := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set w : ℂ := z * ((Real.log n / 2 : ℝ) : ℂ) with hw
  have e1 : Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ) = w * Complex.I := by
    rw [hw]; ring
  have hsin : Complex.exp (w * Complex.I) - Complex.exp (-(w * Complex.I))
      = 2 * Complex.I * Complex.sin w := by
    rw [Complex.sin, show -(w * Complex.I) = -w * Complex.I by ring]
    linear_combination (Complex.exp (w * Complex.I) - Complex.exp (-w * Complex.I)) * hI2
  rw [centeredMultiplier, e1, hsin]
  field_simp

/-! ### Analyticity away from the origin -/

theorem analyticAt_centeredMultiplier (n : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    AnalyticAt ℂ (centeredMultiplier n) ζ := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ)) ζ :=
    (analyticAt_const.mul analyticAt_id).mul analyticAt_const
  have hnum : AnalyticAt ℂ (fun z : ℂ => ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
      * (Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))))) ζ :=
    analyticAt_const.mul (hlin.cexp.sub hlin.neg.cexp)
  have hden : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) ζ :=
    analyticAt_const.mul analyticAt_id
  have hne : (fun z : ℂ => Complex.I * z) ζ ≠ 0 := mul_ne_zero Complex.I_ne_zero hζ
  exact hnum.div hden hne

/-! ### The prime windows retain the exact analytic order -/

/-- The normal jet of the centered prime window: the transform side of `ĉ_n = a_n Ξ_C`. -/
def centeredWindowTransform (n : ℕ) (z : ℂ) : ℂ := centeredMultiplier n z * XiC z

/-- **A prime window with a nonvanishing multiplier retains the exact analytic order of `Ξ_C`.**
This is the multiplicity clause `(15)`--`(16)`: all jets below the order vanish, and the first
nonzero jet is `a_n(ζ) Ξ_C^{(m)}(ζ)`. -/
theorem analyticOrderAt_centeredWindowTransform {n : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hne : centeredMultiplier n ζ ≠ 0) :
    analyticOrderAt (centeredWindowTransform n) ζ = analyticOrderAt XiC ζ := by
  have ha : AnalyticAt ℂ (centeredMultiplier n) ζ := analyticAt_centeredMultiplier n hζ
  have hX : AnalyticAt ℂ XiC ζ := XiC_analytic ζ (Set.mem_univ _)
  have hmul : analyticOrderAt (centeredMultiplier n * XiC) ζ
      = analyticOrderAt (centeredMultiplier n) ζ + analyticOrderAt XiC ζ :=
    analyticOrderAt_mul ha hX
  have hzero : analyticOrderAt (centeredMultiplier n) ζ = 0 :=
    (AnalyticAt.analyticOrderAt_eq_zero ha).mpr hne
  have hfun : centeredWindowTransform n = centeredMultiplier n * XiC := rfl
  rw [hfun, hmul, hzero, zero_add]

/-- **Two literal primes frame every normal direction.**  At every point other than the origin at
least one of the two prime windows has a nonvanishing multiplier, hence retains the exact analytic
order of `Ξ_C` there. -/
theorem two_prime_retains_analyticOrder {ζ : ℂ} (hζ : ζ ≠ 0) :
    analyticOrderAt (centeredWindowTransform 2) ζ = analyticOrderAt XiC ζ
      ∨ analyticOrderAt (centeredWindowTransform 3) ζ = analyticOrderAt XiC ζ := by
  by_cases h2 : centeredMultiplier 2 ζ = 0
  · refine Or.inr (analyticOrderAt_centeredWindowTransform hζ ?_)
    intro h3
    exact hζ (no_common_zero_centered_two_three h2 h3)
  · exact Or.inl (analyticOrderAt_centeredWindowTransform hζ h2)

/-- **The normal frame is nowhere zero on the divisor.**  Every zero of `Ξ_C` is a zero of the same
exact order of at least one prime window transform. -/
theorem two_prime_retains_divisor {ζ : ℂ} (hζ : XiC ζ = 0) :
    ζ ≠ 0 ∧ (analyticOrderAt (centeredWindowTransform 2) ζ = analyticOrderAt XiC ζ
      ∨ analyticOrderAt (centeredWindowTransform 3) ζ = analyticOrderAt XiC ζ) := by
  have hz : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    exact XiC_zero_ne hζ
  exact ⟨hz, two_prime_retains_analyticOrder hz⟩

/-! ### The compact reciprocal coordinate -/

/-- The normal multiplier in the compact reciprocal coordinate `μ = -1/ζ` of the Grushin
inverse. -/
def compactNormalMultiplier (n : ℕ) (μ : ℂ) : ℂ := centeredMultiplier n (-μ⁻¹)

/-- **The compact normal multiplier in closed form**, `A_n(μ) = 2 n^{-1/2} μ sin(L_n/(2μ))`.
The sine of a reciprocal argument exhibits the essential singularity at the compact spectral
boundary `μ = 0`. -/
theorem compactNormalMultiplier_eq (n : ℕ) {μ : ℂ} (hμ : μ ≠ 0) :
    compactNormalMultiplier n μ
      = 2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * μ
        * Complex.sin (μ⁻¹ * ((Real.log n / 2 : ℝ) : ℂ)) := by
  have hne : (-μ⁻¹ : ℂ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hμ)
  rw [compactNormalMultiplier, centeredMultiplier_eq_sin n hne,
    show (-μ⁻¹ : ℂ) * ((Real.log n / 2 : ℝ) : ℂ)
      = -(μ⁻¹ * ((Real.log n / 2 : ℝ) : ℂ)) by ring, Complex.sin_neg]
  field_simp

/-- **The compact multiplier reproduces the normal multiplier on every root block.** -/
theorem compactNormalMultiplier_root (n : ℕ) (ζ : ℂ) :
    compactNormalMultiplier n (-ζ⁻¹) = centeredMultiplier n ζ := by
  rw [compactNormalMultiplier]
  congr 1
  rw [inv_neg, inv_inv, neg_neg]


/-! ### The first-order normalized frame symbol -/

/-- The frame symbol `b_n(t) = t a_n(t) = 2 n^{-1/2} sin(t log n / 2)`. -/
def frameSymbol (n : ℕ) (t : ℝ) : ℝ :=
  2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sin (t * Real.log n / 2)

/-- **The first-order normalization of the multiplier.**  Removing the common first-order decay
leaves a bounded pure sine. -/
theorem mul_centeredMultiplier_eq_frameSymbol (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) * centeredMultiplier n (t : ℂ) = ((frameSymbol n t : ℝ) : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [centeredMultiplier_eq_sin n htc, frameSymbol]
  have hsin : Complex.sin ((t : ℂ) * ((Real.log n / 2 : ℝ) : ℂ))
      = ((Real.sin (t * Real.log n / 2) : ℝ) : ℂ) := by
    rw [show (t : ℂ) * ((Real.log n / 2 : ℝ) : ℂ) = ((t * Real.log n / 2 : ℝ) : ℂ) by
      push_cast; ring]
    rw [← Complex.ofReal_sin]
  rw [hsin]
  field_simp
  push_cast
  ring

theorem abs_frameSymbol_le (n : ℕ) (t : ℝ) :
    |frameSymbol n t| ≤ 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [frameSymbol, abs_mul]
  have h1 : |2 * ((n : ℝ) ^ (-(1 / 2 : ℝ)))| = 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [abs_of_nonneg (by positivity)]
  rw [h1]
  nlinarith [Real.abs_sin_le_one (t * Real.log n / 2), abs_nonneg (Real.sin (t * Real.log n / 2))]

/-- **The multiplier decays like `1/|t|` on the real axis.**  This is the first frame
obstruction: the analytic frame has no uniform lower bound as a bounded Fourier multiplier. -/
theorem norm_centeredMultiplier_le (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖centeredMultiplier n (t : ℂ)‖ ≤ 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) / |t| := by
  have habs : ‖(t : ℂ)‖ = |t| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < |t| := abs_pos.mpr ht
  have h := mul_centeredMultiplier_eq_frameSymbol n ht
  have hnorm : |t| * ‖centeredMultiplier n (t : ℂ)‖ = |frameSymbol n t| := by
    rw [← habs, ← norm_mul, h, Complex.norm_real, Real.norm_eq_abs]
  rw [le_div_iff₀ hpos, mul_comm]
  rw [hnorm]
  exact abs_frameSymbol_le n t

/-- **The two-prime frame symbol pair tends to zero.**  Both multipliers vanish at infinity on the
real axis, so no Bezout pair for them is bounded there. -/
theorem tendsto_norm_centeredMultiplier_atTop (n : ℕ) :
    Tendsto (fun t : ℝ => ‖centeredMultiplier n (t : ℂ)‖) atTop (𝓝 0) := by
  have hdom : Tendsto (fun t : ℝ => 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) / |t|) atTop (𝓝 0) := by
    have habs : Tendsto (fun t : ℝ => |t|) atTop atTop := tendsto_abs_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds habs
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hdom
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact norm_centeredMultiplier_le n (ne_of_gt ht)



/-! ### The zero set of the centered multiplier

Plan input for the conormal generation clause: the zeros of `a_n` form an arithmetic progression
whose reciprocal squares are summable, which is exactly the hypothesis of the corpus genus-one
canonical product. -/

/-- The `k`-th zero of the centered multiplier `a_n`, `w_k = 2 pi k / log n`. -/
def centeredMultiplierZero (n : ℕ) (k : ℤ) : ℂ :=
  (((2 * Real.pi * (k : ℝ) / Real.log n : ℝ)) : ℂ)

theorem centeredMultiplierZero_ne_zero {n : ℕ} (hn : 2 ≤ n) {k : ℤ} (hk : k ≠ 0) :
    centeredMultiplierZero n k ≠ 0 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [centeredMultiplierZero]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  have : (2 : ℝ) * Real.pi * (k : ℝ) ≠ 0 := by
    have := Real.pi_ne_zero
    positivity
  exact div_ne_zero this hlog.ne'

theorem norm_centeredMultiplierZero {n : ℕ} (k : ℤ) :
    ‖centeredMultiplierZero n k‖ = |2 * Real.pi * (k : ℝ) / Real.log n| := by
  rw [centeredMultiplierZero, Complex.norm_real, Real.norm_eq_abs]

/-- **The reciprocal squares of the zeros are summable.**  This is the exact hypothesis of
`RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn`. -/
theorem summable_inv_sq_centeredMultiplierZero {n : ℕ} (hn : 2 ≤ n) :
    Summable (fun k : ℤ => 1 / ‖centeredMultiplierZero n k‖ ^ 2) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hbase : Summable (fun k : ℤ => 1 / ((k : ℝ)) ^ (2 : ℕ)) :=
    (Real.summable_one_div_int_pow).mpr (by norm_num)
  have hc : (0 : ℝ) < (Real.log n / (2 * Real.pi)) ^ 2 := by
    have := Real.pi_pos
    positivity
  refine (hbase.mul_left ((Real.log n / (2 * Real.pi)) ^ 2)).congr fun k => ?_
  rw [norm_centeredMultiplierZero]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hpi := Real.pi_ne_zero
    rw [sq_abs]
    field_simp



/-- The zeros of `a_n` indexed by the nonzero integers. -/
def centeredZero (n : ℕ) (k : {j : ℤ // j ≠ 0}) : ℂ := centeredMultiplierZero n (k : ℤ)

theorem centeredZero_ne_zero {n : ℕ} (hn : 2 ≤ n) (k : {j : ℤ // j ≠ 0}) :
    centeredZero n k ≠ 0 :=
  centeredMultiplierZero_ne_zero hn k.2

theorem summable_inv_sq_centeredZero {n : ℕ} (hn : 2 ≤ n) :
    Summable (fun k : {j : ℤ // j ≠ 0} => 1 / ‖centeredZero n k‖ ^ 2) :=
  (summable_inv_sq_centeredMultiplierZero hn).subtype _

/-- **The canonical product over the zeros of the centered prime multiplier.**  The genus-one
Weierstrass product of the corpus, formed at the arithmetic progression `2 pi k / log n`. -/
def centeredCanonicalProduct (n : ℕ) : ℂ → ℂ :=
  canonicalProductE1Indexed (centeredZero n)

theorem hasProdLocallyUniformlyOn_centeredCanonicalProduct {n : ℕ} (hn : 2 ≤ n) :
    HasProdLocallyUniformlyOn (fun k z => weierstrassE1 (z / centeredZero n k))
      (centeredCanonicalProduct n) Set.univ :=
  canonicalProductE1Indexed_hasProdLocallyUniformlyOn (centeredZero n)
    (centeredZero_ne_zero hn) (summable_inv_sq_centeredZero hn)



theorem analyticOnNhd_centeredCanonicalProduct {n : ℕ} (hn : 2 ≤ n) :
    AnalyticOnNhd ℂ (centeredCanonicalProduct n) Set.univ :=
  canonicalProductE1Indexed_analytic (centeredZero n) (centeredZero_ne_zero hn)
    (summable_inv_sq_centeredZero hn)

/-- **The canonical product vanishes only on the prescribed zero set.** -/
theorem centeredCanonicalProduct_ne_zero {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : ∀ k : {j : ℤ // j ≠ 0}, z ≠ centeredZero n k) :
    centeredCanonicalProduct n z ≠ 0 :=
  canonicalProductE1Indexed_ne_zero (centeredZero n) (centeredZero_ne_zero hn)
    (summable_inv_sq_centeredZero hn) hz



/-- **The zero set of the centered multiplier, off the origin, is exactly the prescribed
arithmetic progression.**  This matches the divisor of `a_n` with that of the canonical product. -/
theorem centeredMultiplier_eq_zero_iff_mem_zeros {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplier n z = 0 ↔ ∃ k : {j : ℤ // j ≠ 0}, z = centeredZero n k := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hlogC : ((Real.log n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have hcast : ∀ m : ℤ, ((2 * Real.pi * (m : ℝ) / Real.log n : ℝ) : ℂ)
      = (2 * ((Real.pi : ℝ) : ℂ) * ((m : ℤ) : ℂ)) / ((Real.log n : ℝ) : ℂ) := by
    intro m
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]
    norm_num
  rw [centeredMultiplier_eq_zero_iff hz, shiftMultiplier_eq_zero_iff hn hz]
  constructor
  · rintro ⟨j, hj⟩
    have hjne : j ≠ 0 := by
      intro h
      rw [h] at hj
      simp only [Int.cast_zero, mul_zero] at hj
      exact hz ((mul_eq_zero.mp hj).resolve_right hlogC)
    refine ⟨⟨j, hjne⟩, ?_⟩
    rw [centeredZero, centeredMultiplierZero, hcast, eq_div_iff hlogC]
    exact hj
  · rintro ⟨k, rfl⟩
    refine ⟨(k : ℤ), ?_⟩
    rw [centeredZero, centeredMultiplierZero, hcast, div_mul_cancel₀ _ hlogC]


/-- The derivative of the centered multiplier off the origin. -/
theorem hasDerivAt_centeredMultiplier (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (centeredMultiplier n)
      ((2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
          * (Complex.cos (w * ((Real.log n / 2 : ℝ) : ℂ)) * ((Real.log n / 2 : ℝ) : ℂ)) * w
        - 2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
          * Complex.sin (w * ((Real.log n / 2 : ℝ) : ℂ)) * 1) / w ^ 2) w := by
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin (z * ((Real.log n / 2 : ℝ) : ℂ)))
      (Complex.cos (w * ((Real.log n / 2 : ℝ) : ℂ)) * ((Real.log n / 2 : ℝ) : ℂ)) w :=
    by
      have h := ((hasDerivAt_id w).mul_const ((Real.log n / 2 : ℝ) : ℂ)).csin
      simpa using h
  have hnum := hsin.const_mul (2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))
  have hquot := hnum.div (hasDerivAt_id w) hw
  refine hquot.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact centeredMultiplier_eq_sin n hz



/-- At the `k`-th zero the phase is an integer multiple of `pi`. -/
theorem centeredZero_mul_halfLog {n : ℕ} (hn : 2 ≤ n) (k : {j : ℤ // j ≠ 0}) :
    centeredZero n k * ((Real.log n / 2 : ℝ) : ℂ) = (((Real.pi * ((k : ℤ) : ℝ)) : ℝ) : ℂ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  rw [centeredZero, centeredMultiplierZero, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-- **The derivative of the centered multiplier at one of its zeros is nonzero.**  At `w_k` the
phase is `pi k`, so the sine vanishes while the cosine is `(-1)^k`, and the quotient rule leaves
`2 c l cos(pi k) / w_k`. -/
theorem deriv_centeredMultiplier_ne_zero {n : ℕ} (hn : 2 ≤ n) (k : {j : ℤ // j ≠ 0}) :
    deriv (centeredMultiplier n) (centeredZero n k) ≠ 0 := by
  have hw : centeredZero n k ≠ 0 := centeredZero_ne_zero hn k
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hprod := centeredZero_mul_halfLog hn k
  have hsin : Complex.sin (centeredZero n k * ((Real.log n / 2 : ℝ) : ℂ)) = 0 := by
    rw [hprod, ← Complex.ofReal_sin]
    have hr : Real.sin (Real.pi * ((k : ℤ) : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_int_mul_pi _
    rw [hr, Complex.ofReal_zero]
  have hcosne : Complex.cos (centeredZero n k * ((Real.log n / 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [hprod, ← Complex.ofReal_cos]
    have hr : Real.cos (Real.pi * ((k : ℤ) : ℝ)) = (-1 : ℝ) ^ (k : ℤ) := by
      rw [mul_comm]; exact Real.cos_int_mul_pi _
    rw [hr]
    exact Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ (by norm_num))
  have hd := hasDerivAt_centeredMultiplier n hw
  rw [hd.deriv, hsin]
  have hc : ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hnR _).ne'
  have hl : ((Real.log n / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hlog two_pos).ne'
  simp only [mul_zero, zero_mul, sub_zero]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) (mul_ne_zero hcosne hl)) hw)
    (pow_ne_zero _ hw)

/-- **The zeros of the centered multiplier are simple.** -/
theorem analyticOrderAt_centeredMultiplier_eq_one {n : ℕ} (hn : 2 ≤ n)
    (k : {j : ℤ // j ≠ 0}) :
    analyticOrderAt (centeredMultiplier n) (centeredZero n k) = 1 :=
  (analyticAt_centeredMultiplier n (centeredZero_ne_zero hn k)
      ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    ((centeredMultiplier_eq_zero_iff_mem_zeros hn (centeredZero_ne_zero hn k)).mpr ⟨k, rfl⟩)
    (deriv_centeredMultiplier_ne_zero hn k)


end HedenmalmThetaSource

end

end RHTower

/-! ### The essential-singular pair on a root block -/

/-- **The essential-singular pair is nonzero on every root block.**  At a zero of `Xi_C` the two
compact normal multipliers, evaluated at the compact spectral parameter `mu = -1/zeta`, do not both
annihilate a nonzero mode.  This is clause `(21)`. -/
theorem essential_pair_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E] [NoZeroSMulDivisors ℂ E]
    {ζ : ℂ} (hζ : XiC ζ = 0) {f : E} (hf : f ≠ 0) :
    (compactNormalMultiplier 2 (-ζ⁻¹) • f, compactNormalMultiplier 3 (-ζ⁻¹) • f)
      ≠ ((0 : E), (0 : E)) := by
  have hz : ζ ≠ 0 := fun h => XiC_zero_ne (h ▸ hζ)
  rw [compactNormalMultiplier_root, compactNormalMultiplier_root]
  intro hpair
  have h2 : centeredMultiplier 2 ζ • f = 0 := congrArg Prod.fst hpair
  have h3 : centeredMultiplier 3 ζ • f = 0 := congrArg Prod.snd hpair
  rcases smul_eq_zero.mp h2 with hc2 | hf0
  · rcases smul_eq_zero.mp h3 with hc3 | hf0
    · exact hz (no_common_zero_centered_two_three hc2 hc3)
    · exact hf hf0
  · exact hf hf0

end HedenmalmThetaSource

end

end RHTower
