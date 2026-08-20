import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The weighted Laplace carrier and its exact prime shifts

The weighted Laplace space is `L²(ℝ₊, e^{-x} dx)`.  Its evaluation vectors `k_z(x) = e^{-z̄ x}`
have the reproducing kernel

`⟨k_η, k_z⟩ = 1/(z + η̄ + 1)`,

and the weighted shift `S_h g(x) = e^h 1_{x ≥ h} g(x - h)` transports the Laplace transform by the
character `e^{-hz}` while scaling the squared norm by exactly `e^h`.  At `h = log n` this is the
critical Weil weight: `‖n^{-1} S_{log n}‖ = n^{-1/2}`.  It is not inserted by normalisation after
the fact — it is the operator norm forced by the weighted boundary.

Compactly supported vectors make the prime side of the accretivity problem exactly finite: a shift
by more than the aperture has zero pairing with the vector it started from.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

/-! ### The half-line exponential integral at complex rate -/

/-- **The half-line Laplace integral at complex rate.**  `∫_0^∞ e^{-cx} dx = 1/c` whenever
`Re c > 0`. -/
theorem integral_cexp_neg_mul_Ioi_zero {c : ℂ} (hc : 0 < c.re) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(c * (x : ℂ)))) = 1 / c := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hnegne : (-c) ≠ 0 := neg_ne_zero.mpr hcne
  set F : ℝ → ℂ := fun x => Complex.exp (-(c * (x : ℂ))) / (-c) with hF
  have hinner : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (-c) * (t : ℂ)) ((-c) * 1) x :=
      (Complex.ofRealCLM.hasDerivAt).const_mul (-c)
    have heq : (fun t : ℝ => (-c) * (t : ℂ)) = fun t : ℝ => -(c * (t : ℂ)) := by
      funext t; ring
    rw [heq] at h1
    simpa using h1
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (Complex.exp (-(c * (x : ℂ)))) x := by
    intro x _
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t : ℂ))))
        (Complex.exp (-(c * (x : ℂ))) * (-c)) x := (hinner x).cexp
    have hdiv := hexp.div_const (-c)
    rwa [mul_div_cancel_right₀ _ hnegne] at hdiv
  have hnormF : ∀ x : ℝ, ‖Complex.exp (-(c * (x : ℂ)))‖ = Real.exp (-(c.re * x)) := by
    intro x
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.neg_re, Complex.mul_re]
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (-(c * (x : ℂ)))) (Ioi 0) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hc) ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with x
      rw [hnormF x]
      simp [neg_mul]
  have hcont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    exact ((Complex.continuous_exp.comp (by fun_prop)).div_const (-c)).continuousAt
  have htend : Tendsto F atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => Real.exp (-(c.re * x))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => c.re * x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc tendsto_id
      have hne : Tendsto (fun x : ℝ => -(c.re * x)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h1
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hne
    have hnorm : Tendsto (fun x : ℝ => ‖F x‖) atTop (𝓝 0) := by
      have heq : ∀ x : ℝ, ‖F x‖ = Real.exp (-(c.re * x)) / ‖c‖ := by
        intro x
        rw [hF]
        simp only [norm_div, hnormF, norm_neg]
      simpa [heq] using hlim.div_const ‖c‖
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [h, hF]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
  field_simp
  ring

/-! ### The weighted Laplace pairing and its evaluation vectors -/

/-- The weighted Laplace pairing on the half line. -/
def weightedInner (g h : ℝ → ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), g x * (starRingEnd ℂ) (h x) * (Real.exp (-x) : ℂ)

/-- The evaluation vector of the weighted Laplace space at `z`. -/
def laplaceEval (z : ℂ) : ℝ → ℂ := fun x => Complex.exp (-((starRingEnd ℂ) z) * (x : ℂ))

/-- **The weighted Laplace reproducing kernel.**  `⟨k_η, k_z⟩ = 1/(z + η̄ + 1)`. -/
theorem weightedInner_laplaceEval {z η : ℂ} (hz : 0 < z.re) (hη : 0 < η.re) :
    weightedInner (laplaceEval η) (laplaceEval z) = 1 / (z + (starRingEnd ℂ) η + 1) := by
  have hterm : ∀ x : ℝ,
      laplaceEval η x * (starRingEnd ℂ) (laplaceEval z x) * (Real.exp (-x) : ℂ)
        = Complex.exp (-((z + (starRingEnd ℂ) η + 1) * (x : ℂ))) := by
    intro x
    have hconj : (starRingEnd ℂ) (laplaceEval z x) = Complex.exp (-z * (x : ℂ)) := by
      rw [laplaceEval, ← Complex.exp_conj]
      congr 1
      simp [map_mul, Complex.conj_ofReal]
    have hweight : ((Real.exp (-x) : ℝ) : ℂ) = Complex.exp (-(x : ℂ)) := by
      rw [Complex.ofReal_exp, Complex.ofReal_neg]
    rw [laplaceEval, hconj, hweight, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hre : 0 < (z + (starRingEnd ℂ) η + 1).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.conj_re]
    linarith
  rw [weightedInner, setIntegral_congr_fun measurableSet_Ioi fun x _ => hterm x,
    integral_cexp_neg_mul_Ioi_zero hre]

/-! ### The weighted shift -/

/-- The weighted shift by `h` on the half line. -/
def weightedLaplaceShift (h : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if h ≤ x then (Real.exp h : ℂ) * g (x - h) else 0

theorem weightedLaplaceShift_of_lt {h x : ℝ} (hx : x < h) (g : ℝ → ℂ) :
    weightedLaplaceShift h g x = 0 := by
  rw [weightedLaplaceShift, if_neg (not_le.mpr hx)]

theorem weightedLaplaceShift_of_le {h x : ℝ} (hx : h ≤ x) (g : ℝ → ℂ) :
    weightedLaplaceShift h g x = (Real.exp h : ℂ) * g (x - h) := by
  rw [weightedLaplaceShift, if_pos hx]

/-- Translation of a half-line integral. -/
theorem setIntegral_Ioi_comp_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a h : ℝ) :
    (∫ y in Ioi (a - h), F (y + h)) = ∫ x in Ioi a, F x := by
  have hmp : MeasurePreserving (fun y : ℝ => y + h) volume volume :=
    measurePreserving_add_right volume h
  have hemb : MeasurableEmbedding (fun y : ℝ => y + h) := measurableEmbedding_addRight h
  have hpre : (fun y : ℝ => y + h) ⁻¹' (Ioi a) = Ioi (a - h) := by
    ext y
    simp [Set.mem_Ioi, sub_lt_iff_lt_add]
  have h1 := hmp.setIntegral_preimage_emb hemb F (Ioi a)
  rw [hpre] at h1
  exact h1

/-- **The exact critical norm scaling.**  On its support the weighted shift multiplies the weighted
squared norm by exactly `e^h`.  The critical weight is the operator norm forced by the weighted
boundary, not a normalisation inserted after the fact. -/
theorem integral_normSq_weightedLaplaceShift (h : ℝ) (g : ℝ → ℂ) :
    (∫ x in Ioi h, ‖weightedLaplaceShift h g x‖ ^ 2 * Real.exp (-x))
      = Real.exp h * ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2 * Real.exp (-x) := by
  have htrans := setIntegral_Ioi_comp_add_right
    (fun x : ℝ => ‖weightedLaplaceShift h g x‖ ^ 2 * Real.exp (-x)) h h
  rw [sub_self] at htrans
  rw [← htrans, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hle : h ≤ y + h := by
    have : (0 : ℝ) < y := hy
    linarith
  rw [weightedLaplaceShift_of_le hle, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos h).le]
  have hexp : Real.exp (-(y + h)) = Real.exp (-y) * Real.exp (-h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcancel : Real.exp h * Real.exp h * Real.exp (-h) = Real.exp h := by
    rw [mul_assoc, ← Real.exp_add]
    norm_num
  rw [add_sub_cancel_right, hexp, mul_pow]
  calc Real.exp h ^ 2 * ‖g y‖ ^ 2 * (Real.exp (-y) * Real.exp (-h))
      = (Real.exp h * Real.exp h * Real.exp (-h)) * (‖g y‖ ^ 2 * Real.exp (-y)) := by ring
    _ = Real.exp h * (‖g y‖ ^ 2 * Real.exp (-y)) := by rw [hcancel]

/-- **The critical prime weight.**  `‖n^{-1} S_{log n} g‖² = n^{-1} ‖g‖²`, so the operator norm of
the `n`-th Euler monomial is exactly `n^{-1/2}`. -/
theorem integral_normSq_primeWeightedShift {n : ℕ} (hn : 1 ≤ n) (g : ℝ → ℂ) :
    (∫ x in Ioi (Real.log n),
        ‖((((n : ℝ)⁻¹ : ℝ) : ℂ)) * weightedLaplaceShift (Real.log n) g x‖ ^ 2 * Real.exp (-x))
      = ((n : ℝ))⁻¹ * ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2 * Real.exp (-x) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.exp (Real.log n) = (n : ℝ) := Real.exp_log hn0
  have hpull : (∫ x in Ioi (Real.log n),
        ‖((((n : ℝ)⁻¹ : ℝ) : ℂ)) * weightedLaplaceShift (Real.log n) g x‖ ^ 2 * Real.exp (-x))
      = ((n : ℝ))⁻¹ ^ 2 * ∫ x in Ioi (Real.log n),
        ‖weightedLaplaceShift (Real.log n) g x‖ ^ 2 * Real.exp (-x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
    ring
  rw [hpull, integral_normSq_weightedLaplaceShift, hlog, ← mul_assoc]
  congr 1
  field_simp

/-- **The exact aperture cutoff.**  A shift by more than the aperture has zero pairing with a
vector supported in the aperture: the prime side of the accretivity problem is exactly finite. -/
theorem weightedInner_weightedLaplaceShift_eq_zero {h A : ℝ} (hA : A < h) {g : ℝ → ℂ}
    (hsupp : ∀ x, A < x → g x = 0) :
    weightedInner (weightedLaplaceShift h g) g = 0 := by
  rw [weightedInner]
  have hzero : ∀ x ∈ Ioi (0 : ℝ),
      weightedLaplaceShift h g x * (starRingEnd ℂ) (g x) * (Real.exp (-x) : ℂ) = 0 := by
    intro x _
    by_cases hx : A < x
    · rw [hsupp x hx]
      simp
    · have hxh : x < h := lt_of_le_of_lt (not_lt.mp hx) hA
      rw [weightedLaplaceShift_of_lt hxh]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hzero]
  simp

/-! ### The Laplace transform of a shift -/

/-- The weighted Laplace transform on the half line. -/
def weightedLaplace (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), g x * Complex.exp (-(z * (x : ℂ))) * (Real.exp (-x) : ℂ)

/-- **The shift transports the Laplace transform by the character `e^{-hz}`.** -/
theorem weightedLaplace_weightedLaplaceShift (h : ℝ) (g : ℝ → ℂ) (z : ℂ) :
    (∫ x in Ioi h,
        weightedLaplaceShift h g x * Complex.exp (-(z * (x : ℂ))) * (Real.exp (-x) : ℂ))
      = Complex.exp (-(z * (h : ℂ))) * weightedLaplace g z := by
  have htrans := setIntegral_Ioi_comp_add_right
    (fun x : ℝ => weightedLaplaceShift h g x * Complex.exp (-(z * (x : ℂ)))
      * (Real.exp (-x) : ℂ)) h h
  rw [sub_self] at htrans
  rw [← htrans, weightedLaplace, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hle : h ≤ y + h := by
    have : (0 : ℝ) < y := hy
    linarith
  have hw : ((Real.exp (-(y + h)) : ℝ) : ℂ)
      = ((Real.exp (-y) : ℝ) : ℂ) * ((Real.exp (-h) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hcexp : Complex.exp (-(z * ((y + h : ℝ) : ℂ)))
      = Complex.exp (-(z * (y : ℂ))) * Complex.exp (-(z * (h : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexph : ((Real.exp h : ℝ) : ℂ) * ((Real.exp (-h) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [weightedLaplaceShift_of_le hle, add_sub_cancel_right, hw, hcexp]
  calc ((Real.exp h : ℝ) : ℂ) * g y * (Complex.exp (-(z * (y : ℂ)))
        * Complex.exp (-(z * (h : ℂ)))) * (((Real.exp (-y) : ℝ) : ℂ) * ((Real.exp (-h) : ℝ) : ℂ))
      = (((Real.exp h : ℝ) : ℂ) * ((Real.exp (-h) : ℝ) : ℂ)) * (Complex.exp (-(z * (h : ℂ)))
          * (g y * Complex.exp (-(z * (y : ℂ))) * ((Real.exp (-y) : ℝ) : ℂ))) := by ring
    _ = Complex.exp (-(z * (h : ℂ)))
          * (g y * Complex.exp (-(z * (y : ℂ))) * ((Real.exp (-y) : ℝ) : ℂ)) := by
        rw [hexph, one_mul]

/-! ### The accretivity kernel -/

/-- The accretivity kernel of a source multiplier on the weighted Laplace space. -/
def accretivityKernel (F : ℂ → ℂ) (z η : ℂ) : ℂ :=
  (F z + (starRingEnd ℂ) (F η)) / (z + (starRingEnd ℂ) η + 1)

/-- **The accretivity kernel is the Hermitian part of the multiplier Gram.** -/
theorem accretivityKernel_eq_add (F : ℂ → ℂ) (z η : ℂ) :
    accretivityKernel F z η
      = F z * (1 / (z + (starRingEnd ℂ) η + 1))
        + (starRingEnd ℂ) (F η * (1 / (η + (starRingEnd ℂ) z + 1))) := by
  rw [accretivityKernel, map_mul, map_div₀, map_one, map_add, map_add, map_one,
    Complex.conj_conj]
  ring

/-- The accretivity kernel is Hermitian. -/
theorem accretivityKernel_conj (F : ℂ → ℂ) (z η : ℂ) :
    (starRingEnd ℂ) (accretivityKernel F z η) = accretivityKernel F η z := by
  rw [accretivityKernel, accretivityKernel, map_div₀, map_add, map_add, map_add, map_one,
    Complex.conj_conj, Complex.conj_conj]
  congr 1
  · ring
  · ring

/-- **The critical coordinate change.**  Under `w = z + 1/2` the accretivity kernel of the shifted
multiplier is exactly the critical logarithmic-derivative kernel. -/
theorem accretivityKernel_shift (L : ℂ → ℂ) (z η : ℂ) :
    accretivityKernel (fun w => L (w + 1 / 2)) z η
      = (L (z + 1 / 2) + (starRingEnd ℂ) (L (η + 1 / 2)))
          / ((z + 1 / 2) + (starRingEnd ℂ) (η + 1 / 2)) := by
  rw [accretivityKernel]
  congr 1
  rw [map_add]
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [h2]
  ring

end GaloisForLFunctions.RHTower
