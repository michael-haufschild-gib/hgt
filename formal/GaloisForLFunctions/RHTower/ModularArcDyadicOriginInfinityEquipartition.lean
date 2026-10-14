import GaloisForLFunctions.RHTower.ModularArcDyadicCriticalLineStrictConvexity

/-!
# Origin–infinity (`(0, 1]` vs `(1, ∞)`) equipartition of the infinite-horizon dyadic Hilbert energy and oscillatory Mellin transform, the `2 sinh(2lv)` energy imbalance law, and strict critical-line balance characterization

In `ModularArcDyadicStripWeightedHilbertMinimum` and `ModularArcDyadicCriticalLineStrictConvexity`,
we proved that the full strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx` of `V_k = arcLineInfiniteDyadicVector k ν` is strictly
midpoint-convex on `(−1/2, 1/2)` and achieves its unique global minimum on the critical line `l = 0`.

In this module we decompose the positive half-line `(0, ∞)` at the self-dual multiplicative pivot
`x = 1` (`v = log x = 0`) into the **origin sector** `(0, 1]` (`Ioc 0 1`) and the **infinity sector**
`(1, ∞)` (`Ioi 1`), and establish the **origin–infinity reflection duality**, **exact `1/2 - 1/2`
critical-line equipartition**, the **`2 sinh(2lv)` energy imbalance law**, and the **strict
critical-line balance characterization** `E_k^{(0, 1]}(l) = E_k^{(1, ∞)}(l) ↔ l = 0`:

1. **Half-line exponential changes of variables (`image_exp_Ioi_zero_eq_Ioi_one`,
   `image_exp_neg_Ici_zero_eq_Ioc_zero_one`,
   `setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul`,
   `setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul`,
   `integrableOn_Ioi_iff_integrable_exp_mul`,
   `setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one`):**
   Under `x = exp v` and `x = exp(−v)`:
   - `∫_{x ∈ (1, ∞)} g(x) dx = ∫_{v ∈ (0, ∞)} e^v g(e^v) dv`,
   - `∫_{x ∈ (0, 1]} g(x) dx = ∫_{v ∈ (0, ∞)} e^{−v} g(e^{−v}) dv`,
   - and for any `g` integrable on `(0, ∞)`,
     `∫_{x ∈ (0, 1]} g(x) dx + ∫_{x ∈ (1, ∞)} g(x) dx = ∫_{x ∈ (0, ∞)} g(x) dx`.
2. **Origin–infinity reflection duality and critical-line equipartition of the oscillatory Mellin
   transform (`setIntegral_Ioi_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioc_zero_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg`,
   `setIntegral_Ioi_one_cos_log_eq_half_cosTransform`,
   `setIntegral_Ioc_zero_one_cos_log_eq_half_cosTransform`):**
   - For all `l, τ ∈ ℝ`,
     `∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{x ∈ (1, ∞)} x^{−l − 1/2} cos(τ log x) V_k(x) dx`.
   - On the critical line `l = 0`, for every `τ ∈ ℝ`, both the `(0, 1]` and `(1, ∞)` oscillatory
     Mellin integrals equal `(1/2) · arcLineInfiniteDyadicCosTransform k ν τ > 0`.
3. **Origin–infinity reflection duality, `1/2 - 1/2` critical-line equipartition, and the
   `2 sinh(2lv)` imbalance law for the strip-weighted Hilbert energy
   (`setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg`,
   `setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq`,
   `setIntegral_Ioi_one_sq_eq_half_setIntegral_Ioi_sq`,
   `setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq`,
   `setIntegral_Ioc_zero_one_lt_setIntegral_Ioi_one_rpow_two_mul_sq_of_pos`,
   `setIntegral_Ioi_one_lt_setIntegral_Ioc_zero_one_rpow_two_mul_sq_of_neg`,
   `setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_iff`,
   `exists_dyadic_originInfinity_equipartition_arcWitness`):**
   - For all `l ∈ ℝ`,
     `∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{−2l} (V_k(x))² dx`.
   - At `l = 0`,
     `∫_{x ∈ (0, 1]} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} (V_k(x))² dx = (1/2) ∫_{x > 0} (V_k(x))² dx > 0`.
   - Across `|l| < 1/2`, the origin–infinity energy imbalance obeys the exact hyperbolic sine law
     `∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx − ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{v ∈ (0, ∞)} 2 sinh(2lv) (Φ_k(v))² dv`.
   - Strictly `E_k^{(0, 1]}(l) < E_k^{(1, ∞)}(l)` for `0 < l < 1/2`, strictly
     `E_k^{(1, ∞)}(l) < E_k^{(0, 1]}(l)` for `−1/2 < l < 0`, and therefore across `|l| < 1/2`,
     `∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx ↔ l = 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Half-line exponential changes of variables on `Ioi 1`, `Ioc 0 1`, and `Ioi 0` -/

/-- The exponential map `v ↦ exp v` carries `(0, ∞)` onto `(1, ∞)`. -/
theorem image_exp_Ioi_zero_eq_Ioi_one :
    Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext y
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Real.one_lt_exp_iff.mpr hx
  · intro hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    exact ⟨Real.log y, Real.log_pos hy, Real.exp_log hy0⟩

/-- The reflected exponential map `v ↦ exp(−v)` carries `[0, ∞)` onto `(0, 1]`. -/
theorem image_exp_neg_Ici_zero_eq_Ioc_zero_one :
    (fun x : ℝ => Real.exp (-x)) '' Ici (0 : ℝ) = Ioc (0 : ℝ) 1 := by
  ext y
  simp only [mem_image, mem_Ici, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.exp_pos (-x), Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)⟩
  · rintro ⟨hy0, hy1⟩
    refine ⟨-Real.log y, neg_nonneg.mpr (Real.log_nonpos hy0.le hy1), ?_⟩
    rw [neg_neg, Real.exp_log hy0]

/-- **Change of variables `x = exp v` on the infinity sector `(1, ∞)`:**
`∫_{x ∈ (1, ∞)} g(x) dx = ∫_{v ∈ (0, ∞)} e^v g(e^v) dv`. -/
theorem setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul (g : ℝ → ℝ) :
    ∫ x in Ioi (1 : ℝ), g x = ∫ v in Ioi (0 : ℝ), Real.exp v * g (Real.exp v) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) (Ioi (0 : ℝ)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Ioi (0 : ℝ)) := Real.exp_injective.injOn
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [image_exp_Ioi_zero_eq_Ioi_one] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [abs_of_pos (Real.exp_pos v), smul_eq_mul]

/-- **Change of variables `x = exp(−v)` on the origin sector `(0, 1]`:**
`∫_{x ∈ (0, 1]} g(x) dx = ∫_{v ∈ (0, ∞)} e^{−v} g(e^{−v}) dv`. -/
theorem setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul (g : ℝ → ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, g x =
      ∫ v in Ioi (0 : ℝ), Real.exp (-v) * g (Real.exp (-v)) := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) (Ici (0 : ℝ)) x := by
    intro x _
    have hd : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * -1) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
    rw [mul_neg_one] at hd
    exact hd.hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => Real.exp (-y)) (Ici (0 : ℝ)) :=
    fun u _ v _ huv => neg_injective (Real.exp_injective huv)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ici hderiv hinj g
  rw [image_exp_neg_Ici_zero_eq_Ioc_zero_one] at h
  rw [h, ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [abs_neg, abs_of_pos (Real.exp_pos (-v)), smul_eq_mul]

/-- **Integrability criterion on `(0, ∞)` under `x = exp v`:**
`IntegrableOn g (Ioi 0) ↔ Integrable (fun v : ℝ => e^v g(e^v))`. -/
theorem integrableOn_Ioi_iff_integrable_exp_mul (g : ℝ → ℝ) :
    IntegrableOn g (Ioi (0 : ℝ)) ↔ Integrable (fun v : ℝ => Real.exp v * g (Real.exp v)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at h
  rw [h]
  refine integrable_congr (Eventually.of_forall fun v => ?_)
  simp only [abs_of_pos (Real.exp_pos v), smul_eq_mul]

/-- **Additivity of set integrals across the origin–infinity partition `(0, 1] ∪ (1, ∞) = (0, ∞)`:**
For any `g : ℝ → ℝ` integrable on `(0, ∞)`,
`∫_{x ∈ (0, 1]} g(x) dx + ∫_{x ∈ (1, ∞)} g(x) dx = ∫_{x ∈ (0, ∞)} g(x) dx`. -/
theorem setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    (∫ x in Ioc (0 : ℝ) 1, g x) + (∫ x in Ioi (1 : ℝ), g x) =
      ∫ x in Ioi (0 : ℝ), g x := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi zero_le_one)), hunion]

/-- **Support-preserving strict positivity on `(0, ∞)`:**
If `f` is non-negative and integrable on `(0, ∞)` with `0 < ∫_{v > 0} f(v) dv`, and `w` is strictly
positive on `(0, ∞)` with `w · f` integrable on `(0, ∞)`, then `0 < ∫_{v > 0} w(v) f(v) dv`. -/
theorem setIntegral_Ioi_pos_of_pos_mul {f w : ℝ → ℝ}
    (hf_int : IntegrableOn f (Ioi (0 : ℝ)))
    (hwf_int : IntegrableOn (fun v => w v * f v) (Ioi (0 : ℝ)))
    (hf_nonneg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ f v)
    (hw_pos : ∀ v ∈ Ioi (0 : ℝ), 0 < w v)
    (hf_pos : 0 < ∫ v in Ioi (0 : ℝ), f v) :
    0 < ∫ v in Ioi (0 : ℝ), w v * f v := by
  have h1 : ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f v :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hf_nonneg)
  have h2 : ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ w v * f v :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv =>
      mul_nonneg (hw_pos v hv).le (hf_nonneg v hv))
  rw [setIntegral_pos_iff_support_of_nonneg_ae h2 hwf_int]
  have hsupp : Function.support (fun v => w v * f v) ∩ Ioi (0 : ℝ) =
      Function.support f ∩ Ioi (0 : ℝ) := by
    ext v
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun ⟨h, hv⟩ => ⟨right_ne_zero_of_mul h, hv⟩,
      fun ⟨h, hv⟩ => ⟨mul_ne_zero (hw_pos v hv).ne' h, hv⟩⟩
  rw [hsupp, ← setIntegral_pos_iff_support_of_nonneg_ae h1 hf_int]
  exact hf_pos

/-! ### Origin–infinity decomposition and reflection duality of the oscillatory Mellin transform -/

/-- **Infinity-sector (`x > 1`) log-scale bridge for the oscillatory Mellin transform (`k ≥ 1`):**
For all `l, τ ∈ ℝ`,
`∫_{x ∈ (1, ∞)} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{v ∈ (0, ∞)} e^{lv} cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) * Real.cos (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- **Origin-sector (`x ∈ (0, 1]`) log-scale bridge for the oscillatory Mellin transform (`k ≥ 1`):**
For all `l, τ ∈ ℝ`,
`∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{v ∈ (0, ∞)} e^{−lv} cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioc_zero_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp (-(l * v)) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos (-v)), Real.log_exp]
  have hprof : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hcos : Real.cos (τ * -v) = Real.cos (τ * v) := by
    rw [mul_neg, Real.cos_neg]
  have hexp : Real.exp (-v) * Real.exp (-v * (l - 1 / 2)) =
      Real.exp (-(l * v)) * Real.exp ((-v) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (-v) * (Real.exp (-v * (l - 1 / 2)) * Real.cos (τ * -v) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v)))
      = (Real.exp (-v) * Real.exp (-v * (l - 1 / 2))) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v)) := by rw [hcos]; ring
    _ = (Real.exp (-(l * v)) * Real.exp ((-v) / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v)) := by rw [hexp]
    _ = Real.exp (-(l * v)) * Real.cos (τ * v) *
          (Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v))) := by ring
    _ = Real.exp (-(l * v)) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
        rw [hprof]

/-- **Origin–infinity functional reflection duality for the oscillatory Mellin transform (`k ≥ 1`):**
For all `l, τ ∈ ℝ`,
`∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{x ∈ (1, ∞)} x^{−l − 1/2} cos(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi (1 : ℝ),
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioc_zero_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq hk ν l τ,
    setIntegral_Ioi_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq hk ν (-l) τ]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [neg_mul]

/-- Integrability of `x ↦ x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x` on `(0, ∞)`
across the open critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`). -/
theorem integrableOn_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
      (Ioi (0 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  rw [integrableOn_Ioi_iff_integrable_exp_mul]
  refine (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ).congr
    (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (l * v) * Real.cos (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp (l * v) * Real.exp (v / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- **Origin–infinity partition identity for the oscillatory Mellin transform across `|l| < 1/2`:**
The sum of the `(0, 1]` and `(1, ∞)` oscillatory Mellin integrals equals the full `(0, ∞)`
oscillatory Mellin integral. -/
theorem setIntegral_Ioc_zero_one_add_Ioi_one_rpow_mul_cos_log_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x :=
  setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one
    (integrableOn_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector hk hν hl τ)

/-- **Exact critical-line (`l = 0`) symmetry between `(0, 1]` and `(1, ∞)` for the oscillatory
Mellin transform (`k ≥ 1`, `τ ∈ ℝ`).** -/
theorem setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
  have h := setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg hk ν 0 τ
  simpa [zero_sub, neg_zero] using h

/-- **Exact `1/2 - 1/2` critical-line equipartition of the oscillatory Mellin transform on `(1, ∞)`:**
For every `k ≥ 2` and `τ ∈ ℝ`,
`∫_{x ∈ (1, ∞)} x^{−1/2} cos(τ log x) V_k(x) dx = (1/2) · arcLineInfiniteDyadicCosTransform k ν τ`. -/
theorem setIntegral_Ioi_one_cos_log_eq_half_cosTransform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (1 / 2 : ℝ) * arcLineInfiniteDyadicCosTransform k ν τ := by
  have hk1 : 1 ≤ k := by omega
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_mul_cos_log_eq hk hν h0 τ
  rw [zero_sub] at hsum
  have heq := setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk1 ν τ
  have hfull := setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hν τ
  linarith

/-- **Exact `1/2 - 1/2` critical-line equipartition of the oscillatory Mellin transform on `(0, 1]`:**
For every `k ≥ 2` and `τ ∈ ℝ`,
`∫_{x ∈ (0, 1]} x^{−1/2} cos(τ log x) V_k(x) dx = (1/2) · arcLineInfiniteDyadicCosTransform k ν τ`. -/
theorem setIntegral_Ioc_zero_one_cos_log_eq_half_cosTransform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (1 / 2 : ℝ) * arcLineInfiniteDyadicCosTransform k ν τ := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk1 ν τ,
    setIntegral_Ioi_one_cos_log_eq_half_cosTransform hk hν τ]

/-! ### Origin–infinity decomposition, `1/2 - 1/2` critical-line equipartition, and `2 sinh(2lv)` imbalance law for the strip-weighted Hilbert energy -/

/-- **General infinity-sector (`x > 1`) log-scale identity for the strip-weighted `L²` norm:**
Under `x = exp v`, for every `l ∈ ℝ` and `f : ℝ → ℝ`,
`∫_{x ∈ (1, ∞)} x^{2l} (f(x))² dx = ∫_{v ∈ (0, ∞)} e^{2lv} (e^{v/2} f(e^v))² dv`. -/
theorem setIntegral_Ioi_one_rpow_two_mul_sq_eq (f : ℝ → ℝ) (l : ℝ) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (f x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), Real.exp (2 * l * v) * (Real.exp (v / 2) * f (Real.exp v)) ^ 2 := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]
  have hexp : Real.exp v * Real.exp (v * (2 * l)) =
      Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp v * (Real.exp (v * (2 * l)) * (f (Real.exp v)) ^ 2)
      = (Real.exp v * Real.exp (v * (2 * l))) * (f (Real.exp v)) ^ 2 := by ring
    _ = (Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2) * (f (Real.exp v)) ^ 2 := by rw [hexp]
    _ = Real.exp (2 * l * v) * (Real.exp (v / 2) * f (Real.exp v)) ^ 2 := by ring

/-- **General origin-sector (`x ∈ (0, 1]`) log-scale identity for the strip-weighted `L²` norm:**
Under `x = exp(−v)`, for every `l ∈ ℝ` and `f : ℝ → ℝ`,
`∫_{x ∈ (0, 1]} x^{2l} (f(x))² dx = ∫_{v ∈ (0, ∞)} e^{−2lv} (e^{−v/2} f(e^{−v}))² dv`. -/
theorem setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq (f : ℝ → ℝ) (l : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (f x) ^ 2) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp (-(2 * l * v)) * (Real.exp ((-v) / 2) * f (Real.exp (-v))) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos (-v)), Real.log_exp]
  have hexp : Real.exp (-v) * Real.exp (-v * (2 * l)) =
      Real.exp (-(2 * l * v)) * (Real.exp ((-v) / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp (-v) * (Real.exp (-v * (2 * l)) * (f (Real.exp (-v))) ^ 2)
      = (Real.exp (-v) * Real.exp (-v * (2 * l))) * (f (Real.exp (-v))) ^ 2 := by ring
    _ = (Real.exp (-(2 * l * v)) * (Real.exp ((-v) / 2)) ^ 2) * (f (Real.exp (-v))) ^ 2 := by
        rw [hexp]
    _ = Real.exp (-(2 * l * v)) * (Real.exp ((-v) / 2) * f (Real.exp (-v))) ^ 2 := by ring

/-- **Infinity-sector (`x > 1`) strip-weighted `L²` energy identity for
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`, `l ∈ ℝ`):**
`∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx = ∫_{v ∈ (0, ∞)} e^{2lv} (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_one_rpow_two_mul_sq_eq]
  simp_rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν]

/-- **Origin-sector (`x ∈ (0, 1]`) strip-weighted `L²` energy identity for
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`, `l ∈ ℝ`):**
`∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{v ∈ (0, ∞)} e^{−2lv} (Φ_k(v))² dv`. -/
theorem setIntegral_Ioc_zero_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v), arcLineInfiniteDyadicProfile_neg]

/-- **Origin–infinity functional reflection duality for the strip-weighted Hilbert energy (`k ≥ 1`):**
For every `l ∈ ℝ`,
`∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{2(−l)} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi (1 : ℝ), x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk ν l,
    setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk ν (-l)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  congr 2; ring

/-- Integrability of `x ↦ x^{2l} · (arcLineInfiniteDyadicVector k ν x)²` on `(0, ∞)` across the open
critical strip `|l| < 1/2` (`k ≥ 2`). -/
theorem integrableOn_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    IntegrableOn (fun x : ℝ => x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)
      (Ioi (0 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  rw [integrableOn_Ioi_iff_integrable_exp_mul]
  refine (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).congr
    (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
  have hexp : Real.exp v * Real.exp (v * (2 * l)) =
      Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp (2 * l * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2
      = (Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2) *
          (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring
    _ = (Real.exp v * Real.exp (v * (2 * l))) *
          (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by rw [hexp]
    _ = Real.exp v * (Real.exp (v * (2 * l)) *
          (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring

/-- **Origin–infinity partition identity for the strip-weighted Hilbert energy across `|l| < 1/2`:**
`∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx + ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx = ∫_{x ∈ (0, ∞)} x^{2l} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) +
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 :=
  setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one
    (integrableOn_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector hk hν hl)

/-- **Exact critical-line (`l = 0`) origin–infinity Hilbert energy equality (`k ≥ 1`):**
`∫_{x ∈ (0, 1]} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) :
    (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have h := setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk ν 0
  simpa using h

/-- **Exact `1/2 - 1/2` critical-line Hilbert energy equipartition on `(1, ∞)` (`k ≥ 2`):**
`∫_{x ∈ (1, ∞)} (V_k(x))² dx = (1/2) ∫_{x ∈ (0, ∞)} (V_k(x))² dx`. -/
theorem setIntegral_Ioi_one_sq_eq_half_setIntegral_Ioi_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      (1 / 2 : ℝ) * ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν h0
  simp only [mul_zero, Real.rpow_zero, one_mul] at hsum
  have heq := setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq hk1 ν
  linarith

/-- **Exact `1/2 - 1/2` critical-line Hilbert energy equipartition on `(0, 1]` (`k ≥ 2`):**
`∫_{x ∈ (0, 1]} (V_k(x))² dx = (1/2) ∫_{x ∈ (0, ∞)} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_sq_eq_half_setIntegral_Ioi_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      (1 / 2 : ℝ) * ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq hk1 ν,
    setIntegral_Ioi_one_sq_eq_half_setIntegral_Ioi_sq hk hν]

/-- **Half-line profile energy identity on `(0, ∞)` (`k ≥ 2`):**
`∫_{v ∈ (0, ∞)} (Φ_k(v))² dv = (1/2) ∫_ℝ (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_eq_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v in Ioi (0 : ℝ), (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      (1 / 2 : ℝ) * ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have h1 := setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν 0
  simp only [mul_zero, zero_mul, Real.rpow_zero, Real.exp_zero, one_mul] at h1
  rw [← h1, setIntegral_Ioi_one_sq_eq_half_setIntegral_Ioi_sq hk hν,
    setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν]

/-- **Strict positivity of the half-line profile energy `∫_{v > 0} (Φ_k(v))² dv > 0` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ v in Ioi (0 : ℝ), (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_eq_half hk hν]
  exact mul_pos (by norm_num) (integral_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **The `2 sinh(2lv)` Origin–Infinity Energy Imbalance Identity across `|l| < 1/2` (`k ≥ 2`):**
`∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx − ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{v ∈ (0, ∞)} 2 sinh(2lv) (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ),
        2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    setIntegral_Ioc_zero_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l]
  have hIl : IntegrableOn
      (fun v : ℝ => Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).integrableOn
  have hIneg : IntegrableOn
      (fun v : ℝ => Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) := by
    have heq : (fun v : ℝ => Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; congr 2; ring
    rw [heq]
    exact (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hl)).integrableOn
  rw [← integral_sub hIl hIneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.sinh_eq]
  ring

/-- **Strict dominance of the infinity sector `(1, ∞)` over `(0, 1]` for `0 < l < 1/2` (`k ≥ 2`):**
Whenever `0 < l < 1/2`,
`∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx < ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_lt_setIntegral_Ioi_one_rpow_two_mul_sq_of_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 2) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hlabs : |l| < 1 / 2 := by rwa [abs_of_pos hl0]
  rw [← sub_pos, setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hlabs]
  have hf_int : IntegrableOn (fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
  have hwf_int : IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) := by
    have heq : (fun v : ℝ => 2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ =>
          Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
            Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; rw [Real.sinh_eq, show -(2 * l * v) = 2 * (-l) * v by ring]; ring
    rw [heq]
    exact (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hlabs).integrableOn.sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hlabs)).integrableOn
  exact setIntegral_Ioi_pos_of_pos_mul hf_int hwf_int
    (fun _ _ => sq_nonneg _)
    (fun v hv => mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)))
    (setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **Strict dominance of the origin sector `(0, 1]` over `(1, ∞)` for `−1/2 < l < 0` (`k ≥ 2`):**
Whenever `−1/2 < l < 0`,
`∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx < ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx`. -/
theorem setIntegral_Ioi_one_lt_setIntegral_Ioc_zero_one_rpow_two_mul_sq_of_neg
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl1 : -(1 / 2 : ℝ) < l) (hl0 : l < 0) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hpos_lt := setIntegral_Ioc_zero_one_lt_setIntegral_Ioi_one_rpow_two_mul_sq_of_pos
    hk hν hpos (l := -l) (by linarith) (by linarith)
  have h1 := setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν (-l)
  rw [neg_neg] at h1
  have h2 := setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l
  linarith

/-- **Strict critical-line origin–infinity balance characterization (`|l| < 1/2`, `k ≥ 2`):**
Across the entire open critical strip `l ∈ (−1/2, 1/2)`,
`∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx ↔ l = 0`.
That is, the critical line `l = 0` (`Re(s) = 1/2`) is the **unique** vertical line in the open
critical strip on which the strip-weighted Hilbert energy of `V_k` is balanced between the origin
sector `(0, 1]` and the infinity sector `(1, ∞)`. -/
theorem setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_iff
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
      l = 0 := by
  have hk1 : 1 ≤ k := by omega
  constructor
  · intro heq
    rcases lt_trichotomy l 0 with hlt | rfl | hgt
    · exfalso
      have h1 : -(1 / 2 : ℝ) < l := (abs_lt.mp hl).1
      exact (setIntegral_Ioi_one_lt_setIntegral_Ioc_zero_one_rpow_two_mul_sq_of_neg
        hk hν hpos h1 hlt).ne heq.symm
    · rfl
    · exfalso
      have h2 : l < 1 / 2 := (abs_lt.mp hl).2
      exact (setIntegral_Ioc_zero_one_lt_setIntegral_Ioi_one_rpow_two_mul_sq_of_pos
        hk hν hpos hgt h2).ne heq
  · rintro rfl
    simpa using setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq hk1 ν

/-- **Master theorem for the origin–infinity (`(0, 1]` vs `(1, ∞)`) equipartition, `2 sinh(2lv)`
energy imbalance law, and strict critical-line balance characterization:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for every integer
`k ≥ 2`, the infinite-horizon dyadic line-model vector `V_k = arcLineInfiniteDyadicVector k ν` and
its log-scale profile `Φ_k = arcLineInfiniteDyadicProfile k ν` satisfy:
1. **Origin–infinity oscillatory Mellin reflection duality and critical-line equipartition:**
   - For all `l, τ ∈ ℝ`,
     `∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{x ∈ (1, ∞)} x^{−l − 1/2} cos(τ log x) V_k(x) dx`.
   - At `l = 0`, for all `τ ∈ ℝ`, both half-line integrals equal
     `(1/2) · arcLineInfiniteDyadicCosTransform k ν τ > 0`.
2. **Origin–infinity strip-weighted Hilbert energy reflection duality and `1/2 - 1/2` critical-line
   equipartition:**
   - For all `l ∈ ℝ`,
     `∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{−2l} (V_k(x))² dx`.
   - At `l = 0`,
     `∫_{x ∈ (0, 1]} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} (V_k(x))² dx = (1/2) ∫_{x > 0} (V_k(x))² dx > 0`.
3. **The `2 sinh(2lv)` origin–infinity energy imbalance law across `|l| < 1/2`:**
   `∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx − ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{v ∈ (0, ∞)} 2 sinh(2lv) (Φ_k(v))² dv`.
4. **Strict off-line imbalance and unique critical-line balance (`|l| < 1/2`):**
   - For `0 < l < 1/2`, strictly `∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx < ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx`.
   - For `−1/2 < l < 0`, strictly `∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx < ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx`.
   - Across `|l| < 1/2`,
     `∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx = ∫_{x ∈ (1, ∞)} x^{2l} (V_k(x))² dx ↔ l = 0` and
     `∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_{x > 0} (V_k(x))² dx ↔ l = 0`. -/
theorem exists_dyadic_originInfinity_equipartition_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0) ∧
      (∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ l τ : ℝ,
          (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
            ∫ x in Ioi (1 : ℝ),
              x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ τ : ℝ,
          (∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
            (1 / 2 : ℝ) * arcLineInfiniteDyadicCosTransform k ν τ ∧
          (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
            (1 / 2 : ℝ) * arcLineInfiniteDyadicCosTransform k ν τ) ∧
        (∀ l : ℝ,
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            ∫ x in Ioi (1 : ℝ), x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        ((∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
          (1 / 2 : ℝ) * ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        ((∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) =
          (1 / 2 : ℝ) * ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
            (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            ∫ v in Ioi (0 : ℝ),
              2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, 0 < l → l < 1 / 2 →
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            ∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, -(1 / 2 : ℝ) < l → l < 0 →
          (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          ((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
            l = 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
            l = 0))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg hk1 ν,
    fun τ => ⟨setIntegral_Ioc_zero_one_cos_log_eq_half_cosTransform hk hsymm τ,
      setIntegral_Ioi_one_cos_log_eq_half_cosTransform hk hsymm τ⟩,
    setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν,
    setIntegral_Ioc_zero_one_sq_eq_half_setIntegral_Ioi_sq hk hsymm,
    setIntegral_Ioi_one_sq_eq_half_setIntegral_Ioi_sq hk hsymm,
    fun l hl => setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hsymm hl,
    fun l hl0 hl =>
      setIntegral_Ioc_zero_one_lt_setIntegral_Ioi_one_rpow_two_mul_sq_of_pos hk hsymm hpd hl0 hl,
    fun l hl1 hl0 =>
      setIntegral_Ioi_one_lt_setIntegral_Ioc_zero_one_rpow_two_mul_sq_of_neg hk hsymm hpd hl1 hl0,
    fun l hl =>
      setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_iff hk hsymm hpd hl,
    fun l hl => setIntegral_Ioi_rpow_two_mul_sq_eq_sq_iff hk hsymm hpd hl⟩

end

end RHTower
