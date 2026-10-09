import GaloisForLFunctions.RHTower.LiouvilleExponentialSumSimplicity

/-!
# The exponential Liouville sum with logarithmic losses: multiplicities of critical zeros

Let `J(t) = Σ_{n ≥ 1} λ(n) e^{-nt}/n`.  If for some `k ≥ 0`

  `J(t) ≥ -C √t (1 + log(1/t)^k)`   for `0 < t ≤ t₀`,

then the Riemann hypothesis holds (`riemannHypothesis_of_liouvilleExpSum_lower_logPow`) and every
zero of `ζ` on the critical line has order at most `k + 1`
(`le_of_liouvilleExpSum_lower_logPow`).  At `k = 0` this is the simplicity statement
`deriv_zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower`.

**Proof.**  As for `k = 0`, with the weight `w_k(u) = e^{-u/2}(1 + u^k)` in place of `e^{-u/2}`.
In `t = e^{-u}` the density `J(e^{-u}) + C w_k(u)` is nonnegative on `u > 0`, and its Laplace
transform is `Γ(z) L(λ, z+1) - E(z) + C W_k(z)` with `W_k` the transform of `w_k(u) du`, which
is holomorphic on `Re z > -½` and satisfies `|W_k(-½ + r + iy)| ≤ W_k(-½ + r) ≪ r^{-k-1}`.
Landau's theorem puts the abscissa at `-½` and the identity theorem gives
`(∫ e^{-zu} dν + E(z) - C W_k(z))(2z+1) Z(z+1) = Γ(z+1) Z(2z+2)` on `Re z > -½`.  At a critical
zero of order `m` the left side is `O(r^{m-k-1})` along `z = ρ - 1 + r`, while the right side
tends to `Γ(ρ)Z(2ρ) ≠ 0`; hence `m ≤ k + 1`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-! ## The weight `w_k(u) = e^{-u/2}(1 + u^k)` -/

/-- `w_k(u) = e^{-u/2}(1 + u^k)`. -/
def liouvilleLogPowWeight (k : ℕ) (u : ℝ) : ℝ := Real.exp (-u / 2) * (1 + u ^ k)

theorem continuous_liouvilleLogPowWeight (k : ℕ) : Continuous (liouvilleLogPowWeight k) := by
  unfold liouvilleLogPowWeight; fun_prop

theorem exp_neg_half_le_liouvilleLogPowWeight (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u / 2) ≤ liouvilleLogPowWeight k u := by
  unfold liouvilleLogPowWeight
  have := Real.exp_pos (-u / 2)
  have : 0 ≤ u ^ k := pow_nonneg hu k
  nlinarith

theorem liouvilleLogPowWeight_pos (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 < liouvilleLogPowWeight k u :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_neg_half_le_liouvilleLogPowWeight k hu)

/-- `u^k e^{-au} ≤ k!(2/a)^k e^{-(a/2)u}` for `a > 0`, `u ≥ 0`. -/
theorem liouville_pow_mul_exp_neg_le (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) ≤ k.factorial * (2 / a) ^ k * Real.exp (-(a / 2) * u) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * u) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h
  have hu' : u ^ k = (2 / a) ^ k * (a / 2 * u) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hsplit : Real.exp (-a * u) = Real.exp (-(a / 2) * u) * Real.exp (-(a / 2 * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hu', hsplit]
  have hE := Real.exp_pos (-(a / 2) * u)
  have h2 : (a / 2 * u) ^ k * Real.exp (-(a / 2 * u)) ≤ k.factorial := by
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(a / 2 * u))).le
    have e : Real.exp (a / 2 * u) * k.factorial * Real.exp (-(a / 2 * u)) = k.factorial := by
      rw [mul_comm (Real.exp (a / 2 * u)), mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]
    linarith
  calc (2 / a) ^ k * (a / 2 * u) ^ k * (Real.exp (-(a / 2) * u) * Real.exp (-(a / 2 * u)))
      = (2 / a) ^ k * Real.exp (-(a / 2) * u) * ((a / 2 * u) ^ k * Real.exp (-(a / 2 * u))) := by
        ring
    _ ≤ (2 / a) ^ k * Real.exp (-(a / 2) * u) * k.factorial :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The weight measure `w_k(u) du` on `(0, ∞)`. -/
def liouvilleWeightMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun u => (Real.toNNReal (liouvilleLogPowWeight k u) : ENNReal))

theorem measurable_toNNReal_liouvilleLogPowWeight (k : ℕ) :
    Measurable (fun u => Real.toNNReal (liouvilleLogPowWeight k u)) :=
  (continuous_liouvilleLogPowWeight k).measurable.real_toNNReal

theorem lintegral_liouvilleWeightMeasure (k : ℕ) (σ : ℝ) :
    laplaceMass (liouvilleWeightMeasure k) σ =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (liouvilleLogPowWeight k u * Real.exp (-σ * u)) := by
  unfold laplaceMass liouvilleWeightMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_toNNReal_liouvilleLogPowWeight k).coe_nnreal_ennreal hg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (liouvilleLogPowWeight_pos k hu0).le,
    ← ENNReal.ofReal_mul (liouvilleLogPowWeight_pos k hu0).le]

theorem isAbscissa_liouvilleWeightMeasure (k : ℕ) :
    IsAbscissa (liouvilleWeightMeasure k) (-1 / 2) := by
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · rw [lintegral_liouvilleWeightMeasure]
    set a : ℝ := σ + 1 / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-a * u) +
        k.factorial * (2 / a) ^ k * Real.exp (-(a / 2) * u)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 ha0).add ((exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _)
    refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
    refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    apply ENNReal.ofReal_le_ofReal
    have e : liouvilleLogPowWeight k u * Real.exp (-σ * u) =
        Real.exp (-a * u) + u ^ k * Real.exp (-a * u) := by
      unfold liouvilleLogPowWeight
      rw [show Real.exp (-a * u) = Real.exp (-u / 2) * Real.exp (-σ * u) by
        rw [← Real.exp_add]; congr 1; rw [ha]; ring]
      ring
    rw [e]
    have := liouville_pow_mul_exp_neg_le k ha0 hu0
    linarith
  · rw [lintegral_liouvilleWeightMeasure, eq_top_iff]
    calc (⊤ : ENNReal) = ENNReal.ofReal 1 * volume (Ioi (0 : ℝ)) := by
          rw [Real.volume_Ioi, ENNReal.ofReal_one, one_mul]
      _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal 1 := by rw [setLIntegral_const]
      _ ≤ ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (liouvilleLogPowWeight k u * Real.exp (-σ * u)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
          apply ENNReal.ofReal_le_ofReal
          have h1 := exp_neg_half_le_liouvilleLogPowWeight k hu0
          have h2 : 1 ≤ Real.exp (-u / 2) * Real.exp (-σ * u) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
          nlinarith [Real.exp_pos (-σ * u)]

/-- The transform `W_k` of the weight measure. -/
def liouvilleWeightTransform (k : ℕ) (z : ℂ) : ℂ := complexLaplace (liouvilleWeightMeasure k) z

theorem analyticAt_liouvilleWeightTransform (k : ℕ) {z : ℂ} (hz : -1 / 2 < z.re) :
    AnalyticAt ℂ (liouvilleWeightTransform k) z := by
  have hopen : IsOpen {w : ℂ | -1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (liouvilleWeightTransform k) {w : ℂ | -1 / 2 < w.re} :=
    fun w hw => (hasDerivAt_complexLaplace (isAbscissa_liouvilleWeightMeasure k)
      hw).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hz)

/-- `W_k(-½ + r) ≤ 1/r + k!2^{k+1}/r^{k+1}` for `r > 0`. -/
theorem laplaceReal_liouvilleWeightMeasure_le (k : ℕ) {r : ℝ} (hr : 0 < r) :
    laplaceReal (liouvilleWeightMeasure k) (-1 / 2 + r) ≤
      1 / r + k.factorial * 2 ^ (k + 1) / r ^ (k + 1) := by
  unfold laplaceReal liouvilleWeightMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul
      (measurable_toNNReal_liouvilleLogPowWeight k)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), Real.toNNReal (liouvilleLogPowWeight k u) •
      Real.exp (-(-1 / 2 + r) * u) = Real.exp (-r * u) + u ^ k * Real.exp (-r * u) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (liouvilleLogPowWeight_pos k hu0).le]
    unfold liouvilleLogPowWeight
    rw [show Real.exp (-r * u) = Real.exp (-u / 2) * Real.exp (-(-1 / 2 + r) * u) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hi1 : IntegrableOn (fun u : ℝ => Real.exp (-r * u)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hr
  have hi3 : IntegrableOn (fun u : ℝ => Real.exp (-(r / 2) * u)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  have hi2 : IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-r * u)) (Ioi 0) := by
    refine Integrable.mono' (hi3.const_mul (k.factorial * (2 / r) ^ k)) ?_ ?_
    · exact (by fun_prop : Continuous fun u : ℝ => u ^ k * Real.exp (-r * u)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      rw [Real.norm_of_nonneg (by positivity)]
      exact liouville_pow_mul_exp_neg_le k hr hu0
  rw [integral_add hi1 hi2]
  have hI1 : ∫ u in Ioi (0 : ℝ), Real.exp (-r * u) = 1 / r := by
    have := integral_exp_mul_Ioi (a := -r) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [this]; field_simp
  have hI3 : ∫ u in Ioi (0 : ℝ), Real.exp (-(r / 2) * u) = 2 / r := by
    have := integral_exp_mul_Ioi (a := -(r / 2)) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [this]; field_simp
  have hI2 : ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-r * u) ≤
      k.factorial * (2 / r) ^ k * (2 / r) := by
    calc ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-r * u)
        ≤ ∫ u in Ioi (0 : ℝ), (k.factorial : ℝ) * (2 / r) ^ k * Real.exp (-(r / 2) * u) :=
          setIntegral_mono_on hi2 (hi3.const_mul _) measurableSet_Ioi fun u hu =>
            liouville_pow_mul_exp_neg_le k hr (le_of_lt hu)
      _ = k.factorial * (2 / r) ^ k * (2 / r) := by rw [integral_const_mul, hI3]
  have e : (k.factorial : ℝ) * (2 / r) ^ k * (2 / r) = k.factorial * 2 ^ (k + 1) / r ^ (k + 1) := by
    rw [div_pow, pow_succ, pow_succ]; field_simp
  rw [hI1]
  linarith

/-! ## The one-sided measure -/

/-- The density `J(e^{-u}) + C w_k(u)`, clipped at `0`. -/
def liouvilleExpDensityPow (k : ℕ) (C : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (liouvilleExpLog u + C * liouvilleLogPowWeight k u)

theorem measurable_liouvilleExpDensityPow (k : ℕ) (C : ℝ) :
    Measurable (liouvilleExpDensityPow k C) :=
  Measurable.real_toNNReal (continuous_liouvilleExpLog.measurable.add
    (measurable_const.mul (continuous_liouvilleLogPowWeight k).measurable))

/-- `ν = (J(e^{-u}) + C w_k(u)) du` on `(0, ∞)`. -/
def liouvilleExpMeasurePow (k : ℕ) (C : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (liouvilleExpDensityPow k C u : ENNReal))

theorem liouvilleExpDensityPow_coe {k : ℕ} {C₀ C : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) {u : ℝ}
    (hu : 0 < u) :
    ((liouvilleExpDensityPow k C u : ℝ)) = liouvilleExpLog u + C * liouvilleLogPowWeight k u := by
  unfold liouvilleExpDensityPow
  have h := hg u hu
  have hw := liouvilleLogPowWeight_pos k hu.le
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem laplaceMass_liouvilleExpMeasurePow_one_ne_top (k : ℕ) (C : ℝ) :
    laplaceMass (liouvilleExpMeasurePow k C) 1 ≠ ⊤ := by
  unfold laplaceMass liouvilleExpMeasurePow
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-1 * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensityPow k C).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => (1 + |C|) * Real.exp (-1 * u) +
      (2 + |C| * k.factorial * 2 ^ k) * Real.exp (-(1 / 2) * u)) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _).add
      ((exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul _)
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hE := Real.exp_pos (-1 * u)
  have hd : ((liouvilleExpDensityPow k C u : ℝ)) ≤ 1 + u + |C| * (1 + u ^ k) := by
    unfold liouvilleExpDensityPow
    rw [Real.coe_toNNReal']
    refine max_le ?_ (by positivity)
    have h1 := abs_liouvilleExpLog_le_of_nonneg hu0.le
    have hw : liouvilleLogPowWeight k u ≤ 1 + u ^ k := by
      unfold liouvilleLogPowWeight
      have := Real.exp_le_one_iff.mpr (show -u / 2 ≤ 0 by linarith)
      have : 0 ≤ 1 + u ^ k := by positivity
      nlinarith
    have hw0 := (liouvilleLogPowWeight_pos k hu0.le).le
    have h3 : C * liouvilleLogPowWeight k u ≤ |C| * (1 + u ^ k) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hw0).trans
        (mul_le_mul_of_nonneg_left hw (abs_nonneg C))
    linarith [le_abs_self (liouvilleExpLog u)]
  have hu2 : u * Real.exp (-1 * u) ≤ 2 * Real.exp (-(1 / 2) * u) := by
    have := liouville_pow_mul_exp_neg_le 1 one_pos hu0.le
    simpa using this
  have hu3 : u ^ k * Real.exp (-1 * u) ≤ k.factorial * 2 ^ k * Real.exp (-(1 / 2) * u) := by
    have := liouville_pow_mul_exp_neg_le k one_pos hu0.le
    simpa using this
  calc ((liouvilleExpDensityPow k C u : ℝ)) * Real.exp (-1 * u)
      ≤ (1 + u + |C| * (1 + u ^ k)) * Real.exp (-1 * u) := mul_le_mul_of_nonneg_right hd hE.le
    _ = (1 + |C|) * Real.exp (-1 * u) + u * Real.exp (-1 * u) +
        |C| * (u ^ k * Real.exp (-1 * u)) := by ring
    _ ≤ (1 + |C|) * Real.exp (-1 * u) + 2 * Real.exp (-(1 / 2) * u) +
        |C| * (k.factorial * 2 ^ k * Real.exp (-(1 / 2) * u)) := by
        gcongr
    _ = _ := by ring

theorem laplaceMass_liouvilleExpMeasurePow_eq_top {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) {σ : ℝ}
    (hσ : σ ≤ -1 / 2) : laplaceMass (liouvilleExpMeasurePow k C) σ = ⊤ := by
  unfold laplaceMass liouvilleExpMeasurePow
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensityPow k C).coe_nnreal_ennreal hg', eq_top_iff]
  calc (⊤ : ENNReal) = ENNReal.ofReal 1 * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal 1 := by rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (liouvilleExpDensityPow k C u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [liouvilleExpDensityPow_coe (by linarith) hg hu0]
        have h1 := hg u hu0
        have hw := exp_neg_half_le_liouvilleLogPowWeight k hu0.le
        have hE2 := Real.exp_pos (-σ * u)
        have h2 : 1 ≤ Real.exp (-u / 2) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hw0 := (liouvilleLogPowWeight_pos k hu0.le).le
        have h3 : Real.exp (-u / 2) ≤ liouvilleExpLog u + C * liouvilleLogPowWeight k u := by
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h3 hE2.le]

theorem isAbscissa_liouvilleExpMeasurePow {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasurePow k C)
        (sInf {σ : ℝ | laplaceMass (liouvilleExpMeasurePow k C) σ ≠ ⊤})
      ∧ -1 / 2 ≤ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasurePow k C) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasurePow k C) σ ≠ ⊤} ≤ 1 := by
  set S := {σ : ℝ | laplaceMass (liouvilleExpMeasurePow k C) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, -1 / 2 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_liouvilleExpMeasurePow_eq_top hC hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨-1 / 2, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1 : ℝ) ∈ S := laplaceMass_liouvilleExpMeasurePow_one_ne_top k C
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h1S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-- The continuation `Φ(z) = κ(z) - E(z) + C W_k(z)`. -/
def liouvilleExpContinuationPow (k : ℕ) (C : ℝ) (z : ℂ) : ℂ :=
  liouvilleExpKernel z - liouvilleExpTail z + C * liouvilleWeightTransform k z

theorem analyticAt_liouvilleExpContinuationPow (k : ℕ) (C : ℝ) {z : ℂ} (hz : -1 / 2 < z.re)
    (hZ : zetaResidueUnit (z + 1) ≠ 0) : AnalyticAt ℂ (liouvilleExpContinuationPow k C) z := by
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold liouvilleExpContinuationPow
  exact ((analyticAt_liouvilleExpKernel (by linarith) h2 hZ).sub
    (differentiable_liouvilleExpTail.analyticAt z)).add
    (analyticAt_const.mul (analyticAt_liouvilleWeightTransform k hz))

/-- On `Re z > 0` the complex transform of `ν` is `Φ(z)`. -/
theorem complexLaplace_liouvilleExpMeasurePow_eq {k : ℕ} {C₀ C : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) {z : ℂ}
    (hz : 0 < z.re) :
    complexLaplace (liouvilleExpMeasurePow k C) z = liouvilleExpContinuationPow k C z := by
  have hW : liouvilleWeightTransform k z = ∫ u in Ioi (0 : ℝ),
      cexp (-z * (u : ℂ)) * (liouvilleLogPowWeight k u : ℂ) := by
    unfold liouvilleWeightTransform complexLaplace liouvilleWeightMeasure
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul
        (measurable_toNNReal_liouvilleLogPowWeight k)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _
      (liouvilleLogPowWeight_pos k hu0).le, mul_comm]
  have hWint : IntegrableOn (fun u : ℝ => cexp (-z * (u : ℂ)) * (liouvilleLogPowWeight k u : ℂ))
      (Ioi 0) := by
    have h := integrable_cexp_of_gt_abscissa (isAbscissa_liouvilleWeightMeasure k)
      (show -1 / 2 < z.re by linarith)
    unfold liouvilleWeightMeasure at h
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul
        (measurable_toNNReal_liouvilleLogPowWeight k)] at h
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _
      (liouvilleLogPowWeight_pos k hu0).le, mul_comm]
  unfold complexLaplace liouvilleExpMeasurePow
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_liouvilleExpDensityPow k C)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), liouvilleExpDensityPow k C u • Complex.exp (-z * (u : ℂ))
      = cexp (-z * u) * (liouvilleExpLog u : ℂ) +
        (C : ℂ) * (cexp (-z * (u : ℂ)) * (liouvilleLogPowWeight k u : ℂ)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, liouvilleExpDensityPow_coe hC hg hu]
    push_cast
    ring
  have i1 := integrableOn_Ioi_liouvilleExpIntegrand hz
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i1 (hWint.const_mul _),
    integral_const_mul, ← hW, integral_Ioi_liouvilleExpLog hz, Gamma_mul_LSeries_eq_kernel hz]
  unfold liouvilleExpContinuationPow
  ring

/-- **Landau: the abscissa of `ν` is `-½`.** -/
theorem abscissa_liouvilleExpMeasurePow_eq {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasurePow k C) (-1 / 2) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_liouvilleExpMeasurePow hC hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (liouvilleExpMeasurePow k C) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hZ : zetaResidueUnit ((c : ℂ) + 1) ≠ 0 := by
      have := zetaResidueUnit_ofReal_ne_zero (t := c + 1) (by linarith)
      simpa using this
    have hcre : -1 / 2 < ((c : ℂ)).re := by simpa using hpos
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit (z + 1) ≠ 0 ∧ -1 / 2 < z.re :=
      (((analyticAt_zetaResidueUnit _).comp
        (analyticAt_id.add analyticAt_const)).continuousAt.eventually_ne hZ).and
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hcre)
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := liouvilleExpContinuationPow k C) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := hball hz
      exact analyticAt_liouvilleExpContinuationPow k C h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (liouvilleExpMeasurePow k C))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ
          (fun t : ℝ => complexLaplace (liouvilleExpMeasurePow k C) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (liouvilleExpMeasurePow k C)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => liouvilleExpContinuationPow k C (t : ℂ))
          (Ioi c) := by
        intro t ht
        have ht' : c < t := ht
        have h1 : AnalyticAt ℂ (liouvilleExpContinuationPow k C) (t : ℂ) := by
          refine analyticAt_liouvilleExpContinuationPow k C (by simp; linarith) ?_
          have := zetaResidueUnit_ofReal_ne_zero (t := t + 1) (by linarith)
          simpa using this
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (2 : ℝ) ∈ Ioi c := by show c < 2; linarith
      have hfg : (fun t : ℝ => complexLaplace (liouvilleExpMeasurePow k C) (t : ℂ))
          =ᶠ[𝓝 (2 : ℝ)] (fun t : ℝ => liouvilleExpContinuationPow k C (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)) fun t ht => ?_
        have ht1 : 0 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_liouvilleExpMeasurePow_eq (by linarith) hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (liouvilleExpMeasurePow k C) (σ : ℂ)
          = liouvilleExpContinuationPow k C (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > -½`.**
`(∫ e^{-zu} dν + E(z) - C W_k(z)) (2z+1) Z(z+1) = Γ(z+1) Z(2z+2)`. -/
theorem liouvilleExpPow_continuation_identity {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u)
    {z : ℂ} (hz : -1 / 2 < z.re) :
    (complexLaplace (liouvilleExpMeasurePow k C) z + liouvilleExpTail z -
        C * liouvilleWeightTransform k z) * ((2 * z + 1) * zetaResidueUnit (z + 1)) =
      Gamma (z + 1) * zetaResidueUnit (2 * z + 2) := by
  have hc := abscissa_liouvilleExpMeasurePow_eq hC hg
  set U : Set ℂ := {w : ℂ | -1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set F : ℂ → ℂ := fun w => (complexLaplace (liouvilleExpMeasurePow k C) w + liouvilleExpTail w
    - C * liouvilleWeightTransform k w) * ((2 * w + 1) * zetaResidueUnit (w + 1)) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have h1 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h2 := differentiable_liouvilleExpTail w
    have h3 : DifferentiableAt ℂ (fun w : ℂ => (C : ℂ) * liouvilleWeightTransform k w) w :=
      (differentiableAt_const _).mul (analyticAt_liouvilleWeightTransform k hw).differentiableAt
    have h4 : DifferentiableAt ℂ (fun w => (2 * w + 1) * zetaResidueUnit (w + 1)) w :=
      (((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).mul
        ((analyticAt_zetaResidueUnit _).differentiableAt.comp w
          (differentiableAt_id.add (differentiableAt_const _)))
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2)) U :=
    fun w hw => ((analyticAt_Gamma_of_pos_re (by simp [hU] at hw ⊢; linarith)).comp
      (analyticAt_id.add analyticAt_const)).mul
      ((analyticAt_zetaResidueUnit _).comp ((analyticAt_const.mul analyticAt_id).add
        analyticAt_const))
  have h1U : (1 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : F =ᶠ[𝓝 (1 : ℂ)] fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    have hw0 : 0 < w.re := hw
    have h2 : 2 * w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit (w + 1) ≠ 0 :=
      zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
    simp only [hF]
    rw [complexLaplace_liouvilleExpMeasurePow_eq (by linarith) hg hw0,
      liouvilleExpContinuationPow]
    have hden : (2 * w + 1) * zetaResidueUnit (w + 1) ≠ 0 := mul_ne_zero h2 hZ
    have e : liouvilleExpKernel w * ((2 * w + 1) * zetaResidueUnit (w + 1)) =
        Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
      unfold liouvilleExpKernel; exact div_mul_cancel₀ _ hden
    linear_combination e
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h1U hev
  exact hEq hz

/-- **A one-sided bound `J ≥ -C₀ w_k` implies RH** (logarithmic form). -/
theorem riemannHypothesis_of_liouvilleExpLog_lower_pow {k : ℕ} {C₀ : ℝ}
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) :
    RiemannHypothesis := by
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro w hw hzero
  have hz : -1 / 2 < (w - 1).re := by simp; linarith
  have hid := liouvilleExpPow_continuation_identity (le_refl (C₀ + 1)) hg hz
  rw [show w - 1 + 1 = w by ring, hzero, mul_zero, mul_zero] at hid
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ2 : zetaResidueUnit (2 * (w - 1) + 2) ≠ 0 := by
    rw [show 2 * (w - 1) + 2 = 2 * w by ring]
    exact zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
  exact mul_ne_zero hG hZ2 hid.symm

/-! ## Orders of critical zeros -/

/-- `‖W_k(z)‖ ≤ W_k(Re z)`. -/
theorem norm_liouvilleWeightTransform_le (k : ℕ) (z : ℂ) :
    ‖liouvilleWeightTransform k z‖ ≤ laplaceReal (liouvilleWeightMeasure k) z.re :=
  norm_complexLaplace_le (liouvilleWeightMeasure k) z

/-- `r^{k+1} ∫ e^{(½ - r)u} dν` stays bounded as `r ↓ 0`. -/
theorem exists_bound_pow_mul_laplaceReal {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C) (hC0 : 0 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u) :
    ∃ B : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      r ^ (k + 1) * laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) ≤ B := by
  set q : ℝ → ℂ := fun r => Gamma ((1 / 2 + r : ℝ) : ℂ) * zetaResidueUnit (1 + 2 * (r : ℂ)) /
    (2 * zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) with hq
  have hZh : zetaResidueUnit ((1 / 2 : ℝ) : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by norm_num)
  have hqc : ContinuousAt q 0 := by
    have hG : ContinuousAt (fun r : ℝ => Gamma ((1 / 2 + r : ℝ) : ℂ)) 0 := by
      have h := (analyticAt_Gamma_of_pos_re (w := ((1 / 2 + 0 : ℝ) : ℂ)) (by simp)).continuousAt
      exact ContinuousAt.comp (g := Gamma) (f := fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ)) h
        (by fun_prop)
    have hZ1 : ContinuousAt (fun r : ℝ => zetaResidueUnit (1 + 2 * (r : ℂ))) 0 :=
      ContinuousAt.comp (g := zetaResidueUnit) (f := fun r : ℝ => 1 + 2 * (r : ℂ))
        (analyticAt_zetaResidueUnit _).continuousAt (by fun_prop)
    have hZ2 : ContinuousAt (fun r : ℝ => zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) 0 :=
      ContinuousAt.comp (g := zetaResidueUnit) (f := fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ))
        (analyticAt_zetaResidueUnit _).continuousAt (by fun_prop)
    refine (hG.mul hZ1).div (continuousAt_const.mul hZ2) ?_
    simpa using mul_ne_zero two_ne_zero hZh
  have hEc : ContinuousAt (fun r : ℝ => liouvilleExpTail ((-1 / 2 + r : ℝ) : ℂ)) 0 :=
    (differentiable_liouvilleExpTail.continuous.comp
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))).continuousAt
  have hbq := (hqc.norm).eventually (gt_mem_nhds (lt_add_one ‖q 0‖))
  have hbE := (hEc.norm).eventually
    (gt_mem_nhds (lt_add_one ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖))
  set Kw : ℝ := 1 + k.factorial * 2 ^ (k + 1) with hKw
  refine ⟨‖q 0‖ + 1 + (‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1) + C * Kw, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hbq, nhdsWithin_le_nhds hbE, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r h1 h2 hr hr1
  have hr0 : 0 < r := hr
  have hr1' : r < 1 := hr1
  set z : ℂ := ((-1 / 2 + r : ℝ) : ℂ) with hz
  have hzre : -1 / 2 < z.re := by simp [hz]; linarith
  have hid := liouvilleExpPow_continuation_identity hC hg hzre
  have hz1 : z + 1 = ((1 / 2 + r : ℝ) : ℂ) := by simp [hz]; ring
  have hz2 : 2 * z + 1 = 2 * (r : ℂ) := by simp [hz]; ring
  have hz3 : 2 * z + 2 = 1 + 2 * (r : ℂ) := by simp [hz]; ring
  rw [hz1, hz2, hz3] at hid
  have hZ : zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ) ≠ 0 :=
    zetaResidueUnit_ofReal_ne_zero (by linarith)
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hL : (r : ℂ) ^ (k + 1) * complexLaplace (liouvilleExpMeasurePow k C) z =
      (r : ℂ) ^ k * q r - (r : ℂ) ^ (k + 1) * liouvilleExpTail z +
        C * ((r : ℂ) ^ (k + 1) * liouvilleWeightTransform k z) := by
    have hq' : q r = Gamma ((1 / 2 + r : ℝ) : ℂ) * zetaResidueUnit (1 + 2 * (r : ℂ)) /
        (2 * zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) := rfl
    rw [hq']
    generalize Gamma ((1 / 2 + r : ℝ) : ℂ) = Gw at hid ⊢
    generalize zetaResidueUnit (1 + 2 * (r : ℂ)) = Z1 at hid ⊢
    generalize hZw : zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ) = Zw at hid hZ ⊢
    generalize complexLaplace (liouvilleExpMeasurePow k C) z = CL at hid ⊢
    generalize liouvilleExpTail z = E at hid ⊢
    generalize liouvilleWeightTransform k z = W at hid ⊢
    generalize hR : (r : ℂ) = R at hid hrc ⊢
    have hden : 2 * R * Zw ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hrc) hZ
    have h' := eq_div_of_mul_eq hden hid
    have hCL : CL = Gw * Z1 / (2 * R * Zw) - E + (C : ℂ) * W := by linear_combination h'
    rw [hCL]
    field_simp
    ring
  rw [complexLaplace_ofReal] at hL
  have hLr := congrArg Complex.re hL
  simp only [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at hLr
  have hrk : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1'.le
  have hrk1 : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0.le hr1'.le
  have hqr : r ^ k * (q r).re ≤ ‖q 0‖ + 1 := by
    have h := (Complex.re_le_norm (q r)).trans h1.le
    have hq0 : 0 ≤ ‖q 0‖ + 1 := by positivity
    by_cases hqre : 0 ≤ (q r).re
    · calc r ^ k * (q r).re ≤ 1 * (q r).re := mul_le_mul_of_nonneg_right hrk hqre
        _ ≤ ‖q 0‖ + 1 := by linarith
    · push Not at hqre
      have : r ^ k * (q r).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hqre.le
      linarith
  have hEr : -(r ^ (k + 1) * (liouvilleExpTail z).re) ≤
      ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1 := by
    have habs : |(liouvilleExpTail z).re| ≤ ‖liouvilleExpTail z‖ := Complex.abs_re_le_norm _
    have h2' : ‖liouvilleExpTail z‖ < ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1 := h2
    have hrabs : r ^ (k + 1) * |(liouvilleExpTail z).re| ≤ |(liouvilleExpTail z).re| :=
      mul_le_of_le_one_left (abs_nonneg _) hrk1
    have := neg_abs_le (liouvilleExpTail z).re
    have : -(r ^ (k + 1) * (liouvilleExpTail z).re) ≤ r ^ (k + 1) * |(liouvilleExpTail z).re| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    linarith
  have hWr : r ^ (k + 1) * (liouvilleWeightTransform k z).re ≤ Kw := by
    have hW := norm_liouvilleWeightTransform_le k z
    have hzre' : z.re = -1 / 2 + r := by simp [hz]
    rw [hzre'] at hW
    have hW2 := (Complex.re_le_norm _).trans (hW.trans (laplaceReal_liouvilleWeightMeasure_le k hr0))
    have hmul := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ r ^ (k + 1))
    have e : r ^ (k + 1) * (1 / r + k.factorial * 2 ^ (k + 1) / r ^ (k + 1)) =
        r ^ k + k.factorial * 2 ^ (k + 1) := by
      field_simp; ring
    rw [e] at hmul
    rw [hKw]
    linarith
  have hCW := mul_le_mul_of_nonneg_left hWr hC0
  linarith

/-- **A one-sided bound `J ≥ -C₀ w_k` caps the order of every critical zero at `k + 1`.** -/
theorem liouvilleExpPow_order_le {k : ℕ} {C₀ C : ℝ} (hC : C₀ + 1 ≤ C) (hC0 : 0 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) {m : ℕ}
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G ρ)
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z) : m ≤ k + 1 := by
  by_contra hm
  push Not at hm
  obtain ⟨B, hB⟩ := exists_bound_pow_mul_laplaceReal hC hC0 hg
  have h2ρ : 2 * ρ ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hρim this
  have hZ2 : zetaResidueUnit (2 * ρ) ≠ 0 := by
    have hre : (2 * ρ).re = 1 := by simp [hρre]
    rw [zetaResidueUnit, Function.update_of_ne h2ρ]
    exact mul_ne_zero (sub_ne_zero.mpr h2ρ) (riemannZeta_ne_zero_of_one_le_re hre.ge)
  have hGam : Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hρre]; norm_num)
  set A₀ : ℝ := ‖Gamma ρ * zetaResidueUnit (2 * ρ)‖ with hA₀
  have hA₀pos : 0 < A₀ := norm_pos_iff.mpr (mul_ne_zero hGam hZ2)
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hLt : Tendsto (fun r : ℝ => ‖Gamma (ρ + r) * zetaResidueUnit (2 * (ρ + r))‖) (𝓝[>] 0)
      (𝓝 A₀) := by
    have hc : ContinuousAt (fun w : ℂ => Gamma w * zetaResidueUnit (2 * w)) ρ :=
      ((analyticAt_Gamma_of_pos_re (by rw [hρre]; norm_num)).mul
        ((analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id))).continuousAt
    exact (hc.tendsto.comp htend).norm
  set K₁ : ℝ := ‖liouvilleExpTail (ρ - 1)‖ + 1 with hK₁
  have hEc : ContinuousAt liouvilleExpTail (ρ - 1) :=
    differentiable_liouvilleExpTail.continuous.continuousAt
  have hEt : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖liouvilleExpTail (ρ - 1 + r)‖ ≤ K₁ := by
    have h' : Tendsto (fun r : ℝ => ρ - 1 + r) (𝓝[>] (0 : ℝ)) (𝓝 (ρ - 1)) := by
      have := htend.sub_const 1
      simpa [sub_add_eq_add_sub] using this
    exact (h'.eventually (hEc.norm.eventually (gt_mem_nhds (lt_add_one _)))).mono fun r h => h.le
  set K₂ : ℝ := ‖2 * ρ - 1‖ + 1 with hK₂
  set K₃ : ℝ := ‖G ρ‖ + 1 with hK₃
  set Kw : ℝ := 1 + k.factorial * 2 ^ (k + 1) with hKw
  set B' : ℝ := |B| + K₁ + C * Kw with hB'
  have hR : Tendsto (fun r : ℝ => r ^ (m - (k + 1)) * (B' * (K₂ * K₃))) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r ^ (m - (k + 1)) * (B' * (K₂ * K₃))) (𝓝 (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ (m - (k + 1)) * (B' * (K₂ * K₃)))) :=
      ((continuous_pow _).mul continuous_const).tendsto 0
    rw [zero_pow (by omega), zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hfac' := htend.eventually hfac
  have hGc : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖G (ρ + r)‖ ≤ K₃ :=
    (htend.eventually (hGan.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _)))).mono
      fun r h => h.le
  have h2c : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖2 * (ρ + r) - 1‖ ≤ K₂ :=
    (htend.eventually (((continuous_const.mul continuous_id).sub
      continuous_const).norm.continuousAt (x := ρ) |>.eventually
        (gt_mem_nhds (lt_add_one _)))).mono fun r h => h.le
  have hle : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖Gamma (ρ + r) * zetaResidueUnit (2 * (ρ + r))‖ ≤
      r ^ (m - (k + 1)) * (B' * (K₂ * K₃)) := by
    filter_upwards [hfac', hGc, h2c, hEt, hB, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with r hr hG hr2 hE hb hr0 hr1
    have hr0' : 0 < r := hr0
    have hr1' : r < 1 := hr1
    set z : ℂ := ρ - 1 + r with hz
    have hzre : -1 / 2 < z.re := by simp [hz, hρre]; linarith
    have hid := liouvilleExpPow_continuation_identity hC hg hzre
    have e1 : z + 1 = ρ + r := by rw [hz]; ring
    have e2 : 2 * z + 2 = 2 * (ρ + r) := by rw [hz]; ring
    have e3 : 2 * z + 1 = 2 * (ρ + r) - 1 := by rw [hz]; ring
    rw [e1, e2, e3, hr, show ρ + (r : ℂ) - ρ = (r : ℂ) by ring, smul_eq_mul] at hid
    set H : ℂ := complexLaplace (liouvilleExpMeasurePow k C) z + liouvilleExpTail z -
      C * liouvilleWeightTransform k z with hH
    have hnorm := congrArg norm hid
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0'] at hnorm
    have hzre' : z.re = -1 / 2 + r := by simp [hz, hρre]; ring
    have hCL : ‖complexLaplace (liouvilleExpMeasurePow k C) z‖ ≤
        laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) := by
      have := norm_complexLaplace_le (liouvilleExpMeasurePow k C) z
      rw [hzre'] at this
      exact this
    have hWz : ‖(C : ℂ) * liouvilleWeightTransform k z‖ ≤
        C * (1 / r + k.factorial * 2 ^ (k + 1) / r ^ (k + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC0]
      refine mul_le_mul_of_nonneg_left ?_ hC0
      have := norm_liouvilleWeightTransform_le k z
      rw [hzre'] at this
      exact this.trans (laplaceReal_liouvilleWeightMeasure_le k hr0')
    have hEz : ‖liouvilleExpTail z‖ ≤ K₁ := by rw [hz]; exact hE
    have hrk1 : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0'.le hr1'.le
    have hrk : r ^ k ≤ 1 := pow_le_one₀ hr0'.le hr1'.le
    have hHle : r ^ (k + 1) * ‖H‖ ≤ B' := by
      have h1 : ‖H‖ ≤ laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) + K₁ +
          C * (1 / r + k.factorial * 2 ^ (k + 1) / r ^ (k + 1)) := by
        have := norm_sub_le (complexLaplace (liouvilleExpMeasurePow k C) z + liouvilleExpTail z)
          ((C : ℂ) * liouvilleWeightTransform k z)
        have := norm_add_le (complexLaplace (liouvilleExpMeasurePow k C) z) (liouvilleExpTail z)
        rw [hH]; linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ r ^ (k + 1))
      have e : r ^ (k + 1) * (laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) + K₁ +
          C * (1 / r + k.factorial * 2 ^ (k + 1) / r ^ (k + 1))) =
          r ^ (k + 1) * laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) +
            r ^ (k + 1) * K₁ + C * (r ^ k + k.factorial * 2 ^ (k + 1)) := by
        field_simp; ring
      rw [e] at h2
      have h3 : r ^ (k + 1) * laplaceReal (liouvilleExpMeasurePow k C) (-1 / 2 + r) ≤ |B| :=
        hb.trans (le_abs_self B)
      have h4 : r ^ (k + 1) * K₁ ≤ K₁ := mul_le_of_le_one_left (by positivity) hrk1
      have h5 : C * (r ^ k + k.factorial * 2 ^ (k + 1)) ≤ C * Kw := by
        rw [hKw]; exact mul_le_mul_of_nonneg_left (by linarith) hC0
      rw [hB']
      linarith
    have hpow : r ^ m = r ^ (m - (k + 1)) * r ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [← hnorm, hpow]
    have hK₂0 : 0 ≤ K₂ := by positivity
    have hK₃0 : 0 ≤ K₃ := by positivity
    calc ‖H‖ * (‖2 * (ρ + r) - 1‖ * (r ^ (m - (k + 1)) * r ^ (k + 1) * ‖G (ρ + r)‖))
        = r ^ (m - (k + 1)) * ((r ^ (k + 1) * ‖H‖) * (‖2 * (ρ + r) - 1‖ * ‖G (ρ + r)‖)) := by
          ring
      _ ≤ r ^ (m - (k + 1)) * (B' * (K₂ * K₃)) := by gcongr
  have := le_of_tendsto_of_tendsto hLt hR hle
  linarith

/-! ## The statement in the variable `t` -/

theorem exists_liouvilleExpLog_lower_pow {k : ℕ} {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ →
      -(C * Real.sqrt t * (1 + Real.log (1 / t) ^ k)) ≤ liouvilleExpSum t) :
    ∃ C₀ : ℝ, ∀ u, 0 < u → -(C₀ * liouvilleLogPowWeight k u) ≤ liouvilleExpLog u := by
  set B : ℝ := 1 + |Real.log t₀| with hB
  refine ⟨max C 0 + B / Real.sqrt t₀, fun u hu => ?_⟩
  set t := Real.exp (-u) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsq : Real.sqrt t = Real.exp (-u / 2) := by
    rw [ht, show Real.exp (-u) = Real.exp (-u / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hlog : Real.log (1 / t) = u := by rw [ht, one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
  have hw : liouvilleLogPowWeight k u = Real.sqrt t * (1 + Real.log (1 / t) ^ k) := by
    rw [hsq, hlog]; rfl
  have hw0 : 0 ≤ 1 + Real.log (1 / t) ^ k := by rw [hlog]; positivity
  have hsq0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hBn : 0 ≤ B := by positivity
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  unfold liouvilleExpLog
  rw [← ht, hw]
  have hW0 : 0 ≤ Real.sqrt t * (1 + Real.log (1 / t) ^ k) := mul_nonneg hst hw0
  rcases le_or_gt t t₀ with htt | htt
  · have h1 := h t ht0 htt
    have h2 : -(max C 0 * (Real.sqrt t * (1 + Real.log (1 / t) ^ k))) ≤
        -(C * Real.sqrt t * (1 + Real.log (1 / t) ^ k)) := by
      have := mul_le_mul_of_nonneg_right (le_max_left C 0) hW0; nlinarith
    have h3 : 0 ≤ B / Real.sqrt t₀ * (Real.sqrt t * (1 + Real.log (1 / t) ^ k)) := by positivity
    nlinarith
  · have hJ := abs_liouvilleExpSum_le_small ht0 ht1
    have hlog' : Real.log (1 / t) ≤ |Real.log t₀| := by
      rw [one_div, Real.log_inv]
      have := Real.log_le_log ht₀ htt.le
      linarith [neg_abs_le (Real.log t₀), le_abs_self (Real.log t₀)]
    have hJ' : -B ≤ liouvilleExpSum t := by
      have := neg_abs_le (liouvilleExpSum t); rw [hB]; linarith
    have h4 : B ≤ B / Real.sqrt t₀ * (Real.sqrt t * (1 + Real.log (1 / t) ^ k)) := by
      have hge : Real.sqrt t₀ ≤ Real.sqrt t * (1 + Real.log (1 / t) ^ k) := by
        have h1 : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt htt.le
        have h2 : 1 ≤ 1 + Real.log (1 / t) ^ k := by rw [hlog]; have := pow_nonneg hu.le k; linarith
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hsq0]
      exact mul_le_mul_of_nonneg_left hge hBn
    have h5 : 0 ≤ max C 0 * (Real.sqrt t * (1 + Real.log (1 / t) ^ k)) :=
      mul_nonneg (le_max_right C 0) hW0
    nlinarith

/-- **A one-sided `√t log^k` bound for the exponential Liouville sum implies RH.**  If
`Σ λ(n) e^{-nt}/n ≥ -C√t(1 + log(1/t)^k)` for `0 < t ≤ t₀`, then RH holds. -/
theorem riemannHypothesis_of_liouvilleExpSum_lower_logPow {k : ℕ} {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ →
      -(C * Real.sqrt t * (1 + Real.log (1 / t) ^ k)) ≤ liouvilleExpSum t) :
    RiemannHypothesis := by
  obtain ⟨C₀, hg⟩ := exists_liouvilleExpLog_lower_pow ht₀ h
  exact riemannHypothesis_of_liouvilleExpLog_lower_pow hg

/-- **… and caps the order of every critical zero at `k + 1`.**  If
`Σ λ(n) e^{-nt}/n ≥ -C√t(1 + log(1/t)^k)` for `0 < t ≤ t₀`, then `ζ` vanishes to order at most
`k + 1` at every point `ρ` with `Re ρ = ½`, `Im ρ ≠ 0`. -/
theorem le_of_liouvilleExpSum_lower_logPow {k : ℕ} {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ →
      -(C * Real.sqrt t * (1 + Real.log (1 / t) ^ k)) ≤ liouvilleExpSum t)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) {m : ℕ}
    (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) : m ≤ k + 1 := by
  obtain ⟨C₀, hg⟩ := exists_liouvilleExpLog_lower_pow ht₀ h
  have hρ1 : ρ ≠ 1 := fun e => by rw [e] at hρre; norm_num at hρre
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt (analyticOn_riemannZeta ρ hρ1)).mp hord
  have hfac' : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • ((z - 1) * g z) := by
    filter_upwards [hfac, zetaResidueUnit_eventuallyEq hρ1] with z hz hZ
    rw [hZ, hz, smul_eq_mul, smul_eq_mul]
    ring
  exact liouvilleExpPow_order_le (C := max C₀ 0 + 1) (by linarith [le_max_left C₀ 0])
    (by positivity) hg hρre hρim ((analyticAt_id.sub analyticAt_const).mul hgan) hfac'

end

end RHTower
