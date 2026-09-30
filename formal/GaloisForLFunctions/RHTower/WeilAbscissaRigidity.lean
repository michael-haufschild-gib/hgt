import GaloisForLFunctions.RHTower.WeilAbscissaScaleBounds

/-!
# Weil-cone rigidity for deviations of absolute abscissa below one

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential_of_rpow_summable`). Let `v : ℕ → ℝ`
with `v(0) = v(1) = 0` and `|v(n)| ≤ 2 log n + A`, and suppose `Σ_n |v(n)| n^{−a} < ∞` for some
`0 < a < 1/2`. If `−ψ_v` is positive definite, then `v = 0`.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable`). A full-cone Weil-positive
`lam` with `Σ_n |lam(n) − Λ(n)| n^{−σ} < ∞` for some `σ < 1` equals `Λ`. In other words, the
Dirichlet series of the deviation of any second point of the Weil cone has absolute abscissa at
least one.

**Proof.** Fix `n₀` and the truncation `P = P_y`, and use the `|ζ|²` notch with the Gaussian mixture
`Ω_L` of notch windows instead of a single window.
* The mixed test is holomorphic in `|Im z| < 1/2`, so the pairing inequality
  `Σ_n v(n) Re M_Ω(log n) ≤ 0` needs only `Σ |v(n)| n^{−c} < ∞` with `c = (a + 1/2)/2`.
* The mixed moment satisfies `‖M_Ω(log n)‖ ≤ C (1 + L²) n^{−c}`. This disposes of `n > N₁`,
  `N₁ ≈ (1 + L)^M`.
* For `n ≤ N₁` the mixed moment is a scale integral of notch moments `M_u`. At scale `u` the
  decaying envelope with `δ = u^{−(1/2+a)}` bounds the remainder by `2u n^{−a}` plus terms uniform
  in `n` that decay in `u`.
* Integrating over the scale, the main term `Y_F e_P ∫ ρ_L log u ≍ Y_F e_P log L` exceeds the
  bounded error unless `Y ≤ 0`.
* The fibre limit of MUST-571 then gives `v(n₀) = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## Pointwise majorants of the scale error -/

theorem div_rpow_pow_le {u η : ℝ} (hu : 1 ≤ u) {K M : ℕ} (hK : (M : ℝ) + 2 ≤ η * K) :
    u / (u ^ η) ^ K ≤ (u ^ (M + 1))⁻¹ := by
  have hu0 : 0 < u := by linarith
  have h1 : (u ^ η) ^ K = u ^ (η * K) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
  have h2 : u ^ (M + 2) ≤ u ^ (η * K) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu (by push_cast; linarith)
  rw [h1, div_le_iff₀ (Real.rpow_pos_of_pos hu0 _), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc u * u ^ (M + 1) = u ^ (M + 2) := by ring
    _ ≤ u ^ (η * K) := h2

theorem mul_exp_neg_sq_le (u : ℝ) :
    u * Real.exp (-(u ^ 2) / 32) ≤ 8 * Real.exp (-(u ^ 2 / 64)) := by
  have h1 : u ≤ 8 * Real.exp (u ^ 2 / 64) := by
    have := Real.add_one_le_exp (u ^ 2 / 64)
    nlinarith [sq_nonneg (u / 8 - 1)]
  have h2 : Real.exp (-(u ^ 2) / 32) = Real.exp (-(u ^ 2 / 64)) * Real.exp (-(u ^ 2 / 64)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : u * Real.exp (-(u ^ 2 / 64)) ≤ 8 := by
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(u ^ 2 / 64))).le
    rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

/-- **Gaussian envelope of a polynomially small scale weight**: for `u > 16`,
`ρ_L(u) u^{−(M+1)} ≤ ((L/2)^{−(M+1)} + e^{−L²/8}) e^{−(u−L)²/2}`. -/
theorem scaleWeight_mul_inv_pow_le {L : ℝ} (hL : 2 ≤ L) (M : ℕ) {u : ℝ} (hu : 16 < u) :
    scaleWeight L u * (u ^ (M + 1))⁻¹ ≤
      (((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * Real.exp (-((u - L) ^ 2 / 2)) := by
  have hu1 : 1 ≤ u := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 0 < L / 2 := by linarith
  set G := Real.exp (-((u - L) ^ 2 / 2)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hρ : scaleWeight L u ≤ G := scaleWeight_le_half L u
  have hA0 : 0 ≤ (u ^ (M + 1))⁻¹ := by positivity
  rcases le_or_gt (L / 2) u with hbig | hsmall
  · have h1 : (u ^ (M + 1))⁻¹ ≤ ((L / 2) ^ (M + 1))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hL2.le hbig _)
    calc scaleWeight L u * (u ^ (M + 1))⁻¹ ≤ G * ((L / 2) ^ (M + 1))⁻¹ :=
          mul_le_mul hρ h1 hA0 hG0.le
      _ ≤ _ := by
          have := Real.exp_pos (-(L ^ 2 / 8))
          nlinarith
  · have h1 : (u ^ (M + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hu1)
    have h2 := scaleWeight_le_of_le_half hL0 hsmall.le
    calc scaleWeight L u * (u ^ (M + 1))⁻¹
        ≤ (Real.exp (-(L ^ 2 / 8)) * G) * 1 := mul_le_mul h2 h1 hA0 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ ((L / 2) ^ (M + 1))⁻¹ * G := by positivity
          nlinarith

/-- The scale error `Σ_{n∈F} |v(n)| w_u(n)`. -/
def errSum (v : ℕ → ℝ) (F : Finset ℕ) (a : ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ F, |v n| * errWeight a K u n

/-- The Gaussian envelope constant of the scale error. -/
def errConst (SF TF L : ℝ) (M : ℕ) : ℝ :=
  2 * SF + TF * (((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8)) +
    8 * Real.exp (-(L ^ 2 / 256)))

theorem errSum_eq (v : ℕ → ℝ) (F : Finset ℕ) (a : ℝ) (K : ℕ) {u : ℝ} (hu : 0 < u) :
    scaleWeight L u / u * errSum v F a K u = scaleWeight L u *
      (2 * ∑ n ∈ F, |v n| * (n : ℝ) ^ (-a) + (∑ n ∈ F, |v n|) *
        (u / (u ^ (1 / 2 - a)) ^ K + u * Real.exp (-(u ^ 2) / 32))) := by
  unfold errSum errWeight
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp
  ring

/-- **Pointwise Gaussian envelope of the scale error** on `u > 16`. -/
theorem scaleWeight_div_mul_errSum_le {L : ℝ} (hL : 2 ≤ L) (v : ℕ → ℝ) (F : Finset ℕ)
    {a : ℝ} {K M : ℕ} (hK : (M : ℝ) + 2 ≤ (1 / 2 - a) * K) {u : ℝ}
    (hu : 16 < u) :
    scaleWeight L u / u * errSum v F a K u ≤
      errConst (∑ n ∈ F, |v n| * (n : ℝ) ^ (-a)) (∑ n ∈ F, |v n|) L M *
        Real.exp (-((u - L) ^ 2 / 2)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hL0 : 0 ≤ L := by linarith
  rw [errSum_eq v F a K hu0]
  set SF := ∑ n ∈ F, |v n| * (n : ℝ) ^ (-a) with hSF
  set TF := ∑ n ∈ F, |v n| with hTF
  have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun n _ => by positivity
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => abs_nonneg _
  set G := Real.exp (-((u - L) ^ 2 / 2)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hρ : scaleWeight L u ≤ G := scaleWeight_le_half L u
  have hρ0 := scaleWeight_pos L u
  have hA : u / (u ^ (1 / 2 - a)) ^ K ≤ (u ^ (M + 1))⁻¹ := div_rpow_pow_le hu1 hK
  have hB := mul_exp_neg_sq_le u
  have hL2 : 0 < L / 2 := by linarith
  -- the two regimes of the scale
  have hA' : scaleWeight L u * (u / (u ^ (1 / 2 - a)) ^ K) ≤
      (((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G :=
    (mul_le_mul_of_nonneg_left hA hρ0.le).trans (scaleWeight_mul_inv_pow_le hL M hu)
  have hB' : scaleWeight L u * (u * Real.exp (-(u ^ 2) / 32)) ≤
      8 * Real.exp (-(L ^ 2 / 256)) * G := by
    have hB0 : 0 ≤ u * Real.exp (-(u ^ 2) / 32) := by positivity
    rcases le_or_gt (L / 2) u with hbig | hsmall
    · have h1 : Real.exp (-(u ^ 2 / 64)) ≤ Real.exp (-(L ^ 2 / 256)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc scaleWeight L u * (u * Real.exp (-(u ^ 2) / 32)) ≤ G * (8 * Real.exp (-(L ^ 2 / 256))) :=
            mul_le_mul hρ (hB.trans (by linarith)) hB0 hG0.le
        _ = _ := by ring
    · have h2 := scaleWeight_le_of_le_half hL0 hsmall.le
      have h3 : Real.exp (-(u ^ 2 / 64)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h4 : Real.exp (-(L ^ 2 / 8)) ≤ Real.exp (-(L ^ 2 / 256)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc scaleWeight L u * (u * Real.exp (-(u ^ 2) / 32))
          ≤ (Real.exp (-(L ^ 2 / 8)) * G) * 8 := mul_le_mul h2 (hB.trans (by linarith)) hB0
            (by positivity)
        _ ≤ (Real.exp (-(L ^ 2 / 256)) * G) * 8 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hG0.le) (by norm_num)
        _ = _ := by ring
  unfold errConst
  calc scaleWeight L u * (2 * SF + TF * (u / (u ^ (1 / 2 - a)) ^ K +
        u * Real.exp (-(u ^ 2) / 32)))
      = 2 * SF * scaleWeight L u + TF * (scaleWeight L u * (u / (u ^ (1 / 2 - a)) ^ K)) +
          TF * (scaleWeight L u * (u * Real.exp (-(u ^ 2) / 32))) := by ring
    _ ≤ 2 * SF * G + TF * ((((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G) +
          TF * (8 * Real.exp (-(L ^ 2 / 256)) * G) := by
        gcongr
    _ = _ := by ring

theorem continuousOn_errSum (v : ℕ → ℝ) (F : Finset ℕ) (a : ℝ) (K : ℕ) :
    Measurable (errSum v F a K) := by
  unfold errSum errWeight
  fun_prop

/-- **The scale error integral**: `∫_{u>16} ρ_L(u) u^{−1} Σ_{n∈F}|v(n)| w_u(n) du ≤ E ∫ e^{−w²/2}`. -/
theorem setIntegral_errSum_le {L : ℝ} (hL : 2 ≤ L) (v : ℕ → ℝ) (F : Finset ℕ) {a : ℝ}
    {K M : ℕ} (hK : (M : ℝ) + 2 ≤ (1 / 2 - a) * K) :
    IntegrableOn (fun u => scaleWeight L u / u * errSum v F a K u) (Ioi 16) ∧
      ∫ u in Ioi 16, scaleWeight L u / u * errSum v F a K u ≤
        errConst (∑ n ∈ F, |v n| * (n : ℝ) ^ (-a)) (∑ n ∈ F, |v n|) L M * gaussHalf := by
  set E := errConst (∑ n ∈ F, |v n| * (n : ℝ) ^ (-a)) (∑ n ∈ F, |v n|) L M with hE
  have hint : IntegrableOn (fun u => scaleWeight L u / u * errSum v F a K u) (Ioi 16) := by
    refine ((integrable_gaussShift L).const_mul E).integrableOn.mono' ?_ ?_
    · exact (((Real.continuous_exp.comp (by fun_prop)).measurable.div measurable_id).mul
        (continuousOn_errSum v F a K)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu16 : (16 : ℝ) < u := hu
      have hnn : 0 ≤ scaleWeight L u / u * errSum v F a K u :=
        mul_nonneg (div_pos (scaleWeight_pos L u) (by linarith)).le
          (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _)
            (errWeight_nonneg a K (by linarith) n))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact scaleWeight_div_mul_errSum_le hL v F hK hu16
  refine ⟨hint, ?_⟩
  calc ∫ u in Ioi 16, scaleWeight L u / u * errSum v F a K u
      ≤ ∫ u in Ioi 16, E * Real.exp (-((u - L) ^ 2 / 2)) :=
        setIntegral_mono_on hint ((integrable_gaussShift L).const_mul E).integrableOn
          measurableSet_Ioi fun u hu => scaleWeight_div_mul_errSum_le hL v F hK hu
    _ = E * ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ E * gaussHalf := by
        have hE0 : 0 ≤ E := by
          rw [hE, errConst]
          have h1 : 0 ≤ ∑ n ∈ F, |v n| * (n : ℝ) ^ (-a) := Finset.sum_nonneg fun n _ => by positivity
          have h2 : 0 ≤ ∑ n ∈ F, |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
          have h3 : 0 < L / 2 := by linarith
          positivity
        refine mul_le_mul_of_nonneg_left ?_ hE0
        rw [← integral_gaussShift L]
        exact setIntegral_le_integral (integrable_gaussShift L)
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)

/-! ## The notch weight -/

theorem continuous_notchWeight (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) :
    Continuous (notchWeight P ε n₀) := by
  have h := (contDiff_notchWeight P ε n₀ 0).continuous
  have e : notchWeight P ε n₀ = fun t => ((notchWeight P ε n₀ t : ℝ) : ℂ).re := by
    funext t; rw [Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp h

theorem exists_notchWeight_bound (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) :
    ∃ CQ, 0 ≤ CQ ∧ (∀ z : ℂ, |z.im| ≤ 1 → ‖notchWeightC P ε n₀ z‖ ≤ CQ) ∧
      ∀ t, |notchWeight P ε n₀ t| ≤ CQ := by
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_norm_notchWeightC_le P ε n₀
  refine ⟨CQ, hCQ0, hCQ, fun t => ?_⟩
  have h := hCQ t (by simp)
  rwa [notchWeightC_ofReal, Complex.norm_real, Real.norm_eq_abs] at h

/-! ## The finite part of the pairing -/

theorem Ioc_disjoint_Ioi' : Disjoint (Ioc (0 : ℝ) 16) (Ioi 16) :=
  Set.disjoint_left.mpr fun _ hx hx' => by
    have h1 := hx.2
    have h2 : (16 : ℝ) < _ := hx'
    linarith

/-- **The finite part of the mixed pairing, from per-scale bounds.** If at every scale `u ≥ 16` the
paired notch moments over `F` are at least `Y_F e_P Re ∫ ω_u log t − D E(u)`, then the paired mixed
moments are at least `Y_F e_P · 2e^{−1} log(L − 1) − D ∫_{u>16} ρ_L(u) u^{−1} E(u) du`, minus the
small scales `u ≤ 16` and the negative half-line. -/
theorem exists_sum_re_mixMoment_ge_of (hP : ∀ p ∈ P, p.Prime) (ε : ℝ) (n₀ : ℕ) :
    ∃ C₁ C₂, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {v : ℕ → ℝ} (F : Finset ℕ) {L : ℝ}, 32 ≤ L →
      ∀ {D : ℝ} {E : ℝ → ℝ}, 0 ≤ D →
      (∀ u, 16 ≤ u → (∑ n ∈ F, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (logWindow u).re - D * E u ≤
        ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u (notchWeight P ε n₀) (Real.log n)).re) →
      IntegrableOn (fun u => scaleWeight L u / u * E u) (Ioi 16) →
      0 ≤ ∑ n ∈ F, v n * mainWeight P ε n₀ n →
      (∑ n ∈ F, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (2 * Real.exp (-1) * Real.log (L - 1)) -
        D * (∫ u in Ioi 16, scaleWeight L u / u * E u) -
        (∑ n ∈ F, |v n|) * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2)) ≤
      ∑ n ∈ F, v n * (mixMoment L (notchWeight P ε n₀) (Real.log n)).re := by
  obtain ⟨CQ, hCQ0, -, hqb⟩ := exists_notchWeight_bound P ε n₀
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_weightedMoment_le_small hqb
  obtain ⟨CN, hCN0, hCN⟩ := exists_norm_mixMomentNeg_le hqb
  refine ⟨16 * Cs, CN, by positivity, hCN0, fun {v} F {L} hL {D E} hD0 hE hEint hY => ?_⟩
  set q := notchWeight P ε n₀ with hq
  have hqc : Continuous q := continuous_notchWeight P ε n₀
  set eP : ℝ := ∏ p : P, (1 - primeHalf p ^ 2) with heP
  have heP0 : 0 < eP := eulerProduct_pos hP
  set Y : ℝ := ∑ n ∈ F, v n * mainWeight P ε n₀ n with hYdef
  set TF : ℝ := ∑ n ∈ F, |v n| with hTF
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => abs_nonneg _
  set X : ℝ → ℝ := fun u => ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re with hX
  have hL0 : 0 ≤ L := by linarith
  -- the scale split
  have hsplit : ∑ n ∈ F, v n * (mixMoment L q (Real.log n)).re =
      (∫ u in Ioi 0, scaleWeight L u / u * X u) +
        ∑ n ∈ F, v n * (mixMomentNeg L q (Real.log n)).re := by
    rw [← sum_mul_re_integral_scale L hqc hqb v F, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mixMoment_eq L hqc hqb, Complex.add_re, mul_add]
  -- integrability of the scale integrand
  have hXint : IntegrableOn (fun u => scaleWeight L u / u * X u) (Ioi 0) := by
    have e : (fun u => scaleWeight L u / u * X u) = fun u => ∑ n ∈ F, v n *
        (((scaleWeight L u / u : ℝ) : ℂ) * ZetaNotch.weightedMoment u q (Real.log n)).re := by
      funext u
      rw [hX, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.re_ofReal_mul]
      ring
    rw [e]
    refine integrable_finsetSum _ fun n _ => ?_
    have h := (integrableOn_scaleMoment L hqc hqb (Real.log n)).re
    simp only [RCLike.re_to_complex] at h
    exact h.const_mul (v n)
  rw [hsplit, ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 16 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi' measurableSet_Ioi (hXint.mono_set Ioc_subset_Ioi_self)
      (hXint.mono_set (Ioi_subset_Ioi (by norm_num)))]
  -- small scales
  have hsmall : |∫ u in Ioc 0 16, scaleWeight L u / u * X u| ≤
      TF * (16 * Cs * Real.exp (-(L - 16) ^ 2)) := by
    have h := norm_setIntegral_le_of_norm_le_const (s := Ioc (0 : ℝ) 16)
      (f := fun u => scaleWeight L u / u * X u) (C := TF * (Cs * Real.exp (-(L - 16) ^ 2)))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) fun u hu => ?_
    · rw [Real.volume_real_Ioc_of_le (by norm_num), Real.norm_eq_abs] at h
      calc |∫ u in Ioc 0 16, scaleWeight L u / u * X u| ≤
            TF * (Cs * Real.exp (-(L - 16) ^ 2)) * (16 - 0) := h
        _ = TF * (16 * Cs * Real.exp (-(L - 16) ^ 2)) := by ring
    · have hu0 : 0 < u := hu.1
      have hXb : |X u| ≤ TF * (Cs * u) := by
        rw [hX, hTF, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (hCs hu0 hu.2 (Real.log n))) (abs_nonneg _)
      have hρ : scaleWeight L u ≤ Real.exp (-(L - 16) ^ 2) := by
        rw [scaleWeight]
        refine Real.exp_le_exp.mpr ?_
        have : (L - 16) ^ 2 ≤ (u - L) ^ 2 := by nlinarith [hu.2]
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_pos (scaleWeight_pos L u) hu0).le]
      calc scaleWeight L u / u * |X u| ≤ scaleWeight L u / u * (TF * (Cs * u)) :=
            mul_le_mul_of_nonneg_left hXb (div_pos (scaleWeight_pos L u) hu0).le
        _ = TF * Cs * scaleWeight L u := by field_simp
        _ ≤ TF * Cs * Real.exp (-(L - 16) ^ 2) :=
            mul_le_mul_of_nonneg_left hρ (mul_nonneg hTF0 hCs0)
        _ = TF * (Cs * Real.exp (-(L - 16) ^ 2)) := by ring
  -- the negative half-line
  have hneg : |∑ n ∈ F, v n * (mixMomentNeg L q (Real.log n)).re| ≤
      TF * (CN * Real.exp (-L ^ 2)) := by
    rw [hTF, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hCN L hL0 _))
      (abs_nonneg _)
  -- large scales
  have hlarge : Y * eP * (2 * Real.exp (-1) * Real.log (L - 1)) -
      D * (∫ u in Ioi 16, scaleWeight L u / u * E u) ≤
      ∫ u in Ioi 16, scaleWeight L u / u * X u := by
    have hmain := setIntegral_scaleWeight_mul_log_ge (show (18 : ℝ) ≤ L by linarith)
    have hlogi := integrableOn_scaleWeight_mul_log L
    have hpt : ∀ u ∈ Ioi (16 : ℝ), Y * eP * (scaleWeight L u * Real.log u) -
        D * (scaleWeight L u / u * E u) ≤ scaleWeight L u / u * X u := by
      intro u hu
      have hu16 : (16 : ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      have h1 := hE u hu16.le
      have h2 := re_logWindow_ge (show (2 : ℝ) ≤ u by linarith)
      have hYe : 0 ≤ Y * eP := mul_nonneg hY heP0.le
      have h3 : Y * eP * (u * Real.log u) - D * E u ≤ X u := by
        have := mul_le_mul_of_nonneg_left h2 hYe
        linarith
      have hw : 0 ≤ scaleWeight L u / u := (div_pos (scaleWeight_pos L u) hu0).le
      calc Y * eP * (scaleWeight L u * Real.log u) - D * (scaleWeight L u / u * E u)
          = scaleWeight L u / u * (Y * eP * (u * Real.log u) - D * E u) := by
            field_simp
        _ ≤ scaleWeight L u / u * X u := mul_le_mul_of_nonneg_left h3 hw
    have hint := setIntegral_mono_on ((hlogi.const_mul (Y * eP)).sub (hEint.const_mul D))
      (hXint.mono_set (Ioi_subset_Ioi (by norm_num))) measurableSet_Ioi hpt
    simp only [Pi.sub_apply] at hint
    rw [integral_sub (hlogi.const_mul (Y * eP)) (hEint.const_mul D), integral_const_mul,
      integral_const_mul] at hint
    have hYe : 0 ≤ Y * eP := mul_nonneg hY heP0.le
    nlinarith [mul_le_mul_of_nonneg_left hmain hYe]
  have h1 := abs_le.mp hsmall
  have h2 := abs_le.mp hneg
  nlinarith

/-- **The finite part of the mixed pairing.** For `n ∈ F`, the mixed moments are at least the main
term `Y_F e_P · 2e^{−1} log(L − 1)`, minus the Gaussian-envelope scale error, the small scales
`u ≤ 16`, and the negative half-line. -/
theorem exists_sum_re_mixMoment_ge (hP : ∀ p ∈ P, p.Prime) (K : ℕ) (ε : ℝ) {n₀ : ℕ}
    (hn₀ : IsSmoothOver P n₀) {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ D C₁ C₂, 0 ≤ D ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (F : Finset ℕ) {L : ℝ},
      32 ≤ L → ∀ {M : ℕ}, (M : ℝ) + 2 ≤ (1 / 2 - a) * K →
      0 ≤ ∑ n ∈ F, v n * mainWeight P ε n₀ n →
      (∑ n ∈ F, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (2 * Real.exp (-1) * Real.log (L - 1)) -
        D * (errConst (∑ n ∈ F, |v n| * (n : ℝ) ^ (-a)) (∑ n ∈ F, |v n|) L M * gaussHalf) -
        (∑ n ∈ F, |v n|) * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2)) ≤
      ∑ n ∈ F, v n * (mixMoment L (notchWeight P ε n₀) (Real.log n)).re := by
  obtain ⟨D, hD0, hD⟩ := exists_sum_re_weightedMoment_ge hP K ε hn₀ ha0 ha
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ := exists_sum_re_mixMoment_ge_of hP ε n₀
  refine ⟨D, C₁, C₂, hD0, hC₁, hC₂, fun {v} hv0 F {L} hL {M} hK hY => ?_⟩
  obtain ⟨hEint, hE⟩ := setIntegral_errSum_le (show (2 : ℝ) ≤ L by linarith) v F (a := a) hK
  have h := hgen F hL hD0 (E := errSum v F a K) (fun u hu => hD hv0 F hu) hEint hY
  have := mul_le_mul_of_nonneg_left hE hD0
  linarith

/-! ## Truncation bookkeeping -/

section Truncation

variable {v : ℕ → ℝ} {a : ℝ}

theorem rpow_neg_le_of_le {n N : ℕ} (hN : 1 ≤ N) (hnN : N ≤ n) {a c : ℝ} (hac : a ≤ c) :
    (n : ℝ) ^ (-c) ≤ (N : ℝ) ^ (-(c - a)) * (n : ℝ) ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hN hnN)
  have e : (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c - a)) * (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hn0]; ring_nf
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hN0 (by exact_mod_cast hnN) (by linarith)

theorem tsum_shift_le (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a)) (k : ℕ) :
    ∑' i : ℕ, |v (i + k)| * ((i + k : ℕ) : ℝ) ^ (-a) ≤ ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) := by
  rw [← hs.sum_add_tsum_nat_add k]
  have : 0 ≤ ∑ i ∈ Finset.range k, |v i| * (i : ℝ) ^ (-a) :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

/-- The tail beyond `N` against `n^{−c}` gains `N^{−(c−a)}`. -/
theorem tsum_tail_rpow_le (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a)) {c : ℝ} (hac : a ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun i : ℕ => |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c)) ∧
      ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c) ≤
        (N : ℝ) ^ (-(c - a)) * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) := by
  have hs' := (summable_nat_add_iff (N + 1)).mpr hs
  have hpt : ∀ i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c) ≤
      (N : ℝ) ^ (-(c - a)) * (|v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-a)) := by
    intro i
    have h := rpow_neg_le_of_le hN (show N ≤ i + (N + 1) by omega) hac
    calc |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c)
        ≤ |v (i + (N + 1))| * ((N : ℝ) ^ (-(c - a)) * ((i + (N + 1) : ℕ) : ℝ) ^ (-a)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := by ring
  have hsum : Summable (fun i : ℕ => |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c)) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hpt (hs'.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c)
      ≤ ∑' i : ℕ, (N : ℝ) ^ (-(c - a)) * (|v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-a)) :=
        hsum.tsum_le_tsum hpt (hs'.mul_left _)
    _ = (N : ℝ) ^ (-(c - a)) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-a) :=
        tsum_mul_left
    _ ≤ (N : ℝ) ^ (-(c - a)) * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) :=
        mul_le_mul_of_nonneg_left (tsum_shift_le hs (N + 1)) (by positivity)

/-- The finite masses: `Σ_{n≤N} |v(n)| n^{−a} ≤ S` and `Σ_{n≤N} |v(n)| ≤ N S`. -/
theorem finite_masses_le (hv0 : v 0 = 0) (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a))
    (ha1 : a ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), |v n| * (n : ℝ) ^ (-a) ≤ ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) ∧
      ∑ n ∈ Finset.range (N + 1), |v n| ≤ N * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) := by
  have h1 : ∑ n ∈ Finset.range (N + 1), |v n| * (n : ℝ) ^ (-a) ≤ ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) :=
    hs.sum_le_tsum _ fun n _ => by positivity
  refine ⟨h1, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ n ∈ Finset.range (N + 1), |v n| ≤ N * (|v n| * (n : ℝ) ^ (-a)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hv0, abs_zero]; simp
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnN : (n : ℝ) ≤ N := by
      have := Finset.mem_range.mp hn
      exact_mod_cast (by omega : n ≤ N)
    have hna : (n : ℝ) ^ a ≤ N := by
      calc (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) ha1
        _ = n := Real.rpow_one _
        _ ≤ N := hnN
    have e : |v n| = |v n| * (n : ℝ) ^ (-a) * (n : ℝ) ^ a := by
      rw [mul_assoc, ← Real.rpow_add hn0', neg_add_cancel, Real.rpow_zero, mul_one]
    have : 0 ≤ |v n| * (n : ℝ) ^ (-a) := by positivity
    calc |v n| = |v n| * (n : ℝ) ^ (-a) * (n : ℝ) ^ a := e
      _ ≤ |v n| * (n : ℝ) ^ (-a) * N := mul_le_mul_of_nonneg_left hna this
      _ = N * (|v n| * (n : ℝ) ^ (-a)) := by ring
  calc ∑ n ∈ Finset.range (N + 1), |v n| ≤ ∑ n ∈ Finset.range (N + 1),
        N * (|v n| * (n : ℝ) ^ (-a)) := Finset.sum_le_sum hpt
    _ = N * ∑ n ∈ Finset.range (N + 1), |v n| * (n : ℝ) ^ (-a) := by rw [Finset.mul_sum]
    _ ≤ N * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) := mul_le_mul_of_nonneg_left h1 hN0.le

end Truncation

/-! ## The two tails -/

section Tails

variable {v : ℕ → ℝ} {a : ℝ}

theorem inv_sqrt_le_rpow {n : ℕ} {c : ℝ} (hc : c ≤ 1 / 2) : (Real.sqrt n)⁻¹ ≤ (n : ℝ) ^ (-c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero]
    exact Real.rpow_nonneg le_rfl _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- **The pairing tail**: if `‖M(log n)‖ ≤ B n^{−c}`, the pairing sum is summable and its part beyond
`N` is at least `−B N^{−(c−a)} S`. -/
theorem pairing_tail (hv0 : v 0 = 0) (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a)) {c : ℝ}
    (hac : a ≤ c) {B : ℝ} (hB : 0 ≤ B) {m : ℕ → ℝ} (hm : ∀ n : ℕ, 1 ≤ n → |m n| ≤ B * (n : ℝ) ^ (-c))
    {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n => v n * m n) ∧
      ∑ n ∈ Finset.range (N + 1), v n * m n -
        B * ((N : ℝ) ^ (-(c - a)) * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a)) ≤ ∑' n, v n * m n := by
  have hbound : ∀ n : ℕ, |v n * m n| ≤ B * (|v n| * (n : ℝ) ^ (-c)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    rw [abs_mul]
    calc |v n| * |m n| ≤ |v n| * (B * (n : ℝ) ^ (-c)) := mul_le_mul_of_nonneg_left (hm n hn) (abs_nonneg _)
      _ = B * (|v n| * (n : ℝ) ^ (-c)) := by ring
  have hsc : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-c) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by linarith)) (abs_nonneg _)
  have hf : Summable fun n => v n * m n :=
    Summable.of_norm_bounded (hsc.mul_left B) fun n => by rw [Real.norm_eq_abs]; exact hbound n
  refine ⟨hf, ?_⟩
  rw [← hf.sum_add_tsum_nat_add (N + 1)]
  obtain ⟨htail_s, htail⟩ := tsum_tail_rpow_le hs hac hN
  have hs2 : Summable fun i : ℕ => |v (i + (N + 1)) * m (i + (N + 1))| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => hbound (i + (N + 1)))
      (htail_s.mul_left B)
  have habs : |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))| ≤
      B * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c) :=
    calc |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))|
        ≤ ∑' i : ℕ, |v (i + (N + 1)) * m (i + (N + 1))| := abs_tsum_le_tsum_abs hs2
      _ ≤ ∑' i : ℕ, B * (|v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c)) :=
          hs2.tsum_le_tsum (fun i => hbound _) (htail_s.mul_left B)
      _ = B * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-c) := tsum_mul_left
  have h1 := abs_le.mp habs
  have h2 := mul_le_mul_of_nonneg_left htail hB
  linarith [h1.1]

end Tails

/-! ## The main-term tail and the scale constants -/

/-- **The main-term tail**: `Σ_n v(n) mainWeight(n) ≤ Σ_{n≤N} v(n) mainWeight(n) + 3√n₀ N^{−(c−a)} S`. -/
theorem mainWeight_tail {v : ℕ → ℝ} {a : ℝ} (hv0 : v 0 = 0)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a)) {c : ℝ} (hac : a ≤ c) (hc : c ≤ 1 / 2)
    {ε : ℝ} (hε : |ε| ≤ 1) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) {N : ℕ} (hN : 1 ≤ N) :
    ∑' n, v n * mainWeight P ε n₀ n ≤ ∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n +
      3 * Real.sqrt n₀ * ((N : ℝ) ^ (-(c - a)) * ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a)) := by
  have hm : ∀ n : ℕ, 1 ≤ n → |-mainWeight P ε n₀ n| ≤ 3 * Real.sqrt n₀ * (n : ℝ) ^ (-c) := by
    intro n hn
    rw [abs_neg]
    refine (abs_mainWeight_le hε hn₀ (by omega)).trans ?_
    exact mul_le_mul_of_nonneg_left (inv_sqrt_le_rpow hc) (by positivity)
  obtain ⟨hf, h⟩ := pairing_tail hv0 hs hac (by positivity) hm hN
  have e1 : ∑' n, v n * -mainWeight P ε n₀ n = -∑' n, v n * mainWeight P ε n₀ n := by
    rw [← tsum_neg]; congr 1; funext n; ring
  have e2 : ∑ n ∈ Finset.range (N + 1), v n * -mainWeight P ε n₀ n =
      -∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n := by
    rw [← Finset.sum_neg_distrib]; congr 1; funext n; ring
  rw [e1, e2] at h
  linarith

theorem one_add_le_three_mul_half {L : ℝ} (hL : 2 ≤ L) : 1 + L ≤ 3 * (L / 2) := by linarith

/-- The truncation length `N = ⌈(1 + L)^M⌉`. -/
theorem truncation_bounds {L : ℝ} (hL : 0 ≤ L) (M : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (hMθ : 2 ≤ (M : ℝ) * θ) :
    1 ≤ ⌈(1 + L) ^ M⌉₊ ∧ (⌈(1 + L) ^ M⌉₊ : ℝ) ≤ 2 * (1 + L) ^ M ∧
      (1 + L ^ 2) * (⌈(1 + L) ^ M⌉₊ : ℝ) ^ (-θ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (1 + L) ^ M := one_le_pow₀ (by linarith)
  have hc := Nat.le_ceil ((1 + L) ^ M)
  have hc' := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + L) ^ M by positivity)
  have hN1 : (1 : ℝ) ≤ (⌈(1 + L) ^ M⌉₊ : ℝ) := h1.trans hc
  refine ⟨by exact_mod_cast hN1, by linarith, ?_⟩
  have hN0 : (0 : ℝ) < (⌈(1 + L) ^ M⌉₊ : ℝ) := by linarith
  have hpow : (1 + L ^ 2) ≤ (⌈(1 + L) ^ M⌉₊ : ℝ) ^ θ := by
    calc 1 + L ^ 2 ≤ (1 + L) ^ (2 : ℝ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
      _ ≤ (1 + L) ^ ((M : ℝ) * θ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hMθ
      _ = ((1 + L) ^ M) ^ θ := by rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
      _ ≤ (⌈(1 + L) ^ M⌉₊ : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) hc hθ.le
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hN0 _)]
  exact hpow

/-- The scale error constant is bounded independently of `L`. -/
theorem errConst_le {L : ℝ} (hL : 32 ≤ L) {M : ℕ} {B : ℝ}
    (hB : ∀ L : ℝ, 0 ≤ L → (1 + L) ^ M * Real.exp (-(L ^ 2 / 256)) ≤ B) {SF TF S : ℝ}
    (hSF : SF ≤ S) (hTF0 : 0 ≤ TF) (hTF : TF ≤ 2 * (1 + L) ^ M * S) (hS : 0 ≤ S) :
    errConst SF TF L M ≤ 2 * S + 2 * 3 ^ M * S + 18 * S * B := by
  have hL0 : 0 ≤ L := by linarith
  have hBL := hB L hL0
  have hL2 : 1 ≤ L / 2 := by linarith
  have hpow : (1 + L) ^ M ≤ 3 ^ M * (L / 2) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (one_add_le_three_mul_half (by linarith)) M
  have hA : TF * ((L / 2) ^ (M + 1))⁻¹ ≤ 2 * 3 ^ M * S := by
    have h1 : (L / 2) ^ M * ((L / 2) ^ (M + 1))⁻¹ ≤ 1 := by
      rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      exact inv_le_one_of_one_le₀ hL2
    calc TF * ((L / 2) ^ (M + 1))⁻¹ ≤ (2 * (3 ^ M * (L / 2) ^ M) * S) * ((L / 2) ^ (M + 1))⁻¹ := by
          refine mul_le_mul_of_nonneg_right (hTF.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hS
      _ = 2 * 3 ^ M * S * ((L / 2) ^ M * ((L / 2) ^ (M + 1))⁻¹) := by ring
      _ ≤ 2 * 3 ^ M * S * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * 3 ^ M * S := mul_one _
  have he1 : Real.exp (-(L ^ 2 / 8)) ≤ Real.exp (-(L ^ 2 / 256)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hG : TF * Real.exp (-(L ^ 2 / 256)) ≤ 2 * S * B := by
    calc TF * Real.exp (-(L ^ 2 / 256)) ≤ (2 * (1 + L) ^ M * S) * Real.exp (-(L ^ 2 / 256)) :=
          mul_le_mul_of_nonneg_right hTF (Real.exp_pos _).le
      _ = 2 * S * ((1 + L) ^ M * Real.exp (-(L ^ 2 / 256))) := by ring
      _ ≤ 2 * S * B := mul_le_mul_of_nonneg_left hBL (by positivity)
  have hG' : TF * Real.exp (-(L ^ 2 / 8)) ≤ 2 * S * B :=
    (mul_le_mul_of_nonneg_left he1 hTF0).trans hG
  unfold errConst
  nlinarith

/-- The small-scale and negative half-line errors are bounded independently of `L`. -/
theorem smallErr_le {L : ℝ} (hL : 32 ≤ L) {M : ℕ} {B : ℝ}
    (hB : ∀ L : ℝ, 0 ≤ L → (1 + L) ^ M * Real.exp (-(L ^ 2 / 256)) ≤ B) {TF S C₁ C₂ : ℝ}
    (hTF0 : 0 ≤ TF) (hTF : TF ≤ 2 * (1 + L) ^ M * S) (hS : 0 ≤ S) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    TF * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2)) ≤ 2 * S * B * (C₁ + C₂) := by
  have hL0 : 0 ≤ L := by linarith
  have hBL := hB L hL0
  have he1 : Real.exp (-(L - 16) ^ 2) ≤ Real.exp (-(L ^ 2 / 256)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (-L ^ 2) ≤ Real.exp (-(L ^ 2 / 256)) := Real.exp_le_exp.mpr (by nlinarith)
  have hG : TF * Real.exp (-(L ^ 2 / 256)) ≤ 2 * S * B := by
    calc TF * Real.exp (-(L ^ 2 / 256)) ≤ (2 * (1 + L) ^ M * S) * Real.exp (-(L ^ 2 / 256)) :=
          mul_le_mul_of_nonneg_right hTF (Real.exp_pos _).le
      _ = 2 * S * ((1 + L) ^ M * Real.exp (-(L ^ 2 / 256))) := by ring
      _ ≤ 2 * S * B := mul_le_mul_of_nonneg_left hBL (by positivity)
  have h1 : TF * Real.exp (-(L - 16) ^ 2) ≤ 2 * S * B := (mul_le_mul_of_nonneg_left he1 hTF0).trans hG
  have h2 : TF * Real.exp (-L ^ 2) ≤ 2 * S * B := (mul_le_mul_of_nonneg_left he2 hTF0).trans hG
  nlinarith [mul_le_mul_of_nonneg_left h1 hC₁, mul_le_mul_of_nonneg_left h2 hC₂]

/-! ## The key inequality -/

theorem summable_rpow_mono {v : ℕ → ℝ} (hv0 : v 0 = 0) {a c : ℝ} (hac : a ≤ c)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a)) :
    Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-c) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hv0]; simp
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (by linarith)) (abs_nonneg _)

theorem rpow_neg_eq_exp_log {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    Real.exp (-(c * Real.log n)) = (n : ℝ) ^ (-c) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  ring_nf

/-- **The key inequality at a fixed truncation.** At every scale `L ≥ 32` the truncated main
functional `Y_F` satisfies `Y ≤ Y_F + 3√n₀ S/(1 + L²)`, and `Y_F e_P 2e^{−1} log(L − 1) ≤ E` when
`Y_F ≥ 0`, with `E` independent of `L`. -/
theorem exists_scale_bound (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) {ε : ℝ}
    (hε : |ε| ≤ 1) {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    ∃ E : ℝ, ∀ L : ℝ, 32 ≤ L → ∃ YF : ℝ,
      ∑' n, v n * mainWeight P ε n₀ n ≤
        YF + 3 * Real.sqrt n₀ * (∑' n : ℕ, |v n| * (n : ℝ) ^ (-a)) / (1 + L ^ 2) ∧
      (0 ≤ YF → YF * (∏ p : P, (1 - primeHalf p ^ 2)) * (2 * Real.exp (-1) * Real.log (L - 1)) ≤
        E) := by
  set S : ℝ := ∑' n : ℕ, |v n| * (n : ℝ) ^ (-a) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  set c : ℝ := (a + 1 / 2) / 2 with hcdef
  have hac : a ≤ c := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hc1 : c < 1 / 2 := by rw [hcdef]; linarith
  set θ : ℝ := c - a with hθdef
  have hθ : 0 < θ := by rw [hθdef, hcdef]; linarith
  set M : ℕ := ⌈2 / θ⌉₊ with hMdef
  have hMθ : 2 ≤ (M : ℝ) * θ := by
    have := Nat.le_ceil (2 / θ)
    rw [← hMdef] at this
    rw [div_le_iff₀ hθ] at this
    linarith
  set K : ℕ := ⌈((M : ℝ) + 2) / (1 / 2 - a)⌉₊ with hKdef
  have hK : (M : ℝ) + 2 ≤ (1 / 2 - a) * K := by
    have := Nat.le_ceil (((M : ℝ) + 2) / (1 / 2 - a))
    rw [← hKdef, div_le_iff₀ (by linarith)] at this
    linarith
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_notchWeight_bound P ε n₀
  have hQb : ∀ z : ℂ, |z.im| ≤ c → ‖notchWeightC P ε n₀ z‖ ≤ CQ := fun z hz =>
    hQb1 z (by linarith)
  obtain ⟨CT, hCT0, hCT⟩ := exists_norm_mixMoment_le hc0.le hc1 (differentiable_notchWeightC P ε n₀)
    hQb (notchWeightC_ofReal P ε n₀)
  obtain ⟨D, C₁, C₂, hD0, hC₁0, hC₂0, hmain⟩ := exists_sum_re_mixMoment_ge hP K ε hn₀ ha0 ha1
  obtain ⟨B, hB0, hB⟩ := exists_pow_mul_exp_neg_le M
  have hsc := summable_rpow_mono hv0 hac hs
  refine ⟨CT * S + D * ((2 * S + 2 * 3 ^ M * S + 18 * S * B) * gaussHalf) +
    2 * S * B * (C₁ + C₂), fun L hL => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hN1, hN2, hN3⟩ := truncation_bounds hL0 M hθ hMθ
  set N : ℕ := ⌈(1 + L) ^ M⌉₊ with hNdef
  have hNθ : (N : ℝ) ^ (-θ) ≤ (1 + L ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity), mul_comm]
    exact hN3
  refine ⟨∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n, ?_, fun hYF => ?_⟩
  · have h := mainWeight_tail hv0 hs hac hc1.le hε hn₀ hN1
    have h2 : 3 * Real.sqrt n₀ * ((N : ℝ) ^ (-(c - a)) * S) ≤
        3 * Real.sqrt n₀ * S / (1 + L ^ 2) := by
      rw [div_eq_mul_inv, mul_assoc (3 * Real.sqrt n₀)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hNθ hS0
    linarith
  · -- the pairing and its tail beyond `N`
    set q := notchWeight P ε n₀ with hq
    have hpair := sum_mul_re_mixMoment_nonpos hv0 hA ha hc0 hc1 hsc hPD L
      (differentiable_notchWeightC P ε n₀) hQb (notchWeightC_ofReal P ε n₀)
      (notchWeight_nonneg P ε n₀)
    have hm : ∀ n : ℕ, 1 ≤ n → |(mixMoment L q (Real.log n)).re| ≤
        (CT * (1 + L ^ 2)) * (n : ℝ) ^ (-c) := by
      intro n hn
      refine (Complex.abs_re_le_norm _).trans ((hCT L hL0 _ (Real.log_natCast_nonneg n)).trans ?_)
      rw [rpow_neg_eq_exp_log hn]
    obtain ⟨-, htail⟩ := pairing_tail hv0 hs hac (by positivity) hm hN1
    have hfin := hmain hv0 (Finset.range (N + 1)) (show (32 : ℝ) ≤ L from hL) hK hYF
    obtain ⟨hSF, hTF⟩ := finite_masses_le hv0 hs (ha1.le.trans (by norm_num)) hN1
    have hTF0 : 0 ≤ ∑ n ∈ Finset.range (N + 1), |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
    have hTF' : ∑ n ∈ Finset.range (N + 1), |v n| ≤ 2 * (1 + L) ^ M * S :=
      hTF.trans (mul_le_mul_of_nonneg_right hN2 hS0)
    have herr := errConst_le hL hB hSF hTF0 hTF' hS0
    have hsmall := smallErr_le hL hB hTF0 hTF' hS0 hC₁0 hC₂0
    rw [← hθdef] at htail
    have hct : CT * (1 + L ^ 2) * ((N : ℝ) ^ (-θ) * S) ≤ CT * S := by
      calc CT * (1 + L ^ 2) * ((N : ℝ) ^ (-θ) * S) = CT * S * ((1 + L ^ 2) * (N : ℝ) ^ (-θ)) := by
            ring
        _ ≤ CT * S * 1 := mul_le_mul_of_nonneg_left hN3 (mul_nonneg hCT0 hS0)
        _ = CT * S := mul_one _
    have hG0 := gaussHalf_nonneg
    have hDerr : D * (errConst (∑ n ∈ Finset.range (N + 1), |v n| * (n : ℝ) ^ (-a))
        (∑ n ∈ Finset.range (N + 1), |v n|) L M * gaussHalf) ≤
        D * ((2 * S + 2 * 3 ^ M * S + 18 * S * B) * gaussHalf) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right herr hG0) hD0
    linarith

/-- **From the scale family to the sign**: if at every scale `L ≥ 32` some truncation `Y_F` has
`Y ≤ Y_F + τ(L)` with `τ(L) → 0`, and `Y_F ≥ 0` forces `Y_F e 2e^{−1} log(L − 1) ≤ E`, then
`Y ≤ 0`. -/
theorem nonpos_of_scale_family_tendsto {Y e E : ℝ} {τ : ℝ → ℝ} (he : 0 < e)
    (hτ : Tendsto τ atTop (𝓝 0))
    (h : ∀ L : ℝ, 32 ≤ L → ∃ YF : ℝ, Y ≤ YF + τ L ∧
      (0 ≤ YF → YF * e * (2 * Real.exp (-1) * Real.log (L - 1)) ≤ E)) :
    Y ≤ 0 := by
  by_contra hY
  push Not at hY
  set k : ℝ := e * (2 * Real.exp (-1)) with hk
  have hk0 : 0 < k := by positivity
  have hev : ∀ᶠ L : ℝ in atTop, 32 ≤ L ∧ τ L ≤ Y / 2 ∧
      Real.exp (2 * |E| / (Y * k)) + 2 ≤ L := by
    filter_upwards [eventually_ge_atTop 32, hτ.eventually_le_const (by linarith : (0 : ℝ) < Y / 2),
      eventually_ge_atTop (Real.exp (2 * |E| / (Y * k)) + 2)] with L h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨L, hL32, hτL, hL2⟩ := hev.exists
  obtain ⟨YF, h1, h2⟩ := h L hL32
  have hYF : Y / 2 ≤ YF := by linarith
  have hlog : 2 * |E| / (Y * k) < Real.log (L - 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hlog0 : 0 < Real.log (L - 1) := Real.log_pos (by linarith)
  have h3 := h2 (by linarith)
  have h4 : Y / 2 * k * Real.log (L - 1) ≤ YF * k * Real.log (L - 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hYF hk0.le) hlog0.le
  have h5 : |E| < Y / 2 * k * Real.log (L - 1) := by
    have hYk : 0 < Y * k := mul_pos hY hk0
    rw [div_lt_iff₀ hYk] at hlog
    nlinarith
  have h6 : YF * k * Real.log (L - 1) = YF * e * (2 * Real.exp (-1) * Real.log (L - 1)) := by
    rw [hk]; ring
  linarith [le_abs_self E]

/-- From the scale family to the sign: `Y ≤ 0`. -/
theorem nonpos_of_scale_family {Y e S₀ E : ℝ} (he : 0 < e)
    (h : ∀ L : ℝ, 32 ≤ L → ∃ YF : ℝ, Y ≤ YF + S₀ / (1 + L ^ 2) ∧
      (0 ≤ YF → YF * e * (2 * Real.exp (-1) * Real.log (L - 1)) ≤ E)) :
    Y ≤ 0 :=
  nonpos_of_scale_family_tendsto he (tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero))) h

/-! ## The theorem -/

/-- **Weil-cone rigidity below the critical abscissa.** If `v(0) = v(1) = 0`,
`|v(n)| ≤ 2 log n + A`, `Σ_n |v(n)| n^{−σ} < ∞` for some `σ < 1/2`, and `−ψ_v` is positive
definite, then `v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential_of_rpow_summable {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {σ : ℝ}
    (hσ : σ < 1 / 2) (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-σ))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  set a : ℝ := max σ (1 / 4) with hadef
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ha1 : a < 1 / 2 := max_lt hσ (by norm_num)
  have hsa : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-a) :=
    summable_rpow_mono hv0 (le_max_left σ (1 / 4)) hs
  have hsq : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹ :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_left (inv_sqrt_le_rpow ha1.le) (abs_nonneg _)) hsa
  refine eq_zero_of_forall_mainWeight_nonpos hv0 hv1 hsq fun y n₀ hn₀2 hy ε hε => ?_
  have hP : ∀ p ∈ primesUpTo y, p.Prime := prime_of_mem_primesUpTo
  have hεabs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨E, hE⟩ := exists_scale_bound hP (isSmoothOver_primesUpTo hn₀2 hy) hεabs hv0 hA ha ha0
    ha1 hsa hPD
  exact nonpos_of_scale_family (eulerProduct_pos hP) hE

/-- The same with `+ψ_v` positive definite. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_rpow_summable {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {σ : ℝ}
    (hσ : σ < 1 / 2) (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-σ))
    (hPD : PositiveDefiniteOnReal fun y => ((RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hneg := eq_zero_of_positiveDefinite_neg_nullPotential_of_rpow_summable (v := fun n => -v n)
    (by simp [hv0]) (by simp [hv1]) hA (fun n => by rw [abs_neg]; exact ha n) hσ
    (by simpa only [abs_neg] using hs)
    (by simpa only [RHTower.WeilRegular.nullPotential_neg, neg_neg] using hPD)
  funext n
  have := congrFun hneg n
  simpa using this

/-- **Corollary (abscissa of a second point of the Weil cone).** A full-cone Weil-positive `lam`
with `Σ_n |lam(n) − Λ(n)| n^{−s} < ∞` for some `s < 1` equals `Λ` on all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {s : ℝ} (hs1 : s < 1)
    (hs : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| * (n : ℝ) ^ (-s)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsv : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(s - 1 / 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    rw [hv, RHTower.WeilExcess.weilDeviation]
    split_ifs with h2
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hn0), Real.sqrt_eq_rpow, div_mul_eq_mul_div,
        div_le_iff₀ (Real.rpow_pos_of_pos hn0 _), mul_assoc, ← Real.rpow_add hn0]
      exact le_of_eq (by ring_nf)
    · rw [abs_zero, zero_mul]
      positivity
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_rpow_summable hv0 hv1 hC0 hC
    (by linarith : s - 1 / 2 < 1 / 2) hsv hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

/-- **Corollary (sub-square-root supports).** If `Σ_{n ∈ S} n^{−τ} < ∞` for some `τ < 1/2` (for
example `#(S ∩ [1, X]) ≪ X^{1/2−η}`), then every full-cone Weil-positive `lam` equal to `Λ` off
`S` equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {S : ℕ → Prop} [DecidablePred S] {τ : ℝ} (hτ : τ < 1 / 2)
    (hS : Summable fun n : ℕ => if S n then (n : ℝ) ^ (-τ) else 0)
    (hoff : ∀ n, 2 ≤ n → ¬ S n → lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  set σ : ℝ := (τ + 1 / 2) / 2 with hσdef
  have hσ : σ < 1 / 2 := by rw [hσdef]; linarith
  have hτσ : 0 < σ - τ := by rw [hσdef]; linarith
  have hsv : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-σ) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hS.mul_left (2 / (σ - τ) + C))
    by_cases hSn : S n
    · rw [if_pos hSn]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hv0, abs_zero, zero_mul]; positivity
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog : Real.log n ≤ (n : ℝ) ^ (σ - τ) / (σ - τ) := Real.log_le_rpow_div hn0.le hτσ
      have hnst : 1 ≤ (n : ℝ) ^ (σ - τ) := Real.one_le_rpow hn1 hτσ.le
      have hvb : |v n| ≤ (2 / (σ - τ) + C) * (n : ℝ) ^ (σ - τ) := by
        have h1 := hC n
        have h2 : 2 * Real.log n ≤ 2 / (σ - τ) * (n : ℝ) ^ (σ - τ) := by
          rw [div_mul_eq_mul_div]; rw [le_div_iff₀ hτσ] at hlog ⊢; linarith
        nlinarith
      have e : (n : ℝ) ^ (σ - τ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-τ) := by
        rw [← Real.rpow_add hn0]; ring_nf
      calc |v n| * (n : ℝ) ^ (-σ) ≤ ((2 / (σ - τ) + C) * (n : ℝ) ^ (σ - τ)) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hvb (by positivity)
        _ = (2 / (σ - τ) + C) * (n : ℝ) ^ (-τ) := by rw [mul_assoc, e]
    · rw [if_neg hSn, mul_zero]
      have hz : v n = 0 := by
        rw [hv, RHTower.WeilExcess.weilDeviation]
        split_ifs with h2
        · rw [hoff n h2 hSn, sub_self, zero_div]
        · rfl
      rw [hz, abs_zero, zero_mul]
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_rpow_summable hv0 hv1 hC0 hC hσ hsv
    hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

end RHTower.WeilAbscissa
