import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawAtDivergentMassIsADiniLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PrimeSignsAndPrimeMeansDoNotDecideTheHalfDampedReceiver

/-!
# Below half damping the local exponents are integers

If `f(d) d^{-ε}` is paid for some `0 < ε < 1/2`, the Mellin continuation of its receiver makes
`C(s) ζ(s)` analytic at `s₁ = 1 − ε + it₀`, where `C(s) = F(s + ε)`, and a ratio of two analytic
functions behaves like an integral power along a horizontal ray. Hence
(`exists_int_localExponent_of_receiverBounded_damped`):

for every height `t₀` there is `k ∈ ℤ` with `log|F(1 + u + it₀)| = k log(1/u) + O(1)` as `u ↓ 0`.

No local prime mean is assumed: the local exponent of a paid pattern exists and is an integer.

* **No local exponent off the real axis**
  (`exists_abs_log_norm_patternSeries_le_of_receiverBounded_damped`): at `t₀ ≠ 0` the bound
  `|cos x| ≤ ¾ + ¼ cos 2x` and the nonvanishing of `ζ` on `Re s = 1` give
  `|log|F(1 + u + it₀)|| ≤ ¾ log(1/u) + O(1)`, so the integer exponent is `0` and `F` stays bounded
  and bounded away from `0` along the ray.

* **Dini patterns are unpaid below half damping** (`not_receiverBounded_damped_of_diniBox`): a Dini
  box gives the exponent `½ − (c/2) Λ(u)/log(1/u)`, and `Λ(u) = o(log(1/u))`
  (`defectProfile_le_mul_log_add`), so the exponent tends to `½`.
* In particular every completely monotone amplitude defect is unpaid at every damping in
  `(0, 1/2)`, at every height `t₀ > 0` (`not_receiverBounded_defectPattern_damped`) and at height zero
  (`not_receiverBounded_halfDefectPattern_damped`): divergent-mass amplitudes can be paid only at
  `ε = 1/2`, through the Dini law.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

variable {w s : ℕ → ℝ}

/-! ### The integer local exponent law -/

/-- **Below half damping the local exponents are integers.** If `|f| ≤ 1` is completely
multiplicative and `f(d) d^{-ε}` is paid for some `0 < ε < 1/2`, then at every height `t₀` there
are `k ∈ ℤ`, `B` and `u₀ > 0` with `|log|F(1 + u + it₀)| − k log(1/u)| ≤ B` on `0 < u < u₀`. -/
theorem exists_int_localExponent_of_receiverBounded_damped {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hR : ReceiverBounded (dampedSignWeight f ε)) (t₀ : ℝ) :
    ∃ k : ℤ, ∃ B u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u < u₀ →
      |Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ -
        k * Real.log u⁻¹| ≤ B := by
  obtain ⟨E, hE⟩ := hR
  set c := dampedSignWeight f ε
  have habs := abs_patternHom_le_one f hf
  have hc : DampedClass 1 ε c := fun d => by
    simp only [c, dampedSignWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (habs d)
  set s₁ : ℂ := ((1 - ε : ℝ) : ℂ) + (t₀ : ℂ) * I
  have hs₁re : s₁.re = 1 - ε := by simp [s₁]
  have hs₁1 : s₁ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hs₁re, Complex.one_re] at this; linarith
  have hΦ : AnalyticAt ℂ (complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d))) s₁ :=
    (differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) fun T => hE T).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) / 2 < s₁.re by rw [hs₁re]; linarith))
  have hζ : AnalyticAt ℂ riemannZeta s₁ := analyticOn_riemannZeta s₁ hs₁1
  set Q : ℂ → ℂ := fun z => complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) z +
    ((∑' d : ℕ, c d / d : ℝ) : ℂ) * riemannZeta z
  have hQ : AnalyticAt ℂ Q s₁ := hΦ.add (analyticAt_const.mul hζ)
  have hray : ∀ u : ℝ, 0 < u → u < ε →
      weightDirichletSeries c (s₁ + u) * riemannZeta (s₁ + u) = Q (s₁ + u) := by
    intro u hu huε
    have hre : (s₁ + u).re = 1 - ε + u := by rw [Complex.add_re, hs₁re, Complex.ofReal_re]
    have hid := complexMellinPairing_eq_zeta_mul_of_summable (c := c) (θ := 1 - ε + u / 2)
      (s := s₁ + u) (by linarith) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (summable_abs_mul_rpow_of_dampedClass hε hc (by linarith))
    simp only [Q]; rw [hid]; ring
  have hCeq : ∀ u : ℝ, weightDirichletSeries c (s₁ + u) =
      ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)) := by
    intro u
    rw [weightDirichletSeries_dampedSignWeight,
      show s₁ + (u : ℂ) + (ε : ℂ) = ((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I by
        simp only [s₁]; push_cast; ring]
  have hFne : ∀ u : ℝ, 0 < u →
      ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)) ≠ 0 :=
    fun u hu => patternSeries_ne_zero hf (by simp; linarith)
  have hIoo : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε
  have hζ0 : ¬ ∀ᶠ z in 𝓝 s₁, riemannZeta z = 0 := fun h =>
    RHTower.analyticOrderAt_riemannZeta_ne_top_of_ne_one hs₁1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨q, Aζ, Bζ, hAζ, hBζ, hζray⟩ := exists_ray_bounds_of_order hζ hζ0
  by_cases hQ0 : ∀ᶠ z in 𝓝 s₁, Q z = 0
  · exfalso
    have hpath : Tendsto (fun u : ℝ => s₁ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₁) := by
      have hcont : Continuous (fun u : ℝ => s₁ + (u : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [Complex.ofReal_zero, add_zero] at h
    obtain ⟨u, hQu, hζu, hu⟩ := ((hpath.eventually hQ0).and (hζray.and hIoo)).exists
    have hprod := hray u hu.1 hu.2
    rw [hQu, hCeq] at hprod
    have h2 : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu.1 _)
    have hζne : riemannZeta (s₁ + u) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le h2 hζu.1)
    exact (mul_ne_zero (hFne u hu.1) hζne) hprod
  obtain ⟨p, AQ, BQ, hAQ, hBQ, hQray⟩ := exists_ray_bounds_of_order hQ hQ0
  obtain ⟨u₀, hu₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hζray.and (hQray.and hIoo))
  refine ⟨(q : ℤ) - p, max |Real.log (AQ / Bζ)| |Real.log (BQ / Aζ)|, u₀, hu₀,
    fun u hu huu₀ => ?_⟩
  obtain ⟨hζu, hQu, hu'⟩ := hsub ⟨hu, huu₀⟩
  have hprod := hray u hu hu'.2
  rw [hCeq] at hprod
  have hnorm : ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ *
      ‖riemannZeta (s₁ + u)‖ = ‖Q (s₁ + u)‖ := by rw [← norm_mul, hprod]
  have hFn0 := norm_pos_iff.mpr (hFne u hu)
  set Fn := ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖
  have hζpos : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu _)
  have hζpos' : 0 < Bζ * u ^ (q : ℝ) := mul_pos hBζ (Real.rpow_pos_of_pos hu _)
  have hlo : AQ / Bζ * u ^ ((p : ℝ) - q) ≤ Fn := by
    rw [Real.rpow_sub hu, div_mul_div_comm, div_le_iff₀ hζpos']
    calc AQ * u ^ (p : ℝ) ≤ ‖Q (s₁ + u)‖ := hQu.1
      _ = Fn * ‖riemannZeta (s₁ + u)‖ := hnorm.symm
      _ ≤ Fn * (Bζ * u ^ (q : ℝ)) := mul_le_mul_of_nonneg_left hζu.2 hFn0.le
  have hhi : Fn ≤ BQ / Aζ * u ^ ((p : ℝ) - q) := by
    rw [Real.rpow_sub hu, div_mul_div_comm, le_div_iff₀ hζpos]
    calc Fn * (Aζ * u ^ (q : ℝ)) ≤ Fn * ‖riemannZeta (s₁ + u)‖ :=
          mul_le_mul_of_nonneg_left hζu.1 hFn0.le
      _ = ‖Q (s₁ + u)‖ := hnorm
      _ ≤ BQ * u ^ (p : ℝ) := hQu.2
  have hA1 : AQ / Bζ ≠ 0 := (div_pos hAQ hBζ).ne'
  have hA2 : BQ / Aζ ≠ 0 := (div_pos hBQ hAζ).ne'
  have hup : u ^ ((p : ℝ) - q) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hl1 := Real.log_le_log (mul_pos (div_pos hAQ hBζ) (Real.rpow_pos_of_pos hu _)) hlo
  have hl2 := Real.log_le_log hFn0 hhi
  rw [Real.log_mul hA1 hup, Real.log_rpow hu] at hl1
  rw [Real.log_mul hA2 hup, Real.log_rpow hu] at hl2
  rw [Real.log_inv]
  push_cast
  have hm1 := le_max_left |Real.log (AQ / Bζ)| |Real.log (BQ / Aζ)|
  have hm2 := le_max_right |Real.log (AQ / Bζ)| |Real.log (BQ / Aζ)|
  rw [abs_le]
  constructor <;> nlinarith [neg_abs_le (Real.log (AQ / Bζ)), le_abs_self (Real.log (BQ / Aζ))]

/-! ### No local exponent off the real axis -/

/-- `|cos x| ≤ ¾ + ¼ cos 2x`, i.e. `y ≤ (1 + y²)/2` at `y = |cos x|`. -/
theorem abs_cos_le_three_quarters_add (x : ℝ) :
    |Real.cos x| ≤ 3 / 4 + 1 / 4 * Real.cos (2 * x) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_abs (Real.cos x), sq_nonneg (|Real.cos x| - 1)]

/-- **The `¾` bound off the real axis.** For `|f| ≤ 1` and `t₀ ≠ 0`,
`|log|F(σ + it₀)|| ≤ ¾ log(1/(σ − 1)) + C` on `1 < σ < 3/2`: the prime sum
`Σ_p f(p) cos(t₀ log p) p^{-σ}` is at most `Σ_p (¾ + ¼ cos(2t₀ log p)) p^{-σ}`, whose oscillating
part is bounded because `ζ` has no zero on the line `Re s = 1`. -/
theorem exists_abs_log_norm_patternSeries_le_three_quarters {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      |Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t₀ : ℂ) * I))‖| ≤
        3 / 4 * Real.log (1 / (σ - 1)) + C := by
  obtain ⟨B, hB⟩ := exists_abs_tsum_oscPattern_le (a := 1) (by norm_num)
    (mul_ne_zero two_ne_zero ht₀)
  refine ⟨primeSquareMass +
    3 / 4 * (2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) + Real.log (3 / 2)) + 1 / 4 * B,
    fun σ hσ hσ2 => ?_⟩
  have hw : 1 < ((σ : ℂ) + (t₀ : ℂ) * I).re := by simpa using hσ
  have hsσ : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hosc : Summable fun p : Nat.Primes => oscPattern 1 (2 * t₀) p * ((p : ℕ) : ℝ) ^ (-σ) :=
    hsσ.of_norm_bounded fun p => by
      rw [oscPattern_prime 1 (2 * t₀) p.2, one_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.abs_cos_le_one _)
  -- the real part of the prime sum is `Σ_p f(p) p^{-σ} cos(t₀ log p)`
  have hre : (primeDirichletSeries f ((σ : ℂ) + (t₀ : ℂ) * I)).re =
      ∑' p : Nat.Primes, f p * (((p : ℕ) : ℝ) ^ (-σ) * Real.cos (t₀ * Real.log (p : ℕ))) := by
    rw [primeDirichletSeries, Complex.re_tsum (summable_primeDirichletSeries hf hw)]
    refine tsum_congr fun p => ?_
    rw [Complex.re_ofReal_mul, RHTower.re_natCast_cpow_neg p.2.pos]
  have hterm : ∀ p : Nat.Primes,
      ‖f p * (((p : ℕ) : ℝ) ^ (-σ) * Real.cos (t₀ * Real.log (p : ℕ)))‖ ≤
        3 / 4 * ((p : ℕ) : ℝ) ^ (-σ) + 1 / 4 * (oscPattern 1 (2 * t₀) p * ((p : ℕ) : ℝ) ^ (-σ)) := by
    intro p
    have hpσ : 0 ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [oscPattern_prime 1 (2 * t₀) p.2, one_mul, mul_assoc (2 : ℝ) t₀, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_nonneg hpσ]
    have hc := abs_cos_le_three_quarters_add (t₀ * Real.log (p : ℕ))
    have h1 := mul_nonneg (sub_nonneg.mpr (hf p p.2)) (mul_nonneg hpσ (abs_nonneg
      (Real.cos (t₀ * Real.log (p : ℕ)))))
    have h2 := mul_nonneg hpσ (sub_nonneg.mpr hc)
    nlinarith
  have hP : |(primeDirichletSeries f ((σ : ℂ) + (t₀ : ℂ) * I)).re| ≤
      3 / 4 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) +
        1 / 4 * ∑' p : Nat.Primes, oscPattern 1 (2 * t₀) p * ((p : ℕ) : ℝ) ^ (-σ) := by
    rw [hre, ← tsum_mul_left, ← tsum_mul_left, ← (hsσ.mul_left _).tsum_add (hosc.mul_left _),
      ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded ((hsσ.mul_left _).add (hosc.mul_left _)).hasSum hterm
  have hM := (abs_le.mp (abs_tsum_primes_rpow_sub_log_le hσ hσ2)).2
  have hO := (abs_le.mp (hB σ hσ hσ2)).2
  have hE := abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le hf hw
  have h1 := abs_sub_abs_le_abs_sub
    (Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t₀ : ℂ) * I))‖)
    (primeDirichletSeries f ((σ : ℂ) + (t₀ : ℂ) * I)).re
  linarith

/-- **No local exponent off the real axis.** If `f(d) d^{-ε}` is paid for some `0 < ε < 1/2`, then
at every height `t₀ ≠ 0` the series `F(1 + u + it₀)` stays bounded and bounded away from `0` as
`u ↓ 0`: its integral local exponent has size at most `¾`, hence vanishes. -/
theorem exists_abs_log_norm_patternSeries_le_of_receiverBounded_damped {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hR : ReceiverBounded (dampedSignWeight f ε)) {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    ∃ B u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u < u₀ →
      |Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖| ≤
        B := by
  obtain ⟨k, B', u₀, hu₀, hk⟩ := exists_int_localExponent_of_receiverBounded_damped hf hε hε2 hR t₀
  obtain ⟨C, hC⟩ := exists_abs_log_norm_patternSeries_le_three_quarters hf ht₀
  suffices hk0 : k = 0 by
    refine ⟨B', u₀, hu₀, fun u hu huu₀ => ?_⟩
    have h := hk u hu huu₀
    rwa [hk0, Int.cast_zero, zero_mul, sub_zero] at h
  by_contra hk0
  obtain ⟨u, hu, huu₀, hu2, huX⟩ : ∃ u : ℝ, 0 < u ∧ u < u₀ ∧ u < 1 / 2 ∧
      u ≤ Real.exp (-(4 * (|B'| + |C| + 1))) :=
    ⟨min (u₀ / 2) (min (1 / 4) (Real.exp (-(4 * (|B'| + |C| + 1))))),
      lt_min (by linarith) (lt_min (by norm_num) (Real.exp_pos _)),
      lt_of_le_of_lt (min_le_left _ _) (by linarith),
      lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hLX : 4 * (|B'| + |C| + 1) ≤ Real.log u⁻¹ := by
    rw [Real.log_inv, le_neg]
    have := Real.log_le_log hu huX
    rwa [Real.log_exp] at this
  have hL0 : 0 ≤ Real.log u⁻¹ := le_trans (by positivity) hLX
  have h34 := hC (1 + u) (by linarith) (by linarith)
  rw [show 1 + u - 1 = u by ring, one_div] at h34
  have hexp := hk u hu huu₀
  rw [abs_le] at h34 hexp
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have : (k : ℝ) * Real.log u⁻¹ ≤ -Real.log u⁻¹ := by nlinarith
    linarith [le_abs_self B', le_abs_self C, neg_abs_le B', neg_abs_le C]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have : Real.log u⁻¹ ≤ (k : ℝ) * Real.log u⁻¹ := by nlinarith
    linarith [le_abs_self B', le_abs_self C, neg_abs_le B', neg_abs_le C]

/-! ### The profile is sublogarithmic -/

/-- **`Λ(u) = o(log(1/u))`**: for every `η > 0`, `Λ(u) ≤ η log(1/u) + C` on `(0, 1/2]`. -/
theorem defectProfile_le_mul_log_add (hd : AdmissibleDefect w s) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 / 2 → defectProfile w s u ≤ η * Real.log u⁻¹ + C := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∑' k, w (k + K) ≤ η := by
    have h := (tendsto_sum_nat_add w).eventually (gt_mem_nhds hη)
    obtain ⟨K, hK⟩ := h.exists
    exact ⟨K, hK.le⟩
  refine ⟨∑ k ∈ Finset.range K, w k * |Real.log (s k)|, fun u hu hu2 => ?_⟩
  have hs := summable_defectProfile hd hu
  rw [defectProfile, ← hs.sum_add_tsum_nat_add K]
  have hL : 0 ≤ Real.log u⁻¹ := by
    rw [Real.log_inv, neg_nonneg]; exact Real.log_nonpos hu.le (by linarith)
  have hhead : ∑ k ∈ Finset.range K, w k * Real.log (s k + u)⁻¹ ≤
      ∑ k ∈ Finset.range K, w k * |Real.log (s k)| :=
    Finset.sum_le_sum fun k _ => by
      refine mul_le_mul_of_nonneg_left ?_ (hd.nonneg k)
      rw [Real.log_inv]
      have := Real.log_le_log (hd.pos k) (show s k ≤ s k + u by linarith)
      linarith [neg_abs_le (Real.log (s k))]
  have htail : ∑' k, w (k + K) * Real.log (s (k + K) + u)⁻¹ ≤ η * Real.log u⁻¹ := by
    have hws : Summable fun k => w (k + K) := hd.summable.comp_injective (add_left_injective K)
    calc ∑' k, w (k + K) * Real.log (s (k + K) + u)⁻¹
        ≤ ∑' k, w (k + K) * Real.log u⁻¹ :=
          (hs.comp_injective (add_left_injective K)).tsum_le_tsum (fun k => by
            refine mul_le_mul_of_nonneg_left ?_ (hd.nonneg _)
            rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
            exact Real.log_le_log hu (by linarith [hd.pos (k + K)])) (hws.mul_right _)
      _ = (∑' k, w (k + K)) * Real.log u⁻¹ := tsum_mul_right
      _ ≤ η * Real.log u⁻¹ := mul_le_mul_of_nonneg_right hK hL
  linarith

/-! ### Dini patterns below half damping -/

/-- **Dini patterns are unpaid below half damping.** A completely multiplicative `|f| ≤ 1` with a
Dini box at a height `t₀ ≥ 0` has local exponent `½ − (c/2) Λ(u)/log(1/u) → ½` there, which is not an
integer up to `O(1)`; so `f(d) d^{-ε}` is unpaid for every `0 < ε < 1/2`. -/
theorem not_receiverBounded_damped_of_diniBox (hd : AdmissibleDefect w s) {c t₀ B : ℝ}
    (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀) {f : ℕ →*₀ ℝ} (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (hB : DiniBox f c t₀ w s B) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight f ε) := by
  intro hR
  obtain ⟨k, B', u₀, hu₀, hk⟩ := exists_int_localExponent_of_receiverBounded_damped hf hε hε2 hR t₀
  have hc2 : 0 < 2 * c + 2 := by linarith
  obtain ⟨C, hC⟩ := defectProfile_le_mul_log_add hd (div_pos one_pos hc2)
  have hcC : 0 ≤ c * |C| := mul_nonneg hc (abs_nonneg C)
  -- a point `u` so small that `log(1/u)` beats every constant in sight
  obtain ⟨u, hu, huu₀, hu4, huX⟩ : ∃ u : ℝ, 0 < u ∧ u < u₀ ∧ u ≤ 1 / 4 ∧
      u ≤ Real.exp (-(8 * (|B| + |B'| + c * |C| + 1))) :=
    ⟨min (u₀ / 2) (min (1 / 4) (Real.exp (-(8 * (|B| + |B'| + c * |C| + 1))))),
      lt_min (by linarith) (lt_min (by norm_num) (Real.exp_pos _)),
      lt_of_le_of_lt (min_le_left _ _) (by linarith),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hLX : 8 * (|B| + |B'| + c * |C| + 1) ≤ Real.log u⁻¹ := by
    rw [Real.log_inv, le_neg]
    have := Real.log_le_log hu huX
    rwa [Real.log_exp] at this
  -- the Dini box on the ray `t = t₀`
  have hvre : (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I).re = 1 + u := by simp
  have hvim : (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I).im = t₀ := by simp
  have hbox := hB (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I) (by rw [hvre]; linarith)
    (by rw [hvre]; linarith) (by rw [hvim]; exact ht₀) (by rw [hvim]; linarith)
  rw [hvre, hvim, show 1 + u - 1 + |t₀ - t₀| = u by rw [sub_self, abs_zero]; ring] at hbox
  have hexp := hk u hu huu₀
  have hΛ0 := defectProfile_nonneg hd hu (by linarith)
  have hΛ1 := hC u hu (by linarith)
  -- `(½ − k) log(1/u) − (c/2) Λ(u)` is bounded by `|B| + |B'|`
  rw [abs_le] at hbox hexp
  have hdiff1 : -(|B| + |B'|) ≤
      (1 / 2 - (k : ℝ)) * Real.log u⁻¹ - c / 2 * defectProfile w s u := by
    linarith [le_abs_self B, le_abs_self B']
  have hdiff2 : (1 / 2 - (k : ℝ)) * Real.log u⁻¹ - c / 2 * defectProfile w s u ≤
      |B| + |B'| := by
    linarith [neg_abs_le B, neg_abs_le B']
  have hL0 : 0 ≤ Real.log u⁻¹ := le_trans (by linarith [abs_nonneg B, abs_nonneg B']) hLX
  -- `(c/2) Λ(u) ≤ ¼ log(1/u) + (c/2)|C|`
  have hcη : c / 2 * (1 / (2 * c + 2)) ≤ 1 / 4 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hcΛ : c / 2 * defectProfile w s u ≤ Real.log u⁻¹ / 4 + c / 2 * |C| := by
    have h := mul_le_mul_of_nonneg_left hΛ1 (by linarith : (0 : ℝ) ≤ c / 2)
    have h2 := mul_le_mul_of_nonneg_right hcη hL0
    have h3 : c / 2 * C ≤ c / 2 * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) (by linarith)
    nlinarith
  rcases le_or_gt k 0 with hk0 | hk0
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have : (1 / 2 : ℝ) * Real.log u⁻¹ ≤ (1 / 2 - (k : ℝ)) * Real.log u⁻¹ := by nlinarith
    linarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have : (1 / 2 - (k : ℝ)) * Real.log u⁻¹ ≤ -(1 / 2) * Real.log u⁻¹ := by nlinarith
    have hcΛ0 : 0 ≤ c / 2 * defectProfile w s u := mul_nonneg (by linarith) hΛ0
    linarith [abs_nonneg B, abs_nonneg B']

/-- **Completely monotone amplitude defects are unpaid below half damping**, at every height
`t₀ > 0`. -/
theorem not_receiverBounded_defectPattern_damped (hd : AdmissibleDefect w s) {c t₀ ε : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑(defectPattern c t₀ w s) ε) := by
  obtain ⟨B, Cl, hB, -, -⟩ := exists_diniBox_defectPattern hd hc hcW ht₀
  exact not_receiverBounded_damped_of_diniBox hd hc ht₀.le
    (fun p _ => abs_defectPattern_le hd hc hcW t₀ p) hB hε hε2

/-- **Completely monotone amplitude defects at height zero are unpaid below half damping.** -/
theorem not_receiverBounded_halfDefectPattern_damped (hd : AdmissibleDefect w s) {c ε : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑(halfDefectPattern c w s) ε) := by
  obtain ⟨B, hB⟩ := exists_diniBox_halfDefectPattern hd hc hcW
  exact not_receiverBounded_damped_of_diniBox hd hc le_rfl
    (fun p _ => abs_halfDefectPattern_le hd hc hcW p) hB hε hε2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
