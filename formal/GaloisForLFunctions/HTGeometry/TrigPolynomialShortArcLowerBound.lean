import Mathlib

/-!
# Trigonometric polynomials on a short arc

For `k ≥ 1` there are `c > 0` and `h₀ > 0` such that every trigonometric polynomial
`p(θ) = Σ_{j<k} y_j e^{ijθ}` satisfies

  `∫₀^h |p(θ)|² dθ ≥ c h^{2k−1} ‖y‖²`   for `0 < h ≤ h₀`

(`exists_integral_shortArcTrigPoly_sq_ge`), with `‖y‖` the sup norm.  The exponent `2k − 1` is the one of
the monomial `θ^{k−1}`: a trigonometric polynomial of degree `< k` can vanish to order `k − 1` at a
point, but not to higher order.

Proof.  On `[0, h]` with `h ≤ 1/k`, `p(θ) = P(θ) + O(‖y‖θ^k)` where
`P(θ) = Σ_{m<k} (iθ)^m μ_m/m!` and `μ_m = Σ_j j^m y_j` (`Complex.exp_bound`).
* The moment map `y ↦ μ` is the transposed Vandermonde matrix of the distinct nodes `0, …, k−1`, so
  `‖y‖ ≤ K ‖μ‖` (`LinearMap.exists_antilipschitzWith`).
* `∫₀^1 |Σ_m b_m s^m|² ds ≥ c_H ‖b‖²`: the left side is continuous in `b` and positive for `b ≠ 0`
  (a nonzero polynomial has finitely many roots), so it has a positive minimum on the unit sphere.
* Scaling `θ = hs`: `∫₀^h |P|² = h ∫₀^1 |Σ_m (ih)^m μ_m/m! s^m|² ≥ c_H h^{2k−1} ‖μ‖²/((k−1)!)²`.
-/

open Complex Real MeasureTheory intervalIntegral Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The trigonometric polynomial `Σ_{j<k} y_j e^{ijθ}`. -/
def shortArcTrigPoly {k : ℕ} (y : Fin k → ℂ) (θ : ℝ) : ℂ :=
  ∑ j : Fin k, y j * Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)

/-- The algebraic polynomial `Σ_{m<k} b_m s^m`. -/
def shortArcCoeffPoly {k : ℕ} (b : Fin k → ℂ) (s : ℝ) : ℂ :=
  ∑ m : Fin k, b m * (s : ℂ) ^ (m : ℕ)

theorem continuous_shortArcTrigPoly {k : ℕ} (y : Fin k → ℂ) : Continuous (shortArcTrigPoly y) := by
  unfold shortArcTrigPoly
  fun_prop

theorem continuous_shortArcCoeffPoly {k : ℕ} (b : Fin k → ℂ) : Continuous (shortArcCoeffPoly b) := by
  unfold shortArcCoeffPoly
  fun_prop

/-- A nonzero coefficient vector gives a polynomial that is nonzero somewhere on `[0, 1]`. -/
theorem exists_shortArcCoeffPoly_ne_zero {k : ℕ} {b : Fin k → ℂ} (hb : b ≠ 0) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, shortArcCoeffPoly b s ≠ 0 := by
  classical
  set q : ℂ[X] := ∑ m : Fin k, Polynomial.C (b m) * X ^ (m : ℕ) with hq
  have hqeval : ∀ s : ℝ, shortArcCoeffPoly b s = q.eval (s : ℂ) := by
    intro s
    simp [shortArcCoeffPoly, hq, Polynomial.eval_finsetSum]
  have hq0 : q ≠ 0 := by
    intro h0
    apply hb
    funext m
    have hc := congrArg (fun p : ℂ[X] => p.coeff (m : ℕ)) h0
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single m] at hc
    · simpa using hc
    · intro j _ hj
      have : (m : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
      simp [this]
    · simp
  by_contra hall
  push Not at hall
  apply hq0
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinf : (Set.Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  have himg : ((fun s : ℝ => (s : ℂ)) '' Set.Icc (0 : ℝ) 1).Infinite :=
    hinf.image Complex.ofReal_injective.injOn
  refine himg.mono ?_
  rintro z ⟨s, hs, rfl⟩
  show q.IsRoot (s : ℂ)
  rw [Polynomial.IsRoot, ← hqeval]
  exact hall s hs

/-- The `L²` mass of `Σ b_m s^m` on `[0, 1]` is positive for `b ≠ 0`. -/
theorem integral_shortArcCoeffPoly_sq_pos {k : ℕ} {b : Fin k → ℂ} (hb : b ≠ 0) :
    0 < ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2 := by
  obtain ⟨s₀, hs₀, hne⟩ := exists_shortArcCoeffPoly_ne_zero hb
  exact intervalIntegral.integral_pos (by norm_num)
    ((continuous_shortArcCoeffPoly b).norm.pow 2).continuousOn (fun s _ => by positivity)
    ⟨s₀, hs₀, by positivity⟩

theorem continuous_integral_shortArcCoeffPoly_sq (k : ℕ) :
    Continuous fun b : Fin k → ℂ => ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2 := by
  have hc : Continuous fun p : (Fin k → ℂ) × ℝ => ‖shortArcCoeffPoly p.1 p.2‖ ^ 2 := by
    unfold shortArcCoeffPoly
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1

/-- **Monomials on `[0, 1]`.**  `∫₀^1 |Σ_m b_m s^m|² ≥ c ‖b‖²` for some `c > 0`. -/
theorem exists_integral_shortArcCoeffPoly_sq_ge (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : Fin k → ℂ, c * ‖b‖ ^ 2 ≤ ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, one_pos, fun b => by simp [Subsingleton.elim b 0, shortArcCoeffPoly]⟩
  have hsph : IsCompact (Metric.sphere (0 : Fin k → ℂ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : Fin k → ℂ) 1).Nonempty := by
    haveI : Nontrivial (Fin k → ℂ) := by
      haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      infer_instance
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨b₀, hb₀, hmin⟩ := hsph.exists_isMinOn hne
    (continuous_integral_shortArcCoeffPoly_sq k).continuousOn
  have hb₀ne : b₀ ≠ 0 := by
    intro h; rw [h] at hb₀; simp at hb₀
  refine ⟨_, integral_shortArcCoeffPoly_sq_pos hb₀ne, fun b => ?_⟩
  rcases eq_or_ne b 0 with rfl | hb
  · rw [norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun s _ => by positivity)
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set u : Fin k → ℂ := (‖b‖⁻¹ : ℂ) • b with hu
  have hu1 : u ∈ Metric.sphere (0 : Fin k → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hbn, inv_mul_cancel₀ hbn.ne']
  have hm := hmin hu1
  simp only [Set.mem_setOf_eq] at hm
  have hscale : ∀ s : ℝ, shortArcCoeffPoly b s = (‖b‖ : ℂ) * shortArcCoeffPoly u s := by
    intro s
    simp only [shortArcCoeffPoly, hu, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hbn.ne'
    field_simp
  have hint : ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2
      = ‖b‖ ^ 2 * ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly u s‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s
    rw [hscale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbn]
    ring
  rw [hint]
  nlinarith [sq_nonneg ‖b‖]

/-- The moment map `y ↦ (Σ_j j^m y_j)_m` is bounded below. -/
theorem exists_moment_antilipschitz (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ y : Fin k → ℂ,
      ‖y‖ ≤ K * ‖fun m : Fin k => ∑ j : Fin k, ((j : ℕ) : ℂ) ^ (m : ℕ) * y j‖ := by
  classical
  set V : Matrix (Fin k) (Fin k) ℂ :=
    Matrix.transpose (Matrix.vandermonde fun j : Fin k => ((j : ℕ) : ℂ)) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    intro a b h
    exact Fin.ext (Nat.cast_injective h)
  have hker : (Matrix.mulVecLin V).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy0, hy⟩)
  obtain ⟨K, hK, hanti⟩ := (Matrix.mulVecLin V).exists_antilipschitzWith hker
  refine ⟨K, by exact_mod_cast hK, fun y => ?_⟩
  have h := hanti.le_mul_dist y 0
  simp only [dist_zero_right, map_zero] at h
  have hmv : (Matrix.mulVecLin V) y = fun m : Fin k => ∑ j : Fin k, ((j : ℕ) : ℂ) ^ (m : ℕ) * y j := by
    funext m
    rw [Matrix.mulVecLin_apply, hV, Matrix.mulVec_transpose]
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hmv] at h
  exact h

/-- **Short-arc lower bound.** -/
theorem exists_integral_shortArcTrigPoly_sq_ge (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ y : Fin k → ℂ,
      c * h ^ (2 * k - 1) * ‖y‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..h, ‖shortArcTrigPoly y θ‖ ^ 2 := by
  obtain ⟨cH, hcH, hH⟩ := exists_integral_shortArcCoeffPoly_sq_ge k
  obtain ⟨K, hK, hKy⟩ := exists_moment_antilipschitz k
  set F : ℝ := ((k - 1).factorial : ℝ) with hF
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  set c₁ : ℝ := cH / (K ^ 2 * F ^ 2) with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  set C₂ : ℝ := 2 * (k : ℝ) * (k : ℝ) ^ k with hC₂
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  refine ⟨c₁ / 4, by positivity, min (1 / (k : ℝ)) (Real.sqrt (c₁ / (4 * C₂ ^ 2))), ?_, ?_⟩
  · have : (0 : ℝ) < k := by exact_mod_cast hk
    exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  intro h hh hh₀ y
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hhk : h ≤ 1 / (k : ℝ) := hh₀.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := hhk.trans (by rw [div_le_one hkpos]; exact_mod_cast hk)
  have hhsq : h ^ 2 ≤ c₁ / (4 * C₂ ^ 2) := by
    have h2 := hh₀.trans (min_le_right _ _)
    calc h ^ 2 ≤ Real.sqrt (c₁ / (4 * C₂ ^ 2)) ^ 2 := pow_le_pow_left₀ hh.le h2 2
      _ = c₁ / (4 * C₂ ^ 2) := Real.sq_sqrt (by positivity)
  -- moments and the Taylor polynomial
  set μ : Fin k → ℂ := fun m => ∑ j : Fin k, ((j : ℕ) : ℂ) ^ (m : ℕ) * y j with hμ
  set P : ℝ → ℂ := fun θ => ∑ m : Fin k, (I * (θ : ℂ)) ^ (m : ℕ) / ((m : ℕ).factorial : ℂ) * μ m
    with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hpc : Continuous (shortArcTrigPoly y) := continuous_shortArcTrigPoly y
  have hPexp : ∀ θ : ℝ, P θ = ∑ j : Fin k, y j *
      ∑ m ∈ Finset.range k, (((j : ℕ) : ℂ) * (θ : ℂ) * I) ^ m / (m.factorial : ℂ) := by
    intro θ
    simp only [hP, hμ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun m => y j * ((((j : ℕ) : ℂ) * (θ : ℂ) * I) ^ m / (m.factorial : ℂ))) k]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow, mul_pow]
    ring
  -- the remainder `p − P`
  have hrem : ∀ θ ∈ Set.Icc (0 : ℝ) h, ‖shortArcTrigPoly y θ - P θ‖ ≤ C₂ * ‖y‖ * θ ^ k := by
    intro θ hθ
    have hθ0 := hθ.1
    have hdiff : shortArcTrigPoly y θ - P θ = ∑ j : Fin k, y j *
        (Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)
          - ∑ m ∈ Finset.range k, (((j : ℕ) : ℂ) * (θ : ℂ) * I) ^ m / (m.factorial : ℂ)) := by
      rw [hPexp, shortArcTrigPoly, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (mul_sub _ _ _).symm
    rw [hdiff]
    have hterm : ∀ j : Fin k, ‖y j * (Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)
          - ∑ m ∈ Finset.range k, (((j : ℕ) : ℂ) * (θ : ℂ) * I) ^ m / (m.factorial : ℂ))‖
        ≤ ‖y‖ * (2 * (k : ℝ) ^ k * θ ^ k) := by
      intro j
      have hjk : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast j.isLt.le
      have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
      have hnorm : ‖((j : ℕ) : ℂ) * (θ : ℂ) * I‖ = (j : ℕ) * θ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hθ0]
      have hle1 : ‖((j : ℕ) : ℂ) * (θ : ℂ) * I‖ ≤ 1 := by
        rw [hnorm]
        calc ((j : ℕ) : ℝ) * θ ≤ k * h := mul_le_mul hjk hθ.2 hθ0 hkpos.le
          _ ≤ k * (1 / k) := mul_le_mul_of_nonneg_left hhk hkpos.le
          _ = 1 := by field_simp
      have hb := Complex.exp_bound hle1 (n := k) (by omega)
      rw [hnorm] at hb
      have hfac : ((k.succ : ℕ) : ℝ) * ((k.factorial : ℝ) * k)⁻¹ ≤ 2 := by
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hkf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
        rw [mul_inv_le_iff₀ (by positivity)]
        push_cast
        nlinarith
      have hpow : (((j : ℕ) : ℝ) * θ) ^ k ≤ (k : ℝ) ^ k * θ ^ k := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hj0 hjk k) (by positivity)
      rw [norm_mul]
      have hyj : ‖y j‖ ≤ ‖y‖ := norm_le_pi_norm y j
      calc ‖y j‖ * ‖Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)
            - ∑ m ∈ Finset.range k, (((j : ℕ) : ℂ) * (θ : ℂ) * I) ^ m / (m.factorial : ℂ)‖
          ≤ ‖y‖ * ((((j : ℕ) : ℝ) * θ) ^ k * (((k.succ : ℕ) : ℝ) * ((k.factorial : ℝ) * k)⁻¹)) :=
            mul_le_mul hyj (by exact_mod_cast hb) (norm_nonneg _) (norm_nonneg _)
        _ ≤ ‖y‖ * ((k : ℝ) ^ k * θ ^ k * 2) := by
            gcongr
        _ = ‖y‖ * (2 * (k : ℝ) ^ k * θ ^ k) := by ring
    calc ‖∑ j : Fin k, _‖ ≤ ∑ j : Fin k, ‖y‖ * (2 * (k : ℝ) ^ k * θ ^ k) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
      _ = C₂ * ‖y‖ * θ ^ k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hC₂]
          ring
  -- the polynomial part
  have hPint : c₁ * h ^ (2 * k - 1) * ‖y‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..h, ‖P θ‖ ^ 2 := by
    set b : Fin k → ℂ := fun m => (I * (h : ℂ)) ^ (m : ℕ) / ((m : ℕ).factorial : ℂ) * μ m with hb
    have hPb : ∀ s : ℝ, P (h * s) = shortArcCoeffPoly b s := by
      intro s
      simp only [hP, shortArcCoeffPoly, hb]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      rw [mul_pow, mul_pow]
      ring
    have hsub : ∫ θ in (0 : ℝ)..h, ‖P θ‖ ^ 2 = h * ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2 := by
      have := intervalIntegral.integral_comp_mul_left (fun θ => ‖P θ‖ ^ 2) hh.ne' (a := 0) (b := 1)
      rw [mul_zero, mul_one] at this
      simp only [hPb] at this
      rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    have hbnorm : h ^ (k - 1) * ‖μ‖ ≤ F * ‖b‖ := by
      obtain ⟨m, hm⟩ : ∃ m : Fin k, ‖μ‖ = ‖μ m‖ := by
        haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
        obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun m => ‖μ m‖)
          Finset.univ_nonempty
        refine ⟨m, le_antisymm ?_ (norm_le_pi_norm μ m)⟩
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hm j (Finset.mem_univ j)
      have hbm : ‖b m‖ = h ^ (m : ℕ) / ((m : ℕ).factorial : ℝ) * ‖μ m‖ := by
        simp only [hb, norm_mul, norm_div, norm_pow, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hh, one_mul, Complex.norm_natCast]
      have hmk : (m : ℕ) ≤ k - 1 := by omega
      have hhpow : h ^ (k - 1) ≤ h ^ (m : ℕ) := pow_le_pow_of_le_one hh.le hh1 hmk
      have hmf : ((m : ℕ).factorial : ℝ) ≤ F := by
        rw [hF]; exact_mod_cast Nat.factorial_le hmk
      have hmf0 : (0 : ℝ) < (m : ℕ).factorial := by exact_mod_cast Nat.factorial_pos _
      rw [hm]
      calc h ^ (k - 1) * ‖μ m‖ ≤ h ^ (m : ℕ) * ‖μ m‖ :=
            mul_le_mul_of_nonneg_right hhpow (norm_nonneg _)
        _ = F * (h ^ (m : ℕ) / F * ‖μ m‖) := by field_simp
        _ ≤ F * (h ^ (m : ℕ) / ((m : ℕ).factorial : ℝ) * ‖μ m‖) := by
            gcongr
        _ = F * ‖b m‖ := by rw [hbm]
        _ ≤ F * ‖b‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm b m) hF0.le
    have hyμ := hKy y
    rw [hsub]
    have hHb := hH b
    have hy2 : ‖y‖ ^ 2 ≤ K ^ 2 * ‖μ‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hyμ 2
    have hμb : h ^ (2 * (k - 1)) * ‖μ‖ ^ 2 ≤ F ^ 2 * ‖b‖ ^ 2 := by
      have h2 := pow_le_pow_left₀ (by positivity) hbnorm 2
      calc h ^ (2 * (k - 1)) * ‖μ‖ ^ 2 = (h ^ (k - 1) * ‖μ‖) ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_comm (k - 1) 2]
        _ ≤ (F * ‖b‖) ^ 2 := h2
        _ = F ^ 2 * ‖b‖ ^ 2 := by rw [mul_pow]
    have hexp : h ^ (2 * k - 1) = h * h ^ (2 * (k - 1)) := by
      rw [← pow_succ']; congr 1; omega
    rw [hexp]
    calc c₁ * (h * h ^ (2 * (k - 1))) * ‖y‖ ^ 2
        ≤ c₁ * (h * h ^ (2 * (k - 1))) * (K ^ 2 * ‖μ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = h * (cH / F ^ 2 * (h ^ (2 * (k - 1)) * ‖μ‖ ^ 2)) := by
          rw [hc₁]; field_simp
      _ ≤ h * (cH / F ^ 2 * (F ^ 2 * ‖b‖ ^ 2)) := by gcongr
      _ = h * (cH * ‖b‖ ^ 2) := by field_simp
      _ ≤ h * ∫ s in (0 : ℝ)..1, ‖shortArcCoeffPoly b s‖ ^ 2 := mul_le_mul_of_nonneg_left hHb hh.le
  -- comparison `|P|² ≤ 2|p|² + 2|p − P|²`
  have hcmp : ∀ θ, ‖P θ‖ ^ 2 ≤ 2 * ‖shortArcTrigPoly y θ‖ ^ 2 + 2 * ‖shortArcTrigPoly y θ - P θ‖ ^ 2 := by
    intro θ
    have h1 : ‖P θ‖ ≤ ‖shortArcTrigPoly y θ‖ + ‖shortArcTrigPoly y θ - P θ‖ := by
      have := norm_sub_le (shortArcTrigPoly y θ) (shortArcTrigPoly y θ - P θ)
      rwa [sub_sub_cancel] at this
    nlinarith [norm_nonneg (P θ), norm_nonneg (shortArcTrigPoly y θ), norm_nonneg (shortArcTrigPoly y θ - P θ),
      sq_nonneg (‖shortArcTrigPoly y θ‖ - ‖shortArcTrigPoly y θ - P θ‖)]
  have hc1 : Continuous fun θ => ‖P θ‖ ^ 2 := by fun_prop
  have hc2 : Continuous fun θ => 2 * ‖shortArcTrigPoly y θ‖ ^ 2 := by fun_prop
  have hc3 : Continuous fun θ => 2 * ‖shortArcTrigPoly y θ - P θ‖ ^ 2 := by fun_prop
  have hc4 : Continuous fun θ => ‖shortArcTrigPoly y θ - P θ‖ ^ 2 := by fun_prop
  have hi1 : IntervalIntegrable (fun θ => ‖P θ‖ ^ 2) volume 0 h := hc1.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => 2 * ‖shortArcTrigPoly y θ‖ ^ 2 + 2 * ‖shortArcTrigPoly y θ - P θ‖ ^ 2)
      volume 0 h := (hc2.add hc3).intervalIntegrable _ _
  have hint1 := intervalIntegral.integral_mono_on hh.le hi1 hi2 (fun θ _ => hcmp θ)
  have hsplit : ∫ θ in (0 : ℝ)..h, (2 * ‖shortArcTrigPoly y θ‖ ^ 2 + 2 * ‖shortArcTrigPoly y θ - P θ‖ ^ 2)
      = 2 * (∫ θ in (0 : ℝ)..h, ‖shortArcTrigPoly y θ‖ ^ 2)
        + 2 * ∫ θ in (0 : ℝ)..h, ‖shortArcTrigPoly y θ - P θ‖ ^ 2 := by
    rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) (hc3.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hint1
  -- the remainder integral
  have hremint : ∫ θ in (0 : ℝ)..h, ‖shortArcTrigPoly y θ - P θ‖ ^ 2 ≤ C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k + 1) := by
    have hb2 : ∀ θ ∈ Set.Icc (0 : ℝ) h, ‖shortArcTrigPoly y θ - P θ‖ ^ 2 ≤ C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k) := by
      intro θ hθ
      have hr := hrem θ hθ
      have hθk : θ ^ k ≤ h ^ k := pow_le_pow_left₀ hθ.1 hθ.2 k
      calc ‖shortArcTrigPoly y θ - P θ‖ ^ 2 ≤ (C₂ * ‖y‖ * θ ^ k) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hr 2
        _ ≤ (C₂ * ‖y‖ * h ^ k) ^ 2 := by
            have h0 : 0 ≤ C₂ * ‖y‖ * θ ^ k := by
              have := hθ.1
              positivity
            gcongr
        _ = C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k) := by ring
    have := intervalIntegral.integral_mono_on hh.le (hc4.intervalIntegrable (μ := volume) 0 h)
      (continuous_const.intervalIntegrable (μ := volume) 0 h) hb2
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    calc _ ≤ h * (C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k)) := this
      _ = C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k + 1) := by ring
  have hsmall : C₂ ^ 2 * ‖y‖ ^ 2 * h ^ (2 * k + 1) ≤ c₁ / 4 * h ^ (2 * k - 1) * ‖y‖ ^ 2 := by
    have hexp : h ^ (2 * k + 1) = h ^ (2 * k - 1) * h ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hexp]
    have hC : C₂ ^ 2 * h ^ 2 ≤ c₁ / 4 := by
      calc C₂ ^ 2 * h ^ 2 ≤ C₂ ^ 2 * (c₁ / (4 * C₂ ^ 2)) := by gcongr
        _ = c₁ / 4 := by field_simp
    have hp : 0 ≤ h ^ (2 * k - 1) * ‖y‖ ^ 2 := by positivity
    nlinarith
  nlinarith [hPint, hint1, hremint, hsmall]

end

end GaloisForLFunctions.HTGeometry
