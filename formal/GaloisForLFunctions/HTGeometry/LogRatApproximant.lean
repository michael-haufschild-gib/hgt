import GaloisForLFunctions.HTGeometry.LogPolyDatum
import GaloisForLFunctions.HTGeometry.RatApproximant

/-!
# Logarithmic rational approximants

The digamma function itself expands as `log s + P(1/s)`, so the approximants of the full shifted
polygamma field carry powers of the principal logarithm.  The right model is a polynomial in the
logarithm with polynomial coefficients, divided by a polynomial: that class is a ring, contains the
rational functions, the jets of positive order and the digamma translates themselves, and its
boundary datum has already been computed.

Growth is what makes the product work, exactly as in the logarithm-free case: the two approximation
orders are raised by the other factor's growth exponent, and the logarithm is dominated by the
height.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

theorem HasTubePolyGrowth.add {f g : ℂ → ℂ} (hf : HasTubePolyGrowth f)
    (hg : HasTubePolyGrowth g) : HasTubePolyGrowth (fun z => f z + g z) := by
  intro M hM
  obtain ⟨mf, Cf, Tf, hCf, hTf, hbf⟩ := hf M hM
  obtain ⟨mg, Cg, Tg, hCg, hTg, hbg⟩ := hg M hM
  refine ⟨max mf mg, Cf + Cg, max Tf Tg, by positivity, le_trans hTf (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have h1 := hbf σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hbg σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hTf (le_trans (le_max_left _ _) ht)
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp1 : t ^ mf ≤ t ^ max mf mg := pow_le_pow_right₀ ht1 (le_max_left _ _)
  have hp2 : t ^ mg ≤ t ^ max mf mg := pow_le_pow_right₀ ht1 (le_max_right _ _)
  refine le_trans (norm_add_le _ _) ?_
  nlinarith

theorem HasTubePolyGrowth.one : HasTubePolyGrowth (fun _ : ℂ => (1 : ℂ)) := by
  intro M hM
  exact ⟨0, 1, 2, zero_le_one, le_rfl, fun σ t _ _ _ => by simp⟩

theorem HasTubePolyGrowth.mul {f g : ℂ → ℂ} (hf : HasTubePolyGrowth f)
    (hg : HasTubePolyGrowth g) : HasTubePolyGrowth (fun z => f z * g z) := by
  intro M hM
  obtain ⟨mf, Cf, Tf, hCf, hTf, hbf⟩ := hf M hM
  obtain ⟨mg, Cg, Tg, hCg, hTg, hbg⟩ := hg M hM
  refine ⟨mf + mg, Cf * Cg, max Tf Tg, by positivity, le_trans hTf (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have h1 := hbf σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hbg σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hTf (le_trans (le_max_left _ _) ht)
  rw [norm_mul, pow_add]
  have hb := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  calc ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Cf * t ^ mf) * (Cg * t ^ mg) := hb
    _ = Cf * Cg * (t ^ mf * t ^ mg) := by ring

theorem HasTubePolyGrowth.pow {f : ℂ → ℂ} (hf : HasTubePolyGrowth f) (n : ℕ) :
    HasTubePolyGrowth (fun z => f z ^ n) := by
  induction n with
  | zero =>
      have h := HasTubePolyGrowth.one
      have heq : (fun _ : ℂ => (1 : ℂ)) = fun z : ℂ => f z ^ 0 := by
        funext z
        rw [pow_zero]
      rwa [heq] at h
  | succ k ih =>
      have h := ih.mul hf
      have heq : (fun z : ℂ => f z ^ k * f z) = fun z : ℂ => f z ^ (k + 1) := by
        funext z
        rw [pow_succ]
      rwa [heq] at h

/-- The principal logarithm is dominated by the height on every tube. -/
theorem norm_clog_vertical_le {M σ t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) (ht : 1 ≤ t) :
    ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 + M + Real.pi) * t := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsone : (1 : ℝ) ≤ ‖s‖ := le_trans ht (norm_vertical_ge_im σ t)
  have hsle : ‖s‖ ≤ (1 + M) * t := norm_vertical_le_of_le hσ hσM ht
  have hlog : Complex.log s = (Real.log ‖s‖ : ℂ) + (Complex.arg s : ℂ) * Complex.I := by
    rw [Complex.log]
  have hnorm : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + |Complex.arg s| := by
    rw [hlog]
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hlogle : |Real.log ‖s‖| ≤ ‖s‖ := by
    rw [abs_of_nonneg (Real.log_nonneg hsone)]
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hsone)
    linarith
  have hargle : |Complex.arg s| ≤ Real.pi := Complex.abs_arg_le_pi s
  have hpi : Real.pi ≤ Real.pi * t := by
    nlinarith [Real.pi_pos]
  calc ‖Complex.log s‖ ≤ |Real.log ‖s‖| + |Complex.arg s| := hnorm
    _ ≤ (1 + M) * t + Real.pi := by linarith
    _ ≤ (1 + M + Real.pi) * t := by nlinarith

theorem hasTubePolyGrowth_clog : HasTubePolyGrowth (fun z => Complex.log z) := by
  intro M hM
  refine ⟨1, 1 + M + Real.pi, 2, by positivity, le_rfl, fun σ t hσ hσM ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [pow_one]
  exact norm_clog_vertical_le hσ hσM ht1

theorem hasTubePolyGrowth_logPolyEval (A : Polynomial (Polynomial ℂ)) :
    HasTubePolyGrowth (fun z => logPolyEval A z) := by
  classical
  refine Polynomial.induction_on A ?_ ?_ ?_
  · intro a
    have h := hasTubePolyGrowth_ratEval a (q := 1) one_ne_zero
    have heq : (fun z : ℂ => Polynomial.eval z a / Polynomial.eval z 1)
        = fun z : ℂ => logPolyEval (Polynomial.C a) z := by
      funext z
      rw [logPolyEval, Polynomial.eval₂_C, Polynomial.eval_one, div_one]
      rfl
    rwa [heq] at h
  · intro p q hp hq
    have h := hp.add hq
    have heq : (fun z : ℂ => logPolyEval p z + logPolyEval q z)
        = fun z : ℂ => logPolyEval (p + q) z := by
      funext z
      rw [logPolyEval, logPolyEval, logPolyEval, Polynomial.eval₂_add]
    rwa [heq] at h
  · intro n a hp
    have h := (hasTubePolyGrowth_ratEval a (q := 1) one_ne_zero).mul
      (hasTubePolyGrowth_clog.mul (hasTubePolyGrowth_clog.pow n))
    have heq : (fun z : ℂ => Polynomial.eval z a / Polynomial.eval z 1
        * (Complex.log z * (Complex.log z) ^ n))
        = fun z : ℂ => logPolyEval (Polynomial.C a * Polynomial.X ^ (n + 1)) z := by
      funext z
      rw [logPolyEval, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval_one, div_one, pow_succ']
      rfl
    rwa [heq] at h

/-- Approximation on every tube, to every order, by a logarithmic polynomial over a polynomial. -/
def HasLogRatApprox (f : ℂ → ℂ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ N : ℕ, ∃ (A : Polynomial (Polynomial ℂ)) (q : Polynomial ℂ) (C T : ℝ),
    q ≠ 0 ∧ 0 ≤ C ∧ 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)
          - logPolyEval A ((σ : ℂ) + (t : ℂ) * Complex.I)
            / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q‖ ≤ C / t ^ N

theorem hasTubePolyGrowth_logPolyEval_div (A : Polynomial (Polynomial ℂ)) {q : Polynomial ℂ}
    (hq : q ≠ 0) : HasTubePolyGrowth (fun z => logPolyEval A z / Polynomial.eval z q) := by
  have h := (hasTubePolyGrowth_logPolyEval A).mul (hasTubePolyGrowth_ratEval 1 hq)
  have heq : (fun z : ℂ => logPolyEval A z
      * (Polynomial.eval z 1 / Polynomial.eval z q))
      = fun z : ℂ => logPolyEval A z / Polynomial.eval z q := by
    funext z
    rw [Polynomial.eval_one]
    ring
  rwa [heq] at h

theorem HasLogRatApprox.hasTubePolyGrowth {f : ℂ → ℂ} (hf : HasLogRatApprox f) :
    HasTubePolyGrowth f := by
  intro M hM
  obtain ⟨A, q, C, T, hq, hC, hT, hb⟩ := hf M hM 0
  obtain ⟨m, C', T', hC', hT', hb'⟩ := hasTubePolyGrowth_logPolyEval_div A hq M hM
  refine ⟨m, C + C', max T T', by positivity, le_trans hT (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have h1 := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hb' σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hT (le_trans (le_max_left _ _) ht)
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htm : (1 : ℝ) ≤ t ^ m := one_le_pow₀ ht1
  rw [pow_zero, div_one] at h1
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsplit : ‖f s‖ ≤ ‖f s - logPolyEval A s / Polynomial.eval s q‖
      + ‖logPolyEval A s / Polynomial.eval s q‖ := by
    have := norm_add_le (f s - logPolyEval A s / Polynomial.eval s q)
      (logPolyEval A s / Polynomial.eval s q)
    simpa using this
  nlinarith

theorem HasRatApprox.hasLogRatApprox {f : ℂ → ℂ} (hf : HasRatApprox f) : HasLogRatApprox f := by
  intro M hM N
  obtain ⟨p, q, C, T, hq, hC, hT, hb⟩ := hf M hM N
  refine ⟨Polynomial.C p, q, C, T, hq, hC, hT, fun σ t hσ hσM ht => ?_⟩
  have h := hb σ t hσ hσM ht
  have heq : logPolyEval (Polynomial.C p) ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) p := by
    rw [logPolyEval, Polynomial.eval₂_C]
    rfl
  rw [heq]
  exact h

theorem HasLogRatApprox.congr {f g : ℂ → ℂ} (hf : HasLogRatApprox f) (h : ∀ z, f z = g z) :
    HasLogRatApprox g := by
  have hfg : f = g := funext h
  rwa [hfg] at hf

theorem HasLogRatApprox.add {f g : ℂ → ℂ} (hf : HasLogRatApprox f) (hg : HasLogRatApprox g) :
    HasLogRatApprox (fun z => f z + g z) := by
  intro M hM N
  obtain ⟨A₁, q₁, C₁, T₁, hq₁, hC₁, hT₁, hb₁⟩ := hf M hM N
  obtain ⟨A₂, q₂, C₂, T₂, hq₂, hC₂, hT₂, hb₂⟩ := hg M hM N
  obtain ⟨U₁, hU₁, hne₁⟩ := exists_height_polyEval_ne_zero hq₁
  obtain ⟨U₂, hU₂, hne₂⟩ := exists_height_polyEval_ne_zero hq₂
  refine ⟨A₁ * Polynomial.C q₂ + Polynomial.C q₁ * A₂, q₁ * q₂, C₁ + C₂,
    max (max T₁ T₂) (max U₁ U₂), mul_ne_zero hq₁ hq₂, by linarith,
    le_trans hT₁ (le_trans (le_max_left _ _) (le_max_left _ _)), fun σ t hσ hσM ht => ?_⟩
  have h1 := hb₁ σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
  have h2 := hb₂ σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
  have hz₁ := hne₁ σ t (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
  have hz₂ := hne₂ σ t (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht)
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hval : logPolyEval (A₁ * Polynomial.C q₂ + Polynomial.C q₁ * A₂) s
      / Polynomial.eval s (q₁ * q₂)
      = logPolyEval A₁ s / Polynomial.eval s q₁ + logPolyEval A₂ s / Polynomial.eval s q₂ := by
    have hC₂ : logPolyEval (Polynomial.C q₂) s = Polynomial.eval s q₂ := by
      rw [logPolyEval, Polynomial.eval₂_C]
      rfl
    have hC₁ : logPolyEval (Polynomial.C q₁) s = Polynomial.eval s q₁ := by
      rw [logPolyEval, Polynomial.eval₂_C]
      rfl
    rw [logPolyEval, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul,
      ← logPolyEval, ← logPolyEval, ← logPolyEval, ← logPolyEval, hC₁, hC₂,
      Polynomial.eval_mul, div_add_div _ _ hz₁ hz₂]
  rw [hval]
  have hsplit : f s + g s - (logPolyEval A₁ s / Polynomial.eval s q₁
      + logPolyEval A₂ s / Polynomial.eval s q₂)
      = (f s - logPolyEval A₁ s / Polynomial.eval s q₁)
        + (g s - logPolyEval A₂ s / Polynomial.eval s q₂) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hsum : C₁ / t ^ N + C₂ / t ^ N = (C₁ + C₂) / t ^ N := by ring
  linarith

theorem HasLogRatApprox.neg {f : ℂ → ℂ} (hf : HasLogRatApprox f) :
    HasLogRatApprox (fun z => -f z) := by
  intro M hM N
  obtain ⟨A, q, C, T, hq, hC, hT, hb⟩ := hf M hM N
  refine ⟨-A, q, C, T, hq, hC, hT, fun σ t hσ hσM ht => ?_⟩
  have h := hb σ t hσ hσM ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hval : logPolyEval (-A) s = -logPolyEval A s := by
    rw [logPolyEval, logPolyEval, Polynomial.eval₂_neg]
  have hsplit : -f s - logPolyEval (-A) s / Polynomial.eval s q
      = -(f s - logPolyEval A s / Polynomial.eval s q) := by
    rw [hval, neg_div]
    ring
  rw [hsplit, norm_neg]
  exact h

theorem HasLogRatApprox.sub {f g : ℂ → ℂ} (hf : HasLogRatApprox f) (hg : HasLogRatApprox g) :
    HasLogRatApprox (fun z => f z - g z) := by
  have h := hf.add hg.neg
  simpa [sub_eq_add_neg] using h

theorem HasLogRatApprox.mul {f g : ℂ → ℂ} (hf : HasLogRatApprox f) (hg : HasLogRatApprox g) :
    HasLogRatApprox (fun z => f z * g z) := by
  intro M hM N
  obtain ⟨mf, Cf, Tf, hCf, hTf, hbf⟩ := hf.hasTubePolyGrowth M hM
  obtain ⟨A₁, q₁, C₁, T₁, hq₁, hC₁, hT₁, hb₁⟩ := hf M hM (N + 0)
  obtain ⟨A₂, q₂, C₂, T₂, hq₂, hC₂, hT₂, hb₂⟩ := hg M hM (N + mf)
  obtain ⟨mg, Cg, Tg, hCg, hTg, hbg⟩ := hasTubePolyGrowth_logPolyEval_div A₂ hq₂ M hM
  obtain ⟨A₁', q₁', C₁', T₁', hq₁', hC₁', hT₁', hb₁'⟩ := hf M hM (N + mg)
  refine ⟨A₁' * A₂, q₁' * q₂, Cf * C₂ + Cg * C₁', max (max Tf Tg) (max T₁' T₂),
    mul_ne_zero hq₁' hq₂, by positivity,
    le_trans hTf (le_trans (le_max_left _ _) (le_max_left _ _)), fun σ t hσ hσM ht => ?_⟩
  have hgf := hbf σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
  have hgg := hbg σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
  have h1 := hb₁' σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
  have h2 := hb₂ σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hTf (le_trans (le_max_left _ _) (le_max_left _ _)) |>.trans ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set B₁ : ℂ := logPolyEval A₁' s / Polynomial.eval s q₁' with hB₁
  set B₂ : ℂ := logPolyEval A₂ s / Polynomial.eval s q₂ with hB₂
  have hprod : logPolyEval (A₁' * A₂) s / Polynomial.eval s (q₁' * q₂) = B₁ * B₂ := by
    rw [logPolyEval, Polynomial.eval₂_mul, ← logPolyEval, ← logPolyEval, Polynomial.eval_mul,
      hB₁, hB₂, div_mul_div_comm]
  rw [hprod]
  have hsplit : f s * g s - B₁ * B₂ = f s * (g s - B₂) + B₂ * (f s - B₁) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hfirst : ‖f s * (g s - B₂)‖ ≤ Cf * C₂ / t ^ N := by
    rw [norm_mul]
    have hb : ‖f s‖ * ‖g s - B₂‖ ≤ (Cf * t ^ mf) * (C₂ / t ^ (N + mf)) :=
      mul_le_mul hgf h2 (norm_nonneg _) (by positivity)
    refine le_trans hb (le_of_eq ?_)
    rw [pow_add]
    field_simp
  have hsecond : ‖B₂ * (f s - B₁)‖ ≤ Cg * C₁' / t ^ N := by
    rw [norm_mul]
    have hb : ‖B₂‖ * ‖f s - B₁‖ ≤ (Cg * t ^ mg) * (C₁' / t ^ (N + mg)) :=
      mul_le_mul hgg h1 (norm_nonneg _) (by positivity)
    refine le_trans hb (le_of_eq ?_)
    rw [pow_add]
    field_simp
  have hadd : Cf * C₂ / t ^ N + Cg * C₁' / t ^ N = (Cf * C₂ + Cg * C₁') / t ^ N := by ring
  linarith

/-- **The digamma translates are approximable with logarithms.** -/
theorem hasLogRatApprox_digamma_shift {lam : ℝ} (hlam : 0 ≤ lam) :
    HasLogRatApprox (fun z => Complex.digamma (z + (lam : ℂ))) := by
  intro M hM N
  obtain ⟨P, C, T, hC, hT, hb⟩ := exists_digamma_shift_expansion lam N
  refine ⟨Polynomial.C (invReverse P) + Polynomial.X * Polynomial.C (Polynomial.X ^ P.natDegree),
    Polynomial.X ^ P.natDegree, C, T, pow_ne_zero _ Polynomial.X_ne_zero, hC, hT,
    fun σ t hσ hσM ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos htpos
  have hval := hb σ t hσ (by linarith) ht
  have harg : (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ) := by
    push_cast
    ring
  rw [harg] at hval
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hden : Polynomial.eval s (Polynomial.X ^ P.natDegree) = s ^ P.natDegree := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  have hnum : logPolyEval
      (Polynomial.C (invReverse P) + Polynomial.X * Polynomial.C (Polynomial.X ^ P.natDegree)) s
      = (invReverse P).eval s + Complex.log s * s ^ P.natDegree := by
    rw [logPolyEval, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  rw [hnum, hden]
  have hsplit : ((invReverse P).eval s + Complex.log s * s ^ P.natDegree) / s ^ P.natDegree
      = P.eval (1 / s) + Complex.log s := by
    have hinv : P.eval (1 / s) = (invReverse P).eval s / s ^ P.natDegree := by
      rw [eval_inv_eq_div P hs, Polynomial.eval_pow, Polynomial.eval_X]
    rw [add_div, mul_div_assoc, div_self (pow_ne_zero _ hs), mul_one, hinv]
  rw [hsplit]
  have hrewrite : Complex.digamma (s + (lam : ℂ)) - (P.eval (1 / s) + Complex.log s)
      = Complex.digamma (s + (lam : ℂ)) - Complex.log s - P.eval (1 / s) := by ring
  rw [hrewrite]
  refine le_trans hval ?_
  have hpow : t ^ N ≤ t ^ (N + 1) := pow_le_pow_right₀ ht1 (by omega)
  exact div_le_div_of_nonneg_left hC (by positivity) hpow

/-- The first digamma jet at the unit translate is logarithmically rationally approximable. -/
theorem hasLogRatApprox_digamma_one_shift_firstJet :
    HasLogRatApprox (fun z => iteratedDeriv 1 Complex.digamma (z + (1 : ℂ))) := by
  have h_one : (0 : ℝ) ≤ 1 := zero_le_one
  exact
    (hasRatApprox_iteratedDeriv_digamma_shift (lam := (1 : ℝ)) h_one 0).hasLogRatApprox

/-- Digamma itself is logarithmically rationally approximable on vertical tubes. -/
theorem hasLogRatApprox_digamma :
    HasLogRatApprox (fun z : ℂ => Complex.digamma z) := by
  simpa using (hasLogRatApprox_digamma_shift (lam := (0 : ℝ)) le_rfl)

/-- Digamma has polynomial growth on every fixed vertical tube. -/
theorem hasTubePolyGrowth_digamma :
    HasTubePolyGrowth (fun z : ℂ => Complex.digamma z) :=
  HasLogRatApprox.hasTubePolyGrowth hasLogRatApprox_digamma

end

end GaloisForLFunctions.HTGeometry
