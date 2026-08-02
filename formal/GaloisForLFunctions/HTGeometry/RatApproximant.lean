import GaloisForLFunctions.HTGeometry.RationalTubeGrowth
import GaloisForLFunctions.HTGeometry.ShiftedDigammaExpansionVertical

/-!
# Rational approximants on a vertical tube

The expansions of the digamma jets produce polynomials in `1/s`.  Such a polynomial is a rational
function of `s` whose denominator is a power of `s`, so the natural class to carry through the
algebra is: functions that on every tube are approximated, to every order in the height, by a
quotient of two polynomials.

The class contains the rational functions themselves and the shifted digamma jets, and is closed
under sums and products — for the product the two approximation orders are raised by the growth
exponents of the other factor, which the class itself supplies.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The reversal that turns a polynomial in `1/s` into a polynomial in `s`. -/
def invReverse (Q : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (Q.natDegree + 1),
    Polynomial.C (Q.coeff k) * Polynomial.X ^ (Q.natDegree - k)

theorem eval_invReverse (Q : Polynomial ℂ) {s : ℂ} (hs : s ≠ 0) :
    (invReverse Q).eval s = s ^ Q.natDegree * Q.eval (1 / s) := by
  rw [invReverse, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum_range (p := Q) (1 / s), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkey : s ^ (Q.natDegree - k) = s ^ Q.natDegree / s ^ k := by
    rw [eq_div_iff (pow_ne_zero k hs), ← pow_add]
    congr 1
    omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hkey, div_pow, one_pow]
  ring

/-- A polynomial in `1/s` is a quotient of two polynomials in `s`. -/
theorem eval_inv_eq_div (Q : Polynomial ℂ) {s : ℂ} (hs : s ≠ 0) :
    Q.eval (1 / s) = (invReverse Q).eval s / (Polynomial.X ^ Q.natDegree).eval s := by
  rw [Polynomial.eval_pow, Polynomial.eval_X, eval_invReverse Q hs, mul_comm,
    mul_div_assoc, div_self (pow_ne_zero _ hs), mul_one]

/-- Approximation on every tube, to every order in the height, by a quotient of polynomials. -/
def HasRatApprox (f : ℂ → ℂ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ N : ℕ, ∃ (p q : Polynomial ℂ) (C T : ℝ), q ≠ 0 ∧ 0 ≤ C ∧ 2 ≤ T ∧
    ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)
          - Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) p
            / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q‖ ≤ C / t ^ N

/-- An approximable function has polynomial tube growth: the zeroth-order approximant is a rational
function, and the error it leaves is bounded. -/
theorem HasRatApprox.hasTubePolyGrowth {f : ℂ → ℂ} (hf : HasRatApprox f) :
    HasTubePolyGrowth f := by
  intro M hM
  obtain ⟨p, q, C, T, hq, hC, hT, hb⟩ := hf M hM 0
  obtain ⟨m, C', T', hC', hT', hb'⟩ := hasTubePolyGrowth_ratEval p hq M hM
  refine ⟨m, C + C', max T T', by positivity, le_trans hT (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have h1 := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hb' σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hT (le_trans (le_max_left _ _) ht)
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htm : (1 : ℝ) ≤ t ^ m := one_le_pow₀ ht1
  rw [pow_zero, div_one] at h1
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsplit : ‖f s‖ ≤ ‖f s - Polynomial.eval s p / Polynomial.eval s q‖
      + ‖Polynomial.eval s p / Polynomial.eval s q‖ := by
    have := norm_add_le (f s - Polynomial.eval s p / Polynomial.eval s q)
      (Polynomial.eval s p / Polynomial.eval s q)
    simpa using this
  nlinarith

/-- A quotient of polynomials approximates itself. -/
theorem hasRatApprox_ratEval (p : Polynomial ℂ) {q : Polynomial ℂ} (hq : q ≠ 0) :
    HasRatApprox (fun z => Polynomial.eval z p / Polynomial.eval z q) := by
  intro M hM N
  exact ⟨p, q, 0, 2, hq, le_rfl, le_rfl, fun σ t _ _ _ => by simp⟩

theorem hasRatApprox_const (a : ℂ) : HasRatApprox (fun _ => a) := by
  have h := hasRatApprox_ratEval (Polynomial.C a) (q := 1) one_ne_zero
  simpa using h

theorem HasRatApprox.add {f g : ℂ → ℂ} (hf : HasRatApprox f) (hg : HasRatApprox g) :
    HasRatApprox (fun z => f z + g z) := by
  intro M hM N
  obtain ⟨p₁, q₁, C₁, T₁, hq₁, hC₁, hT₁, hb₁⟩ := hf M hM N
  obtain ⟨p₂, q₂, C₂, T₂, hq₂, hC₂, hT₂, hb₂⟩ := hg M hM N
  obtain ⟨U₁, hU₁, hne₁⟩ := exists_height_polyEval_ne_zero hq₁
  obtain ⟨U₂, hU₂, hne₂⟩ := exists_height_polyEval_ne_zero hq₂
  refine ⟨p₁ * q₂ + q₁ * p₂, q₁ * q₂, C₁ + C₂, max (max T₁ T₂) (max U₁ U₂),
    mul_ne_zero hq₁ hq₂, by linarith, le_trans hT₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun σ t hσ hσM ht => ?_⟩
  have h1 := hb₁ σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
  have h2 := hb₂ σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
  have hz₁ := hne₁ σ t (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
  have hz₂ := hne₂ σ t (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht)
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsplit : f s + g s - Polynomial.eval s (p₁ * q₂ + q₁ * p₂) / Polynomial.eval s (q₁ * q₂)
      = (f s - Polynomial.eval s p₁ / Polynomial.eval s q₁)
        + (g s - Polynomial.eval s p₂ / Polynomial.eval s q₂) := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
      ← div_add_div _ _ hz₁ hz₂]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hsum : C₁ / t ^ N + C₂ / t ^ N = (C₁ + C₂) / t ^ N := by ring
  linarith

theorem HasRatApprox.neg {f : ℂ → ℂ} (hf : HasRatApprox f) : HasRatApprox (fun z => -f z) := by
  intro M hM N
  obtain ⟨p, q, C, T, hq, hC, hT, hb⟩ := hf M hM N
  refine ⟨-p, q, C, T, hq, hC, hT, fun σ t hσ hσM ht => ?_⟩
  have h := hb σ t hσ hσM ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsplit : -f s - Polynomial.eval s (-p) / Polynomial.eval s q
      = -(f s - Polynomial.eval s p / Polynomial.eval s q) := by
    rw [Polynomial.eval_neg, neg_div]
    ring
  rw [hsplit, norm_neg]
  exact h

theorem HasRatApprox.sub {f g : ℂ → ℂ} (hf : HasRatApprox f) (hg : HasRatApprox g) :
    HasRatApprox (fun z => f z - g z) := by
  have h := hf.add hg.neg
  simpa [sub_eq_add_neg] using h

theorem HasRatApprox.mul {f g : ℂ → ℂ} (hf : HasRatApprox f) (hg : HasRatApprox g) :
    HasRatApprox (fun z => f z * g z) := by
  intro M hM N
  obtain ⟨mf, Cf, Tf, hCf, hTf, hbf⟩ := hf.hasTubePolyGrowth M hM
  obtain ⟨mg, Cg, Tg, hCg, hTg, hbg⟩ := hg.hasTubePolyGrowth M hM
  obtain ⟨p₁, q₁, C₁, T₁, hq₁, hC₁, hT₁, hb₁⟩ := hf M hM (N + mg)
  obtain ⟨p₂, q₂, C₂, T₂, hq₂, hC₂, hT₂, hb₂⟩ := hg M hM (N + mf)
  refine ⟨p₁ * p₂, q₁ * q₂, Cf * C₂ + (Cg + C₂) * C₁, max (max Tf Tg) (max T₁ T₂),
    mul_ne_zero hq₁ hq₂, by positivity,
    le_trans hTf (le_trans (le_max_left _ _) (le_max_left _ _)), fun σ t hσ hσM ht => ?_⟩
  have hgf := hbf σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
  have hgg := hbg σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
  have h1 := hb₁ σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
  have h2 := hb₂ σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht)
  have ht2 : (2 : ℝ) ≤ t := le_trans hTf (le_trans (le_max_left _ _) (le_max_left _ _)) |>.trans ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set A₁ : ℂ := Polynomial.eval s p₁ / Polynomial.eval s q₁ with hA₁
  set A₂ : ℂ := Polynomial.eval s p₂ / Polynomial.eval s q₂ with hA₂
  have hprod : Polynomial.eval s (p₁ * p₂) / Polynomial.eval s (q₁ * q₂) = A₁ * A₂ := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hA₁, hA₂, div_mul_div_comm]
  rw [hprod]
  have hsplit : f s * g s - A₁ * A₂ = f s * (g s - A₂) + A₂ * (f s - A₁) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  -- the second approximant inherits the growth of `g`
  have hA₂bound : ‖A₂‖ ≤ (Cg + C₂) * t ^ mg := by
    have hsub : ‖A₂‖ ≤ ‖g s‖ + ‖g s - A₂‖ := by
      have := norm_sub_le (g s) (g s - A₂)
      simpa using this
    have hdec : C₂ / t ^ (N + mf) ≤ C₂ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [one_le_pow₀ (n := N + mf) ht1, hC₂]
    have hone : (1 : ℝ) ≤ t ^ mg := one_le_pow₀ ht1
    nlinarith
  have hfirst : ‖f s * (g s - A₂)‖ ≤ Cf * C₂ / t ^ N := by
    rw [norm_mul]
    have hb : ‖f s‖ * ‖g s - A₂‖ ≤ (Cf * t ^ mf) * (C₂ / t ^ (N + mf)) :=
      mul_le_mul hgf h2 (norm_nonneg _) (by positivity)
    refine le_trans hb (le_of_eq ?_)
    rw [pow_add]
    field_simp
  have hsecond : ‖A₂ * (f s - A₁)‖ ≤ (Cg + C₂) * C₁ / t ^ N := by
    rw [norm_mul]
    have hb : ‖A₂‖ * ‖f s - A₁‖ ≤ ((Cg + C₂) * t ^ mg) * (C₁ / t ^ (N + mg)) :=
      mul_le_mul hA₂bound h1 (norm_nonneg _) (by positivity)
    refine le_trans hb (le_of_eq ?_)
    rw [pow_add]
    field_simp
  have hadd : Cf * C₂ / t ^ N + (Cg + C₂) * C₁ / t ^ N
      = (Cf * C₂ + (Cg + C₂) * C₁) / t ^ N := by ring
  linarith

/-- **The shifted digamma jets are approximable.**  Their vertical expansion is a polynomial in
`1/s`, hence a quotient of polynomials, and its error beats every power of the height. -/
theorem hasRatApprox_iteratedDeriv_digamma_shift {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    HasRatApprox (fun z => iteratedDeriv (j + 1) Complex.digamma (z + (lam : ℂ))) := by
  intro M hM N
  obtain ⟨Q, C, T, hC, hT, hb⟩ := exists_iteratedDeriv_digamma_shift_expansion lam j N
  refine ⟨invReverse Q, Polynomial.X ^ Q.natDegree, C, T, pow_ne_zero _ Polynomial.X_ne_zero,
    hC, hT, fun σ t hσ hσM ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos htpos
  have hval := hb σ t hσ (by linarith) ht
  have harg : (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ) := by
    push_cast
    ring
  rw [harg] at hval
  rw [← eval_inv_eq_div Q hs]
  refine le_trans hval ?_
  have hpow : t ^ N ≤ t ^ (N + 1) := by
    refine pow_le_pow_right₀ ht1 ?_
    omega
  refine div_le_div_of_nonneg_left hC (by positivity) hpow

end

end GaloisForLFunctions.HTGeometry
