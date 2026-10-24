import GaloisForLFunctions.RHTower.XiSliceHeatCoshCountermodel

/-!
# Exact heat law for a Gaussian background with a double pair factor

The literal Gaussian average of `exp(a*x²) * (δ²-x²)²` is integrable when
`λ > 0` and `2*a*λ < 1`. Completing the square gives its Mehler formula.
Its everywhere convergent even power series has coefficient sign

`(X-k-t)² + (4*t-1)*k + 2*t²`,

where `t=a*λ` and `X=a*(1-2*a*λ)*δ²`. For `a > 0`, all offsets have
nonnegative coefficients exactly when `a*λ ≥ 1/4`. Below this threshold,
an explicit integer coefficient is negative at every sufficiently large offset.
-/

open MeasureTheory Filter Topology

namespace RHTower.DeBruijn
noncomputable section

/-- The variance rescaling in the Gaussian heat transform. -/
def gaussianModelScale (a lam : ℝ) : ℝ := 1 - 2 * a * lam

/-- A Gaussian background with a squared pair factor. -/
def gaussianModel (δ a x : ℝ) : ℝ := Real.exp (a * x ^ 2) * (δ ^ 2 - x ^ 2) ^ 2

/-- Gaussian heat of variance `λ`, defined by its actual integral. -/
def gaussianModelHeat (δ a lam x : ℝ) : ℝ :=
  ∫ u : ℝ, gaussDensity (lam / 2) u * gaussianModel δ a (x + u)

theorem gaussianModelScale_pos {a lam : ℝ} (h : 2 * a * lam < 1) :
    0 < gaussianModelScale a lam := sub_pos.mpr h

theorem gaussianModel_offset (δ a : ℝ) : gaussianModel δ a δ = 0 := by
  simp only [gaussianModel, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- Completing the square preserves the normalization as well as the exponent. -/
theorem gaussDensity_mul_exp_sq_mehler {a lam : ℝ}
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (x u : ℝ) :
    gaussDensity (lam / 2) u * Real.exp (a * (x + u) ^ 2) =
      gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        Real.exp (a / gaussianModelScale a lam * x ^ 2) *
          gaussDensity ((lam / gaussianModelScale a lam) / 2)
            (u - 2 * a * lam * x / gaussianModelScale a lam) := by
  have hm := gaussianModelScale_pos hconv
  have hnorm : (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ)) =
      gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        (4 * Real.pi * ((lam / gaussianModelScale a lam) / 2)) ^ (-(1 / 2 : ℝ)) := by
    rw [show 4 * Real.pi * ((lam / gaussianModelScale a lam) / 2) =
        (4 * Real.pi * (lam / 2)) / gaussianModelScale a lam by ring,
      Real.div_rpow (by positivity) hm.le]
    field_simp [(Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ))).ne']
  have hexp : -(u ^ 2 / (4 * (lam / 2))) + a * (x + u) ^ 2 =
      a / gaussianModelScale a lam * x ^ 2 +
        -((u - 2 * a * lam * x / gaussianModelScale a lam) ^ 2 /
          (4 * ((lam / gaussianModelScale a lam) / 2))) := by
    field_simp [hlam.ne', hm.ne']
    dsimp only [gaussianModelScale]
    ring
  unfold gaussDensity
  rw [mul_assoc, ← Real.exp_add, hexp, hnorm, Real.exp_add]
  ring

/-- The Mehler formula for the quartic model, including absolute integrability. -/
theorem integrable_and_integral_gaussianModel {a lam : ℝ}
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (δ x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * gaussianModel δ a (x + u)) ∧
      gaussianModelHeat δ a lam x =
        gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
          Real.exp (a / gaussianModelScale a lam * x ^ 2) *
            coshModelQuartic δ (lam / gaussianModelScale a lam)
              (x / gaussianModelScale a lam) := by
  have hm := gaussianModelScale_pos hconv
  obtain ⟨hi, hv⟩ := integrable_and_integral_gaussDensity_quartic
    (div_pos hlam hm) δ (x / gaussianModelScale a lam)
  have harg (u : ℝ) : x + u = x / gaussianModelScale a lam +
      (u - 2 * a * lam * x / gaussianModelScale a lam) := by
    field_simp [hm.ne']
    dsimp only [gaussianModelScale]
    ring
  have hf : (fun u : ℝ => gaussDensity (lam / 2) u * gaussianModel δ a (x + u)) =
      fun u => (gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        Real.exp (a / gaussianModelScale a lam * x ^ 2)) *
          ((fun v => gaussDensity ((lam / gaussianModelScale a lam) / 2) v *
            (δ ^ 2 - (x / gaussianModelScale a lam + v) ^ 2) ^ 2)
              (u - 2 * a * lam * x / gaussianModelScale a lam)) := by
    funext u
    dsimp only [gaussianModel]
    rw [← mul_assoc, gaussDensity_mul_exp_sq_mehler hlam hconv, harg u]
    ring
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact (hi.comp_sub_right _).const_mul _
  · unfold gaussianModelHeat
    rw [hf, integral_const_mul, integral_sub_right_eq_self
      (fun v : ℝ => gaussDensity ((lam / gaussianModelScale a lam) / 2) v *
        (δ ^ 2 - (x / gaussianModelScale a lam + v) ^ 2) ^ 2), hv]

theorem gaussianModelHeat_eq {a lam : ℝ}
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (δ x : ℝ) :
    gaussianModelHeat δ a lam x =
      gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        Real.exp (a / gaussianModelScale a lam * x ^ 2) *
          coshModelQuartic δ (lam / gaussianModelScale a lam)
            (x / gaussianModelScale a lam) :=
  (integrable_and_integral_gaussianModel hlam hconv δ x).2

/-- The coefficient sign polynomial, written as a square plus an affine term. -/
def gaussianModelCoefficientPolynomial (t X : ℝ) (k : ℕ) : ℝ :=
  (X - (k : ℝ) - t) ^ 2 + (4 * t - 1) * (k : ℝ) + 2 * t ^ 2

theorem gaussianModelCoefficientPolynomial_eq (t X : ℝ) (k : ℕ) :
    gaussianModelCoefficientPolynomial t X k =
      (k : ℝ) * ((k : ℝ) - 1) + (6 * t - 2 * X) * (k : ℝ) +
        (X ^ 2 - 2 * t * X + 3 * t ^ 2) := by
  unfold gaussianModelCoefficientPolynomial
  ring

/-- The coefficient of `x^(2*k)` in the heated Gaussian model. -/
def gaussianModelHeatCoeff (δ a lam : ℝ) (k : ℕ) : ℝ :=
  gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
    (a / gaussianModelScale a lam) ^ k /
      ((k.factorial : ℝ) * (a * gaussianModelScale a lam) ^ 2) *
        gaussianModelCoefficientPolynomial (a * lam)
          (a * gaussianModelScale a lam * δ ^ 2) k

private theorem exp_series (z : ℝ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp z

private theorem exp_series_first (z : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (z ^ n / (n.factorial : ℝ)))
      (z * Real.exp z) := by
  have hs (n : ℕ) : ((n + 1 : ℕ) : ℝ) * (z ^ (n + 1) / ((n + 1).factorial : ℝ)) =
      z * (z ^ n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have h : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * (z ^ (n + 1) / ((n + 1).factorial : ℝ)))
      (z * Real.exp z) := by simpa only [hs] using (exp_series z).mul_left z
  simpa using (hasSum_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * (z ^ n / (n.factorial : ℝ))) 1).1 h

private theorem exp_series_second (z : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (z ^ n / (n.factorial : ℝ)))
      (z ^ 2 * Real.exp z) := by
  have hs (n : ℕ) : ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
      (z ^ (n + 2) / ((n + 2).factorial : ℝ)) = z ^ 2 * (z ^ n / (n.factorial : ℝ)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      pow_add]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn' : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have h : HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
      (z ^ (n + 2) / ((n + 2).factorial : ℝ))) (z ^ 2 * Real.exp z) := by
    simpa only [hs] using (exp_series z).mul_left (z ^ 2)
  simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (z ^ n / (n.factorial : ℝ))) 2).1 h

private theorem exp_series_quadratic (z b c : ℝ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ) *
      ((n : ℝ) * ((n : ℝ) - 1) + b * (n : ℝ) + c))
        (Real.exp z * (z ^ 2 + b * z + c)) := by
  have h := ((exp_series_second z).add ((exp_series_first z).mul_left b)).add
    ((exp_series z).mul_left c)
  convert h using 1
  · ext n
    ring
  · ring

/-- An everywhere convergent even series for the literal heat integral. -/
theorem hasSum_gaussianModelHeatCoeff {a lam : ℝ} (ha : 0 < a)
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (δ x : ℝ) :
    HasSum (fun k : ℕ => gaussianModelHeatCoeff δ a lam k * x ^ (2 * k))
      (gaussianModelHeat δ a lam x) := by
  have hm := gaussianModelScale_pos hconv
  have h := (exp_series_quadratic (a / gaussianModelScale a lam * x ^ 2)
    (6 * (a * lam) - 2 * (a * gaussianModelScale a lam * δ ^ 2))
    ((a * gaussianModelScale a lam * δ ^ 2) ^ 2 -
      2 * (a * lam) * (a * gaussianModelScale a lam * δ ^ 2) + 3 * (a * lam) ^ 2)).mul_left
        (gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) / (a * gaussianModelScale a lam) ^ 2)
  have hv : gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) / (a * gaussianModelScale a lam) ^ 2 *
      (Real.exp (a / gaussianModelScale a lam * x ^ 2) *
        ((a / gaussianModelScale a lam * x ^ 2) ^ 2 +
          (6 * (a * lam) - 2 * (a * gaussianModelScale a lam * δ ^ 2)) *
            (a / gaussianModelScale a lam * x ^ 2) +
          ((a * gaussianModelScale a lam * δ ^ 2) ^ 2 -
            2 * (a * lam) * (a * gaussianModelScale a lam * δ ^ 2) + 3 * (a * lam) ^ 2))) =
        gaussianModelHeat δ a lam x := by
    rw [gaussianModelHeat_eq hlam hconv]
    unfold coshModelQuartic
    field_simp [ha.ne', hm.ne']
    ring
  rw [hv] at h
  refine h.congr_fun fun k => ?_
  simp only [gaussianModelHeatCoeff, gaussianModelCoefficientPolynomial_eq, mul_pow, pow_mul]
  ring

/-- Ordinary power series coefficients, with every odd coefficient zero. -/
def gaussianModelHeatTaylorCoeff (δ a lam : ℝ) (n : ℕ) : ℝ :=
  if Even n then gaussianModelHeatCoeff δ a lam (n / 2) else 0

@[simp] theorem gaussianModelHeatTaylorCoeff_even (δ a lam : ℝ) (k : ℕ) :
    gaussianModelHeatTaylorCoeff δ a lam (2 * k) = gaussianModelHeatCoeff δ a lam k := by
  have he : Even (2 * k) := ⟨k, by omega⟩
  simp [gaussianModelHeatTaylorCoeff, he]

@[simp] theorem gaussianModelHeatTaylorCoeff_odd (δ a lam : ℝ) (k : ℕ) :
    gaussianModelHeatTaylorCoeff δ a lam (2 * k + 1) = 0 := by
  have he : ¬ Even (2 * k + 1) := by rintro ⟨j, hj⟩; omega
  simp only [gaussianModelHeatTaylorCoeff, if_neg he]

theorem hasSum_gaussianModelHeatTaylorCoeff {a lam : ℝ} (ha : 0 < a)
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (δ x : ℝ) :
    HasSum (fun n : ℕ => gaussianModelHeatTaylorCoeff δ a lam n * x ^ n)
      (gaussianModelHeat δ a lam x) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun i j hij => by
    dsimp only at hij
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      gaussianModelHeatTaylorCoeff δ a lam n * x ^ n = 0 := by
    intro n hn
    have he : ¬ Even n := by
      rintro ⟨k, hk⟩
      exact hn ⟨k, by dsimp only; omega⟩
    simp only [gaussianModelHeatTaylorCoeff, if_neg he, zero_mul]
  rw [← hinj.hasSum_iff hzero]
  simpa only [Function.comp_def, gaussianModelHeatTaylorCoeff_even] using
    hasSum_gaussianModelHeatCoeff ha hlam hconv δ x

private theorem coefficient_prefactor_pos {a lam : ℝ} (ha : 0 < a)
    (hconv : 2 * a * lam < 1) (k : ℕ) :
    0 < gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
      (a / gaussianModelScale a lam) ^ k /
        ((k.factorial : ℝ) * (a * gaussianModelScale a lam) ^ 2) := by
  have hm := gaussianModelScale_pos hconv
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hm _) (pow_pos (div_pos ha hm) _))
    (mul_pos hf (sq_pos_of_pos (mul_pos ha hm)))

/-- At and above the threshold every even coefficient is strictly positive. -/
theorem gaussianModelHeatCoeff_pos {a lam : ℝ} (ha : 0 < a)
    (hconv : 2 * a * lam < 1) (hthreshold : 1 / 4 ≤ a * lam) (δ : ℝ) (k : ℕ) :
    0 < gaussianModelHeatCoeff δ a lam k := by
  apply mul_pos (coefficient_prefactor_pos ha hconv k)
  have ht : 0 < a * lam := lt_of_lt_of_le (by norm_num) hthreshold
  have hk : 0 ≤ (4 * (a * lam) - 1) * (k : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hs := sq_nonneg (a * gaussianModelScale a lam * δ ^ 2 - (k : ℝ) - a * lam)
  have ht2 := sq_pos_of_pos ht
  dsimp only [gaussianModelCoefficientPolynomial]
  linarith

/-- Below threshold a positive offset gives a strictly negative coefficient. -/
theorem exists_pos_offset_gaussianModelHeatCoeff_neg {a lam : ℝ} (ha : 0 < a)
    (hlam : 0 < lam) (hthreshold : a * lam < 1 / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ, gaussianModelHeatCoeff δ a lam k < 0 := by
  have ht := mul_pos ha hlam
  have hconv : 2 * a * lam < 1 := by nlinarith only [hthreshold]
  have hm := gaussianModelScale_pos hconv
  have hd : 0 < 1 - 4 * (a * lam) := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (a * lam) ^ 2 / (1 - 4 * (a * lam)))
  have hkp : 2 * (a * lam) ^ 2 < (k : ℝ) * (1 - 4 * (a * lam)) :=
    (div_lt_iff₀ hd).mp hk
  let δ := Real.sqrt (((k : ℝ) + a * lam) / (a * gaussianModelScale a lam))
  have hδarg : 0 < ((k : ℝ) + a * lam) / (a * gaussianModelScale a lam) :=
    div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) ht) (mul_pos ha hm)
  have hδ : 0 < δ := Real.sqrt_pos.2 hδarg
  have hX : a * gaussianModelScale a lam * δ ^ 2 = (k : ℝ) + a * lam := by
    rw [show δ ^ 2 = ((k : ℝ) + a * lam) / (a * gaussianModelScale a lam) from
      Real.sq_sqrt hδarg.le]
    field_simp
  refine ⟨δ, hδ, k, mul_neg_of_pos_of_neg (coefficient_prefactor_pos ha hconv k) ?_⟩
  dsimp only [gaussianModelCoefficientPolynomial]
  rw [hX]
  nlinarith only [hkp]

/-- Exact threshold for nonnegative coefficients at every offset. -/
theorem forall_gaussianModelHeatCoeff_nonneg_iff {a lam : ℝ} (ha : 0 < a)
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) :
    (∀ δ : ℝ, ∀ k : ℕ, 0 ≤ gaussianModelHeatCoeff δ a lam k) ↔ 1 / 4 ≤ a * lam := by
  constructor
  · intro h
    by_contra ht
    obtain ⟨δ, _, k, hk⟩ := exists_pos_offset_gaussianModelHeatCoeff_neg ha hlam (lt_of_not_ge ht)
    exact (not_lt_of_ge (h δ k)) hk
  · intro ht δ k
    exact (gaussianModelHeatCoeff_pos ha hconv ht δ k).le

/-- A natural floor supplies an explicit detecting coefficient, including rounding. -/
theorem gaussianModelCoefficientPolynomial_floor_neg {t X : ℝ} (ht : t < 1 / 4)
    (hX : 1 + (1 + 2 * t ^ 2) / (1 - 4 * t) < X - t) :
    gaussianModelCoefficientPolynomial t X (Nat.floor (X - t)) < 0 := by
  have hd : 0 < 1 - 4 * t := by linarith
  have hq : 0 < (1 + 2 * t ^ 2) / (1 - 4 * t) := div_pos (by positivity) hd
  have hy : 0 ≤ X - t := by linarith
  have hlo := Nat.floor_le hy
  have hhi := Nat.lt_floor_add_one (X - t)
  have hfrac0 : 0 ≤ X - t - (Nat.floor (X - t) : ℝ) := sub_nonneg.mpr hlo
  have hfrac1 : X - t - (Nat.floor (X - t) : ℝ) < 1 := by linarith
  have hsq : (X - t - (Nat.floor (X - t) : ℝ)) ^ 2 < 1 := by
    nlinarith only [hfrac0, hfrac1]
  have hk : (1 + 2 * t ^ 2) / (1 - 4 * t) < (Nat.floor (X - t) : ℝ) := by linarith
  have hprod := (div_lt_iff₀ hd).mp hk
  dsimp only [gaussianModelCoefficientPolynomial]
  nlinarith only [hsq, hprod]

/-- Every sufficiently large fixed offset has a negative coefficient below threshold. -/
theorem gaussianModelHeatCoeff_floor_neg {δ a lam : ℝ} (ha : 0 < a)
    (hconv : 2 * a * lam < 1) (hthreshold : a * lam < 1 / 4)
    (hδ : 1 + (1 + 2 * (a * lam) ^ 2) / (1 - 4 * (a * lam)) <
      a * gaussianModelScale a lam * δ ^ 2 - a * lam) :
    gaussianModelHeatCoeff δ a lam
      (Nat.floor (a * gaussianModelScale a lam * δ ^ 2 - a * lam)) < 0 :=
  mul_neg_of_pos_of_neg (coefficient_prefactor_pos ha hconv _)
    (gaussianModelCoefficientPolynomial_floor_neg hthreshold hδ)

/-- Below the sharp scaled heat, every fixed positive offset is detected in all sufficiently
dense Gaussian backgrounds. The bound is uniform over every density above one explicit cutoff. -/
theorem exists_dense_gaussianModelHeatCoeff_neg {δ κ : ℝ} (hδ : 0 < δ)
    (hκ : 0 < κ) (hthreshold : κ < 1 / 4) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ k : ℕ, gaussianModelHeatCoeff δ a (κ / a) k < 0 := by
  have hm : 0 < 1 - 2 * κ := by linarith
  have hd : 0 < 1 - 4 * κ := by linarith
  have hden : 0 < (1 - 2 * κ) * δ ^ 2 := mul_pos hm (sq_pos_of_pos hδ)
  let C := κ + 1 + (1 + 2 * κ ^ 2) / (1 - 4 * κ)
  have hC : 0 < C := by dsimp only [C]; positivity
  let A := (C + 1) / ((1 - 2 * κ) * δ ^ 2)
  have hA : 0 < A := div_pos (by linarith) hden
  refine ⟨A, hA, fun a ha => ?_⟩
  have ha0 : 0 < a := hA.trans_le ha
  have he : a * (κ / a) = κ := by field_simp
  have hconv : 2 * a * (κ / a) < 1 := by nlinarith only [he, hm]
  have hscale : gaussianModelScale a (κ / a) = 1 - 2 * κ := by
    unfold gaussianModelScale
    nlinarith only [he]
  have hbound : C + 1 ≤ a * ((1 - 2 * κ) * δ ^ 2) := (div_le_iff₀ hden).mp ha
  have hoffset : 1 + (1 + 2 * (a * (κ / a)) ^ 2) / (1 - 4 * (a * (κ / a))) <
      a * gaussianModelScale a (κ / a) * δ ^ 2 - a * (κ / a) := by
    rw [he, hscale]
    dsimp only [C] at hbound
    nlinarith only [hbound]
  exact ⟨_, gaussianModelHeatCoeff_floor_neg ha0 hconv (by rwa [he]) hoffset⟩

/-- Above the sharp scaled heat, positivity needs no limiting density. -/
theorem gaussianModelHeatCoeff_pos_at_scaled_heat {a κ : ℝ} (ha : 0 < a)
    (hthreshold : 1 / 4 ≤ κ) (hconv : κ < 1 / 2) (δ : ℝ) (k : ℕ) :
    0 < gaussianModelHeatCoeff δ a (κ / a) k := by
  have he : a * (κ / a) = κ := by field_simp
  exact gaussianModelHeatCoeff_pos ha (by nlinarith only [he, hconv]) (by rwa [he]) δ k

/-- The ordinary coefficients, including the zero odd coefficients, have the same exact threshold. -/
theorem forall_gaussianModelHeatTaylorCoeff_nonneg_iff {a lam : ℝ} (ha : 0 < a)
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) :
    (∀ δ : ℝ, ∀ n : ℕ, 0 ≤ gaussianModelHeatTaylorCoeff δ a lam n) ↔ 1 / 4 ≤ a * lam := by
  rw [← forall_gaussianModelHeatCoeff_nonneg_iff ha hlam hconv]
  constructor
  · intro h δ k
    simpa only [gaussianModelHeatTaylorCoeff_even] using h δ (2 * k)
  · intro h δ n
    unfold gaussianModelHeatTaylorCoeff
    split_ifs
    · exact h δ (n / 2)
    · exact le_rfl

end
end RHTower.DeBruijn
