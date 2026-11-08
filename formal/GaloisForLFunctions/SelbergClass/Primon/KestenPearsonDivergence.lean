import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodRatios

/-!
# Exact Pearson divergences of prime spectral laws

The actual Radon--Nikodym derivatives have integrable squared deviations
from one. Their expectations give rational closed formulas for both
semicircle comparisons and every ordered prime pair.
-/

open MeasureTheory Filter

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Pearson divergence from a prime spectral law to the semicircle law. -/
def kestenSemicirclePearsonDivergence (p : Nat.Primes) : ℝ :=
  ∫ x, (((kestenSpectralLaw p : Measure ℝ).rnDeriv (semicircleSpectralLaw : Measure ℝ) x).toReal - 1) ^ 2
    ∂(semicircleSpectralLaw : Measure ℝ)

/-- Pearson divergence from the semicircle law to a prime spectral law. -/
def semicircleKestenPearsonDivergence (p : Nat.Primes) : ℝ :=
  ∫ x, (((semicircleSpectralLaw : Measure ℝ).rnDeriv (kestenSpectralLaw p : Measure ℝ) x).toReal - 1) ^ 2
    ∂(kestenSpectralLaw p : Measure ℝ)

/-- Pearson divergence between two ordered prime spectral laws. -/
def kestenPearsonDivergence (p q : Nat.Primes) : ℝ :=
  ∫ x, (((kestenSpectralLaw p : Measure ℝ).rnDeriv (kestenSpectralLaw q : Measure ℝ) x).toReal - 1) ^ 2
    ∂(kestenSpectralLaw q : Measure ℝ)

/-- The prime-to-semicircle Radon--Nikodym derivative is the rational likelihood. -/
theorem rnDeriv_kesten_semicircle_toReal (p : Nat.Primes) :
    (fun x => ((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (semicircleSpectralLaw : Measure ℝ) x).toReal) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
        kestenLikelihood p := by
  have hr : (kestenSpectralLaw p : Measure ℝ).rnDeriv (semicircleSpectralLaw : Measure ℝ) =ᵐ[
      (semicircleSpectralLaw : Measure ℝ)]
      (fun u => ENNReal.ofReal (kestenBetaWeight p u)) ∘ heckeSquareCoordinate := by
    rw [kestenSpectralLaw_eq_semicircle_withDensity]
    exact Measure.rnDeriv_withDensity _
      ((continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        continuous_heckeSquareCoordinate.measurable)
  filter_upwards [hr] with x hx
  rw [hx]
  exact ENNReal.toReal_ofReal (kestenLikelihood_pos p x).le

/-- The reverse Radon--Nikodym derivative is the reciprocal likelihood. -/
theorem rnDeriv_semicircle_kesten_toReal (p : Nat.Primes) :
    (fun x => ((semicircleSpectralLaw : Measure ℝ).rnDeriv
      (kestenSpectralLaw p : Measure ℝ) x).toReal) =ᵐ[(kestenSpectralLaw p : Measure ℝ)]
        (fun x => (kestenLikelihood p x)⁻¹) := by
  have hm : Measurable (fun u : ℝ => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) :=
    (continuous_kestenBetaWeight p).measurable.inv.ennreal_ofReal
  have hr : (semicircleSpectralLaw : Measure ℝ).rnDeriv (kestenSpectralLaw p : Measure ℝ) =ᵐ[
      (kestenSpectralLaw p : Measure ℝ)]
      (fun u => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) ∘ heckeSquareCoordinate := by
    rw [semicircleSpectralLaw_eq_kesten_withDensity]
    exact Measure.rnDeriv_withDensity _ (hm.comp continuous_heckeSquareCoordinate.measurable)
  filter_upwards [hr] with x hx
  rw [hx]
  exact ENNReal.toReal_ofReal (inv_nonneg.mpr (kestenLikelihood_pos p x).le)

/-- Every pairwise Radon--Nikodym derivative is a quotient of rational likelihoods. -/
theorem rnDeriv_kesten_prime_toReal (p q : Nat.Primes) :
    (fun x => ((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (kestenSpectralLaw q : Measure ℝ) x).toReal) =ᵐ[(kestenSpectralLaw q : Measure ℝ)]
        (fun x => kestenLikelihood p x / kestenLikelihood q x) := by
  have hm : Measurable (fun u : ℝ =>
      ENNReal.ofReal (kestenBetaWeight p u / kestenBetaWeight q u)) :=
    ((continuous_kestenBetaWeight p).measurable.div (continuous_kestenBetaWeight q).measurable).ennreal_ofReal
  have hr : (kestenSpectralLaw p : Measure ℝ).rnDeriv (kestenSpectralLaw q : Measure ℝ) =ᵐ[
      (kestenSpectralLaw q : Measure ℝ)]
      (fun u => ENNReal.ofReal (kestenBetaWeight p u / kestenBetaWeight q u)) ∘
        heckeSquareCoordinate := by
    rw [kestenSpectralLaw_eq_prime_withDensity p q]
    exact Measure.rnDeriv_withDensity _ (hm.comp continuous_heckeSquareCoordinate.measurable)
  filter_upwards [hr] with x hx
  rw [hx]
  exact ENNReal.toReal_ofReal (div_nonneg (kestenLikelihood_pos p x).le (kestenLikelihood_pos q x).le)

/-- The actual prime-to-semicircle squared Radon--Nikodym deviation is integrable. -/
theorem integrable_kesten_semicircle_pearson (p : Nat.Primes) :
    Integrable (fun x => (((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (semicircleSpectralLaw : Measure ℝ) x).toReal - 1) ^ 2) (semicircleSpectralLaw : Measure ℝ) := by
  have hi : Integrable (fun x => (kestenLikelihood p x - 1) ^ 2)
      (semicircleSpectralLaw : Measure ℝ) := integrable_semicircleSpectralLaw_continuous
        ⟨_, ((continuous_kestenLikelihood p).sub continuous_const).pow 2⟩
  apply hi.congr
  filter_upwards [rnDeriv_kesten_semicircle_toReal p] with x hx
  rw [hx]

/-- The actual reverse squared Radon--Nikodym deviation is integrable. -/
theorem integrable_semicircle_kesten_pearson (p : Nat.Primes) :
    Integrable (fun x => (((semicircleSpectralLaw : Measure ℝ).rnDeriv
      (kestenSpectralLaw p : Measure ℝ) x).toReal - 1) ^ 2) (kestenSpectralLaw p : Measure ℝ) := by
  have hi : Integrable (fun x => ((kestenLikelihood p x)⁻¹ - 1) ^ 2)
      (kestenSpectralLaw p : Measure ℝ) := integrable_kestenSpectralLaw_continuous p
        ⟨_, ((continuous_kestenLikelihood_inv p).sub continuous_const).pow 2⟩
  apply hi.congr
  filter_upwards [rnDeriv_semicircle_kesten_toReal p] with x hx
  rw [hx]

/-- Every actual pairwise squared Radon--Nikodym deviation is integrable. -/
theorem integrable_kesten_prime_pearson (p q : Nat.Primes) :
    Integrable (fun x => (((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (kestenSpectralLaw q : Measure ℝ) x).toReal - 1) ^ 2) (kestenSpectralLaw q : Measure ℝ) := by
  have hi : Integrable (fun x => (kestenLikelihood p x / kestenLikelihood q x - 1) ^ 2)
      (kestenSpectralLaw q : Measure ℝ) := integrable_kestenSpectralLaw_continuous q
        ⟨_, ((continuous_kestenLikelihood_ratio p q).sub continuous_const).pow 2⟩
  apply hi.congr
  filter_upwards [rnDeriv_kesten_prime_toReal p q] with x hx
  rw [hx]

/-- Prime-to-semicircle Pearson divergence is the inverse quadratic prime defect. -/
theorem kestenSemicirclePearsonDivergence_eq (p : Nat.Primes) :
    kestenSemicirclePearsonDivergence p = ((p : ℝ) ^ 2 - 1)⁻¹ := by
  unfold kestenSemicirclePearsonDivergence
  have he : (fun x => (((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (semicircleSpectralLaw : Measure ℝ) x).toReal - 1) ^ 2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
        (fun x => (kestenLikelihood p x - 1) ^ 2) := by
    filter_upwards [rnDeriv_kesten_semicircle_toReal p] with x hx
    rw [hx]
  rw [integral_congr_ae he, integral_semicircleLikelihood_centered_sq]

/-- Semicircle-to-prime Pearson divergence is the reciprocal of `p(p+1)`. -/
theorem semicircleKestenPearsonDivergence_eq (p : Nat.Primes) :
    semicircleKestenPearsonDivergence p = ((p : ℝ) * ((p : ℝ) + 1))⁻¹ := by
  unfold semicircleKestenPearsonDivergence
  have he : (fun x => (((semicircleSpectralLaw : Measure ℝ).rnDeriv
      (kestenSpectralLaw p : Measure ℝ) x).toReal - 1) ^ 2) =ᵐ[(kestenSpectralLaw p : Measure ℝ)]
        (fun x => ((kestenLikelihood p x)⁻¹) ^ 2 - 2 * (kestenLikelihood p x)⁻¹ + 1) := by
    filter_upwards [rnDeriv_semicircle_kesten_toReal p] with x hx
    rw [hx]
    ring
  have hi : Integrable (fun x => (kestenLikelihood p x)⁻¹) (kestenSpectralLaw p : Measure ℝ) :=
    integrable_kestenSpectralLaw_continuous p ⟨_, continuous_kestenLikelihood_inv p⟩
  have hj : Integrable (fun x => ((kestenLikelihood p x)⁻¹) ^ 2) (kestenSpectralLaw p : Measure ℝ) :=
    integrable_kestenSpectralLaw_continuous p ⟨_, (continuous_kestenLikelihood_inv p).pow 2⟩
  rw [integral_congr_ae he,
    integral_add (f := fun x => ((kestenLikelihood p x)⁻¹) ^ 2 - 2 * (kestenLikelihood p x)⁻¹)
      (g := fun _ => 1) (hj.sub (hi.const_mul 2)) (integrable_const 1),
    integral_sub (g := fun x => 2 * (kestenLikelihood p x)⁻¹) hj (hi.const_mul 2),
    integral_const_mul, integral_kestenLikelihood_inv_sq, integral_kestenLikelihood_inv]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- Every ordered prime-pair Pearson divergence has an exact rational value. -/
theorem kestenPearsonDivergence_eq (p q : Nat.Primes) :
    kestenPearsonDivergence p q = ((p : ℝ) - (q : ℝ)) ^ 2 /
      ((q : ℝ) * ((q : ℝ) + 1) * ((p : ℝ) ^ 2 - 1)) := by
  unfold kestenPearsonDivergence
  have he : (fun x => (((kestenSpectralLaw p : Measure ℝ).rnDeriv
      (kestenSpectralLaw q : Measure ℝ) x).toReal - 1) ^ 2) =ᵐ[(kestenSpectralLaw q : Measure ℝ)]
        (fun x => (kestenLikelihood p x / kestenLikelihood q x) ^ 2 -
          2 * (kestenLikelihood p x / kestenLikelihood q x) + 1) := by
    filter_upwards [rnDeriv_kesten_prime_toReal p q] with x hx
    rw [hx]
    ring
  have hi : Integrable (fun x => kestenLikelihood p x / kestenLikelihood q x)
      (kestenSpectralLaw q : Measure ℝ) :=
    integrable_kestenSpectralLaw_continuous q ⟨_, continuous_kestenLikelihood_ratio p q⟩
  have hj : Integrable (fun x => (kestenLikelihood p x / kestenLikelihood q x) ^ 2)
      (kestenSpectralLaw q : Measure ℝ) :=
    integrable_kestenSpectralLaw_continuous q ⟨_, (continuous_kestenLikelihood_ratio p q).pow 2⟩
  rw [integral_congr_ae he,
    integral_add (f := fun x => (kestenLikelihood p x / kestenLikelihood q x) ^ 2 -
      2 * (kestenLikelihood p x / kestenLikelihood q x)) (g := fun _ => 1)
      (hj.sub (hi.const_mul 2)) (integrable_const 1),
    integral_sub (g := fun x => 2 * (kestenLikelihood p x / kestenLikelihood q x)) hj (hi.const_mul 2),
    integral_const_mul, integral_kestenLikelihood_ratio_sq, integral_kestenLikelihood_ratio]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- Directed prime-pair Pearson divergence is nonnegative as an actual squared integral. -/
theorem kestenPearsonDivergence_nonneg (p q : Nat.Primes) : 0 ≤ kestenPearsonDivergence p q :=
  integral_nonneg fun _ => sq_nonneg _

/-- Pearson divergence distinguishes exactly the unequal prime labels. -/
theorem kestenPearsonDivergence_eq_zero_iff (p q : Nat.Primes) :
    kestenPearsonDivergence p q = 0 ↔ p = q := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hpd : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  rw [kestenPearsonDivergence_eq, div_eq_zero_iff]
  simp only [mul_ne_zero (mul_ne_zero hq0 hq1) hpd, or_false, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact_mod_cast h
  · rintro rfl
    rfl

/-- The exact pairwise Pearson value is strictly positive precisely for distinct primes. -/
theorem kestenPearsonDivergence_pos_iff (p q : Nat.Primes) :
    0 < kestenPearsonDivergence p q ↔ p ≠ q := by
  constructor
  · intro h he
    exact h.ne' ((kestenPearsonDivergence_eq_zero_iff p q).2 he)
  · intro he
    apply lt_of_le_of_ne (kestenPearsonDivergence_nonneg p q)
    intro hz
    exact he ((kestenPearsonDivergence_eq_zero_iff p q).1 hz.symm)

/-- Reversing the ordered prime pair changes Pearson divergence by an exact cubic difference. -/
theorem kestenPearsonDivergence_sub_swap (p q : Nat.Primes) :
    kestenPearsonDivergence p q - kestenPearsonDivergence q p =
      ((q : ℝ) - (p : ℝ)) ^ 3 /
        ((p : ℝ) * (q : ℝ) * ((p : ℝ) ^ 2 - 1) * ((q : ℝ) ^ 2 - 1)) := by
  rw [kestenPearsonDivergence_eq, kestenPearsonDivergence_eq]
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith only [hq])
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hpd : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  have hqd : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hq, sq_nonneg ((q : ℝ) - 1)]
  field_simp [hp0, hq0, hp1, hq1, hpd, hqd]
  ring

/-- Pearson divergence is larger from the smaller prime law to the larger prime law. -/
theorem kestenPearsonDivergence_swap_lt_iff (p q : Nat.Primes) :
    kestenPearsonDivergence q p < kestenPearsonDivergence p q ↔ (p : ℕ) < (q : ℕ) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith only [hp]
  have hq0 : 0 < (q : ℝ) := by linarith only [hq]
  have hpd : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  have hqd : 0 < (q : ℝ) ^ 2 - 1 := by nlinarith only [hq, sq_nonneg ((q : ℝ) - 1)]
  have hd := mul_pos (mul_pos (mul_pos hp0 hq0) hpd) hqd
  constructor
  · intro h
    have hc := mul_pos (sub_pos.mpr h) hd
    rw [kestenPearsonDivergence_sub_swap, div_mul_cancel₀ _ hd.ne'] at hc
    have hpq : (p : ℝ) < (q : ℝ) := by
      by_contra hn
      have hz : (q : ℝ) - (p : ℝ) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hn)
      have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((q : ℝ) - (p : ℝ))) hz
      nlinarith only [hc, hm]
    exact_mod_cast hpq
  · intro h
    have hpq : (p : ℝ) < (q : ℝ) := by exact_mod_cast h
    apply sub_pos.mp
    rw [kestenPearsonDivergence_sub_swap]
    exact div_pos (pow_pos (sub_pos.mpr hpq) 3) hd

end
end GaloisForLFunctions.SelbergClass.Primon
