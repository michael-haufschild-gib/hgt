import GaloisForLFunctions.SelbergClass.Primon.KestenEntropyIntegrals

/-!
# Closed relative entropies of the prime spectral family

Every comparison between two prime laws, or between a prime law and the
semicircle law, has finite relative entropy. The exact values follow from
the mixed logarithmic expectations of the rational density weights.
-/

open MeasureTheory InformationTheory Set

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Prime-to-semicircle relative entropy as an explicit real expression. -/
def kestenSemicircleEntropyValue (p : Nat.Primes) : ℝ :=
  Real.log (1 + (p : ℝ)⁻¹) + ((p : ℝ) - 1) * Real.log (1 - ((p : ℝ)⁻¹) ^ 2)

/-- Semicircle-to-prime relative entropy as an explicit real expression. -/
def semicircleKestenEntropyValue (p : Nat.Primes) : ℝ :=
  (p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹)

/-- Relative entropy between two prime laws as an explicit logarithmic expression. -/
def kestenRelativeEntropyValue (p q : Nat.Primes) : ℝ :=
  Real.log (1 + (p : ℝ)⁻¹) - Real.log (1 + (q : ℝ)⁻¹) +
    ((p : ℝ) - 1) * (Real.log (1 - ((p : ℝ)⁻¹) ^ 2) -
      Real.log (1 - ((p : ℝ) * (q : ℝ))⁻¹))

/-- Every prime-to-semicircle relative entropy is finite. -/
theorem kesten_semicircle_klDiv_ne_top (p : Nat.Primes) :
    klDiv (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ) ≠ ⊤ :=
  klDiv_ne_top (kestenSpectralLaw_ac_semicircle p)
    ((integrable_kestenLogLikelihood p p).congr (llr_kesten_semicircle p).symm)

/-- Every reverse semicircle-to-prime relative entropy is finite. -/
theorem semicircle_kesten_klDiv_ne_top (p : Nat.Primes) :
    klDiv (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ) ≠ ⊤ :=
  klDiv_ne_top (semicircleSpectralLaw_ac_kesten p)
    ((integrable_semicircleLogLikelihood p).neg.congr (llr_semicircle_kesten p).symm)

/-- Every directed relative entropy between two prime spectral laws is finite. -/
theorem kesten_prime_klDiv_ne_top (p q : Nat.Primes) :
    klDiv (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ) ≠ ⊤ :=
  klDiv_ne_top (kestenSpectralLaw_ac_prime p q)
    (((integrable_kestenLogLikelihood p p).sub (integrable_kestenLogLikelihood q p)).congr
      (llr_kesten_prime p q).symm)

/-- Exact real value of prime-to-semicircle relative entropy. -/
theorem toReal_klDiv_kesten_semicircle (p : Nat.Primes) :
    (klDiv (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ)).toReal =
      kestenSemicircleEntropyValue p := by
  rw [toReal_klDiv_of_measure_eq (kestenSpectralLaw_ac_semicircle p) (by simp),
    integral_congr_ae (llr_kesten_semicircle p), integral_kestenLogLikelihood_self]
  rfl

/-- Exact real value of semicircle-to-prime relative entropy. -/
theorem toReal_klDiv_semicircle_kesten (p : Nat.Primes) :
    (klDiv (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ)).toReal =
      semicircleKestenEntropyValue p := by
  rw [toReal_klDiv_of_measure_eq (semicircleSpectralLaw_ac_kesten p) (by simp),
    integral_congr_ae (llr_semicircle_kesten p), integral_neg, integral_semicircleLogLikelihood]
  unfold semicircleKestenEntropyValue
  ring

/-- Exact real value of every prime-to-prime relative entropy. -/
theorem toReal_klDiv_kesten_prime (p q : Nat.Primes) :
    (klDiv (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ)).toReal =
      kestenRelativeEntropyValue p q := by
  rw [toReal_klDiv_of_measure_eq (kestenSpectralLaw_ac_prime p q) (by simp),
    integral_congr_ae (llr_kesten_prime p q),
    integral_sub (integrable_kestenLogLikelihood p p) (integrable_kestenLogLikelihood q p),
    integral_kestenLogLikelihood_self, integral_kestenLogLikelihood_cross]
  unfold kestenRelativeEntropyValue
  rw [mul_comm (q : ℝ) (p : ℝ)]
  ring

/-- The actual prime-to-semicircle divergence is the finite explicit logarithmic expression. -/
theorem klDiv_kesten_semicircle (p : Nat.Primes) :
    klDiv (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ) =
      ENNReal.ofReal (kestenSemicircleEntropyValue p) := by
  rw [← toReal_klDiv_kesten_semicircle]
  exact (ENNReal.ofReal_toReal (kesten_semicircle_klDiv_ne_top p)).symm

/-- The actual reverse divergence is the finite logarithmic deficit. -/
theorem klDiv_semicircle_kesten (p : Nat.Primes) :
    klDiv (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ) =
      ENNReal.ofReal (semicircleKestenEntropyValue p) := by
  rw [← toReal_klDiv_semicircle_kesten]
  exact (ENNReal.ofReal_toReal (semicircle_kesten_klDiv_ne_top p)).symm

/-- Every actual prime-to-prime divergence has the explicit finite value. -/
theorem klDiv_kesten_prime (p q : Nat.Primes) :
    klDiv (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ) =
      ENNReal.ofReal (kestenRelativeEntropyValue p q) := by
  rw [← toReal_klDiv_kesten_prime]
  exact (ENNReal.ofReal_toReal (kesten_prime_klDiv_ne_top p q)).symm

/-- The explicit prime-to-semicircle entropy expression is nonnegative. -/
theorem kestenSemicircleEntropyValue_nonneg (p : Nat.Primes) : 0 ≤ kestenSemicircleEntropyValue p := by
  rw [← toReal_klDiv_kesten_semicircle]
  exact ENNReal.toReal_nonneg

/-- The reverse logarithmic deficit is nonnegative. -/
theorem semicircleKestenEntropyValue_nonneg (p : Nat.Primes) : 0 ≤ semicircleKestenEntropyValue p := by
  rw [← toReal_klDiv_semicircle_kesten]
  exact ENNReal.toReal_nonneg

/-- The closed prime-to-prime entropy expression is nonnegative. -/
theorem kestenRelativeEntropyValue_nonneg (p q : Nat.Primes) : 0 ≤ kestenRelativeEntropyValue p q := by
  rw [← toReal_klDiv_kesten_prime]
  exact ENNReal.toReal_nonneg

/-- The spectral law determines its prime: the second moment already separates prime labels. -/
theorem kestenSpectralMeasure_injective :
    Function.Injective (fun p : Nat.Primes => (kestenSpectralLaw p : Measure ℝ)) := by
  intro p q he
  have hm := congrArg (fun μ : Measure ℝ => ∫ x : ℝ, x ^ 2 ∂μ) he
  change (∫ x : ℝ, x ^ 2 ∂(kestenSpectralLaw p : Measure ℝ)) =
    (∫ x : ℝ, x ^ 2 ∂(kestenSpectralLaw q : Measure ℝ)) at hm
  rw [(kestenSpectralLaw_hasMoments p 2).2, (kestenSpectralLaw_hasMoments q 2).2] at hm
  apply Subtype.ext
  apply le_antisymm
  · by_contra hn
    have ht := (kestenMoment_even_lt_iff p q 0).2 (lt_of_not_ge hn)
    norm_num only [Nat.zero_add, Nat.mul_one] at ht
    exact ht.ne hm
  · by_contra hn
    have ht := (kestenMoment_even_lt_iff q p 0).2 (lt_of_not_ge hn)
    norm_num only [Nat.zero_add, Nat.mul_one] at ht
    exact ht.ne hm.symm

/-- No finite-prime spectral law equals the semicircle law. -/
theorem kestenSpectralMeasure_ne_semicircle (p : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) ≠ (semicircleSpectralLaw : Measure ℝ) := by
  intro he
  have hm := congrArg (fun μ : Measure ℝ => ∫ x : ℝ, x ^ 2 ∂μ) he
  change (∫ x : ℝ, x ^ 2 ∂(kestenSpectralLaw p : Measure ℝ)) =
    (∫ x : ℝ, x ^ 2 ∂(semicircleSpectralLaw : Measure ℝ)) at hm
  rw [(kestenSpectralLaw_hasMoments p 2).2, (semicircleSpectralLaw_hasMoments 2).2,
    show semicircleMoment 2 = (catalan 1 : ℝ) from semicircleMoment_even 1] at hm
  have ht := catalan_lt_kestenMoment_even_succ p 0
  norm_num only [Nat.zero_add, Nat.mul_one] at ht
  exact ht.ne hm.symm

/-- The closed pairwise entropy vanishes exactly for equal prime labels. -/
theorem kestenRelativeEntropyValue_eq_zero_iff (p q : Nat.Primes) :
    kestenRelativeEntropyValue p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hk : klDiv (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ) = 0 := by
      rw [klDiv_kesten_prime, h, ENNReal.ofReal_zero]
    exact kestenSpectralMeasure_injective (klDiv_eq_zero_iff.mp hk)
  · rintro rfl
    rw [← toReal_klDiv_kesten_prime, klDiv_self, ENNReal.toReal_zero]

/-- Every comparison of distinct primes has strictly positive real relative entropy. -/
theorem kestenRelativeEntropyValue_pos_iff (p q : Nat.Primes) :
    0 < kestenRelativeEntropyValue p q ↔ p ≠ q := by
  constructor
  · intro h hpq
    exact h.ne' ((kestenRelativeEntropyValue_eq_zero_iff p q).2 hpq)
  · intro hpq
    apply lt_of_le_of_ne (kestenRelativeEntropyValue_nonneg p q)
    intro he
    exact hpq ((kestenRelativeEntropyValue_eq_zero_iff p q).1 he.symm)

/-- Every finite prime has strictly positive entropy relative to the semicircle law. -/
theorem kestenSemicircleEntropyValue_pos (p : Nat.Primes) : 0 < kestenSemicircleEntropyValue p := by
  rw [← toReal_klDiv_kesten_semicircle]
  apply ENNReal.toReal_pos _ (kesten_semicircle_klDiv_ne_top p)
  intro h
  exact kestenSpectralMeasure_ne_semicircle p (klDiv_eq_zero_iff.mp h)

/-- The reverse semicircle-to-prime entropy is also strictly positive. -/
theorem semicircleKestenEntropyValue_pos (p : Nat.Primes) : 0 < semicircleKestenEntropyValue p := by
  rw [← toReal_klDiv_semicircle_kesten]
  apply ENNReal.toReal_pos _ (semicircle_kesten_klDiv_ne_top p)
  intro h
  exact kestenSpectralMeasure_ne_semicircle p (klDiv_eq_zero_iff.mp h).symm

end
end GaloisForLFunctions.SelbergClass.Primon
