import GaloisForLFunctions.HTGeometry.GermFactorial

/-!
# Reduced fractions in a unique factorization domain, and for analytic germs

Any fraction can be reduced: dividing numerator and denominator by their greatest common divisor
leaves a pair with no common non-unit factor.  Two reduced presentations of the same fraction have
associated numerators and associated denominators — the cross-multiplied identity plus relative
primality forces each denominator to divide the other.

Applied to the germ ring, whose factoriality is `instUniqueFactorizationMonoidAnalyticGerm`, this
gives every meromorphic germ a locally reduced presentation, unique up to units.  That uniqueness is
what supplies the comparison constants a Siegel-type count needs on the overlaps of a cover: the
ratio of two local denominators of the same meromorphic function is a unit, hence bounded on
compacta, whereas the ratio of two arbitrary presentations need not be.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [CommRing α] [IsDomain α]

/-- **Every fraction reduces.**  Dividing by the greatest common divisor leaves a relatively prime
numerator and denominator with the same cross product. -/
theorem exists_reduced_fraction [GCDMonoid α] (a b : α) (hb : b ≠ 0) :
    ∃ a' b' : α, b' ≠ 0 ∧ IsRelPrime a' b' ∧ a * b' = a' * b := by
  obtain ⟨a', ha'⟩ := gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := gcd_dvd_right a b
  have hd : gcd a b ≠ 0 := by
    intro h
    rw [gcd_eq_zero_iff] at h
    exact hb h.2
  have hb'0 : b' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hb'
    exact hb hb'
  refine ⟨a', b', hb'0, ?_, ?_⟩
  · intro z hza hzb
    obtain ⟨s, hs⟩ := hza
    obtain ⟨t, ht⟩ := hzb
    have hdvd : gcd a b * z ∣ gcd a b := by
      refine dvd_gcd ⟨s, ?_⟩ ⟨t, ?_⟩
      · calc a = gcd a b * a' := ha'
          _ = gcd a b * (z * s) := by rw [hs]
          _ = gcd a b * z * s := by ring
      · calc b = gcd a b * b' := hb'
          _ = gcd a b * (z * t) := by rw [ht]
          _ = gcd a b * z * t := by ring
    obtain ⟨k, hk⟩ := hdvd
    have hone : (1 : α) = z * k := by
      refine mul_left_cancel₀ hd ?_
      rw [mul_one]
      calc gcd a b = gcd a b * z * k := hk
        _ = gcd a b * (z * k) := by ring
    exact isUnit_iff_exists_inv.mpr ⟨k, hone.symm⟩
  · calc a * b' = gcd a b * a' * b' := by rw [← ha']
      _ = a' * (gcd a b * b') := by ring
      _ = a' * b := by rw [← hb']

/-- **Reduced presentations of the same fraction have associated denominators.** -/
theorem associated_den_of_reduced [DecompositionMonoid α] {a₁ b₁ a₂ b₂ : α}
    (h₁ : IsRelPrime a₁ b₁) (h₂ : IsRelPrime a₂ b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) : Associated b₁ b₂ := by
  have hd₁ : b₁ ∣ b₂ := by
    refine h₁.symm.dvd_of_dvd_mul_left ?_
    exact ⟨a₂, by linear_combination hcross⟩
  have hd₂ : b₂ ∣ b₁ := by
    refine h₂.symm.dvd_of_dvd_mul_left ?_
    exact ⟨a₁, by linear_combination -hcross⟩
  exact associated_of_dvd_dvd hd₁ hd₂

/-- **Reduced presentations of the same fraction have associated numerators.** -/
theorem associated_num_of_reduced [DecompositionMonoid α] {a₁ b₁ a₂ b₂ : α}
    (h₁ : IsRelPrime a₁ b₁) (h₂ : IsRelPrime a₂ b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) : Associated a₁ a₂ := by
  have hd₁ : a₁ ∣ a₂ := by
    refine h₁.dvd_of_dvd_mul_left ?_
    exact ⟨b₂, by linear_combination -hcross⟩
  have hd₂ : a₂ ∣ a₁ := by
    refine h₂.dvd_of_dvd_mul_left ?_
    exact ⟨b₁, by linear_combination hcross⟩
  exact associated_of_dvd_dvd hd₁ hd₂

/-! ## The germ ring -/

variable {n : ℕ}

/-- **Every germ fraction has a reduced presentation.** -/
theorem exists_reduced_germ_fraction (a b : AnalyticGerm (0 : Fin n → ℂ)) (hb : b ≠ 0) :
    ∃ a' b' : AnalyticGerm (0 : Fin n → ℂ), b' ≠ 0 ∧ IsRelPrime a' b' ∧ a * b' = a' * b := by
  letI := UniqueFactorizationMonoid.toGCDMonoid (AnalyticGerm (0 : Fin n → ℂ))
  exact exists_reduced_fraction a b hb

/-- **The denominator of a reduced presentation is determined up to a unit.** -/
theorem associated_den_of_reduced_germ {a₁ b₁ a₂ b₂ : AnalyticGerm (0 : Fin n → ℂ)}
    (h₁ : IsRelPrime a₁ b₁) (h₂ : IsRelPrime a₂ b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) : Associated b₁ b₂ :=
  associated_den_of_reduced h₁ h₂ hcross

/-- **The numerator of a reduced presentation is determined up to a unit.** -/
theorem associated_num_of_reduced_germ {a₁ b₁ a₂ b₂ : AnalyticGerm (0 : Fin n → ℂ)}
    (h₁ : IsRelPrime a₁ b₁) (h₂ : IsRelPrime a₂ b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) : Associated a₁ a₂ :=
  associated_num_of_reduced h₁ h₂ hcross

end GaloisForLFunctions.HTGeometry
