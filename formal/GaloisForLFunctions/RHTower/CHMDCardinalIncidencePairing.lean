import GaloisForLFunctions.RHTower.CHMDCardinalGraphGeometry

/-! # Cardinal orbit incidence extracts a literal even Schwarz value -/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower

def cardinalOrbitWeight (a z : ℂ) : ℝ :=
  (unsignedOrbitIndicator a z + unsignedOrbitIndicator a (conj z))/2

def cardinalOrbitMass (a : ℂ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ)

theorem summable_cardinalOrbitMass (a : ℂ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ)) := by
  apply summable_of_cardinalOrbit_support (a := a)
  intro ρ hρ
  obtain ⟨hA, hB⟩ := unsignedOrbitIndicator_pair_eq_zero hρ
  simp [cardinalOrbitWeight, hA, hB]

theorem cardinalOrbit_mem_reverse {a b : ℂ} (h : a ∈ cardinalOrbit b) :
    b ∈ cardinalOrbit a := by
  simp only [cardinalOrbit, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl (by rw [h, neg_neg]))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, conj_conj])))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, map_neg, conj_conj, neg_neg])))

theorem unsignedOrbitIndicator_sq (a z : ℂ) :
    unsignedOrbitIndicator a z ^ 2 = unsignedOrbitIndicator a z := by
  unfold unsignedOrbitIndicator
  split_ifs <;> norm_num

theorem cardinalOrbitWeight_eq_sq_of_real {a : ℂ} (hi : a.im = 0) (z : ℂ) :
    cardinalOrbitWeight a z = cardinalOrbitWeight a z ^ 2 := by
  have hc : conj a = a := by apply Complex.ext <;> simp [hi]
  rw [cardinalOrbitWeight, unsignedOrbitIndicator_conj, hc]
  have h := unsignedOrbitIndicator_sq a z
  nlinarith

theorem cardinalOrbitWeight_eq_two_sq_of_nonreal {a : ℂ} (ha : 0 < a.re)
    (hi : a.im ≠ 0) (z : ℂ) : cardinalOrbitWeight a z = 2 * cardinalOrbitWeight a z ^ 2 := by
  have hA := unsignedOrbitIndicator_sq a z
  have hB := unsignedOrbitIndicator_sq a (conj z)
  have hAB := unsignedOrbitIndicators_disjoint ha hi z
  unfold cardinalOrbitWeight
  nlinarith

theorem cardinalOrbitMass_eq_positive_of_real {a : ℂ} (hi : a.im = 0) :
    cardinalOrbitMass a = cardinalPositiveMass a := by
  apply tsum_congr
  intro ρ
  change (zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ) =
    (zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ)^2
  exact congrArg (fun t : ℝ => (zetaZeroConfig.mult ρ : ℝ) * t)
    (cardinalOrbitWeight_eq_sq_of_real hi (gammaOf ρ))

theorem cardinalOrbitMass_eq_two_positive {a : ℂ} (ha : 0 < a.re) (hi : a.im ≠ 0) :
    cardinalOrbitMass a = 2 * cardinalPositiveMass a := by
  rw [cardinalPositiveMass, ← tsum_mul_left]
  apply tsum_congr
  intro ρ
  change (zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ) =
    2 * ((zetaZeroConfig.mult ρ : ℝ) * cardinalOrbitWeight a (gammaOf ρ)^2)
  calc
    _ = (zetaZeroConfig.mult ρ : ℝ) * (2 * cardinalOrbitWeight a (gammaOf ρ)^2) :=
      congrArg (fun t : ℝ => (zetaZeroConfig.mult ρ : ℝ) * t)
        (cardinalOrbitWeight_eq_two_sq_of_nonreal ha hi (gammaOf ρ))
    _ = _ := by ring

theorem cardinalOrbitMass_pos {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    0 < cardinalOrbitMass a := by
  by_cases hi : a.im = 0
  · rw [cardinalOrbitMass_eq_positive_of_real hi]
    exact cardinalPositiveMass_pos_of_zero hz
  · rw [cardinalOrbitMass_eq_two_positive ha hi]
    exact mul_pos (by norm_num) (cardinalPositiveMass_pos_of_zero hz)

/-- Orbit collisions on the real axis are retained in the coefficient. -/
theorem cardinalOrbitValue_mul_readout_re {C : ℂ → ℂ}
    (he : ∀ z, C (-z) = C z) (hc : ∀ z, C (conj z) = conj (C z)) (a c z : ℂ) :
    (C z * cardinalOrbitValue a c z).re = cardinalOrbitWeight a z * (c * C a).re := by
  have hA : (C z * c * (unsignedOrbitIndicator a z : ℂ)).re =
      unsignedOrbitIndicator a z * (c * C a).re := by
    by_cases h : z = a ∨ z = -a
    · have hv : C z = C a := by
        rcases h with rfl | rfl
        · rfl
        · exact he a
      simp [unsignedOrbitIndicator, h, hv, mul_comm]
    · simp [unsignedOrbitIndicator, h]
  have hB : (C z * conj c * (unsignedOrbitIndicator a (conj z) : ℂ)).re =
      unsignedOrbitIndicator a (conj z) * (c * C a).re := by
    by_cases h : conj z = a ∨ conj z = -a
    · have hv : C (conj z) = C a := by
        rcases h with h | h
        · rw [h]
        · rw [h, he]
      rw [hc] at hv
      have hz : C z = conj (C a) := by simpa using congrArg conj hv
      simp only [unsignedOrbitIndicator, if_pos h, Complex.ofReal_one, mul_one, one_mul, hz]
      rw [← map_mul, Complex.conj_re, mul_comm]
    · simp [unsignedOrbitIndicator, h]
  have hx : C z * cardinalOrbitValue a c z =
      (C z*c*(unsignedOrbitIndicator a z : ℂ) +
        C z*conj c*(unsignedOrbitIndicator a (conj z) : ℂ))/2 := by
    unfold cardinalOrbitValue
    ring
  rw [hx]
  simp only [Complex.div_ofNat_re, Complex.add_re, hA, hB]
  unfold cardinalOrbitWeight
  ring

theorem tsum_cardinalOrbitValue_mul_readout_re {C : ℂ → ℂ}
    (he : ∀ z, C (-z) = C z) (hc : ∀ z, C (conj z) = conj (C z)) (a c : ℂ) :
    (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (C (gammaOf ρ) * cardinalOrbitValue a c (gammaOf ρ)).re) =
        cardinalOrbitMass a * (c * C a).re := by
  simp_rw [cardinalOrbitValue_mul_readout_re he hc, ← mul_assoc]
  rw [tsum_mul_right]
  rfl

end RHTower
