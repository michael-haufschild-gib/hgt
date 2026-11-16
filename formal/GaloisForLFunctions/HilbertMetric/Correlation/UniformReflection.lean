import GaloisForLFunctions.HilbertMetric.Correlation.ExceptionalEnergy
import Mathlib.Tactic

/-!
# Uniform-channel reflection of correlation packets

Khoze's flavour scattering matrix `I - (2/N) 11ᵀ`
(https://arxiv.org/abs/2611.17253, equation (15)) acts on arbitrary Hilbert-valued
packets. It reverses their coherent sum, fixes every pairwise difference, and
preserves both coherent energy and the sum of individual energies. These are
exact identities for constructed packets; no scattering model is assumed.
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HilbertMetric
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflection of the constant channel, with the orthogonal channels fixed. -/
def uniformReflection {N : ℕ} (v : Fin (N + 1) → E) (i : Fin (N + 1)) : E :=
  v i - (2 / (N + 1 : ℝ)) • ∑ j, v j

/-- The coherent sum is reversed exactly. -/
theorem sum_uniformReflection {N : ℕ} (v : Fin (N + 1) → E) :
    (∑ i, uniformReflection v i) = -(∑ i, v i) := by
  have hc : (N + 1 : ℝ) ≠ 0 := by positivity
  have hcancel : (N + 1 : ℝ) * (2 / (N + 1 : ℝ)) = 2 := by field_simp
  simp only [uniformReflection, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add,
    Nat.cast_one, hcancel]
  module

/-- Flavour differences survive reflection without alteration. -/
theorem uniformReflection_sub {N : ℕ} (v : Fin (N + 1) → E) (i j : Fin (N + 1)) :
    uniformReflection v i - uniformReflection v j = v i - v j := by
  simp only [uniformReflection]
  abel

/-- Applying the channel reflection twice recovers the original packet. -/
theorem uniformReflection_involutive {N : ℕ} (v : Fin (N + 1) → E) :
    uniformReflection (uniformReflection v) = v := by
  funext i
  rw [uniformReflection, sum_uniformReflection, uniformReflection, smul_neg]
  abel

/-- Reflection preserves the corpus's coherent Gram energy. -/
theorem packetEnergy_uniformReflection {N : ℕ} (v : Fin (N + 1) → E) :
    packetEnergy Finset.univ (uniformReflection v) = packetEnergy Finset.univ v := by
  simp only [packetEnergy, sum_uniformReflection, norm_neg]

/-- The individual energy mass is preserved as well as the coherent energy. -/
theorem sum_norm_sq_uniformReflection {N : ℕ} (v : Fin (N + 1) → E) :
    (∑ i, ‖uniformReflection v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  have hc : (N + 1 : ℝ) ≠ 0 := by positivity
  simp only [uniformReflection, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← sum_inner, real_inner_self_eq_norm_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- A linear charge changes only through its total coupling to the constant channel. -/
theorem weighted_sum_uniformReflection {N : ℕ} (v : Fin (N + 1) → E)
    (w : Fin (N + 1) → ℝ) :
    (∑ i, w i • uniformReflection v i) =
      (∑ i, w i • v i) - ((2 / (N + 1 : ℝ)) * ∑ i, w i) • ∑ i, v i := by
  simp only [uniformReflection, smul_sub, smul_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, ← Finset.sum_mul, mul_comm (∑ i, w i)]

/-- Four-channel reflection of an integral incoming charge. -/
def fourCharge (v : Fin 4 → ℤ) (i : Fin 4) : ℚ :=
  (v i : ℚ) - (∑ j, v j : ℤ) / 2

/-- Exactly the even-total-charge lattice survives four-channel reflection integrally. -/
theorem fourCharge_integral_iff (v : Fin 4 → ℤ) :
    (∀ i, ∃ z : ℤ, fourCharge v i = (z : ℚ)) ↔ Even (∑ j, v j) := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h 0
    refine ⟨v 0 - z, ?_⟩
    have he : ((∑ j, v j : ℤ) : ℚ) =
        ((v 0 : ℚ) - z) + ((v 0 : ℚ) - z) := by
      dsimp only [fourCharge] at hz
      linarith only [hz]
    exact_mod_cast he
  · rintro ⟨z, hz⟩ i
    refine ⟨v i - z, ?_⟩
    simp only [fourCharge, hz, Int.cast_add, Int.cast_sub]
    ring

/-- Every entry of the four-channel scattering matrix carries one quarter of a unit input's energy. -/
theorem fourChannel_energy_share (i j : Fin 4) :
    ((if i = j then (1 : ℝ) else 0) - 1 / 2)^2 = 1 / 4 := by
  by_cases h : i = j <;> simp [h] <;> norm_num

#print axioms uniformReflection_involutive
#print axioms sum_norm_sq_uniformReflection
#print axioms packetEnergy_uniformReflection
#print axioms weighted_sum_uniformReflection
#print axioms fourCharge_integral_iff

end
end GaloisForLFunctions.HilbertMetric
