import GaloisForLFunctions.RHTower.Representation.EndpointExteriorProduct
import GaloisForLFunctions.RHTower.Representation.EndpointCharacterCriterion
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.AlternatingComplexColoring

/-!
# Nonnegative arithmetic alternating projections at every rank

The actual endpoint divisor weights realize the prescribed arithmetic cycle class function
as a complex fixed-word trace. Its alternating projection is the corresponding derivative
of the normalized squared center lift, hence is nonnegative without a zero-location premise.
-/

noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace RHTower
open GaloisForLFunctions.SymmetricCharacters

/-- The complex endpoint alphabet has total mass one. -/
theorem tsum_xiEndpointComplexColor :
    (∑' q, xiStripEdgeWeight q / (xiEndpointColorMass : ℂ)) = 1 := by
  rw [tsum_div_const, hasSum_xiStripEdgeWeight.tsum_eq, ← xiEndpointColorMass_complex_eq]
  exact div_self (Complex.ofReal_ne_zero.mpr xiEndpointColorMass_pos.ne')

/-- Fixed-word traces retain the full arithmetic moments, including fixed points. -/
theorem complexWordCharacter_xiEndpoint {X : Type*} [Fintype X] (σ : Equiv.Perm X) :
    complexWordCharacter (fun q => xiStripEdgeWeight q / (xiEndpointColorMass : ℂ)) σ =
      xiEndpointArithmeticCharacter σ := by
  rw [complexWordCharacter_eq_complexCycleCharacter _
    (summable_xiStripEdgeWeight.div_const _) tsum_xiEndpointComplexColor]
  simp only [complexCycleCharacter, div_pow, tsum_div_const]
  rw [xiEndpointArithmeticCharacter, cycleMomentCharacter]
  have hcast (s : Multiset ℝ) : (s.prod : ℂ) = (s.map (fun x : ℝ => (x : ℂ))).prod :=
    map_multiset_prod Complex.ofRealHom s
  rw [hcast, Multiset.map_map]
  simp only [Function.comp_def, xiEndpointArithmeticCycle_complex]

/-- The sign projection equals the corresponding derivative of the arithmetic exterior series. -/
theorem xiEndpointArithmeticCharacter_alternating_eq (n : ℕ) :
    complexAlternatingMass (X := Fin n) xiEndpointArithmeticCharacter =
      iteratedDeriv n xiEndpointExteriorSeries 0 := by
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat XiZeroCopy
  letI : LinearOrder XiZeroCopy := LinearOrder.lift' c hc
  have he : (xiEndpointArithmeticCharacter : Equiv.Perm (Fin n) → ℂ) =
      complexWordCharacter (fun q => xiStripEdgeWeight q / (xiEndpointColorMass : ℂ)) := by
    funext σ
    exact (complexWordCharacter_xiEndpoint σ).symm
  rw [he]
  rw [sum_sign_complexWordCharacter_eq_subset _ (summable_xiStripEdgeWeight.div_const _)]
  change (n.factorial : ℂ) * xiEndpointExteriorCoefficient n = _
  rw [xiEndpointExteriorCoefficient_eq_deriv]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [hn]

/-- Every column Young projection of the prescribed arithmetic character is nonnegative. -/
theorem xiEndpointArithmeticCharacter_alternating_nonneg (n : ℕ) :
    0 ≤ complexAlternatingMass (X := Fin n) xiEndpointArithmeticCharacter := by
  rw [xiEndpointArithmeticCharacter_alternating_eq]
  exact nonnegTaylorAtZero_xiEndpointExteriorSeries.2 n

end RHTower
