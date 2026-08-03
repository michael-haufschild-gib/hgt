import GaloisForLFunctions.HTGeometry.AiryTowerSeparatedCore

/-!
# Simultaneous Puiseux realization of separated Airy towers

Every finite labelled family of strict divisor chains receives explicit nonzero complex
coefficients.  The coefficients are positive integers, so equal first factors have distinct powers
and hence lie in distinct power-orbits.  This gives a fully explicit simultaneous leading-separated
family of finite Puiseux polynomials.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Ordered rational slopes of a ramified characteristic. -/
def Characteristic.slopes {R beta : ℕ} : Characteristic R beta → List ℚ
  | .terminal .. => [(beta : ℚ) / (R : ℚ)]
  | .step (E := _) (gamma := _) _ _ _ _ _ tail =>
      (beta : ℚ) / (R : ℚ) :: tail.slopes

/-- Finite Puiseux polynomial represented by its ordered slope/coefficient monomials. -/
abbrev PuiseuxPolynomial := List (ℚ × ℂ)

/-- Canonical Airy polynomial attached to a divisor chain and one common nonzero coefficient. -/
def StrictDivisorChain.airyPolynomial {R : ℕ} (d : StrictDivisorChain R)
    (coefficient : ℂ) : PuiseuxPolynomial :=
  d.toCharacteristic.slopes.map (fun slope => (slope, coefficient))

/-- The polynomial records exactly the slope list of the canonical Airy characteristic. -/
@[simp] theorem StrictDivisorChain.map_fst_airyPolynomial {R : ℕ}
    (d : StrictDivisorChain R) (coefficient : ℂ) :
    (d.airyPolynomial coefficient).map Prod.fst = d.toCharacteristic.slopes := by
  simp [StrictDivisorChain.airyPolynomial, List.map_map, Function.comp_def]

/-- Every coefficient of a canonical Airy polynomial is the chosen common coefficient. -/
theorem StrictDivisorChain.coefficient_of_mem_airyPolynomial {R : ℕ}
    (d : StrictDivisorChain R) {coefficient : ℂ} {slope : ℚ} {c : ℂ}
    (h : (slope, c) ∈ d.airyPolynomial coefficient) : c = coefficient := by
  simp only [StrictDivisorChain.airyPolynomial, List.mem_map] at h
  obtain ⟨x, _, hx⟩ := h
  exact congrArg Prod.snd hx.symm

/-- Finite labelled family of strict divisor chains. -/
structure AiryChainFamily (n : ℕ) where
  ramification : Fin n → ℕ
  chain : ∀ i, StrictDivisorChain (ramification i)

namespace AiryChainFamily

/-- First multiplicative factor of the labelled Airy chain. -/
def firstFactor {n : ℕ} (family : AiryChainFamily n) (i : Fin n) : ℕ :=
  (family.chain i).toAiryHead.firstFactor

theorem firstFactor_pos {n : ℕ} (family : AiryChainFamily n) (i : Fin n) :
    0 < family.firstFactor i := by
  exact lt_of_lt_of_le Nat.zero_lt_two (family.chain i).toAiryHead.factor_ge_two

/-- Explicit coefficient assigned to label `i`. -/
def separatedCoefficient {n : ℕ} (_family : AiryChainFamily n) (i : Fin n) : ℂ :=
  (i.val + 1 : ℕ)

theorem separatedCoefficient_ne_zero {n : ℕ} (family : AiryChainFamily n) (i : Fin n) :
    family.separatedCoefficient i ≠ 0 := by
  change ((i.val + 1 : ℕ) : ℂ) ≠ 0
  exact_mod_cast Nat.succ_ne_zero i.val

/-- Distinct labels have distinct positive powers of their explicit coefficients. -/
theorem separatedCoefficient_pow_ne {n a : ℕ} (family : AiryChainFamily n)
    (ha : 0 < a) {i j : Fin n} (hij : i ≠ j) :
    family.separatedCoefficient i ^ a ≠ family.separatedCoefficient j ^ a := by
  intro h
  change ((i.val + 1 : ℕ) : ℂ) ^ a = ((j.val + 1 : ℕ) : ℂ) ^ a at h
  have hnat : (i.val + 1) ^ a = (j.val + 1) ^ a := by
    exact_mod_cast h
  have hbase := Nat.pow_left_injective (Nat.ne_of_gt ha) hnat
  apply hij
  exact Fin.ext (Nat.add_right_cancel hbase)

/-- Explicit labelled Puiseux polynomial. -/
def separatedPolynomial {n : ℕ} (family : AiryChainFamily n) (i : Fin n) :
    PuiseuxPolynomial :=
  (family.chain i).airyPolynomial (family.separatedCoefficient i)

theorem separatedPolynomial_coefficients_ne_zero {n : ℕ} (family : AiryChainFamily n)
    (i : Fin n) {slope : ℚ} {c : ℂ} (h : (slope, c) ∈ family.separatedPolynomial i) :
    c ≠ 0 := by
  rw [(family.chain i).coefficient_of_mem_airyPolynomial h]
  exact family.separatedCoefficient_ne_zero i

/-- Equal-slope leading coefficients of distinct labels lie in distinct power-orbits. -/
theorem leading_power_orbits_pairwise_distinct {n : ℕ} (family : AiryChainFamily n)
    {i j : Fin n} (hij : i ≠ j) (hfactor : family.firstFactor i = family.firstFactor j) :
    family.separatedCoefficient i ^ family.firstFactor i ≠
      family.separatedCoefficient j ^ family.firstFactor j := by
  rw [← hfactor]
  exact family.separatedCoefficient_pow_ne (family.firstFactor_pos i) hij

/-- Constructive simultaneous realization certificate for a family of strict divisor chains. -/
structure SeparatedRealization {n : ℕ} (family : AiryChainFamily n) where
  polynomial : Fin n → PuiseuxPolynomial
  polynomial_eq : ∀ i, polynomial i = family.separatedPolynomial i
  coefficients_nonzero : ∀ i slope c, (slope, c) ∈ polynomial i → c ≠ 0
  leading_power_separated : ∀ i j, i ≠ j → family.firstFactor i = family.firstFactor j →
    family.separatedCoefficient i ^ family.firstFactor i ≠
      family.separatedCoefficient j ^ family.firstFactor j

/-- Every finite divisor-chain family has an explicit simultaneous leading-separated Puiseux
realization. -/
def simultaneousSeparatedRealization {n : ℕ} (family : AiryChainFamily n) :
    SeparatedRealization family where
  polynomial := family.separatedPolynomial
  polynomial_eq := fun _ => rfl
  coefficients_nonzero := fun i _ _ h => family.separatedPolynomial_coefficients_ne_zero i h
  leading_power_separated := fun _ _ hij hfactor =>
    family.leading_power_orbits_pairwise_distinct hij hfactor

end AiryChainFamily

end IrregularStokes
end GaloisForLFunctions
