import GaloisForLFunctions.HTGeometry.AdaptiveEigenframeTwoQuerySourceMemory

/-!
# Energy-matched eigenframe source memory

Instead of squaring every Pauli-transfer entry before aggregation, contract the transfer matrix
against the Hamiltonian coefficient vector first.  Signed product-eigenframe extraction realizes
that contraction as one forward-query mean.  Every conserved coefficient vector then gives its
exact inverse-participation ratio, uniformly in time.
-/

open scoped BigOperators Matrix
open Matrix NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- `ℓ¹` mass of a finite real coefficient vector. -/
def finiteCoefficientL1Mass [Fintype ι] (h : ι → ℝ) : ℝ :=
  ∑ i, |h i|

/-- Signed, coefficient-matched product-eigenframe statistic.  Absolute coefficient products,
normalized by `‖h‖₁²`, are the trial probabilities; coefficient signs and the prepared output
eigenvalue are included in the bounded trial outcome. -/
def energyMatchedEigenframeAmplitude [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) : ℝ :=
  (∑ output : ι, ∑ input : ι,
      h output * h input *
        ((∑ b : σ → Bool,
            pauliEigenframeSign (label output) b *
              pauliEigenframeExpectation U (label input) (label output) b) /
          (Fintype.card (σ → Bool) : ℝ))) /
    (finiteCoefficientL1Mass h) ^ 2

/-- Signed eigenframe extraction turns the physical randomized mean into the coefficient quadratic
form of the exact Pauli-transfer compression. -/
theorem energyMatchedEigenframeAmplitude_eq_transfer [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    energyMatchedEigenframeAmplitude label h U =
      (∑ output : ι, ∑ input : ι,
        h output * h input * dictionaryPauliTransfer label U output input) /
        (finiteCoefficientL1Mass h) ^ 2 := by
  unfold energyMatchedEigenframeAmplitude dictionaryPauliTransfer
  simp_rw [average_pauliEigenframeExpectation_eq_transfer]

/-- A fixed transfer coordinate makes the energy-matched statistic equal exactly to the
coefficient inverse-participation ratio. -/
theorem energyMatchedEigenframeAmplitude_eq_of_fixed [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hfix : dictionaryPauliTransfer label U *ᵥ h = h) :
    energyMatchedEigenframeAmplitude label h U =
      (∑ i, (h i) ^ 2) / (finiteCoefficientL1Mass h) ^ 2 := by
  rw [energyMatchedEigenframeAmplitude_eq_transfer]
  congr 1
  calc
    (∑ output : ι, ∑ input : ι,
        h output * h input * dictionaryPauliTransfer label U output input) =
        ∑ output : ι, h output *
          (dictionaryPauliTransfer label U *ᵥ h) output := by
            apply Finset.sum_congr rfl
            intro output _houtput
            rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro input _hinput
            ring
    _ = ∑ output : ι, h output * h output := by rw [hfix]
    _ = ∑ output : ι, (h output) ^ 2 := by
      apply Finset.sum_congr rfl
      intro output _houtput
      ring

/-- Finite-dimensional Cauchy: the coefficient inverse-participation ratio is at least inverse
support cardinality.  Equality is attained by equal-magnitude coefficients. -/
theorem one_div_card_le_coefficientL2Sq_div_l1Sq
    [Fintype ι] [Nonempty ι] (h : ι → ℝ) (hh : h ≠ 0) :
    1 / (Fintype.card ι : ℝ) ≤
      (∑ i, (h i) ^ 2) / (finiteCoefficientL1Mass h) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hh
  have hl1pos : 0 < finiteCoefficientL1Mass h := by
    unfold finiteCoefficientL1Mass
    apply Finset.sum_pos'
    · exact fun j _hj => abs_nonneg (h j)
    · exact ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι => (1 : ℝ)) (fun j => |h j|)
  have hCS' : (finiteCoefficientL1Mass h) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ j, (h j) ^ 2 := by
    simpa [finiteCoefficientL1Mass, sq_abs] using hCS
  apply (div_le_div_iff₀ hcard (sq_pos_of_pos hl1pos)).2
  simpa [mul_comm] using hCS'

/-- Every nonzero fixed transfer coordinate produces an inverse-dictionary one-query mean. -/
theorem energyMatchedEigenframeAmplitude_ge_card_inv_of_fixed
    [Fintype ι] [Nonempty ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ) (hh : h ≠ 0)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hfix : dictionaryPauliTransfer label U *ᵥ h = h) :
    1 / (Fintype.card ι : ℝ) ≤ energyMatchedEigenframeAmplitude label h U := by
  rw [energyMatchedEigenframeAmplitude_eq_of_fixed label h U hfix]
  exact one_div_card_le_coefficientL2Sq_div_l1Sq h hh

/-- Exact autonomous value for every finite Pauli dictionary containing the Hamiltonian support. -/
theorem autonomous_energyMatchedEigenframeAmplitude_eq
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) =
      (∑ P, (pauliDictionaryEnergyCoordinates p H P) ^ 2) /
        (finiteCoefficientL1Mass (pauliDictionaryEnergyCoordinates p H)) ^ 2 := by
  apply energyMatchedEigenframeAmplitude_eq_of_fixed
  exact autonomousDictionaryPauliTransfer_fixes_energy p H hsupport t

/-- Permanent arbitrary-dictionary lower bound for every nonzero autonomous Hamiltonian. -/
theorem autonomous_energyMatchedEigenframeAmplitude_ge
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    1 / (Fintype.card {P // p P} : ℝ) ≤
      energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) := by
  apply energyMatchedEigenframeAmplitude_ge_card_inv_of_fixed
  · exact pauliDictionaryEnergyCoordinates_ne_zero p H hH hsupport
  · exact autonomousDictionaryPauliTransfer_fixes_energy p H hsupport t

/-- Fixed-body Majorana specialization: the permanent signed mean pays one inverse dictionary,
`binom(2n,q)⁻¹`, rather than its square and no Jordan--Wigner weight factor. -/
theorem autonomous_majoranaQBody_energyMatchedEigenframeAmplitude_ge
    {n q : ℕ} (hq : q ≤ 2 * n)
    (c : MajoranaQBodyIndex n q → ℝ) (hc : c ≠ 0) (t : ℝ) :
    1 / (Nat.choose (2 * n) q : ℝ) ≤
      energyMatchedEigenframeAmplitude
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (pauliDictionaryEnergyCoordinates (MajoranaQBodyDictionary n q)
          (majoranaQBodyHamiltonian c))
        (exp (t • ((-Complex.I) •
          ((majoranaQBodyHamiltonian c : selfAdjoint
            (Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hq
  rw [← majoranaQBodyDictionary_card]
  exact autonomous_energyMatchedEigenframeAmplitude_ge
    (MajoranaQBodyDictionary n q) (majoranaQBodyHamiltonian c)
    (majoranaQBodyHamiltonian_ne_zero c hc)
    (majoranaQBodyHamiltonian_hasDictionarySupport c) t

end

end GaloisForLFunctions.HTGeometry
