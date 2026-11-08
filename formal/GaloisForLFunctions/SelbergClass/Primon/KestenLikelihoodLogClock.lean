import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodCompletion

/-!
# Prime logarithmic clocks on likelihood observables

Weighting the prime likelihood at `p` by `(log p)/pᵐ` defines a graph on
finite prime packets. For every finite `m`, its closure is the entire
product of the closed likelihood Hilbert space with itself. This transfers
the Hardy logarithmic-germ rigidity theorem to actual spectral likelihoods.
-/

open _root_.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Finite likelihood packets, viewed in their closed spectral span. -/
def kestenLikelihoodPacket : (Nat.Primes →₀ ℝ) →ₗ[ℝ] KestenLikelihoodHilbert :=
  hardyLikelihoodUnitary.toLinearEquiv.toLinearMap.comp primeHardyKernelMap

/-- Multiplication of prime packet coefficients by the finite-order logarithmic weight. -/
def kestenLikelihoodLogClock (m : ℕ) :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] KestenLikelihoodHilbert :=
  hardyLikelihoodUnitary.toLinearEquiv.toLinearMap.comp (primeFiniteTraceClock m)

/-- The closed-span packet has exactly its original semicircle `L²` representative. -/
theorem coe_kestenLikelihoodPacket (c : Nat.Primes →₀ ℝ) :
    (kestenLikelihoodPacket c : SemicircleL2) = kestenLikelihoodMap c :=
  hardyLikelihoodEmbedding_map c

/-- A single prime clock column is its actual likelihood, with weight `(log p)/pᵐ`. -/
theorem coe_kestenLikelihoodLogClock_single (m : ℕ) (p : Nat.Primes) (c : ℝ) :
    (kestenLikelihoodLogClock m (Finsupp.single p c) : SemicircleL2) =
      c • ((Real.log (p : ℝ) * (p : ℝ)⁻¹ ^ m) • kestenLikelihoodVector p) := by
  change (hardyLikelihoodUnitary (primeFiniteTraceClock m (Finsupp.single p c)) :
    SemicircleL2) = _
  rw [primeFiniteTraceClock_single, map_smul, map_smul]
  change c • ((Real.log (p : ℝ) * primeReciprocal p ^ m) •
    (hardyLikelihoodUnitary (primeHardyKernel p) : SemicircleL2)) = _
  rw [hardyLikelihoodUnitary_kernel]
  rfl

/-- Every finite-order likelihood clock has maximally multivalued graph closure. -/
theorem kestenLikelihoodLogClock_graphClosure_eq_top (m : ℕ) :
    (realLinearGraphSubmodule kestenLikelihoodPacket
      (kestenLikelihoodLogClock m)).topologicalClosure = ⊤ := by
  apply realLinearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y h
  have hrel : PrimeTailLogRelation m (hardyLikelihoodUnitary.symm x)
      (hardyLikelihoodUnitary.symm y) := by
    intro p
    have hp := h (Finsupp.single p 1)
    change inner ℝ (hardyLikelihoodUnitary (primeHardyKernelMap (Finsupp.single p 1))) x +
      inner ℝ (hardyLikelihoodUnitary (primeFiniteTraceClock m (Finsupp.single p 1))) y = 0 at hp
    simp only [primeHardyKernelMap_single, primeFiniteTraceClock_single, one_smul] at hp
    rw [← hardyLikelihoodUnitary.apply_symm_apply x,
      ← hardyLikelihoodUnitary.apply_symm_apply y,
      hardyLikelihoodUnitary.inner_map_map, hardyLikelihoodUnitary.inner_map_map,
      inner_smul_left] at hp
    simpa only [conj_trivial] using hp
  obtain ⟨hx, hy⟩ := primeTailLogRelation_eq_zero m hrel
  constructor
  · apply hardyLikelihoodUnitary.symm.injective
    simpa using hx
  · apply hardyLikelihoodUnitary.symm.injective
    simpa using hy

end
end GaloisForLFunctions.SelbergClass.Primon

