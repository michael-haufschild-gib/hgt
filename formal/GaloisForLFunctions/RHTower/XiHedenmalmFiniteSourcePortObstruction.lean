import GaloisForLFunctions.RHTower.XiHedenmalmInvariantHomogenization
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Infinite-dimensional obstruction for Hedenmalm source ports

The minimal coordinate-stable port containing the actual theta source cannot be finite
dimensional.  The completed source is nonzero on a neighbourhood of the spectral centre, so
multiplication by it embeds the polynomial ring into the function space.  Coordinate stability
then places an arbitrarily large independent polynomial orbit inside every honest source port.
-/

open Complex Filter Set

noncomputable section

namespace RHTower

/-- Polynomial coordinate orbit of the actual completed theta source. -/
def xiPolynomialSourceOrbit : Polynomial ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun P := fun z => P.eval z * XiC z
  map_add' P Q := by
    funext z
    simp [add_mul]
  map_smul' a P := by
    funext z
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Multiplication by `XiC` is injective on complex polynomials.  Global cancellation in the
pointwise function ring is unavailable because `XiC` has zeros; the nonzero analytic germ at zero
instead supplies infinitely many cancellation points. -/
theorem xiPolynomialSourceOrbit_injective :
    Function.Injective xiPolynomialSourceOrbit := by
  intro P Q hPQ
  have hXi_ne : {z : ℂ | XiC z ≠ 0} ∈ nhds 0 :=
    (XiC_analytic 0 (Set.mem_univ 0)).continuousAt.eventually_ne XiC_zero_ne
  have hinfinite : Set.Infinite {z : ℂ | XiC z ≠ 0} :=
    infinite_of_mem_nhds 0 hXi_ne
  have hroots : {z : ℂ | XiC z ≠ 0} ⊆
      {z : ℂ | Polynomial.IsRoot (P - Q) z} := by
    intro z hz
    change Polynomial.eval z (P - Q) = 0
    rw [Polynomial.eval_sub, sub_eq_zero]
    apply mul_right_cancel₀ hz
    exact congrFun hPQ z
  have hzero : P - Q = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot (P - Q) (hinfinite.mono hroots)
  exact sub_eq_zero.mp hzero

/-- The full spectral-coordinate orbit `z^n XiC(z)` is linearly independent. -/
theorem xiCoordinateOrbit_linearIndependent :
    LinearIndependent ℂ (fun n : ℕ => fun z : ℂ => z ^ n * XiC z) := by
  have hX : LinearIndependent ℂ
      (fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n) := by
    have hb := (Polynomial.basisMonomials ℂ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  have hmap := hX.map' xiPolynomialSourceOrbit
    (LinearMap.ker_eq_bot.mpr xiPolynomialSourceOrbit_injective)
  simpa [Function.comp_def, xiPolynomialSourceOrbit] using hmap

/-- Every coordinate-stable port containing `XiC` contains independent families of arbitrary
finite size. -/
theorem exists_linearIndependent_mem_coordinateStableXiSourcePort
    (S : Submodule ℂ (ℂ → ℂ)) (hXi : XiC ∈ S)
    (hstab : ∀ F ∈ S, xiCoordinateMultiplication F ∈ S) (n : ℕ) :
    ∃ v : Fin n → (ℂ → ℂ),
      (∀ i, v i ∈ S) ∧ LinearIndependent ℂ v := by
  let v : Fin n → (ℂ → ℂ) := fun i z => z ^ (i : ℕ) * XiC z
  refine ⟨v, ?_, ?_⟩
  · intro i
    simpa [v] using eval_mul_XiC_mem_of_coordinateMultiplication_stable
      S hXi hstab ((Polynomial.X : Polynomial ℂ) ^ (i : ℕ))
  · exact xiCoordinateOrbit_linearIndependent.comp
      (fun i : Fin n => (i : ℕ)) Fin.val_injective

/-- **Finite-source-port obstruction.**  No finite-dimensional complex function subspace can
contain the actual completed theta source and remain stable under spectral-coordinate
multiplication. -/
theorem not_finiteDimensional_coordinateStableXiSourcePort
    (S : Submodule ℂ (ℂ → ℂ)) (hXi : XiC ∈ S)
    (hstab : ∀ F ∈ S, xiCoordinateMultiplication F ∈ S) :
    ¬ FiniteDimensional ℂ S := by
  intro hfin
  obtain ⟨v, hvmem, hvind⟩ :=
    exists_linearIndependent_mem_coordinateStableXiSourcePort S hXi hstab
      (Module.finrank ℂ S + 1)
  have hv'ind : LinearIndependent ℂ (fun i => (⟨v i, hvmem i⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hvind
  have hcard := hv'ind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end RHTower
