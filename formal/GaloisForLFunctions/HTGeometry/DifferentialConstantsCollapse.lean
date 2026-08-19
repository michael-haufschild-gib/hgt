import GaloisForLFunctions.HTGeometry.BaseFieldCollapse
import GaloisForLFunctions.HTGeometry.DifferentialSolutionSpace
import GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw

/-!
# Solutions of a linear differential equation that form a ring are constants

An element all of whose powers solve one monic scalar linear differential equation of order `n`
satisfies a nonzero polynomial relation with constant coefficients — the `n + 1` powers cannot be
independent over the constants — so it is algebraic over the constants, and when those are
algebraically closed it is itself a constant.

The consequence recorded here is the one the classification of matrix algebras needs: for a
multiplicatively closed set of matrices containing the identity, the scalars `c` with `c • 1` in the
set form a ring, so if they all solve one such equation they are all constants.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {K : Type*} [Field K] [Differential K]

/-- **A power family of solutions collapses to the constants.**  If every power of `x` solves a
fixed monic scalar linear differential equation and the constants are algebraically closed, then
`x` is itself a constant. -/
theorem deriv_eq_zero_of_solution_powers [IsAlgClosed (differentialConstants K)]
    {n : ℕ} (a : Fin n → K) {x : K}
    (hx : ∀ m : ℕ, differentialJet n (x ^ m)
      = ∑ i, a i * differentialJet (i : ℕ) (x ^ m)) :
    x′ = 0 := by
  classical
  obtain ⟨d, hdconst, ⟨m₀, hm₀⟩, hrel⟩ :=
    exists_constantCoeff_relation_of_powers a (x := x) (fun m => hx (m : ℕ))
  set g : Fin (n + 1) → differentialConstants K := fun m => ⟨d m, hdconst m⟩ with hg
  have hgne : ∃ m, g m ≠ 0 := by
    refine ⟨m₀, ?_⟩
    intro h0
    exact hm₀ (congrArg Subtype.val h0)
  have hrel' : ∑ m, algebraMap (differentialConstants K) K (g m) * x ^ (m : ℕ) = 0 := hrel
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_polynomial_relation hgne hrel'
  rw [hc]
  exact c.2

omit [Differential K] in
/-- The powers of a scalar matrix stay scalar. -/
theorem smul_one_pow (c : K) (m : ℕ) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)) ^ m = (c ^ m) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

/-- **The line stabiliser of the identity is constant.**  If the scalars `c` with `c • 1` in a
multiplicatively closed set all solve one monic scalar linear differential equation, and the
constants are algebraically closed, then every such scalar is a constant. -/
theorem exists_eq_algebraMap_of_smul_one_solution
    [IsAlgClosed (differentialConstants K)]
    (A : Submodule (differentialConstants K) (Matrix (Fin 2) (Fin 2) K))
    (hone : (1 : Matrix (Fin 2) (Fin 2) K) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) {n : ℕ} (a : Fin n → K)
    (hsol : ∀ c : K, c • (1 : Matrix (Fin 2) (Fin 2) K) ∈ A →
      differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c) :
    ∀ c : K, c • (1 : Matrix (Fin 2) (Fin 2) K) ∈ A →
      ∃ c₀ : differentialConstants K, c = algebraMap (differentialConstants K) K c₀ := by
  intro c hc
  have hpow : ∀ m : ℕ, (c ^ m) • (1 : Matrix (Fin 2) (Fin 2) K) ∈ A := by
    intro m
    induction m with
    | zero => simpa using hone
    | succ m ih =>
        have hprod := hmul _ ih _ hc
        rwa [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← pow_succ] at hprod
  have hzero : c′ = 0 :=
    deriv_eq_zero_of_solution_powers a (fun m => hsol (c ^ m) (hpow m))
  exact ⟨⟨c, hzero⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
