import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PrimitiveRootProjectors

/-!
# Coefficient descent in diagonal cyclic actions

A vector with one cyclic eigenvalue has zero coordinates at every
basis vector with a different eigenvalue. For character weights that
increase under multiplication by `A`, an eigenvector of weight `j`
for the `A`th cyclic action can only involve smaller basis weights.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- A diagonal operator multiplies each basis coordinate by its corresponding eigenvalue. -/
theorem diagonal_basis_repr (B : Module.Basis ι K V) (S : V →ₗ[K] V) (eigenvalue : ι → K)
    (hS : ∀ i, S (B i) = eigenvalue i • B i) (v : V) (i : ι) :
    B.repr (S v) i = eigenvalue i * B.repr v i := by
  classical
  conv_lhs => rw [← B.sum_repr v]
  rw [map_sum, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simpa only [map_smul, hS, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_true, smul_eq_mul, mul_one] using
        mul_comm (B.repr v i) (eigenvalue i)
  · intro j _ hji
    simp only [map_smul, hS, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg hji, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- An eigenvector has zero coefficient at every diagonal basis vector with a different eigenvalue. -/
theorem diagonal_eigenvector_coefficient_zero (B : Module.Basis ι K V)
    (S : V →ₗ[K] V) (eigenvalue : ι → K) (hS : ∀ i, S (B i) = eigenvalue i • B i)
    (v : V) (μ : K) (hv : S v = μ • v) (i : ι) (hi : eigenvalue i ≠ μ) :
    B.repr v i = 0 := by
  have h := congrArg (fun x : V => B.repr x i) hv
  rw [diagonal_basis_repr B S eigenvalue hS, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : (eigenvalue i - μ) * B.repr v i = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi)

/-- Rising character residues force an eigenvector for the powered cyclic action to have lower weights. -/
theorem diagonal_character_weight_descent
    (B : Module.Basis ι K V) (S : V →ₗ[K] V) (M A : ℕ) (hM : 0 < M)
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) (weight : ι → ℕ)
    (hS : ∀ i, S (B i) = ζ ^ (A * weight i) • B i)
    (hrise : ∀ i, weight i < (A * weight i) % M)
    (v : V) (j : ℕ) (hj : j < M) (hv : S v = ζ ^ j • v)
    (i : ι) (hji : j ≤ weight i) : B.repr v i = 0 := by
  apply diagonal_eigenvector_coefficient_zero B S (fun i => ζ ^ (A * weight i)) hS v
    (ζ ^ j) hv i
  intro heq
  have hmod : ζ ^ (A * weight i) = ζ ^ ((A * weight i) % M) := by
    conv_lhs => rw [← Nat.div_add_mod (A * weight i) M]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [hmod] at heq
  have hw := hζ.pow_inj (Nat.mod_lt _ hM) hj heq
  exact (not_lt_of_ge hji) (hw ▸ hrise i)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
