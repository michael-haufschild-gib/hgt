import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity

/-!
# Quadratic Casimir from antisymmetric structure constants

For a finite matrix family closed under commutators, antisymmetry of the
structure constants in the two contracted indices forces its quadratic
Casimir to commute with every generator.  The proof is representation-free
and applies over both `ℝ` and `ℂ`.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem antisymmetric_symmetric_double_sum_eq_zero
    {𝕜 J M : Type*}
    [RCLike 𝕜] [Fintype J]
    [AddCommGroup M] [Module 𝕜 M]
    (c : J → J → 𝕜) (F : J → J → M)
    (hc : ∀ a k, c k a = -c a k)
    (hF : ∀ a k, F k a = F a k) :
    ∑ a, ∑ k, c a k • F a k = 0 := by
  let S : M := ∑ a, ∑ k, c a k • F a k
  have hSneg : S = -S := by
    calc
      S = ∑ k, ∑ a, c a k • F a k := by rw [Finset.sum_comm]
      _ = ∑ k, ∑ a, -(c k a • F k a) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro a _
            rw [hc k a, hF k a]
            simp
      _ = -S := by simp [S]
  have htwo : (2 : 𝕜) • S = 0 := by
    calc
      (2 : 𝕜) • S = S + S := by module
      _ = S + -S := congrArg (fun z => S + z) hSneg
      _ = 0 := add_neg_cancel S
  have htwo_ne : (2 : 𝕜) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp htwo).resolve_left htwo_ne

/-- A finite matrix representation with structure constants antisymmetric in
the two contracted indices has a central quadratic Casimir. -/
theorem quadraticCasimir_commutes_of_antisymmetric_structure
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (c : J → J → J → 𝕜)
    (hbracket : ∀ a b,
      A a * A b - A b * A a = ∑ k, c a b k • A k)
    (hanti : ∀ a b k, c k b a = -c a b k)
    (b : J) :
    (∑ a, A a * A a) * A b = A b * (∑ a, A a * A a) := by
  classical
  rw [Finset.sum_mul, Matrix.mul_sum]
  rw [← sub_eq_zero]
  calc
    (∑ a, A a * A a * A b) - ∑ a, A b * (A a * A a) =
        ∑ a, ((A a * A a) * A b - A b * (A a * A a)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ a,
        (A a * (A a * A b - A b * A a) +
          (A a * A b - A b * A a) * A a) := by
          apply Finset.sum_congr rfl
          intro a _
          noncomm_ring
    _ = ∑ a, ∑ k, c a b k • (A a * A k + A k * A a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hbracket]
          simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul,
            Matrix.smul_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          module
    _ = 0 := antisymmetric_symmetric_double_sum_eq_zero
      (fun a k => c a b k) (fun a k => A a * A k + A k * A a)
      (fun a k => hanti a b k) (fun a k => by simp [add_comm])

end

end GaloisForLFunctions.HTGeometry
