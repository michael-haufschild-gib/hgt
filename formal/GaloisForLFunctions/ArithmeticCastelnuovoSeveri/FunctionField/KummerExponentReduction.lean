import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerBranchIrreducibility
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reduction of Kummer branch exponents

In `z^(n+1) = c x (1-x^(b+1))^R`, the function field depends only on
`R` modulo `n+1`. Multiplying the radical in the reduced model by the
removed branch power constructs an embedding of the original field.
Both fields have degree `n+1` over the rational base, so this embedding
is an isomorphism. The result holds over every coefficient field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K]

/-- Euclidean division removes an exact covering-degree power from the branch polynomial. -/
theorem kummerBranch_reduce_exponent (c : Kˣ) (b R n : ℕ) :
    kummerBranch c b R =
      ((1 - X ^ (b + 1)) ^ (R / (n + 1))) ^ (n + 1) *
        kummerBranch c b (R % (n + 1)) := by
  have hR : R / (n + 1) * (n + 1) + R % (n + 1) = R :=
    by simpa only [Nat.mul_comm] using Nat.div_add_mod R (n + 1)
  unfold kummerBranch
  rw [← pow_mul]
  calc
    _ = C (c : K) * X *
        ((1 - X ^ (b + 1)) ^ (R / (n + 1) * (n + 1)) *
          (1 - X ^ (b + 1)) ^ (R % (n + 1))) := by rw [← pow_add, hR]
    _ = _ := by ring

/-- The original radical realized as a scaled radical in the reduced function field. -/
def kummerReducedRoot (c : Kˣ) (b R n : ℕ) :
    KummerBranchField c b (R % (n + 1)) n :=
  algebraMap K[X] (KummerBranchField c b (R % (n + 1)) n)
      ((1 - X ^ (b + 1)) ^ (R / (n + 1))) *
    AdjoinRoot.root (kummerBranchFieldPolynomial c b (R % (n + 1)) n)

/-- The scaled radical satisfies the original branch equation. -/
theorem kummerReducedRoot_pow (c : Kˣ) (b R n : ℕ) :
    kummerReducedRoot c b R n ^ (n + 1) =
      algebraMap K[X] (KummerBranchField c b (R % (n + 1)) n) (kummerBranch c b R) := by
  rw [kummerReducedRoot, mul_pow, kummerBranchField_root_pow,
    ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X])
      (KummerBranchField c b (R % (n + 1)) n), ← map_pow, ← map_mul,
    ← kummerBranch_reduce_exponent]

/-- Evaluation at the scaled radical embeds the original Kummer field into its reduced model. -/
def kummerExponentReductionHom (c : Kˣ) (b R n : ℕ) :
    KummerBranchField c b R n →ₐ[FractionRing K[X]]
      KummerBranchField c b (R % (n + 1)) n :=
  AdjoinRoot.liftAlgHom (kummerBranchFieldPolynomial c b R n)
    (Algebra.ofId (FractionRing K[X]) (KummerBranchField c b (R % (n + 1)) n))
    (kummerReducedRoot c b R n) (by
      simp only [kummerBranchFieldPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      apply sub_eq_zero.mpr
      change kummerReducedRoot c b R n ^ (n + 1) =
        algebraMap (FractionRing K[X]) (KummerBranchField c b (R % (n + 1)) n)
          (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))
      rw [← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X])
        (KummerBranchField c b (R % (n + 1)) n)]
      exact kummerReducedRoot_pow c b R n)

/-- Reduction of the branch exponent modulo the covering degree preserves the actual function field. -/
def kummerExponentReductionEquiv (c : Kˣ) (b R n : ℕ) :
    KummerBranchField c b R n ≃ₐ[FractionRing K[X]]
      KummerBranchField c b (R % (n + 1)) n := by
  letI : FiniteDimensional (FractionRing K[X]) (KummerBranchField c b R n) :=
    (show (kummerBranchFieldPolynomial c b R n).Monic from
      monic_X_pow_sub_C _ (Nat.succ_ne_zero n)).finite_adjoinRoot
  letI : FiniteDimensional (FractionRing K[X]) (KummerBranchField c b (R % (n + 1)) n) :=
    (show (kummerBranchFieldPolynomial c b (R % (n + 1)) n).Monic from
      monic_X_pow_sub_C _ (Nat.succ_ne_zero n)).finite_adjoinRoot
  let f := kummerExponentReductionHom c b R n
  refine AlgEquiv.ofBijective f ⟨f.injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) ?_).mp f.injective
  rw [kummerBranchField_finrank, kummerBranchField_finrank]

/-- The field isomorphism sends the named radical to its explicit branch-scaled replacement. -/
theorem kummerExponentReductionEquiv_root (c : Kˣ) (b R n : ℕ) :
    kummerExponentReductionEquiv c b R n (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) =
      kummerReducedRoot c b R n := by
  change kummerExponentReductionHom c b R n (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = _
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

#print axioms kummerExponentReductionEquiv

/-- Equal branch exponents define canonically identical Kummer extensions. -/
def kummerExponentCongrEquiv (c : Kˣ) (b R S n : ℕ) (h : R = S) :
    KummerBranchField c b R n ≃ₐ[FractionRing K[X]] KummerBranchField c b S n := by
  subst S
  exact AlgEquiv.refl

/-- Adding any multiple of the covering degree preserves the function field over its rational base. -/
def kummerExponentShiftEquiv (c : Kˣ) (b R n k : ℕ) :
    KummerBranchField c b (R + k * (n + 1)) n ≃ₐ[FractionRing K[X]] KummerBranchField c b R n := by
  have hmod : (R + k * (n + 1)) % (n + 1) = R % (n + 1) := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, add_zero, Nat.mod_mod]
  exact ((kummerExponentReductionEquiv c b (R + k * (n + 1)) n).trans
    (kummerExponentCongrEquiv c b _ _ n hmod)).trans
    (kummerExponentReductionEquiv c b R n).symm

#print axioms kummerExponentShiftEquiv
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
