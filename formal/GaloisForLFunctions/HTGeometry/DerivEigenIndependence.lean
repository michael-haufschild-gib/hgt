/-
# Derivation eigenvectors with distinct eigenvalues are independent

If `E i` are nonzero elements of a differential field extension with `(E i)′ = λ i · E i`, and no
eigenvalue difference `λ j - λ i` is the logarithmic derivative of a nonzero base element, then the
`E i` are linearly independent over the base.

The proof is the classical minimal-relation induction: normalise a relation at one slot so that
coefficient is `1`, differentiate, subtract `λ` times the original — the normalised slot drops out
because its coefficient is constant — and conclude by induction that every other coefficient
satisfies `c′ = (λ_j - λ_i) c`, which the rigidity hypothesis forbids.

Over `ℂ(s)` the hypothesis is automatic: a nonzero rational function never has a nonzero constant
logarithmic derivative.  So exponentials with distinct complex frequencies, together with the
constant `1`, are linearly independent over `ℂ(s)`.
-/
import GaloisForLFunctions.HTGeometry.RationalExponentialShadow
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.DerivEigen

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

theorem deriv_algebraMap_mul (c : F) (x : M) :
    (algebraMap F M c * x)′ = algebraMap F M c′ * x + algebraMap F M c * x′ := by
  rw [Derivation.leibniz, deriv_algebraMap]
  simp only [smul_eq_mul]
  ring

/-- Strong-induction core of the eigenvector independence lemma. -/
theorem eigen_sum_eq_zero_aux {ι : Type*} [DecidableEq ι]
    (lam : ι → F) (E : ι → M)
    (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hrigid : ∀ i j : ι, i ≠ j → ∀ c : F, c ≠ 0 → c′ ≠ (lam j - lam i) * c) :
    ∀ n : ℕ, ∀ s : Finset ι, s.card ≤ n → ∀ g : ι → F,
      (∑ i ∈ s, algebraMap F M (g i) * E i) = 0 → ∀ i ∈ s, g i = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hs g _ i hi
      exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hs)) (by
        intro h
        rw [h] at hi
        exact absurd hi (Finset.notMem_empty i))
  | succ n ih =>
      intro s hs g hsum i hi
      by_contra hgi
      -- there is a nonzero coefficient; normalise at it
      set c : ι → F := fun k => g k / g i with hc
      have hci : c i = 1 := by
        rw [hc]
        exact div_self hgi
      have hcsum : (∑ k ∈ s, algebraMap F M (c k) * E k) = 0 := by
        have hscale : (∑ k ∈ s, algebraMap F M (c k) * E k)
            = algebraMap F M (g i)⁻¹ * ∑ k ∈ s, algebraMap F M (g k) * E k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          show algebraMap F M (g k / g i) * E k = _
          rw [div_eq_inv_mul, map_mul]
          ring
        rw [hscale, hsum, mul_zero]
      -- differentiate and eliminate the normalised slot
      have hderiv : (∑ k ∈ s, algebraMap F M (c k) * E k)′
          = ∑ k ∈ s, (algebraMap F M (c k)′ * E k
            + algebraMap F M (c k) * algebraMap F M (lam k) * E k) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [deriv_algebraMap_mul, heig k]
        ring
      have hzero : (∑ k ∈ s, (algebraMap F M (c k)′ * E k
          + algebraMap F M (c k) * algebraMap F M (lam k) * E k)) = 0 := by
        rw [← hderiv, hcsum, map_zero]
      have hnew : (∑ k ∈ s, algebraMap F M ((c k)′ + c k * (lam k - lam i)) * E k) = 0 := by
        have hsplit : (∑ k ∈ s, algebraMap F M ((c k)′ + c k * (lam k - lam i)) * E k)
            = (∑ k ∈ s, (algebraMap F M (c k)′ * E k
                + algebraMap F M (c k) * algebraMap F M (lam k) * E k))
              - algebraMap F M (lam i) * ∑ k ∈ s, algebraMap F M (c k) * E k := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_add, map_mul, map_sub]
          ring
        rw [hsplit, hzero, hcsum, mul_zero, sub_zero]
      -- the normalised slot drops out
      have hdi : (c i)′ + c i * (lam i - lam i) = 0 := by
        rw [hci, sub_self, mul_zero, add_zero]
        simp
      have herase : (∑ k ∈ s.erase i, algebraMap F M ((c k)′ + c k * (lam k - lam i)) * E k)
          = 0 := by
        have := Finset.sum_erase_add s
          (fun k => algebraMap F M ((c k)′ + c k * (lam k - lam i)) * E k) hi
        rw [hdi, map_zero, zero_mul, add_zero] at this
        rw [this]
        exact hnew
      have hcard : (s.erase i).card ≤ n := by
        have := Finset.card_erase_of_mem hi
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      have hall := ih (s.erase i) hcard
        (fun k => (c k)′ + c k * (lam k - lam i)) herase
      -- rigidity kills every other coefficient
      have hczero : ∀ k ∈ s.erase i, c k = 0 := by
        intro k hk
        by_contra hck
        have hne : k ≠ i := Finset.ne_of_mem_erase hk
        have heq : (c k)′ = (lam i - lam k) * c k := by
          have := hall k hk
          have hexp : (c k)′ + c k * (lam k - lam i) = 0 := this
          linear_combination hexp
        exact hrigid k i hne (c k) hck heq
      -- only the normalised slot survives, contradicting the relation
      have honly : (∑ k ∈ s, algebraMap F M (c k) * E k) = algebraMap F M (c i) * E i := by
        rw [← Finset.sum_erase_add s (fun k => algebraMap F M (c k) * E k) hi]
        have : (∑ k ∈ s.erase i, algebraMap F M (c k) * E k) = 0 := by
          refine Finset.sum_eq_zero (fun k hk => ?_)
          rw [hczero k hk, map_zero, zero_mul]
        rw [this, zero_add]
      rw [honly, hci, map_one, one_mul] at hcsum
      exact hE i hcsum

/-- **Lemma 2.**  Derivation eigenvectors with distinct eigenvalues, none of whose eigenvalue
differences is a logarithmic derivative in the base, are linearly independent over the base. -/
theorem linearIndependent_of_deriv_eigen {ι : Type*} [DecidableEq ι]
    (lam : ι → F) (E : ι → M)
    (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hrigid : ∀ i j : ι, i ≠ j → ∀ c : F, c ≠ 0 → c′ ≠ (lam j - lam i) * c) :
    LinearIndependent F E := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  refine eigen_sum_eq_zero_aux lam E hE heig hrigid s.card s le_rfl g ?_ i hi
  rw [← hsum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.smul_def]

end GaloisForLFunctions.DerivEigen

namespace GaloisForLFunctions.DerivEigen

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RationalShadow

noncomputable section

local instance expEigenRatFuncDifferential : Differential (RatFunc ℂ) :=
  GaloisForLFunctions.ratFuncCoordinateDifferential

/-- **Lemma 2 over the rational base.**  Derivation eigenvectors with distinct complex
frequencies — the abstract form of `exp (λ_i s)` together with the constant `1` — are linearly
independent over `ℂ(s)`. -/
theorem linearIndependent_expEigen_over_ratFunc
    {M : Type*} [Field M] [Algebra (RatFunc ℂ) M] [Differential M]
    [DifferentialAlgebra (RatFunc ℂ) M]
    {ι : Type*} [DecidableEq ι] (lam : ι → ℂ) (hlam : Function.Injective lam) (E : ι → M)
    (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′
      = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i) :
    LinearIndependent (RatFunc ℂ) E := by
  classical
  refine linearIndependent_of_deriv_eigen
    (fun i => algebraMap ℂ (RatFunc ℂ) (lam i)) E hE heig ?_
  intro i j hij c hc
  have hdiff : algebraMap ℂ (RatFunc ℂ) (lam j) - algebraMap ℂ (RatFunc ℂ) (lam i)
      = algebraMap ℂ (RatFunc ℂ) (lam j - lam i) := by
    rw [map_sub]
  have hne : lam j - lam i ≠ 0 := by
    intro h
    exact hij (hlam (by linear_combination -h))
  rw [hdiff]
  have hbridge : c′ = ratFuncCoordinateDerivation ℂ c := rfl
  rw [hbridge]
  exact ratFuncCoordinateDerivation_ne_smul hc hne

end

end GaloisForLFunctions.DerivEigen
