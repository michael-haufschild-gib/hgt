import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.EulerJetsDetectTheDiagonal
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialSyzygiesForceTheMixedJets

/-!
# The polynomial image of Stepanov syzygies

A paired polynomial retains the two factors in separate variable copies.
Its Euler jets on the diagonal are the polynomial first-factor syzygies.
Adams substitution sends the diagonal ideal to the fixed-point ideal,
including the coordinate hyperplanes omitted by the fixed torus.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

/-- The integral ideal of the full affine Adams fixed locus. -/
def adamsFixedIdeal (q : ℕ) : Ideal (MvPolynomial σ ℤ) :=
  Ideal.span (Set.range fun j : σ => (X j : MvPolynomial σ ℤ) ^ q - X j)

/-- First factors use the outer variables; second factors lie in the coefficient ring. -/
def stepanovPairPolynomial {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ) :
    MvPolynomial σ (MvPolynomial σ ℤ) :=
  ∑ i, MvPolynomial.map (C : ℤ →+* MvPolynomial σ ℤ) (f i) * C (g i)

/-- Apply Adams to the coefficient variables and identify the outer variables with the result. -/
def stepanovDiagonalMap (q : ℕ) :
    MvPolynomial σ (MvPolynomial σ ℤ) →+* MvPolynomial σ ℤ :=
  eval₂Hom (adams q).toRingHom X

theorem eval_X_map_C (F : MvPolynomial σ ℤ) :
    eval (X : σ → MvPolynomial σ ℤ)
      (MvPolynomial.map (C : ℤ →+* MvPolynomial σ ℤ) F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.map_C, eval_C]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F j hF => simp only [map_mul, MvPolynomial.map_X, eval_X, hF]

/-- The diagonal Euler jets of a paired polynomial are precisely its first-factor moments. -/
theorem eval_eulerWord_stepanovPairPolynomial {m : ℕ} (L : List σ)
    (f g : Fin m → MvPolynomial σ ℤ) :
    eval (X : σ → MvPolynomial σ ℤ) (polynomialEulerWord L (stepanovPairPolynomial f g)) =
      stepanovWordMoment L f g := by
  simp only [stepanovPairPolynomial, map_sum, polynomialEulerWord_mul_C,
    polynomialEulerWord_map, map_mul, eval_X_map_C, eval_C]
  rfl

/-- Global polynomial syzygies are exactly membership in the ordinary diagonal-ideal power. -/
theorem stepanovPairPolynomial_mem_diagonal_pow_iff (r : ℕ) {m : ℕ}
    (f g : Fin m → MvPolynomial σ ℤ) :
    stepanovPairPolynomial f g ∈ polynomialPointIdeal (X : σ → MvPolynomial σ ℤ) ^ r ↔
      ∀ L : List σ, L.length < r → stepanovWordMoment L f g = 0 := by
  rw [← polynomialEulerVanishesToOrder_iff_mem_pointIdeal_pow _ (fun j => MvPolynomial.X_ne_zero j)]
  simp only [PolynomialEulerVanishesToOrder, eval_eulerWord_stepanovPairPolynomial]

theorem adams_C (q : ℕ) (c : ℤ) : adams q (C c : MvPolynomial σ ℤ) = C c := by
  simp only [adams, aeval_C, MvPolynomial.algebraMap_eq]

theorem stepanovDiagonalMap_X (q : ℕ) (j : σ) :
    stepanovDiagonalMap q (X j : MvPolynomial σ (MvPolynomial σ ℤ)) = X j :=
  eval₂_X _ _ _

theorem stepanovDiagonalMap_C (q : ℕ) (G : MvPolynomial σ ℤ) :
    stepanovDiagonalMap q (C G : MvPolynomial σ (MvPolynomial σ ℤ)) = adams q G :=
  eval₂Hom_C _ _ _

/-- The outer variables provide an integral section of the Adams substitution map. -/
theorem stepanovDiagonalMap_lift (q : ℕ) (F : MvPolynomial σ ℤ) :
    stepanovDiagonalMap q (MvPolynomial.map (C : ℤ →+* MvPolynomial σ ℤ) F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.map_C, stepanovDiagonalMap_C, adams_C]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F j hF => simp only [map_mul, MvPolynomial.map_X, stepanovDiagonalMap_X, hF]

theorem stepanovDiagonalMap_surjective (q : ℕ) :
    Function.Surjective (stepanovDiagonalMap (σ := σ) q) :=
  fun F => ⟨MvPolynomial.map C F, stepanovDiagonalMap_lift q F⟩

theorem stepanovDiagonalMap_pair (q : ℕ) {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ) :
    stepanovDiagonalMap q (stepanovPairPolynomial f g) = stepanovAux q f g := by
  simp only [stepanovPairPolynomial, stepanovAux, map_sum, map_mul,
    stepanovDiagonalMap_lift, stepanovDiagonalMap_C]

theorem stepanovDiagonalMap_generator (q : ℕ) (j : σ) :
    stepanovDiagonalMap q ((X j : MvPolynomial σ (MvPolynomial σ ℤ)) - C (X j)) =
      (X j : MvPolynomial σ ℤ) - X j ^ q := by
  rw [map_sub, stepanovDiagonalMap_X, stepanovDiagonalMap_C, adams_X]

/-- The full affine fixed-point ideal is the image of the integral diagonal ideal. -/
theorem map_diagonalIdeal_stepanov (q : ℕ) :
    Ideal.map (stepanovDiagonalMap q) (polynomialPointIdeal (X : σ → MvPolynomial σ ℤ)) =
      adamsFixedIdeal q := by
  apply le_antisymm
  · rw [polynomialPointIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨G, ⟨j, rfl⟩, rfl⟩
    rw [stepanovDiagonalMap_generator]
    change (X j : MvPolynomial σ ℤ) - X j ^ q ∈ adamsFixedIdeal q
    have hg : (X j : MvPolynomial σ ℤ) ^ q - X j ∈ adamsFixedIdeal q :=
      Ideal.subset_span ⟨j, rfl⟩
    simpa only [neg_sub] using (adamsFixedIdeal q).neg_mem hg
  · rw [adamsFixedIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change (X j : MvPolynomial σ ℤ) ^ q - X j ∈
      Ideal.map (stepanovDiagonalMap q) (polynomialPointIdeal (X : σ → MvPolynomial σ ℤ))
    have hg : (X j : MvPolynomial σ (MvPolynomial σ ℤ)) - C (X j) ∈
        polynomialPointIdeal (X : σ → MvPolynomial σ ℤ) := Ideal.subset_span ⟨j, rfl⟩
    have hm := Ideal.mem_map_of_mem (stepanovDiagonalMap q) hg
    rw [stepanovDiagonalMap_generator] at hm
    simpa only [neg_sub] using
      (Ideal.map (stepanovDiagonalMap q) (polynomialPointIdeal (X : σ → MvPolynomial σ ℤ))).neg_mem hm

/-- Every polynomial in two copies of the variables is a finite paired sum over the integers. -/
theorem exists_stepanovPairPolynomial (Q : MvPolynomial σ (MvPolynomial σ ℤ)) :
    ∃ m, ∃ f g : Fin m → MvPolynomial σ ℤ, stepanovPairPolynomial f g = Q := by
  classical
  let e : Fin (Fintype.card Q.support) ≃ Q.support := (Fintype.equivFin Q.support).symm
  refine ⟨Fintype.card Q.support, (fun i => monomial (e i : σ →₀ ℕ) (1 : ℤ)),
    (fun i => Q.coeff (e i)), ?_⟩
  calc
    stepanovPairPolynomial (fun i => monomial (e i : σ →₀ ℕ) (1 : ℤ))
        (fun i => Q.coeff (e i)) =
        ∑ i, monomial (e i : σ →₀ ℕ) (Q.coeff (e i)) := by
      unfold stepanovPairPolynomial
      apply sum_congr rfl
      intro i _
      rw [MvPolynomial.map_monomial, map_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
    _ = ∑ a : Q.support, monomial (a : σ →₀ ℕ) (Q.coeff a) :=
      e.sum_comp (fun a : Q.support =>
        (monomial (a : σ →₀ ℕ) (Q.coeff a) : MvPolynomial σ (MvPolynomial σ ℤ)))
    _ = Q := by
      rw [Finset.univ_eq_attach]
      exact (Finset.sum_attach Q.support
        (fun a : σ →₀ ℕ => (monomial a (Q.coeff a) : MvPolynomial σ (MvPolynomial σ ℤ)))).trans Q.as_sum.symm

/-- Exact image classification: polynomial syzygies produce precisely the fixed-point ideal power. -/
theorem mem_adamsFixedIdeal_pow_iff_stepanov_syzygies (q r : ℕ) (F : MvPolynomial σ ℤ) :
    F ∈ adamsFixedIdeal q ^ r ↔
      ∃ m, ∃ f g : Fin m → MvPolynomial σ ℤ,
        (∀ L : List σ, L.length < r → stepanovWordMoment L f g = 0) ∧
          stepanovAux q f g = F := by
  constructor
  · intro hF
    rw [← map_diagonalIdeal_stepanov q, ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective (stepanovDiagonalMap q) (stepanovDiagonalMap_surjective q)] at hF
    obtain ⟨Q, hQ, hQF⟩ := hF
    obtain ⟨m, f, g, hpair⟩ := exists_stepanovPairPolynomial Q
    rw [← hpair] at hQ hQF
    rw [stepanovDiagonalMap_pair] at hQF
    exact ⟨m, f, g, (stepanovPairPolynomial_mem_diagonal_pow_iff r f g).mp hQ, hQF⟩
  · rintro ⟨m, f, g, hsy, hF⟩
    have hQ := (stepanovPairPolynomial_mem_diagonal_pow_iff r f g).mpr hsy
    have hm := Ideal.mem_map_of_mem (stepanovDiagonalMap q) hQ
    rw [Ideal.map_pow, map_diagonalIdeal_stepanov, stepanovDiagonalMap_pair, hF] at hm
    exact hm

#print axioms stepanovPairPolynomial_mem_diagonal_pow_iff
#print axioms mem_adamsFixedIdeal_pow_iff_stepanov_syzygies

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
