import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Infinite support forces strict Cayley--Toeplitz positivity

The finite Cayley--Toeplitz section of a finite real measure is the Gram matrix of its conjugate
Cayley monomials in `L²`.  Infinite topological support makes those monomials linearly independent:
an `L²` dependence would give a polynomial vanishing on the infinite injective Cayley image of the
support.  Hence every finite section is positive definite.  This removes positive definiteness as
an additional hypothesis from the paper's complete inverse-Cholesky coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Matrix Polynomial
open Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

/-- The conjugate `n`th Cayley monomial as an element of `L²(μ)`.  Conjugation aligns mathlib's
inner-product convention with the paper's Toeplitz indexing `c_(i-j)`. -/
noncomputable def cayleyConjugateMonomialLp (mu : Measure ℝ) [IsFiniteMeasure mu]
    (n : ℕ) : Lp ℂ 2 mu :=
  MemLp.toLp (fun x : ℝ => star (realCayley x ^ n)) <|
    MemLp.of_bound ((continuous_star.comp (continuous_realCayley.pow n)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun x => by simp [norm_realCayley])

/-- The `L²` representative of a conjugate Cayley monomial is the expected pointwise function. -/
theorem cayleyConjugateMonomialLp_coeFn_ae (mu : Measure ℝ) [IsFiniteMeasure mu]
    (n : ℕ) :
    ⇑(cayleyConjugateMonomialLp mu n) =ᵐ[mu]
      fun x : ℝ => star (realCayley x ^ n) :=
  (MemLp.of_bound ((continuous_star.comp (continuous_realCayley.pow n)).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun x => by simp [norm_realCayley])).coeFn_toLp

/-- The Hermitian completion of the nonnegative Cayley moments is the integral of the corresponding
integer Cayley power. -/
theorem cayleyMomentZ_eq_integral_zpow (mu : Measure ℝ) [IsFiniteMeasure mu]
    (q : ℤ) :
    cayleyMomentZ mu q = ∫ x : ℝ, realCayley x ^ q ∂mu := by
  cases q with
  | ofNat n => simp [cayleyMomentZ, cayleyMoment]
  | negSucc n =>
      rw [cayleyMomentZ, cayleyMoment]
      change conj (∫ x : ℝ, realCayley x ^ (n + 1) ∂mu) = _
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_pow, ← Complex.inv_eq_conj (norm_realCayley x)]
      simp [zpow_negSucc]

/-- Inner products of conjugate Cayley monomials are exactly the two-sided Cayley moments. -/
theorem cayleyConjugateMonomialLp_inner (mu : Measure ℝ) [IsFiniteMeasure mu]
    (i j : ℕ) :
    inner ℂ (cayleyConjugateMonomialLp mu i) (cayleyConjugateMonomialLp mu j) =
      cayleyMomentZ mu ((i : ℤ) - (j : ℤ)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [cayleyMomentZ_eq_integral_zpow]
  apply integral_congr_ae
  filter_upwards [cayleyConjugateMonomialLp_coeFn_ae mu i,
    cayleyConjugateMonomialLp_coeFn_ae mu j] with x hi hj
  rw [hi, hj]
  have hne : realCayley x ≠ 0 := by
    intro hzero
    have := congrArg norm hzero
    rw [norm_realCayley] at this
    norm_num at this
  simp [RCLike.inner_apply, ← Complex.inv_eq_conj (norm_realCayley x),
    zpow_natCast_sub_natCast₀ hne, div_eq_mul_inv, mul_comm]

/-- Every finite Cayley--Toeplitz section is literally a Hilbert-space Gram matrix. -/
theorem circleToeplitzGram_eq_gram_cayleyConjugateMonomialLp
    (mu : Measure ℝ) [IsFiniteMeasure mu] (N : ℕ) :
    circleToeplitzGram N (cayleyMomentZ mu) =
      Matrix.gram ℂ (fun i : Fin (N + 1) => cayleyConjugateMonomialLp mu i) := by
  ext i j
  exact (cayleyConjugateMonomialLp_inner mu i j).symm

/-- A continuous function that vanishes almost everywhere vanishes on the measure support. -/
theorem continuous_eq_zero_on_support_of_ae_eq_zero
    (mu : Measure ℝ) (f : ℝ → ℂ) (hfcont : Continuous f)
    (hfzero : f =ᵐ[mu] 0) : ∀ x ∈ mu.support, f x = 0 := by
  intro x hx
  by_contra hfx
  have hopen : IsOpen {y : ℝ | f y ≠ 0} :=
    (isClosed_eq hfcont continuous_const).isOpen_compl
  have hnhds : {y : ℝ | f y ≠ 0} ∈ 𝓝 x :=
    hopen.mem_nhds hfx
  have hpos : 0 < mu {y : ℝ | f y ≠ 0} :=
    (Measure.mem_support_iff_forall (μ := mu) x).mp hx _ hnhds
  have hnull : mu {y : ℝ | f y ≠ 0} = 0 := by
    change mu ({y : ℝ | f y = 0}ᶜ) = 0
    exact mem_ae_iff.mp hfzero
  exact hpos.ne' hnull

/-- Infinite support makes every finite family of conjugate Cayley monomials linearly independent
in `L²(μ)`. -/
theorem linearIndependent_cayleyConjugateMonomialLp_of_infiniteSupport
    (mu : Measure ℝ) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    LinearIndependent ℂ
      (fun i : Fin (N + 1) => cayleyConjugateMonomialLp mu i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let p : Polynomial ℂ :=
    ∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  let f : ℝ → ℂ := fun x => p.eval (star (realCayley x))
  have hfcont : Continuous f := by
    exact p.continuous.comp (continuous_star.comp continuous_realCayley)
  have hsumcoe :
      ⇑(∑ i : Fin (N + 1), c i • cayleyConjugateMonomialLp mu i) =ᵐ[mu] f := by
    classical
    dsimp only [f, p]
    simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    induction (Finset.univ : Finset (Fin (N + 1))) using Finset.induction_on with
    | empty => simpa using! (Lp.coeFn_zero ℂ 2 mu)
    | @insert a S ha ih =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add
            (c a • cayleyConjugateMonomialLp mu a)
            (∑ i ∈ S, c i • cayleyConjugateMonomialLp mu i),
          Lp.coeFn_smul (c a) (cayleyConjugateMonomialLp mu a),
          cayleyConjugateMonomialLp_coeFn_ae mu a, ih] with x hadd hsmul hmono htail
        rw [hadd]
        change ⇑(c a • cayleyConjugateMonomialLp mu a) x +
          ⇑(∑ i ∈ S, c i • cayleyConjugateMonomialLp mu i) x = _
        rw [hsmul, Pi.smul_apply, hmono, htail]
        simp [Finset.sum_insert ha]
  have hfzero : f =ᵐ[mu] 0 := by
    exact hsumcoe.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc)
  have hsuppzero : ∀ x ∈ mu.support, f x = 0 :=
    continuous_eq_zero_on_support_of_ae_eq_zero mu f hfcont hfzero
  let S : Set ℂ := (fun x : ℝ => star (realCayley x)) '' mu.support
  have hSinfinite : S.Infinite := by
    apply hmu.image
    exact (star_injective.comp injective_realCayley).injOn
  have hSroot : S ⊆ {z : ℂ | p.IsRoot z} := by
    rintro z ⟨x, hx, rfl⟩
    exact hsuppzero x hx
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p (hSinfinite.mono hSroot)
  intro i
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff (i : ℕ)) hpzero
  simp [p] at hcoeff
  have hi : (∑ x : Fin (N + 1), if (i : ℕ) = (x : ℕ) then c x else 0) = c i := by
    classical
    calc
      (∑ x : Fin (N + 1), if (i : ℕ) = (x : ℕ) then c x else 0) =
          (if (i : ℕ) = (i : ℕ) then c i else 0) := by
        apply Finset.sum_eq_single i
        · intro b hb hbi
          have hnat : (i : ℕ) ≠ (b : ℕ) := fun h => hbi (Fin.ext h.symm)
          simp [hnat]
        · simp
      _ = c i := by simp
  rw [hi] at hcoeff
  exact hcoeff

/-- **Strict finite-frame positivity from support alone.** Every finite Cayley--Toeplitz Gram
section of a finite real measure with infinite topological support is positive definite. -/
theorem circleToeplitzGram_posDef_of_infiniteSupport
    (mu : Measure ℝ) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    (circleToeplitzGram N (cayleyMomentZ mu)).PosDef := by
  rw [circleToeplitzGram_eq_gram_cayleyConjugateMonomialLp]
  exact Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_cayleyConjugateMonomialLp_of_infiniteSupport mu hmu N)

end
end GaloisForLFunctions.HTGeometry
