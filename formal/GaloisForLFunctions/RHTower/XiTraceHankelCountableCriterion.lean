import GaloisForLFunctions.RHTower.XiTraceHankelCriterion
import Mathlib.Algebra.Polynomial.OfFn

/-!
# A countable integer-polynomial criterion for RH

The real-polynomial trace-Hankel criterion can be reduced exactly to integer polynomials.  At each
fixed degree the Xi trace-Hankel value is a continuous quadratic form in finitely many real
coefficients.  Rational coefficient vectors are dense, and a common positive denominator turns a
rational polynomial into an integer polynomial without changing the sign of the quadratic value.

Thus the RH-equivalent test family is countable.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Xi trace-Hankel form on a length-`n` coefficient vector is the finite quadratic moment
form with matrix entries `xiCentralReciprocalMoment (i + j)`. -/
theorem xiCentralTraceHankel_ofFn (n : ℕ) (a : Fin n → ℝ) :
    xiCentralTraceHankel (Polynomial.ofFn n a) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((a i * a j : ℝ) : ℂ) *
          xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ)) := by
  let D := MeromorphicOn.divisor xi Set.univ
  let lam : ↥D.support → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  let momentTerm : ℕ → ↥D.support → ℂ := fun k ρ =>
    ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ ^ (k + 1)
  have hmoment (k : ℕ) : Summable (momentTerm k) := by
    simpa only [D, lam, momentTerm] using xi_central_reciprocal_moment_summable k
  have heval (ρ : ↥D.support) :
      evalRealPolynomial (Polynomial.ofFn n a) (lam ρ) =
        ∑ i : Fin n, ((a i : ℝ) : ℂ) * lam ρ ^ (i : ℕ) := by
    rw [evalRealPolynomial, Polynomial.ofFn_eq_sum_monomial]
    simp
  rw [xiCentralTraceHankel]
  calc
    (∑' ρ, xiCentralTraceHankelTerm (Polynomial.ofFn n a) ρ) =
        ∑' ρ : ↥D.support, ∑ i : Fin n, ∑ j : Fin n,
          ((a i * a j : ℝ) : ℂ) *
            momentTerm ((i : ℕ) + (j : ℕ)) ρ := by
      apply tsum_congr
      intro ρ
      rw [xiCentralTraceHankelTerm]
      change ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ *
          evalRealPolynomial (Polynomial.ofFn n a) (lam ρ) ^ (2 : ℕ) = _
      rw [heval, pow_two]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [momentTerm]
      rw [pow_add]
      push_cast
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((a i * a j : ℝ) : ℂ) * ∑' ρ : ↥D.support,
          momentTerm ((i : ℕ) + (j : ℕ)) ρ := by
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Summable.tsum_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [tsum_mul_left]
        · intro j _
          exact (hmoment ((i : ℕ) + (j : ℕ))).mul_left
            (((a i * a j : ℝ) : ℂ))
      · intro i _
        exact summable_sum (fun j _ =>
          (hmoment ((i : ℕ) + (j : ℕ))).mul_left (((a i * a j : ℝ) : ℂ)))
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((a i * a j : ℝ) : ℂ) *
          xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [xiCentralReciprocalMoment, D, lam, momentTerm]

/-- The finite coefficient-vector realization of the real Xi trace-Hankel quadratic form. -/
def xiCentralTraceHankelVector (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  (xiCentralTraceHankel (Polynomial.ofFn n a)).re

/-- At every fixed degree, the Xi trace-Hankel value is continuous in the coefficients. -/
theorem continuous_xiCentralTraceHankelVector (n : ℕ) :
    Continuous (xiCentralTraceHankelVector n) := by
  rw [show xiCentralTraceHankelVector n = fun a : Fin n → ℝ =>
      (∑ i : Fin n, ∑ j : Fin n,
        ((a i * a j : ℝ) : ℂ) *
          xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ))).re by
    funext a
    rw [xiCentralTraceHankelVector, xiCentralTraceHankel_ofFn]]
  fun_prop

/-- Homogeneity of the finite coefficient-vector Xi trace-Hankel form. -/
theorem xiCentralTraceHankelVector_smul (n : ℕ) (c : ℝ) (a : Fin n → ℝ) :
    xiCentralTraceHankelVector n (c • a) =
      c ^ (2 : ℕ) * xiCentralTraceHankelVector n a := by
  simp only [xiCentralTraceHankelVector]
  rw [xiCentralTraceHankel_ofFn, xiCentralTraceHankel_ofFn]
  have hcomplex :
      (∑ i : Fin n, ∑ j : Fin n,
        (((c • a) i * (c • a) j : ℝ) : ℂ) *
          xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ))) =
      ((c ^ (2 : ℕ) : ℝ) : ℂ) *
        ∑ i : Fin n, ∑ j : Fin n,
          ((a i * a j : ℝ) : ℂ) *
            xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hcomplex]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem denseRange_ratCast_fin (n : ℕ) :
    DenseRange (fun a : Fin n → ℚ => fun i => (a i : ℝ)) := by
  simpa [Pi.map_apply] using!
    (DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast))

/-- The countable integer-polynomial trace-Hankel positivity criterion. -/
def XiCentralTraceHankelIntNonnegative : Prop :=
  ∀ p : Polynomial ℤ,
    0 ≤ (xiCentralTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Integer-polynomial positivity already implies positivity for every real polynomial. -/
theorem xiCentralTraceHankelNonnegative_of_int
    (hint : XiCentralTraceHankelIntNonnegative) :
    XiCentralTraceHankelNonnegative := by
  intro p
  let n := p.natDegree + 1
  let a : Fin n → ℝ := Polynomial.toFn n p
  have hp : Polynomial.ofFn n a = p := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hclosed : IsClosed {x : Fin n → ℝ | 0 ≤ xiCentralTraceHankelVector n x} := by
    exact isClosed_Ici.preimage (continuous_xiCentralTraceHankelVector n)
  have hrat : ∀ q : Fin n → ℚ,
      0 ≤ xiCentralTraceHankelVector n (fun i => (q i : ℝ)) := by
    intro q
    obtain ⟨D, hDpos, z, hz⟩ := RHTower.exists_nat_pos_int_scale_rat_vector q
    let pz : Polynomial ℤ := Polynomial.ofFn n z
    have hpzmap : pz.map (Int.castRingHom ℝ) =
        Polynomial.ofFn n (fun i => (z i : ℝ)) := by
      ext k
      by_cases hk : k < n
      · simp [pz, hk]
      · have hnk : n ≤ k := Nat.le_of_not_gt hk
        simp [pz, hnk]
    have hzreal : (fun i => (z i : ℝ)) = fun i => (D : ℝ) * (q i : ℝ) := by
      funext i
      exact_mod_cast hz i
    have hscaled := hint pz
    rw [hpzmap] at hscaled
    change 0 ≤ xiCentralTraceHankelVector n (fun i => (z i : ℝ)) at hscaled
    rw [hzreal, show (fun i => (D : ℝ) * (q i : ℝ)) =
        (D : ℝ) • (fun i => (q i : ℝ)) by rfl,
      xiCentralTraceHankelVector_smul] at hscaled
    have hDsq : 0 < (D : ℝ) ^ (2 : ℕ) := sq_pos_of_pos (by exact_mod_cast hDpos)
    exact nonneg_of_mul_nonneg_right hscaled hDsq
  have hall : ∀ x : Fin n → ℝ, 0 ≤ xiCentralTraceHankelVector n x := by
    intro x
    exact (denseRange_ratCast_fin n).induction_on x hclosed hrat
  have ha := hall a
  rw [xiCentralTraceHankelVector, hp] at ha
  exact ha

/-- **Countable trace-Hankel criterion for RH.** It is enough, and necessary, to test the Xi
quadratic value on the countable family `ℤ[X]`. -/
theorem xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis :
    XiCentralTraceHankelIntNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro hint
    exact riemannHypothesis_of_xiCentralTraceHankelNonnegative
      (xiCentralTraceHankelNonnegative_of_int hint)
  · intro hRH p
    exact xiCentralTraceHankelNonnegative_of_riemannHypothesis hRH
      (p.map (Int.castRingHom ℝ))

/-- The unrestricted per-test nonnegative-limit formulation.  This deliberately records only the
scalar content of a proposed Gram approximation: no common carrier, coefficient-linearity, or
source construction is required. -/
def XiCentralTraceHankelIntNonnegativeLimit : Prop :=
  ∀ p : Polynomial ℤ,
    ∃ energy : ℕ → ℝ,
      (∀ j, 0 ≤ energy j) ∧
        Tendsto energy atTop
          (𝓝 (xiCentralTraceHankel (p.map (Int.castRingHom ℝ))).re)

/-- Arbitrary polynomial-dependent limits of nonnegative scalars contain exactly the same sign
content as integer-polynomial trace-Hankel nonnegativity.  Therefore a per-test Gram route gains
independent mathematical content only from extra source-side coherence imposed on its kernels. -/
theorem xiCentralTraceHankelIntNonnegativeLimit_iff_nonnegative :
    XiCentralTraceHankelIntNonnegativeLimit ↔ XiCentralTraceHankelIntNonnegative := by
  constructor
  · intro hlimit p
    obtain ⟨energy, henergy, hconv⟩ := hlimit p
    exact isClosed_Ici.mem_of_tendsto hconv
      (Filter.Eventually.of_forall henergy)
  · intro hnonneg p
    refine ⟨fun _ => (xiCentralTraceHankel
      (p.map (Int.castRingHom ℝ))).re, ?_, tendsto_const_nhds⟩
    intro j
    exact hnonneg p

/-- **Unrestricted per-test nonnegative-limit criterion for RH.**  This is an exact audit theorem,
not a source construction: the missing RH-bearing input is a canonical semilocal family whose
nonnegative energies converge without reading the Xi divisor or its sign. -/
theorem xiCentralTraceHankelIntNonnegativeLimit_iff_riemannHypothesis :
    XiCentralTraceHankelIntNonnegativeLimit ↔ RiemannHypothesis := by
  rw [xiCentralTraceHankelIntNonnegativeLimit_iff_nonnegative,
    xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis]

end

end RHTower
