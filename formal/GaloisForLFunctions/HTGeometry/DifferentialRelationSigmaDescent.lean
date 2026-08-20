import GaloisForLFunctions.HTGeometry.SigmaIdealConstantCoefficients
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver

/-!
# Differential relations descend to the constants of the shift

Shifting the coefficients of a differential polynomial is a ring automorphism which evaluation
intertwines with a shift fixing the point, so the relation ideal of a `σ`-invariant point is a
`σ`-ideal.  Over a field the minimal-support argument then replaces a nonzero relation by one whose
coefficients are `σ`-invariant.

This is what makes the constants of a Picard--Vessiot situation carry the differential relations of
the comparison matrix: a relation over the base descends to a relation over the constants, which the
differential points can then be evaluated at.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {ι K R : Type*} [Field K] [CommRing R] [Algebra K R] [Differential K] [Differential R]

/-- The coefficientwise shift of differential polynomials. -/
def differentialPolynomialSigma (σK : K ≃+* K) :
    DifferentialPolynomial ι K ≃+* DifferentialPolynomial ι K :=
  MvPolynomial.mapEquiv _ σK

omit [Differential K] in
@[simp] theorem differentialPolynomialSigma_monomial (σK : K ≃+* K) (u : (ι × ℕ) →₀ ℕ) (a : K) :
    differentialPolynomialSigma (ι := ι) σK (MvPolynomial.monomial u a)
      = MvPolynomial.monomial u (σK a) := by
  simp [differentialPolynomialSigma]

omit [Differential K] in
@[simp] theorem differentialPolynomialSigma_X (σK : K ≃+* K) (s : ι × ℕ) :
    differentialPolynomialSigma (ι := ι) (K := K) σK (MvPolynomial.X s) = MvPolynomial.X s := by
  simp [differentialPolynomialSigma]

omit [Differential K] in
@[simp] theorem differentialPolynomialSigma_C (σK : K ≃+* K) (a : K) :
    differentialPolynomialSigma (ι := ι) σK (MvPolynomial.C a) = MvPolynomial.C (σK a) := by
  simp [differentialPolynomialSigma]

omit [Differential K] in
/-- Evaluation intertwines the coefficientwise shift with a shift fixing the point. -/
theorem differentialPolynomialEvalOver_sigma (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσδ : ∀ z : R, σR (Differential.deriv z) = Differential.deriv (σR z))
    (x : ι → R) (hx : ∀ i, σR (x i) = x i) (P : DifferentialPolynomial ι K) :
    differentialPolynomialEvalOver (K := K) x (differentialPolynomialSigma σK P)
      = σR (differentialPolynomialEvalOver (K := K) x P) := by
  have hjet : ∀ (n : ℕ) (i : ι), σR (differentialJet n (x i)) = differentialJet n (x i) := by
    intro n
    induction n with
    | zero => intro i; rw [differentialJet_zero, hx]
    | succ n ih =>
        intro i
        rw [differentialJet_succ, hσδ, ih]
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [differentialPolynomialSigma_C, differentialPolynomialEvalOver_C,
        differentialPolynomialEvalOver_C, hcompat]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P s hP =>
      rw [map_mul, differentialPolynomialSigma_X, map_mul, hP, map_mul, map_mul,
        differentialPolynomialEvalOver_X, hjet]

theorem isSigmaSimple_of_field {F : Type*} [Field F] (σ : F ≃+* F) : IsSigmaSimple σ := by
  intro I _
  exact I.eq_bot_or_top

omit [Differential K] in
/-- **`σ`-descent of differential relations.**  A differential relation over the base satisfied by a
`σ`-invariant point can be replaced by one whose coefficients are `σ`-invariant. -/
theorem exists_sigmaFixed_relation [DecidableEq ι] (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσδ : ∀ z : R, σR (Differential.deriv z) = Differential.deriv (σR z))
    (x : ι → R) (hx : ∀ i, σR (x i) = x i)
    {P : DifferentialPolynomial ι K} (hP : P ≠ 0)
    (hPx : differentialPolynomialEvalOver (K := K) x P = 0) :
    ∃ Q : DifferentialPolynomial ι K, Q ≠ 0 ∧
      (∀ u : (ι × ℕ) →₀ ℕ, σK (MvPolynomial.coeff u Q) = MvPolynomial.coeff u Q) ∧
      differentialPolynomialEvalOver (K := K) x Q = 0 := by
  classical
  have hbσ : ∀ u : (ι × ℕ) →₀ ℕ,
      differentialPolynomialSigma (ι := ι) (K := K) σK (MvPolynomial.monomial u (1 : K))
        = MvPolynomial.monomial u (1 : K) := by
    intro u
    rw [differentialPolynomialSigma_monomial, map_one]
  have hmul : ∀ (a : K) (u : (ι × ℕ) →₀ ℕ),
      algebraMap K (DifferentialPolynomial ι K) a * MvPolynomial.monomial u (1 : K)
        = MvPolynomial.monomial u a := by
    intro a u
    show MvPolynomial.C a * MvPolynomial.monomial u (1 : K) = _
    rw [MvPolynomial.C_mul_monomial, mul_one]
  have hli : BasisIndependentOver K (fun u : (ι × ℕ) →₀ ℕ =>
      (MvPolynomial.monomial u (1 : K) : DifferentialPolynomial ι K)) := by
    intro t ρ hsum j hj
    have hcoeff := congrArg (MvPolynomial.coeff j) hsum
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
    rw [Finset.sum_eq_single j] at hcoeff
    · rw [hmul, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
      exact hcoeff
    · intro u _ hu
      rw [hmul, MvPolynomial.coeff_monomial, if_neg hu]
    · intro hcon
      exact absurd hj hcon
  have hI : IsSigmaIdeal (differentialPolynomialSigma (ι := ι) (K := K) σK)
      (differentialRelationIdealOver (K := K) x) := by
    intro z hz
    rw [mem_differentialRelationIdealOver_iff] at hz ⊢
    rw [differentialPolynomialEvalOver_sigma σK σR hcompat hσδ x hx, hz, map_zero]
  have hmem : (∑ u ∈ P.support, algebraMap K (DifferentialPolynomial ι K)
        (MvPolynomial.coeff u P) * MvPolynomial.monomial u (1 : K))
      ∈ differentialRelationIdealOver (K := K) x := by
    rw [Finset.sum_congr rfl fun u _ => hmul (MvPolynomial.coeff u P) u,
      ← MvPolynomial.as_sum P, mem_differentialRelationIdealOver_iff]
    exact hPx
  have hne : ∃ u ∈ P.support, MvPolynomial.coeff u P ≠ 0 := by
    obtain ⟨u, hu⟩ : ∃ u, MvPolynomial.coeff u P ≠ 0 := by
      by_contra hcon
      refine hP (MvPolynomial.ext _ _ fun u => ?_)
      rw [MvPolynomial.coeff_zero]
      by_contra hne
      exact hcon ⟨u, hne⟩
    exact ⟨u, MvPolynomial.mem_support_iff.mpr hu, hu⟩
  obtain ⟨t, d, hconst, hdI, hdne⟩ :=
    exists_nonzero_constant_coeff_mem_sigmaIdeal (R := K) (A := DifferentialPolynomial ι K) σK
      (differentialPolynomialSigma (ι := ι) (K := K) σK)
      (fun a => by
        show differentialPolynomialSigma (ι := ι) (K := K) σK (MvPolynomial.C a)
          = MvPolynomial.C (σK a)
        rw [differentialPolynomialSigma_C])
      (isSigmaSimple_of_field σK)
      (fun u : (ι × ℕ) →₀ ℕ => (MvPolynomial.monomial u (1 : K) : DifferentialPolynomial ι K))
      hbσ hli (differentialRelationIdealOver (K := K) x) hI P.support
      (fun u => MvPolynomial.coeff u P) hne hmem
  refine ⟨∑ u ∈ t, algebraMap K (DifferentialPolynomial ι K) (d u)
    * MvPolynomial.monomial u (1 : K), hdne, ?_, ?_⟩
  · intro u
    rw [Finset.sum_congr rfl fun v _ => hmul (d v) v, MvPolynomial.coeff_sum]
    by_cases hu : u ∈ t
    · rw [Finset.sum_eq_single u]
      · rw [MvPolynomial.coeff_monomial, if_pos rfl]
        exact hconst u hu
      · intro v _ hv
        rw [MvPolynomial.coeff_monomial, if_neg hv]
      · intro hcon
        exact absurd hu hcon
    · have hzero : ∀ v ∈ t, MvPolynomial.coeff u (MvPolynomial.monomial v (d v)) = 0 := by
        intro v hv
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro hcon
        exact hu (hcon ▸ hv)
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, map_zero]
  · rw [← mem_differentialRelationIdealOver_iff]
    exact hdI

end

end GaloisForLFunctions.HTGeometry
