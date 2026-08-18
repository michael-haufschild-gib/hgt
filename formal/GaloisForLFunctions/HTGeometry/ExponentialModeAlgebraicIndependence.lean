/-
# Algebraic independence of exponential modes and of the jets of the mixed carrier

Algebraic independence of a family is linear independence of its monomials
(`BigradedCorank.algebraicIndependent_iff_linearIndependent_monomialValue`), and every monomial in
a family of derivation eigenvectors is itself an eigenvector, with eigenvalue the weighted sum of
the exponents.  Rigidity of the base — no nonzero element has a nonzero constant logarithmic
derivative — therefore upgrades linear independence of the modes to algebraic independence, as soon
as distinct exponent vectors carry distinct weights.  Over `C(s)` that separation is exactly
`Q`-linear independence of the frequencies.

The first `r` jets of `q + ∑_i E_i` are obtained from the modes by an affine substitution whose
linear part is the Vandermonde matrix of the frequencies, so they inherit algebraic independence;
the `r`-th monic constant-coefficient operator returns the rational shadow.  Together this is the
card's exact algebraic-differential order `r`.
-/
import GaloisForLFunctions.HTGeometry.ExponentialRationalLeadingDegree
import GaloisForLFunctions.HTGeometry.BigradedCorankLattice
import GaloisForLFunctions.HTGeometry.MvPolynomialLinearSubstitution

noncomputable section

open scoped Differential
open scoped Matrix

namespace GaloisForLFunctions.DerivEigen

open GaloisForLFunctions GaloisForLFunctions.HTGeometry GaloisForLFunctions.DerivEigen
open GaloisForLFunctions.HTGeometry.BigradedCorank

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

omit [Differential F] [DifferentialAlgebra F M] in
/-- A power of a derivation eigenvector is an eigenvector. -/
theorem deriv_pow_eigen {x : M} {μ : F} (h : x′ = algebraMap F M μ * x) (n : ℕ) :
    (x ^ n)′ = algebraMap F M ((n : F) * μ) * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (x ^ n * x)′ = x ^ n • x′ + x • (x ^ n)′ := Derivation.leibniz _ _ _
      rw [pow_succ, hstep, ih, h]
      simp only [smul_eq_mul]
      push_cast
      ring

omit [Differential F] [DifferentialAlgebra F M] in
/-- A finite product of eigenvectors is an eigenvector with the summed eigenvalue. -/
theorem deriv_prod_eigen {ι : Type*} (s : Finset ι) (y : ι → M) (ν : ι → F)
    (h : ∀ i ∈ s, (y i)′ = algebraMap F M (ν i) * y i) :
    (∏ i ∈ s, y i)′ = algebraMap F M (∑ i ∈ s, ν i) * ∏ i ∈ s, y i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hmem : ∀ i ∈ s, (y i)′ = algebraMap F M (ν i) * y i :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hprev := ih hmem
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hstep : (y a * ∏ i ∈ s, y i)′
          = y a • (∏ i ∈ s, y i)′ + (∏ i ∈ s, y i) • (y a)′ := Derivation.leibniz _ _ _
      rw [hstep, hprev, h a (Finset.mem_insert_self a s)]
      simp only [smul_eq_mul, map_add]
      ring

/-- The eigenvalue of the monomial attached to an exponent vector. -/
def eigenWeight {ι : Type*} (lam : ι → F) (d : ι →₀ ℕ) : F := ∑ i ∈ d.support, (d i : F) * lam i

theorem deriv_monomialValue {ι : Type*} (lam : ι → F) (E : ι → M)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i) (d : ι →₀ ℕ) :
    (monomialValue E d)′ = algebraMap F M (eigenWeight lam d) * monomialValue E d := by
  rw [monomialValue, eigenWeight]
  exact deriv_prod_eigen _ _ _ (fun i _ => deriv_pow_eigen (heig i) (d i))

omit [Differential M] in
theorem monomialValue_ne_zero {ι : Type*} (E : ι → M) (hE : ∀ i, E i ≠ 0) (d : ι →₀ ℕ) :
    monomialValue E d ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hE i))

/-- **Eigenvectors with rigid weight differences are algebraically independent.**  Algebraic
independence is linear independence of the monomials, and every monomial is again an eigenvector,
with eigenvalue the weighted sum of the exponents. -/
theorem algebraicIndependent_of_deriv_eigen {ι : Type*}
    (lam : ι → F) (E : ι → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hrigid : ∀ d e : ι →₀ ℕ, d ≠ e → ∀ c : F, c ≠ 0 →
      c′ ≠ (eigenWeight lam e - eigenWeight lam d) * c) :
    AlgebraicIndependent F E := by
  classical
  rw [algebraicIndependent_iff_linearIndependent_monomialValue]
  exact linearIndependent_of_deriv_eigen (eigenWeight lam) (monomialValue E)
    (monomialValue_ne_zero E hE) (fun d => deriv_monomialValue lam E heig d) hrigid


open GaloisForLFunctions.LinDiffOp
open Polynomial

theorem differentialJet_sum {ι : Type*} (s : Finset ι) (x : ι → M) (k : ℕ) :
    differentialJet k (∑ i ∈ s, x i) = ∑ i ∈ s, differentialJet k (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact differentialJet_zero_apply k
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, differentialJet_add_apply, ih, Finset.sum_insert ha]

theorem differentialJet_sum_eigen {r : ℕ} (lam : Fin r → F) (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i) (k : ℕ) :
    differentialJet k (∑ i, E i) = ∑ i, algebraMap F M (lam i ^ k) * E i := by
  rw [differentialJet_sum]
  exact Finset.sum_congr rfl (fun i _ => differentialJet_eigen (hlamc i) (heig i) k)

/-- **The `r`-th jet is an affine combination of the lower ones.**  The monic constant-coefficient
annihilator sends the mixed carrier to the rational shadow. -/
theorem linOp_factorPoly_carrier {r : ℕ} (lam : Fin r → F) (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i) (q : F) :
    linOp (factorPoly (List.ofFn lam)).coeff r (algebraMap F M q + ∑ i, E i)
      = algebraMap F M (opList (List.ofFn lam) q) := by
  classical
  set l : List F := List.ofFn lam with hl
  have hlength : l.length = r := by rw [hl, List.length_ofFn]
  have hlconst : ∀ mu ∈ l, mu′ = 0 := by
    intro mu hmu
    rw [hl, List.mem_ofFn] at hmu
    obtain ⟨i, rfl⟩ := hmu
    exact hlamc i
  have hdegFac : (factorPoly l).natDegree ≤ r := by rw [factorPoly_natDegree, hlength]
  have hbase : linOpBase (factorPoly l).coeff r q = opList l q := by
    rw [← hlength]; exact linOpBase_factorPoly hlconst q
  have hmodes : ∀ i, symbolEval (factorPoly l).coeff r (lam i) = 0 := by
    intro i
    rw [symbolEval_coeff_eq_eval hdegFac]
    refine factorPoly_eval_eq_zero ?_
    rw [hl, List.mem_ofFn]
    exact ⟨i, rfl⟩
  rw [linOp_add, linOp_algebraMap, hbase, linOp_sum]
  have hzero : (∑ i, linOp (factorPoly l).coeff r (E i)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [linOp_eigen _ _ (hlamc i) (heig i), hmodes i, map_zero, zero_mul]
  rw [hzero, add_zero]

end GaloisForLFunctions.DerivEigen

namespace GaloisForLFunctions.DerivEigen

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Translation of the variables of a polynomial ring. -/
noncomputable def transSubst {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval fun k => MvPolynomial.X k + MvPolynomial.C (v k)

@[simp] theorem transSubst_X {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (k : Fin n) :
    transSubst v (MvPolynomial.X k) = MvPolynomial.X k + MvPolynomial.C (v k) := by
  rw [transSubst, MvPolynomial.aeval_X]

/-- **A translation substitution is injective.** -/
theorem transSubst_injective {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    Function.Injective (transSubst v) := by
  have hcomp : (transSubst (-v)).comp (transSubst v)
      = AlgHom.id R (MvPolynomial (Fin n) R) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    rw [AlgHom.comp_apply, transSubst_X, map_add, transSubst_X, AlgHom.id_apply]
    have hC : transSubst (-v) (MvPolynomial.C (v k)) = MvPolynomial.C (v k) := by
      rw [transSubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    rw [hC]
    simp [Pi.neg_apply]
  intro p q hpq
  have h := congrArg (transSubst (-v)) hpq
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp, AlgHom.id_apply, AlgHom.id_apply] at h
  exact h

end GaloisForLFunctions.DerivEigen

namespace GaloisForLFunctions.DerivEigen

open GaloisForLFunctions GaloisForLFunctions.HTGeometry GaloisForLFunctions.DerivEigen
open GaloisForLFunctions.LinDiffOp

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

/-- **Vandermonde transfer.**  If the modes are algebraically independent then so are the first
`r` jets of the mixed carrier. -/
theorem algebraicIndependent_jets {r : ℕ} (lam : Fin r → F) (hlaminj : Function.Injective lam)
    (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hAI : AlgebraicIndependent F E) (q : F) :
    AlgebraicIndependent F
      (fun k : Fin r => differentialJet (k : ℕ) (algebraMap F M q + ∑ i, E i)) := by
  classical
  set A : Matrix (Fin r) (Fin r) F := (Matrix.vandermonde lam)ᵀ with hA
  set v : Fin r → F := fun k => differentialJet (k : ℕ) q with hv
  have hAapp : ∀ k i, A k i = lam i ^ (k : ℕ) := by
    intro k i
    rw [hA, Matrix.transpose_apply, Matrix.vandermonde_apply]
  have hdet : IsUnit A.det := by
    rw [hA, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hlaminj)
  set Θ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial (Fin r) F :=
    (matrixSubst A).comp (transSubst v) with hΘ
  have hΘinj : Function.Injective Θ :=
    (matrixSubst_injective hdet).comp (transSubst_injective v)
  have hx : ∀ k : Fin r, differentialJet (k : ℕ) (algebraMap F M q + ∑ i, E i)
      = algebraMap F M (v k) + ∑ i, algebraMap F M (A k i) * E i := by
    intro k
    rw [differentialJet_add_apply, differentialJet_algebraMap_of_differentialAlgebra,
      differentialJet_sum_eigen lam hlamc E heig]
    simp only [hAapp, hv]
  have hcomp : (MvPolynomial.aeval (fun k : Fin r =>
        differentialJet (k : ℕ) (algebraMap F M q + ∑ i, E i)) :
      MvPolynomial (Fin r) F →ₐ[F] M) = (MvPolynomial.aeval E).comp Θ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, hΘ, AlgHom.comp_apply, transSubst_X,
      map_add, matrixSubst_X, matrixSubst_C, map_add, map_sum, MvPolynomial.aeval_C, hx k,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [algebraicIndependent_iff]
  intro p hp
  have h1 : MvPolynomial.aeval E (Θ p) = 0 := by
    rw [← AlgHom.comp_apply, ← hcomp]
    exact hp
  exact hΘinj (by rw [algebraicIndependent_iff.mp hAI (Θ p) h1, map_zero])

end GaloisForLFunctions.DerivEigen

namespace GaloisForLFunctions.DerivEigen

open GaloisForLFunctions GaloisForLFunctions.HTGeometry GaloisForLFunctions.DerivEigen
open GaloisForLFunctions.LinDiffOp GaloisForLFunctions.RationalShadow

attribute [local instance] GaloisForLFunctions.ratFuncCoordinateDifferential

variable {M : Type*} [Field M] [Algebra (RatFunc ℂ) M] [Differential M]
  [DifferentialAlgebra (RatFunc ℂ) M]

/-- The complex weight of an exponent vector. -/
def weightC {r : ℕ} (lam : Fin r → ℂ) (d : Fin r →₀ ℕ) : ℂ := ∑ i ∈ d.support, (d i : ℂ) * lam i

theorem weightC_eq_univ_sum {r : ℕ} (lam : Fin r → ℂ) (d : Fin r →₀ ℕ) :
    weightC lam d = ∑ i, (d i : ℂ) * lam i := by
  rw [weightC]
  refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)
  rw [Finsupp.notMem_support_iff.mp hi]
  simp

theorem eigenWeight_algebraMap {r : ℕ} (lam : Fin r → ℂ) (d : Fin r →₀ ℕ) :
    eigenWeight (fun i => algebraMap ℂ (RatFunc ℂ) (lam i)) d
      = algebraMap ℂ (RatFunc ℂ) (weightC lam d) := by
  rw [eigenWeight, weightC, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_natCast]

theorem weightC_sub_ne_zero {r : ℕ} (lam : Fin r → ℂ)
    (hind : ∀ m : Fin r → ℤ, (∑ i, (m i : ℂ) * lam i) = 0 → ∀ i, m i = 0)
    {d e : Fin r →₀ ℕ} (hde : d ≠ e) : weightC lam e - weightC lam d ≠ 0 := by
  intro hzero
  set m : Fin r → ℤ := fun i => (e i : ℤ) - (d i : ℤ) with hm
  have hsum : (∑ i, (m i : ℂ) * lam i) = 0 := by
    rw [← hzero, weightC_eq_univ_sum, weightC_eq_univ_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm]
    push_cast
    ring
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hde
  have hmi : m i = 0 := hind m hsum i
  simp only [hm] at hmi
  omega

/-- **Lemma 5, first half.**  Exponential modes with `Z`-independent frequencies are algebraically
independent over `C(s)`. -/
theorem algebraicIndependent_expEigen_over_ratFunc {r : ℕ} (lam : Fin r → ℂ)
    (hind : ∀ m : Fin r → ℤ, (∑ i, (m i : ℂ) * lam i) = 0 → ∀ i, m i = 0)
    (E : Fin r → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′
      = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i) :
    AlgebraicIndependent (RatFunc ℂ) E := by
  refine algebraicIndependent_of_deriv_eigen (fun i => algebraMap ℂ (RatFunc ℂ) (lam i)) E hE
    heig ?_
  intro d e hde c hc
  rw [eigenWeight_algebraMap, eigenWeight_algebraMap, ← map_sub, ratFuncDeriv_eq]
  exact ratFuncCoordinateDerivation_ne_smul hc (weightC_sub_ne_zero lam hind hde)

theorem int_independent_of_rat_linearIndependent {r : ℕ} {lam : Fin r → ℂ}
    (hQ : LinearIndependent ℚ lam) :
    ∀ m : Fin r → ℤ, (∑ i, (m i : ℂ) * lam i) = 0 → ∀ i, m i = 0 := by
  intro m hsum i
  have hg : (∑ i, ((m i : ℚ)) • lam i) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Rat.smul_def]
    push_cast
    ring
  have := (Fintype.linearIndependent_iff.mp hQ) (fun j => ((m j : ℚ))) hg i
  exact_mod_cast this

/-- **Lemma 5.**  With `Q`-linearly independent frequencies the first `r` jets of the mixed
carrier are algebraically independent over `C(s)`, while the `r`-th order monic
constant-coefficient operator sends the carrier into `C(s)`: the exact algebraic-differential
order is `r`. -/
theorem exact_algebraic_differential_order {r : ℕ} (lam : Fin r → ℂ)
    (hQ : LinearIndependent ℚ lam)
    (E : Fin r → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′
      = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i)
    (q : RatFunc ℂ) :
    AlgebraicIndependent (RatFunc ℂ)
        (fun k : Fin r => differentialJet (k : ℕ) (algebraMap (RatFunc ℂ) M q + ∑ i, E i))
      ∧ linOp (factorPoly (List.ofFn fun i => algebraMap ℂ (RatFunc ℂ) (lam i))).coeff r
          (algebraMap (RatFunc ℂ) M q + ∑ i, E i)
        = algebraMap (RatFunc ℂ) M (shiftedDerivProd (List.ofFn lam) q) := by
  classical
  set lamF : Fin r → RatFunc ℂ := fun i => algebraMap ℂ (RatFunc ℂ) (lam i) with hlamFdef
  have hKinj : Function.Injective (algebraMap ℂ (RatFunc ℂ)) :=
    (algebraMap ℂ (RatFunc ℂ)).injective
  have hlamFinj : Function.Injective lamF := hKinj.comp hQ.injective
  have hlamFc : ∀ i, (lamF i)′ = 0 := fun i => deriv_algebraMap_C (lam i)
  have hAI : AlgebraicIndependent (RatFunc ℂ) E :=
    algebraicIndependent_expEigen_over_ratFunc lam
      (int_independent_of_rat_linearIndependent hQ) E hE heig
  refine ⟨algebraicIndependent_jets lamF hlamFinj hlamFc E heig hAI q, ?_⟩
  have hofn : List.ofFn lamF = (List.ofFn lam).map (algebraMap ℂ (RatFunc ℂ)) := by
    rw [List.map_ofFn]; rfl
  rw [linOp_factorPoly_carrier lamF hlamFc E heig q, hofn, opList_map_algebraMap]

end GaloisForLFunctions.DerivEigen
