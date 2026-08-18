/-
# Linear differential operators separate a rational part from exponential modes

A base-coefficient operator `A = ∑_j c_j D^j` acts on a derivation eigenvector through its symbol,
`A E = (∑_j c_j λ^j) E`, and on a base element through the corresponding operator inside the base.
So on a carrier `q + ∑_i E_i` with distinct nonzero constant eigenvalues, `A` decomposes into one
base term and one term per mode.

Independence of the modes together with the constant `1` — which holds whenever no nonzero
eigenvalue difference is a logarithmic derivative in the base — then forces each piece to vanish
separately: the base operator kills `q`, and the symbol vanishes at every eigenvalue.
-/
import GaloisForLFunctions.HTGeometry.DerivEigenIndependence

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions GaloisForLFunctions.HTGeometry GaloisForLFunctions.DerivEigen

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

/-- A base-coefficient linear differential operator of order at most `n`. -/
def linOp (c : ℕ → F) (n : ℕ) (x : M) : M :=
  ∑ j ∈ Finset.range (n + 1), algebraMap F M (c j) * differentialJet j x

/-- Its action inside the base field. -/
def linOpBase (c : ℕ → F) (n : ℕ) (q : F) : F :=
  ∑ j ∈ Finset.range (n + 1), c j * differentialJet j q

/-- The symbol of the operator, evaluated at a scalar. -/
def symbolEval (c : ℕ → F) (n : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range (n + 1), c j * x ^ j

omit [Differential F] [DifferentialAlgebra F M] in
theorem differentialJet_zero_apply (j : ℕ) : differentialJet j (0 : M) = 0 := by
  induction j with
  | zero => simp
  | succ j ihj => rw [differentialJet_succ, ihj, map_zero]

theorem deriv_pow_eq_zero {μ : F} (hμ : μ′ = 0) (j : ℕ) : ((μ ^ j))′ = 0 := by
  induction j with
  | zero => simp
  | succ k ihk =>
      rw [pow_succ, Derivation.leibniz, ihk, hμ]
      simp

omit [Differential F] [DifferentialAlgebra F M] in
theorem linOp_add (c : ℕ → F) (n : ℕ) (x y : M) :
    linOp c n (x + y) = linOp c n x + linOp c n y := by
  rw [linOp, linOp, linOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [differentialJet_add_apply]
  ring

omit [Differential F] [DifferentialAlgebra F M] in
theorem linOp_sum {ι : Type*} (c : ℕ → F) (n : ℕ) (s : Finset ι) (x : ι → M) :
    linOp c n (∑ i ∈ s, x i) = ∑ i ∈ s, linOp c n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, linOp]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [differentialJet_zero_apply, mul_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, linOp_add, ih, Finset.sum_insert hi]

/-- Iterated derivatives of an eigenvector are scalar multiples of it. -/
theorem differentialJet_eigen {x : M} {μ : F} (hμ : μ′ = 0)
    (h : x′ = algebraMap F M μ * x) (j : ℕ) :
    differentialJet j x = algebraMap F M (μ ^ j) * x := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [differentialJet_succ, ih, deriv_algebraMap_mul, h]
      rw [deriv_pow_eq_zero hμ j, map_zero, zero_mul, zero_add, pow_succ, map_mul]
      ring

/-- The operator acts on an eigenvector through its symbol. -/
theorem linOp_eigen (c : ℕ → F) (n : ℕ) {x : M} {μ : F} (hμ : μ′ = 0)
    (h : x′ = algebraMap F M μ * x) :
    linOp c n x = algebraMap F M (symbolEval c n μ) * x := by
  rw [linOp, symbolEval, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [differentialJet_eigen hμ h, map_mul]
  ring

/-- The operator acts on a base element through the base operator. -/
theorem linOp_algebraMap (c : ℕ → F) (n : ℕ) (q : F) :
    linOp c n (algebraMap F M q) = algebraMap F M (linOpBase c n q) := by
  rw [linOp, linOpBase, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [differentialJet_algebraMap_of_differentialAlgebra, map_mul]

end GaloisForLFunctions.LinDiffOp

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions GaloisForLFunctions.HTGeometry GaloisForLFunctions.DerivEigen

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

/-- **Separation of the rational part from the exponential modes.**  If a base-coefficient linear
differential operator annihilates a carrier `q + ∑ E i` whose modes are derivation eigenvectors
with distinct nonzero constant eigenvalues, then it annihilates the rational part and its symbol
vanishes at every eigenvalue. -/
theorem linOp_eq_zero_separation {ι : Type*} [DecidableEq ι] [Fintype ι]
    (lam : ι → F) (hlam : Function.Injective lam) (hlam0 : ∀ i, lam i ≠ 0)
    (hlamc : ∀ i, (lam i)′ = 0)
    (E : ι → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hconst : ∀ μ : F, μ′ = 0 → μ ≠ 0 → ∀ c : F, c ≠ 0 → c′ ≠ μ * c)
    (q : F) (c : ℕ → F) (n : ℕ)
    (h : linOp c n (algebraMap F M q + ∑ i, E i) = 0) :
    linOpBase c n q = 0 ∧ ∀ i, symbolEval c n (lam i) = 0 := by
  classical
  set lamO : Option ι → F := fun o => o.elim 0 lam with hlamO
  set EO : Option ι → M := fun o => o.elim 1 E with hEO
  have hEOne : ∀ o, EO o ≠ 0 := by
    rintro (_ | i)
    · exact one_ne_zero
    · exact hE i
  have heigO : ∀ o, (EO o)′ = algebraMap F M (lamO o) * EO o := by
    rintro (_ | i)
    · show (1 : M)′ = algebraMap F M 0 * 1
      rw [map_zero, zero_mul]
      simp
    · exact heig i
  have hlamOinj : Function.Injective lamO := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd hij.symm (hlam0 j)
    · exact absurd hij (hlam0 i)
    · exact congrArg some (hlam hij)
  have hrigidO : ∀ i j : Option ι, i ≠ j → ∀ d : F, d ≠ 0 → d′ ≠ (lamO j - lamO i) * d := by
    intro i j hij d hd
    have hlamOc : ∀ o : Option ι, (lamO o)′ = 0 := by
      rintro (_ | k)
      · show ((0 : F))′ = 0
        exact map_zero _
      · exact hlamc k
    refine hconst (lamO j - lamO i) ?_ ?_ d hd
    · rw [map_sub, hlamOc j, hlamOc i, sub_zero]
    · intro hzero
      exact hij (hlamOinj (sub_eq_zero.mp hzero)).symm
  have hind : LinearIndependent F EO :=
    linearIndependent_of_deriv_eigen lamO EO hEOne heigO hrigidO
  -- expand the operator on the carrier
  set coef : Option ι → F := fun o => o.elim (linOpBase c n q) (fun i => symbolEval c n (lam i))
    with hcoef
  have hexpand : (∑ o : Option ι, algebraMap F M (coef o) * EO o) = 0 := by
    rw [Fintype.sum_option]
    have hnone : algebraMap F M (coef none) * EO none
        = algebraMap F M (linOpBase c n q) := by
      show algebraMap F M (linOpBase c n q) * (1 : M) = _
      rw [mul_one]
    have hsome : ∀ i : ι, algebraMap F M (coef (some i)) * EO (some i)
        = linOp c n (E i) := by
      intro i
      show algebraMap F M (symbolEval c n (lam i)) * E i = _
      rw [linOp_eigen c n (hlamc i) (heig i)]
    rw [hnone]
    have hrewrite : (∑ i : ι, algebraMap F M (coef (some i)) * EO (some i))
        = ∑ i : ι, linOp c n (E i) := Finset.sum_congr rfl (fun i _ => hsome i)
    rw [hrewrite, ← linOp_sum, ← linOp_algebraMap, ← linOp_add]
    exact h
  have hzero : ∀ o : Option ι, coef o = 0 := by
    intro o
    have := linearIndependent_iff'.mp hind Finset.univ coef ?_ o (Finset.mem_univ o)
    · exact this
    · rw [← hexpand]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      rw [Algebra.smul_def]
  exact ⟨hzero none, fun i => hzero (some i)⟩

end GaloisForLFunctions.LinDiffOp

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F : Type*} [Field F] [Differential F]

/-- The base operator attached to a polynomial symbol, read at a prescribed order bound. -/
theorem linOpBase_congr {c d : ℕ → F} {n : ℕ} (h : ∀ j ≤ n, c j = d j) (q : F) :
    linOpBase c n q = linOpBase d n q := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- Differentiating a base operator with constant coefficients shifts the jet index. -/
theorem deriv_linOpBase {P : Polynomial F} {n : ℕ} (hcoef : ∀ j, (P.coeff j)′ = 0) (q : F) :
    (linOpBase P.coeff n q)′
      = ∑ j ∈ Finset.range (n + 1), P.coeff j * differentialJet (j + 1) q := by
  rw [linOpBase, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hcoef j]
  simp only [smul_eq_mul, mul_zero, add_zero, differentialJet_succ]

/-- One linear factor of the symbol corresponds to one factor `a·D - b` of the operator. -/
theorem linOpBase_linear_mul {P : Polynomial F} {n : ℕ} (hP : P.natDegree ≤ n)
    (hcoef : ∀ j, (P.coeff j)′ = 0) {a b : F} (q : F) :
    linOpBase ((Polynomial.C a * Polynomial.X - Polynomial.C b) * P).coeff (n + 1) q
      = a * (linOpBase P.coeff n q)′ - b * linOpBase P.coeff n q := by
  have hcoeffj : ∀ j : ℕ,
      ((Polynomial.C a * Polynomial.X - Polynomial.C b) * P).coeff j
        = a * (Polynomial.X * P).coeff j - b * P.coeff j := by
    intro j
    rw [sub_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul]
  have htop : P.coeff (n + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [linOpBase]
  have hsplit : ∀ j ∈ Finset.range (n + 1 + 1),
      ((Polynomial.C a * Polynomial.X - Polynomial.C b) * P).coeff j * differentialJet j q
        = a * ((Polynomial.X * P).coeff j * differentialJet j q)
          - b * (P.coeff j * differentialJet j q) := by
    intro j _
    rw [hcoeffj j]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  · congr 1
    rw [deriv_linOpBase hcoef q]
    have hshift : (∑ i ∈ Finset.range (n + 1 + 1),
          (Polynomial.X * P).coeff i * differentialJet i q)
        = (∑ i ∈ Finset.range (n + 1),
            (Polynomial.X * P).coeff (i + 1) * differentialJet (i + 1) q)
          + (Polynomial.X * P).coeff 0 * differentialJet 0 q :=
      Finset.sum_range_succ' _ (n + 1)
    rw [hshift]
    have hzero : (Polynomial.X * P).coeff 0 * differentialJet 0 q = 0 := by
      rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, zero_mul]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.coeff_X_mul]
  · congr 1
    rw [linOpBase, Finset.sum_range_succ, htop, zero_mul, add_zero]

end GaloisForLFunctions.LinDiffOp

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F : Type*} [Field F] [Differential F]

/-- The constant-coefficient annihilator `∏ (D - μ)` attached to a list of exponents. -/
def opList (l : List F) (q : F) : F := l.foldr (fun mu y => y′ - mu * y) q

@[simp] theorem opList_nil (q : F) : opList ([] : List F) q = q := rfl

@[simp] theorem opList_cons (mu : F) (l : List F) (q : F) :
    opList (mu :: l) q = (opList l q)′ - mu * opList l q := rfl

/-- The monic symbol polynomial of that annihilator. -/
def factorPoly (l : List F) : Polynomial F :=
  (l.map (fun mu => Polynomial.X - Polynomial.C mu)).prod

omit [Differential F] in
@[simp] theorem factorPoly_nil : factorPoly ([] : List F) = 1 := rfl

omit [Differential F] in
@[simp] theorem factorPoly_cons (mu : F) (l : List F) :
    factorPoly (mu :: l) = (Polynomial.X - Polynomial.C mu) * factorPoly l := rfl

omit [Differential F] in
theorem factorPoly_monic (l : List F) : (factorPoly l).Monic := by
  induction l with
  | nil => simp
  | cons mu l ih =>
      rw [factorPoly_cons]
      exact (monic_X_sub_C mu).mul ih

omit [Differential F] in
theorem factorPoly_natDegree (l : List F) : (factorPoly l).natDegree = l.length := by
  induction l with
  | nil => simp
  | cons mu l ih =>
      rw [factorPoly_cons, (monic_X_sub_C mu).natDegree_mul (factorPoly_monic l),
        natDegree_X_sub_C, ih, List.length_cons]
      omega

theorem factorPoly_coeff_deriv {l : List F} (hl : ∀ mu ∈ l, mu′ = 0) (j : ℕ) :
    ((factorPoly l).coeff j)′ = 0 := by
  induction l generalizing j with
  | nil =>
      rw [factorPoly_nil, Polynomial.coeff_one]
      by_cases h : j = 0
      · rw [if_pos h]
        simp
      · rw [if_neg h]
        simp
  | cons mu l ih =>
      have hmu : mu′ = 0 := hl mu List.mem_cons_self
      have ihl : ∀ k, ((factorPoly l).coeff k)′ = 0 := fun k =>
        ih (fun a ha => hl a (List.mem_cons_of_mem mu ha)) k
      have hexp : (factorPoly (mu :: l)).coeff j
          = (Polynomial.X * factorPoly l).coeff j - mu * (factorPoly l).coeff j := by
        rw [factorPoly_cons, sub_mul, Polynomial.coeff_sub, Polynomial.C_mul']
        simp
      rw [hexp, map_sub, Derivation.leibniz, hmu, ihl j]
      have hxc : ((Polynomial.X * factorPoly l).coeff j)′ = 0 := by
        cases j with
        | zero =>
            rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
            simp
        | succ k =>
            rw [Polynomial.coeff_X_mul]
            exact ihl k
      rw [hxc]
      simp

/-- **The symbol of the constant-coefficient annihilator is `∏ (X - μ)`.** -/
theorem linOpBase_factorPoly {l : List F} (hl : ∀ mu ∈ l, mu′ = 0) (q : F) :
    linOpBase (factorPoly l).coeff l.length q = opList l q := by
  induction l generalizing q with
  | nil =>
      rw [factorPoly_nil, opList_nil, linOpBase]
      simp
  | cons mu l ih =>
      have hmu : mu′ = 0 := hl mu List.mem_cons_self
      have hltail : ∀ a ∈ l, a′ = 0 := fun a ha => hl a (List.mem_cons_of_mem mu ha)
      have hdeg : (factorPoly l).natDegree ≤ l.length :=
        le_of_eq (factorPoly_natDegree l)
      have hfac : factorPoly (mu :: l)
          = (Polynomial.C 1 * Polynomial.X - Polynomial.C mu) * factorPoly l := by
        rw [factorPoly_cons, Polynomial.C_1, one_mul]
      rw [List.length_cons, hfac,
        linOpBase_linear_mul hdeg (factorPoly_coeff_deriv hltail) q, one_mul,
        ih hltail q, opList_cons]

end GaloisForLFunctions.LinDiffOp
