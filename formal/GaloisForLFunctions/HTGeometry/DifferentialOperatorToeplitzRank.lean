import GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms
import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Differential-operator Toeplitz rank

A polynomial differential-operator row is lifted to every output jet by multiplication by a power
of `X`.  On each finite jet packet these shifted rows form a finite Toeplitz coefficient matrix.
Polynomial linear independence of the original rows forces ordinary linear independence of every
such Toeplitz matrix.  Consequently a full-row-rank polynomial differential-operator matrix sends a
differentially independent source family to a differentially independent output family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial Matrix
open scoped Differential

noncomputable section

/-- Applying a monomial differential operator selects the corresponding jet. -/
theorem differentialOperatorApply_monomial
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (n : ℕ) (c : C) (x : K) :
    differentialOperatorApply (Polynomial.monomial n c) x =
      algebraMap C K c * differentialJet n x := by
  simp [differentialOperatorApply]

/-- Differential-operator application is additive in the operator polynomial. -/
theorem differentialOperatorApply_add
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (P Q : Polynomial C) (x : K) :
    differentialOperatorApply (P + Q) x =
      differentialOperatorApply P x + differentialOperatorApply Q x := by
  classical
  unfold differentialOperatorApply
  apply Polynomial.sum_add_index
  · intro n
    simp
  · intro n a b
    simp [add_mul]

/-- Differentiating an operator output multiplies its operator polynomial by `X`. -/
theorem deriv_differentialOperatorApply
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (P : Polynomial C) (x : K) :
    (differentialOperatorApply P x)′ =
      differentialOperatorApply (Polynomial.X * P) x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [differentialOperatorApply_add, map_add, hP, hQ, mul_add,
        differentialOperatorApply_add]
  | monomial n c =>
      rw [differentialOperatorApply_monomial, Derivation.leibniz]
      simp only [smul_eq_mul, hconst, mul_zero, add_zero]
      rw [Polynomial.X_mul_monomial, differentialOperatorApply_monomial]
      rw [differentialJet_succ]

/-- The `n`-th jet of an operator output is obtained by multiplying the operator by `X ^ n`. -/
theorem differentialJet_differentialOperatorApply
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (P : Polynomial C) (x : K) (n : ℕ) :
    differentialJet n (differentialOperatorApply P x) =
      differentialOperatorApply (Polynomial.X ^ n * P) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        deriv_differentialOperatorApply hconst]
      congr 1
      rw [pow_succ']
      ring

/-- Every differential jet commutes with a finite sum. -/
theorem differentialJet_finset_sum
    {K ι : Type*} [Field K] [Differential K]
    (s : Finset ι) (f : ι → K) (n : ℕ) :
    differentialJet n (s.sum f) = s.sum (fun i => differentialJet n (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (differentialJet_succ n (f i)).symm

/-- Apply one row of a polynomial differential-operator matrix to a source family. -/
def differentialOperatorRowApply
    {C K ι κ : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype κ] (L : ι → κ → Polynomial C) (x : κ → K) (i : ι) : K :=
  Finset.univ.sum fun j => differentialOperatorApply (L i j) (x j)

/-- The jet formula for a row of a polynomial differential-operator matrix. -/
theorem differentialJet_differentialOperatorRowApply
    {C K ι κ : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype κ] (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C) (x : κ → K) (i : ι) (n : ℕ) :
    differentialJet n (differentialOperatorRowApply L x i) =
      Finset.univ.sum fun j =>
        differentialOperatorApply (Polynomial.X ^ n * L i j) (x j) := by
  rw [differentialOperatorRowApply, differentialJet_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact differentialJet_differentialOperatorApply hconst (L i j) (x j) n

/-- A common strict degree bound for a finite packet of shifted operator rows. -/
def operatorJetBound
    {C ι κ : Type*} [Field C] [Fintype κ]
    (L : ι → κ → Polynomial C) (t : Set (ι × ℕ)) (ht : t.Finite) : ℕ :=
  1 + ht.toFinset.sum (fun p =>
    Finset.univ.sum fun j => p.2 + (L p.1 j).natDegree)

/-- Every shifted entry indexed by the finite packet lies below `operatorJetBound`. -/
theorem operatorJetBound_degree
    {C ι κ : Type*} [Field C] [Fintype κ]
    (L : ι → κ → Polynomial C) (t : Set (ι × ℕ)) (ht : t.Finite)
    (p : t) (j : κ) :
    (Polynomial.X ^ p.1.2 * L p.1.1 j).natDegree < operatorJetBound L t ht := by
  have hpMem : p.1 ∈ ht.toFinset := ht.mem_toFinset.mpr p.2
  have hinner : p.1.2 + (L p.1.1 j).natDegree ≤
      Finset.univ.sum (fun k => p.1.2 + (L p.1.1 k).natDegree) := by
    let g : κ → ℕ := fun k => p.1.2 + (L p.1.1 k).natDegree
    have hs := Finset.single_le_sum (s := Finset.univ) (f := g)
      (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
    simpa [g] using hs
  let f : ι × ℕ → ℕ := fun q =>
    Finset.univ.sum fun k => q.2 + (L q.1 k).natDegree
  have houter : f p.1 ≤ ∑ q ∈ ht.toFinset, f q :=
    Finset.single_le_sum (s := ht.toFinset) (fun q hq => Nat.zero_le _) hpMem
  have hdeg : (Polynomial.X ^ p.1.2 * L p.1.1 j).natDegree ≤
      p.1.2 + (L p.1.1 j).natDegree := by
    simpa only [Polynomial.natDegree_X_pow] using
      (Polynomial.natDegree_mul_le (p := Polynomial.X ^ p.1.2) (q := L p.1.1 j))
  dsimp [operatorJetBound]
  dsimp [f] at houter
  omega

/-- The finite coefficient matrix of all shifted operator rows in a finite output-jet packet. -/
def operatorToeplitzMatrix
    {C ι κ : Type*} [Field C] [Fintype κ]
    (L : ι → κ → Polynomial C) (t : Set (ι × ℕ)) (ht : t.Finite) :
    Matrix t (κ × Fin (operatorJetBound L t ht)) C :=
  fun p q => (Polynomial.X ^ p.1.2 * L p.1.1 q.1).coeff q.2

/-- Coefficient extraction as an additive homomorphism. -/
def polynomialCoeffAddHom {C : Type*} [Semiring C] (n : ℕ) : Polynomial C →+ C where
  toFun P := P.coeff n
  map_zero' := Polynomial.coeff_zero n
  map_add' P Q := Polynomial.coeff_add P Q n

/-- A degree-bounded operator application is a finite linear form in the corresponding jets. -/
theorem differentialOperatorApply_eq_fin_sum
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (P : Polynomial C) (x : K) (B : ℕ) (hdeg : P.natDegree < B) :
    differentialOperatorApply P x =
      ∑ n : Fin B, algebraMap C K (P.coeff n) * differentialJet n x := by
  unfold differentialOperatorApply
  rw [Polynomial.sum_over_range' P (by intro n; simp) B hdeg]
  rw [← Fin.sum_univ_eq_sum_range]

/-- A finite packet of output jets is the Toeplitz matrix applied to a source-jet rectangle. -/
theorem differentialOperatorOutputJet_eq_matrixLinearForms
    {C K ι κ : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype κ] (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C) (x : κ → K)
    (t : Set (ι × ℕ)) (ht : t.Finite) (p : t) :
    differentialJet p.1.2 (differentialOperatorRowApply L x p.1.1) =
      matrixLinearForms (operatorToeplitzMatrix L t ht)
        (fun q : κ × Fin (operatorJetBound L t ht) => differentialJet q.2.1 (x q.1)) p := by
  rw [differentialJet_differentialOperatorRowApply hconst]
  unfold matrixLinearForms operatorToeplitzMatrix
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  rw [differentialOperatorApply_eq_fin_sum _ _ _ (operatorJetBound_degree L t ht p j)]

/-- Polynomially independent operator rows yield independent rows in every finite Toeplitz lift. -/
theorem operatorToeplitzMatrix_rows_linearIndependent
    {C ι κ : Type*} [Field C] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (L : ι → κ → Polynomial C)
    (hL : LinearIndependent (Polynomial C) L)
    (t : Set (ι × ℕ)) (ht : t.Finite) :
    LinearIndependent C (operatorToeplitzMatrix L t ht).row := by
  classical
  letI : Finite t := ht
  letI : Fintype t := Fintype.ofFinite t
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  let A : ι → Polynomial C := fun i =>
    ∑ r : t, if r.1.1 = i then
      Polynomial.C (a r) * Polynomial.X ^ r.1.2 else 0
  have hrewrite : (∑ i, A i • L i) =
      ∑ r : t, (Polynomial.C (a r) * Polynomial.X ^ r.1.2) • L r.1.1 := by
    funext j
    simp [A, Finset.sum_mul, Finset.sum_comm]
  have hright : (∑ r : t,
      (Polynomial.C (a r) * Polynomial.X ^ r.1.2) • L r.1.1) = 0 := by
    funext j
    apply Polynomial.ext
    intro k
    simp only [Pi.zero_apply, Polynomial.coeff_zero]
    rw [Finset.sum_apply]
    change polynomialCoeffAddHom k
      (∑ r : t, (Polynomial.C (a r) * Polynomial.X ^ r.1.2) * L r.1.1 j) = 0
    rw [map_sum]
    by_cases hk : k < operatorJetBound L t ht
    · let kf : Fin (operatorJetBound L t ht) := ⟨k, hk⟩
      have hc := congrFun ha (j, kf)
      simpa [polynomialCoeffAddHom, operatorToeplitzMatrix, Matrix.row,
        Pi.smul_apply, smul_eq_mul,
        mul_assoc, Polynomial.coeff_C_mul] using hc
    · apply Finset.sum_eq_zero
      intro r hr
      change ((Polynomial.C (a r) * Polynomial.X ^ r.1.2) *
        L r.1.1 j).coeff k = 0
      rw [mul_assoc, Polynomial.coeff_C_mul]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · simp
      · exact (operatorJetBound_degree L t ht r j).trans_le (Nat.le_of_not_gt hk)
  have hAzero : ∀ i, A i = 0 := by
    apply (Fintype.linearIndependent_iff.mp hL A)
    rw [hrewrite]
    exact hright
  have hpzero := congrArg (fun P : Polynomial C => P.coeff p.1.2) (hAzero p.1.1)
  have hpcoeff : (A p.1.1).coeff p.1.2 = a p := by
    change polynomialCoeffAddHom p.1.2
      (∑ r : t, if r.1.1 = p.1.1 then
        Polynomial.C (a r) * Polynomial.X ^ r.1.2 else 0) = a p
    rw [map_sum]
    rw [Finset.sum_eq_single p]
    · simp [polynomialCoeffAddHom]
    · intro r hr hrp
      by_cases hri : r.1.1 = p.1.1
      · rw [if_pos hri]
        have hrn : r.1.2 ≠ p.1.2 := by
          intro heq
          apply hrp
          apply Subtype.ext
          exact Prod.ext hri heq
        have hrn' : p.1.2 ≠ r.1.2 := Ne.symm hrn
        simp [polynomialCoeffAddHom, Polynomial.coeff_C_mul, hrn']
      · simp [polynomialCoeffAddHom, hri]
    · intro hpnot
      exact (hpnot (Finset.mem_univ p)).elim
  change (A p.1.1).coeff p.1.2 = 0 at hpzero
  exact hpcoeff ▸ hpzero

/-- Full polynomial row rank preserves differential algebraic independence.

This is the nonlinear-rank theorem: no algebraic relation among arbitrary output jets can appear
after applying a polynomial differential-operator matrix whose rows are independent over `C[X]`.
-/
theorem differentialIndependent_differentialOperatorRows
    {C K ι κ : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (hL : LinearIndependent (Polynomial C) L)
    (x : κ → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (differentialOperatorRowApply L x) := by
  classical
  unfold DifferentialIndependent at hx ⊢
  apply algebraicIndependent_of_finite_type
  intro t ht
  letI : Finite t := ht
  letI : Fintype t := Fintype.ofFinite t
  let B := operatorJetBound L t ht
  let sourceJet : κ × Fin B → K := fun q => differentialJet q.2.1 (x q.1)
  let sourceIndex : κ × Fin B → κ × ℕ := fun q => (q.1, q.2.1)
  have hsourceIndex : Function.Injective sourceIndex := by
    rintro ⟨j, n⟩ ⟨j', n'⟩ h
    simp only [sourceIndex, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, Fin.ext h.2⟩
  have hxB : AlgebraicIndependent C sourceJet := by
    have hcomp := hx.comp sourceIndex hsourceIndex
    have hsourceJet :
        ((fun p : κ × ℕ => differentialJet p.2 (x p.1)) ∘ sourceIndex) =
          sourceJet := by
      funext q
      rfl
    rw [hsourceJet] at hcomp
    exact hcomp
  have hrows := operatorToeplitzMatrix_rows_linearIndependent L hL t ht
  have hforms := algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    (operatorToeplitzMatrix L t ht) hrows sourceJet hxB
  simpa only [sourceJet, B,
    differentialOperatorOutputJet_eq_matrixLinearForms hconst L x t ht] using hforms

/-- Constant scalar multiplication of an operator becomes scalar multiplication of its output. -/
theorem differentialOperatorApply_C_mul
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (c : C) (P : Polynomial C) (x : K) :
    differentialOperatorApply (Polynomial.C c * P) x =
      algebraMap C K c * differentialOperatorApply P x := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [mul_add, differentialOperatorApply_add, hP, hQ,
        differentialOperatorApply_add, mul_add]
  | monomial n a =>
      rw [Polynomial.C_mul_monomial, differentialOperatorApply_monomial,
        differentialOperatorApply_monomial, map_mul, mul_assoc]

/-- Composition of constant-coefficient differential operators is polynomial multiplication. -/
theorem differentialOperatorApply_mul
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (P Q : Polynomial C) (x : K) :
    differentialOperatorApply P (differentialOperatorApply Q x) =
      differentialOperatorApply (P * Q) x := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
      rw [differentialOperatorApply_add, hP, hR, add_mul,
        differentialOperatorApply_add]
  | monomial n c =>
      rw [differentialOperatorApply_monomial,
        differentialJet_differentialOperatorApply hconst]
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
        differentialOperatorApply_C_mul]

/-- A constant-coefficient differential operator commutes with finite sums. -/
theorem differentialOperatorApply_finset_sum
    {C K ι : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (P : Polynomial C) (s : Finset ι) (f : ι → K) :
    differentialOperatorApply P (s.sum f) =
      s.sum fun i => differentialOperatorApply P (f i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [differentialOperatorApply_add, hP, hQ, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact (differentialOperatorApply_add P Q (f i)).symm
  | monomial n c =>
      rw [differentialOperatorApply_monomial, differentialJet_finset_sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (differentialOperatorApply_monomial n c (f i)).symm

/-- A common strict degree bound for a finite family of operator polynomials. -/
def polynomialFamilyDegreeBound
    {C ι : Type*} [Field C] [Fintype ι] (A : ι → Polynomial C) : ℕ :=
  1 + ∑ i, (A i).natDegree

/-- Every member of a polynomial family lies below its common degree bound. -/
theorem polynomialFamilyDegreeBound_degree
    {C ι : Type*} [Field C] [Fintype ι]
    (A : ι → Polynomial C) (i : ι) :
    (A i).natDegree < polynomialFamilyDegreeBound A := by
  let f : ι → ℕ := fun j => (A j).natDegree
  have hi : f i ≤ ∑ j, f j :=
    Finset.single_le_sum (s := Finset.univ) (f := f)
      (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  dsimp [polynomialFamilyDegreeBound]
  dsimp [f] at hi
  omega

/-- A differential linear relation among a differentially independent finite family has all
operator coefficients zero. -/
theorem differentialOperatorApplications_coefficients_eq_zero
    {C K ι : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [DecidableEq ι]
    (y : ι → K) (hy : DifferentialIndependent C y)
    (A : ι → Polynomial C)
    (hA : ∑ i, differentialOperatorApply (A i) (y i) = 0) :
    ∀ i, A i = 0 := by
  classical
  let B := polynomialFamilyDegreeBound A
  let jets : ι × Fin B → K := fun q => differentialJet q.2.1 (y q.1)
  have hjetsAI : AlgebraicIndependent C jets := by
    unfold DifferentialIndependent at hy
    let e : ι × Fin B → ι × ℕ := fun q => (q.1, q.2.1)
    have he : Function.Injective e := by
      rintro ⟨i, n⟩ ⟨j, m⟩ h
      simp only [e, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, Fin.ext h.2⟩
    have hcomp := hy.comp e he
    have hjets :
        ((fun p : ι × ℕ => differentialJet p.2 (y p.1)) ∘ e) = jets := by
      funext q
      rfl
    rw [hjets] at hcomp
    exact hcomp
  have hjetsLI : LinearIndependent C jets := hjetsAI.linearIndependent
  have hcoeff : ∀ q : ι × Fin B, (A q.1).coeff q.2.1 = 0 := by
    rw [Fintype.linearIndependent_iff] at hjetsLI
    let coeff : ι × Fin B → C := fun q => (A q.1).coeff q.2.1
    have hlinear : ∑ q, coeff q • jets q = 0 := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i, ∑ n, coeff (i, n) • jets (i, n) =
            ∑ i, differentialOperatorApply (A i) (y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [differentialOperatorApply_eq_fin_sum (A i) (y i) B
            (polynomialFamilyDegreeBound_degree A i)]
          simp only [coeff, jets, Algebra.smul_def]
        _ = 0 := hA
    exact hjetsLI coeff hlinear
  intro i
  apply Polynomial.ext
  intro n
  by_cases hn : n < B
  · exact hcoeff (i, ⟨n, hn⟩)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((polynomialFamilyDegreeBound_degree A i).trans_le (Nat.le_of_not_gt hn))

/-- **Exact differential-operator matroid law.**  On a differentially independent source family,
a finite family of polynomial differential-operator rows has differentially independent outputs
if and only if its rows are linearly independent over the polynomial operator ring `C[X]`.

Thus the complete nonlinear differential-independence matroid of the outputs is exactly the linear
operator-row matroid: it has neither hidden nonlinear circuits nor lost operator circuits.
-/
theorem differentialIndependent_differentialOperatorRows_iff
    {C K ι κ : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (differentialOperatorRowApply L x) ↔
      LinearIndependent (Polynomial C) L := by
  constructor
  · intro hy
    rw [Fintype.linearIndependent_iff]
    intro A hrow
    apply differentialOperatorApplications_coefficients_eq_zero
      (differentialOperatorRowApply L x) hy A
    have hrowj : ∀ j, ∑ i, A i * L i j = 0 := by
      intro j
      have hj := congrFun hrow j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj
    calc
      ∑ i, differentialOperatorApply (A i) (differentialOperatorRowApply L x i) =
          ∑ i, ∑ j, differentialOperatorApply (A i)
            (differentialOperatorApply (L i j) (x j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [differentialOperatorRowApply]
        rw [differentialOperatorApply_finset_sum]
      _ = ∑ i, ∑ j, differentialOperatorApply (A i * L i j) (x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact differentialOperatorApply_mul hconst (A i) (L i j) (x j)
      _ = ∑ j, ∑ i, differentialOperatorApply (A i * L i j) (x j) :=
        Finset.sum_comm
      _ = ∑ j, differentialOperatorApply (∑ i, A i * L i j) (x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        induction (Finset.univ : Finset ι) using Finset.induction_on with
        | empty => simp [differentialOperatorApply]
        | @insert i s hi ih =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi,
              differentialOperatorApply_add, ih]
      _ = 0 := by simp [hrowj, differentialOperatorApply]
  · intro hL
    exact differentialIndependent_differentialOperatorRows hconst L hL x hx

/-- **Nonzero linear differential observations preserve hypertranscendence.**  If the coefficient
field is constant for the ambient derivation, applying any nonzero polynomial in the derivation to
a hypertranscendental observable leaves a hypertranscendental observable.  Thus a finite
constant-coefficient input--output filter cannot hide the complete differential observation
structure of a clock. -/
theorem hypertranscendentalOver_differentialOperatorApply
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    {P : Polynomial C} (hP : P ≠ 0) {x : K}
    (hx : HypertranscendentalOver C x) :
    HypertranscendentalOver C (differentialOperatorApply P x) := by
  let L : Unit → Unit → Polynomial C := fun _ _ => P
  let source : Unit → K := fun _ => x
  have hsource : DifferentialIndependent C source := by
    simpa only [source] using
      (hypertranscendentalOver_iff_differentialIndependent_singleton C x).mp hx
  have hL : LinearIndependent (Polynomial C) L := by
    apply linearIndependent_unique_iff.mpr
    intro hzero
    apply hP
    exact congrFun hzero Unit.unit
  have hout := differentialIndependent_differentialOperatorRows
    hconst L hL source hsource
  apply (hypertranscendentalOver_iff_differentialIndependent_singleton
    C (differentialOperatorApply P x)).mpr
  have hrow : differentialOperatorRowApply L source =
      fun _ : Unit => differentialOperatorApply P x := by
    funext i
    cases i
    simp [differentialOperatorRowApply, L, source]
  rw [hrow] at hout
  exact hout

end

end GaloisForLFunctions.HTGeometry
