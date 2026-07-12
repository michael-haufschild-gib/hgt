import GaloisForLFunctions.Hurwitz.JointPowerOrbit
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Degreewise separation on multicolumn power orbits

A single common power orbit separates all monomials only under multiplicative independence.
Independent columns carry more information: after taking one finite difference in each of `L`
columns, every polynomial of total degree at most `L` is reduced to the component that is linear in
every column.  That component only sees the degree-one nodes.  Consequently pairwise distinct
nontrivial nodes suffice for top-degree separation.
-/

open Complex

namespace HurwitzJointOrbit

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of a monomial exponent vector to one column. -/
def columnSlice {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) : ι →₀ ℕ :=
  Finsupp.comapDomain.addMonoidHom
    (f := fun j : ι => (j, n)) (fun _ _ h => congrArg Prod.fst h) d

@[simp]
theorem columnSlice_apply {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) (j : ι) :
    columnSlice d n j = d (j, n) := by
  simp [columnSlice]

/-- Value of the monomial in column `n` at the node family `q`. -/
def columnMonomialValue {L : ℕ} (q : ι → ℂ) (n : Fin L)
    (d : (ι × Fin L) →₀ ℕ) : ℂ :=
  monomialValue q (columnSlice d n)

/-- The total exponent carried by one column. -/
def columnDegree {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) : ℕ :=
  (columnSlice d n).degree

theorem columnDegree_eq_zero_iff {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) :
    columnDegree d n = 0 ↔ columnSlice d n = 0 := by
  rw [columnDegree, Finsupp.degree_eq_zero_iff]

theorem columnMonomialValue_of_columnDegree_eq_zero {L : ℕ} (q : ι → ℂ)
    (d : (ι × Fin L) →₀ ℕ) (n : Fin L) (h : columnDegree d n = 0) :
    columnMonomialValue q n d = 1 := by
  rw [columnMonomialValue, (columnDegree_eq_zero_iff d n).mp h]
  simp [monomialValue]

theorem exists_columnSlice_eq_single_of_columnDegree_eq_one {L : ℕ}
    (d : (ι × Fin L) →₀ ℕ) (n : Fin L) (h : columnDegree d n = 1) :
    ∃ j : ι, columnSlice d n = Finsupp.single j 1 := by
  exact (Finsupp.sum_eq_one_iff (columnSlice d n)).mp h

theorem columnMonomialValue_of_columnSlice_eq_single {L : ℕ} (q : ι → ℂ)
    (d : (ι × Fin L) →₀ ℕ) (n : Fin L) (j : ι)
    (h : columnSlice d n = Finsupp.single j 1) :
    columnMonomialValue q n d = q j := by
  rw [columnMonomialValue, h, monomialValue]
  simp

theorem degree_eq_sum_columnDegree {L : ℕ} (d : (ι × Fin L) →₀ ℕ) :
    d.degree = ∑ n : Fin L, columnDegree d n := by
  classical
  change d.sum (fun _ e => e) =
    ∑ n : Fin L, (columnSlice d n).sum (fun _ e => e)
  rw [Finsupp.sum_fintype d _ (fun _ => rfl)]
  have hs : ∀ n : Fin L, (columnSlice d n).sum (fun _ e => e) =
      ∑ j : ι, d (j, n) := by
    intro n
    rw [Finsupp.sum_fintype (columnSlice d n) _ (fun _ => rfl)]
    simp only [columnSlice_apply]
  rw [Finset.sum_congr rfl (fun n _ => hs n)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- A monomial on a product power grid factors into its column characters. -/
theorem monomialValue_powerGrid {L : ℕ} (q : ι → ℂ) (m : Fin L → ℕ)
    (d : (ι × Fin L) →₀ ℕ) :
    monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d =
      ∏ n : Fin L, (columnMonomialValue q n d) ^ m n := by
  classical
  rw [monomialValue, Finsupp.prod_pow, Fintype.prod_prod_type]
  simp only [columnMonomialValue, monomialValue, Finsupp.prod_pow, columnSlice_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro n _
  calc
    ∏ j : ι, (q j ^ m n) ^ d (j, n) =
        ∏ j : ι, (q j ^ d (j, n)) ^ m n := by
          apply Finset.prod_congr rfl
          intro j _
          rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (∏ j : ι, q j ^ d (j, n)) ^ m n := by
      simpa using
        (Finset.prod_pow Finset.univ (m n) (fun j : ι => q j ^ d (j, n)))

theorem monomialValue_powerGrid_update_succ {L : ℕ} (q : ι → ℂ)
    (m : Fin L → ℕ) (n : Fin L) (d : (ι × Fin L) →₀ ℕ) :
    monomialValue
          (fun jk : ι × Fin L => q jk.1 ^ (Function.update m n (m n + 1)) jk.2) d -
        monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d =
      monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d *
        (columnMonomialValue q n d - 1) := by
  classical
  rw [monomialValue_powerGrid, monomialValue_powerGrid]
  let b : Fin L → ℂ := fun r => columnMonomialValue q r d ^ m r
  have hupdate :
      (fun r : Fin L =>
          columnMonomialValue q r d ^ (Function.update m n (m n + 1)) r) =
        Function.update b n
          (columnMonomialValue q n d ^ (m n + 1)) := by
    funext r
    by_cases hr : r = n
    · subst hr
      simp [b]
    · simp [Function.update_of_ne hr, b]
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ n)]
  rw [show (∏ x ∈ Finset.univ \ {n}, b x) =
      ∏ x ∈ Finset.univ \ {n},
        columnMonomialValue q x d ^ m x by rfl]
  rw [show (∏ x : Fin L, columnMonomialValue q x d ^ m x) =
      b n * ∏ x ∈ Finset.univ \ {n}, b x by
        rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ n)]]
  dsimp only [b]
  rw [pow_succ]
  ring

/-- Coefficientwise finite difference in a set of independent columns. -/
def columnDifferenceSet {L : ℕ} (q : ι → ℂ) (S : Finset (Fin L))
    (P : MvPolynomial (ι × Fin L) ℂ) : MvPolynomial (ι × Fin L) ℂ :=
  P.sum fun d c =>
    MvPolynomial.monomial d (c * ∏ n ∈ S, (columnMonomialValue q n d - 1))

theorem coeff_columnDifferenceSet {L : ℕ} (q : ι → ℂ) (S : Finset (Fin L))
    (P : MvPolynomial (ι × Fin L) ℂ) (d : (ι × Fin L) →₀ ℕ) :
    MvPolynomial.coeff d (columnDifferenceSet q S P) =
      MvPolynomial.coeff d P * ∏ n ∈ S, (columnMonomialValue q n d - 1) := by
  classical
  rw [columnDifferenceSet, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ P.support
  · rw [Finset.sum_eq_single d]
    · simp [hd]
    · intro e heP hed
      simp [hed]
    · simp [hd]
  · have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hcoeff, zero_mul]
    apply Finset.sum_eq_zero
    intro e he
    simp [show e ≠ d from fun h => hd (h ▸ he)]

@[simp]
theorem columnDifferenceSet_empty {L : ℕ} (q : ι → ℂ)
    (P : MvPolynomial (ι × Fin L) ℂ) :
    columnDifferenceSet q ∅ P = P := by
  apply MvPolynomial.ext
  intro d
  simp [coeff_columnDifferenceSet]

theorem columnDifferenceSet_insert {L : ℕ} (q : ι → ℂ) (S : Finset (Fin L))
    (n : Fin L) (hn : n ∉ S) (P : MvPolynomial (ι × Fin L) ℂ) :
    columnDifferenceSet q (insert n S) P =
      columnDifferenceSet q {n} (columnDifferenceSet q S P) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_columnDifferenceSet, coeff_columnDifferenceSet, coeff_columnDifferenceSet]
  rw [Finset.prod_insert hn]
  simp only [Finset.prod_singleton]
  ring

/-- A one-column coefficientwise difference is the forward finite difference of the power-grid
evaluation in that column. -/
theorem eval_columnDifferenceSet_singleton {L : ℕ} (q : ι → ℂ) (n : Fin L)
    (P : MvPolynomial (ι × Fin L) ℂ) (m : Fin L → ℕ) :
    MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2)
        (columnDifferenceSet q {n} P) =
      MvPolynomial.eval
          (fun jk : ι × Fin L =>
            q jk.1 ^ (Function.update m n (m n + 1)) jk.2) P -
        MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2) P := by
  classical
  rw [columnDifferenceSet, MvPolynomial.sum_def]
  simp only [map_sum]
  simp_rw [MvPolynomial.eval_monomial]
  simp only [Finset.prod_singleton]
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  change MvPolynomial.coeff d P * (columnMonomialValue q n d - 1) *
      monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d =
    MvPolynomial.coeff d P *
        monomialValue
          (fun jk : ι × Fin L =>
            q jk.1 ^ (Function.update m n (m n + 1)) jk.2) d -
      MvPolynomial.coeff d P *
        monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d
  have hmono := monomialValue_powerGrid_update_succ q m n d
  calc
    MvPolynomial.coeff d P * (columnMonomialValue q n d - 1) *
          monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d =
        MvPolynomial.coeff d P *
          (monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d *
            (columnMonomialValue q n d - 1)) := by ring
    _ = MvPolynomial.coeff d P *
        (monomialValue
            (fun jk : ι × Fin L =>
              q jk.1 ^ (Function.update m n (m n + 1)) jk.2) d -
          monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) d) := by
      rw [hmono]
    _ = _ := by ring

/-- Every iterated column difference of a polynomial vanishing on the product power grid still
vanishes on that grid. -/
theorem columnDifferenceSet_grid_zero {L : ℕ} (q : ι → ℂ)
    (P : MvPolynomial (ι × Fin L) ℂ)
    (hgrid : ∀ m : Fin L → ℕ,
      MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2) P = 0) :
    ∀ S : Finset (Fin L), ∀ m : Fin L → ℕ,
      MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2)
        (columnDifferenceSet q S P) = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro m
      simpa using hgrid m
  | @insert n S hn ih =>
      intro m
      rw [columnDifferenceSet_insert q S n hn]
      rw [eval_columnDifferenceSet_singleton]
      rw [ih (Function.update m n (m n + 1)), ih m, sub_zero]

lemma eq_one_of_one_le_of_sum_le_card {L : ℕ} (f : Fin L → ℕ)
    (hpos : ∀ n, 1 ≤ f n) (hsum : (∑ n, f n) ≤ L) :
    ∀ n, f n = 1 := by
  classical
  intro n
  have hrest : L - 1 ≤ ∑ r ∈ (Finset.univ : Finset (Fin L)).erase n, f r := by
    calc
      L - 1 = ((Finset.univ : Finset (Fin L)).erase n).card := by simp
      _ = ∑ _r ∈ (Finset.univ : Finset (Fin L)).erase n, 1 := by simp
      _ ≤ ∑ r ∈ (Finset.univ : Finset (Fin L)).erase n, f r := by
        exact Finset.sum_le_sum fun r _ => hpos r
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin L)) f
    (Finset.mem_univ n)
  have htotal : f n + ∑ r ∈ (Finset.univ : Finset (Fin L)).erase n, f r ≤ L := by
    rw [hsplit]
    exact hsum
  have hL : 1 ≤ L := by omega
  omega

/-- After differencing every column, every coefficient below the number of columns vanishes. -/
theorem coeff_columnDifferenceSet_univ_eq_zero_of_degree_lt {L : ℕ} (q : ι → ℂ)
    (P : MvPolynomial (ι × Fin L) ℂ) (d : (ι × Fin L) →₀ ℕ)
    (hd : d.degree < L) :
    MvPolynomial.coeff d (columnDifferenceSet q Finset.univ P) = 0 := by
  classical
  have hex : ∃ n : Fin L, columnDegree d n = 0 := by
    by_contra h
    push_neg at h
    have hpos : ∀ n : Fin L, 1 ≤ columnDegree d n :=
      fun n => Nat.one_le_iff_ne_zero.mpr (h n)
    have hle : L ≤ ∑ n : Fin L, columnDegree d n := by
      calc
        L = ∑ _n : Fin L, 1 := by simp
        _ ≤ ∑ n : Fin L, columnDegree d n :=
          Finset.sum_le_sum fun n _ => hpos n
    rw [← degree_eq_sum_columnDegree] at hle
    omega
  obtain ⟨n, hn⟩ := hex
  rw [coeff_columnDifferenceSet]
  have hfactor : columnMonomialValue q n d - 1 = 0 := by
    rw [columnMonomialValue_of_columnDegree_eq_zero q d n hn, sub_self]
  rw [Finset.prod_eq_zero (Finset.mem_univ n) hfactor, mul_zero]

/-- A surviving coefficient of the all-column difference at degree at most `L` is linear in every
column. -/
theorem columnDegree_eq_one_of_coeff_columnDifferenceSet_univ_ne_zero {L : ℕ}
    (q : ι → ℂ) (P : MvPolynomial (ι × Fin L) ℂ)
    (d : (ι × Fin L) →₀ ℕ) (hdeg : d.degree ≤ L)
    (hcoeff : MvPolynomial.coeff d (columnDifferenceSet q Finset.univ P) ≠ 0) :
    ∀ n : Fin L, columnDegree d n = 1 := by
  classical
  have hprod : ∏ n : Fin L, (columnMonomialValue q n d - 1) ≠ 0 := by
    rw [coeff_columnDifferenceSet] at hcoeff
    exact fun h => hcoeff (by rw [h, mul_zero])
  have hpos : ∀ n : Fin L, 1 ≤ columnDegree d n := by
    intro n
    apply Nat.one_le_iff_ne_zero.mpr
    intro hn
    have hvalue := columnMonomialValue_of_columnDegree_eq_zero q d n hn
    have hfactor : columnMonomialValue q n d - 1 = 0 := by rw [hvalue, sub_self]
    apply hprod
    exact Finset.prod_eq_zero (Finset.mem_univ n) hfactor
  apply eq_one_of_one_le_of_sum_le_card (fun n => columnDegree d n) hpos
  rwa [← degree_eq_sum_columnDegree]

end

end HurwitzJointOrbit
