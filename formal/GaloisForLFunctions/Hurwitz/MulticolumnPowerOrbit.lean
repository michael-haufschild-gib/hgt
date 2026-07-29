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
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ n)]]
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
  have hL : 1 ≤ L := by
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by subst L; exact Fin.elim0 n)
  have hpred : L - 1 + 1 = L := Nat.sub_add_cancel hL
  apply Nat.le_antisymm _ (hpos n)
  apply Nat.le_of_add_le_add_right (b := L - 1)
  calc
    f n + (L - 1) ≤ f n + ∑ r ∈ (Finset.univ : Finset (Fin L)).erase n, f r :=
      Nat.add_le_add_left hrest _
    _ ≤ L := htotal
    _ = L - 1 + 1 := hpred.symm
    _ = 1 + (L - 1) := Nat.add_comm _ _

/-- After differencing every column, every coefficient below the number of columns vanishes. -/
theorem coeff_columnDifferenceSet_univ_eq_zero_of_degree_lt {L : ℕ} (q : ι → ℂ)
    (P : MvPolynomial (ι × Fin L) ℂ) (d : (ι × Fin L) →₀ ℕ)
    (hd : d.degree < L) :
    MvPolynomial.coeff d (columnDifferenceSet q Finset.univ P) = 0 := by
  classical
  have hex : ∃ n : Fin L, columnDegree d n = 0 := by
    by_contra h
    push Not at h
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

/-- Vandermonde separation for a finite index type rather than an explicitly enumerated `Fin`. -/
theorem power_sum_coeff_zero_fintype (b c : ι → ℂ) (hb : Function.Injective b)
    (h : ∀ m : ℕ, ∑ i : ι, c i * b i ^ m = 0) : c = 0 := by
  let e := Fintype.equivFin ι
  let b' : Fin (Fintype.card ι) → ℂ := fun k => b (e.symm k)
  let c' : Fin (Fintype.card ι) → ℂ := fun k => c (e.symm k)
  have hb' : Function.Injective b' := hb.comp e.symm.injective
  have h' : ∀ m : ℕ, ∑ k, c' k * b' k ^ m = 0 := by
    intro m
    simpa [b', c'] using (e.symm.sum_comp (fun i => c i * b i ^ m)).trans (h m)
  have hc' := power_sum_coeff_zero hb' h'
  funext i
  have hi := congrFun hc' (e i)
  simpa [c'] using hi

/-- Tensor Vandermonde separation.  Independent column times and pairwise distinct nodes separate
every coefficient indexed by one label in each column. -/
theorem tensor_power_sum_coeff_zero (q : ι → ℂ) (hq : Function.Injective q) :
    ∀ (L : ℕ) (c : (Fin L → ι) → ℂ),
      (∀ m : Fin L → ℕ,
        ∑ f : Fin L → ι, c f * ∏ n : Fin L, q (f n) ^ m n = 0) →
      c = 0 := by
  intro L
  induction L with
  | zero =>
      intro c h
      funext f
      have h0 := h (fun n => Fin.elim0 n)
      have hf : f = default := Subsingleton.elim _ _
      rw [hf]
      simpa only [Fintype.prod_empty, mul_one, Fintype.sum_unique] using h0
  | succ L ih =>
      intro c h
      have hhead : ∀ mtail : Fin L → ℕ, ∀ m0 : ℕ,
          ∑ j : ι,
            (∑ g : Fin L → ι,
              c (Fin.cons j g) * ∏ n : Fin L, q (g n) ^ mtail n) * q j ^ m0 = 0 := by
        intro mtail m0
        have hm := h (Fin.cons m0 mtail)
        rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => ι)).sum_comp] at hm
        rw [Fintype.sum_prod_type] at hm
        have hm' :
            ∑ j : ι, ∑ g : Fin L → ι,
              c (Fin.cons j g) *
                (q j ^ m0 * ∏ n : Fin L, q (g n) ^ mtail n) = 0 := by
          simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using hm
        calc
          ∑ j : ι,
              (∑ g : Fin L → ι,
                c (Fin.cons j g) * ∏ n : Fin L, q (g n) ^ mtail n) * q j ^ m0 =
            ∑ j : ι, ∑ g : Fin L → ι,
              c (Fin.cons j g) *
                (q j ^ m0 * ∏ n : Fin L, q (g n) ^ mtail n) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro g _
                  ring
          _ = 0 := hm'
      have htail : ∀ j : ι, ∀ mtail : Fin L → ℕ,
          ∑ g : Fin L → ι,
            c (Fin.cons j g) * ∏ n : Fin L, q (g n) ^ mtail n = 0 := by
        intro j mtail
        let A : ι → ℂ := fun r =>
          ∑ g : Fin L → ι,
            c (Fin.cons r g) * ∏ n : Fin L, q (g n) ^ mtail n
        have hA : A = 0 := power_sum_coeff_zero_fintype q A hq (hhead mtail)
        exact congrFun hA j
      funext f
      rw [← Fin.cons_self_tail f]
      have hcj := ih (fun g : Fin L → ι => c (Fin.cons (f 0) g)) (htail (f 0))
      exact congrFun hcj (Fin.tail f)

/-- The monomial selecting one label in every column. -/
def columnTuple {L : ℕ} (f : Fin L → ι) : (ι × Fin L) →₀ ℕ :=
  ∑ n : Fin L, Finsupp.single (f n, n) 1

@[simp]
theorem columnTuple_apply {L : ℕ} (f : Fin L → ι) (j : ι) (n : Fin L) :
    columnTuple f (j, n) = if j = f n then 1 else 0 := by
  classical
  rw [columnTuple]
  rw [Finsupp.finsetSum_apply]
  simp_rw [Finsupp.single_apply]
  change (∑ r : Fin L, if (f r, r) = (j, n) then 1 else 0) = _
  by_cases hj : j = f n
  · rw [if_pos hj]
    rw [Finset.sum_eq_single n]
    · simp [hj]
    · intro r _ hr
      simp [Prod.ext_iff, hr]
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r = n
    · subst r
      simp [show f n ≠ j from fun h => hj h.symm]
    · simp [Prod.ext_iff, hr]

theorem columnSlice_columnTuple {L : ℕ} (f : Fin L → ι) (n : Fin L) :
    columnSlice (columnTuple f) n = Finsupp.single (f n) 1 := by
  ext j
  simp [columnTuple_apply, Finsupp.single_apply, eq_comm]

theorem columnDegree_columnTuple {L : ℕ} (f : Fin L → ι) (n : Fin L) :
    columnDegree (columnTuple f) n = 1 := by
  rw [columnDegree, columnSlice_columnTuple]
  simp

theorem degree_columnTuple {L : ℕ} (f : Fin L → ι) :
    (columnTuple f).degree = L := by
  rw [degree_eq_sum_columnDegree]
  simp [columnDegree_columnTuple]

theorem columnTuple_injective {L : ℕ} :
    Function.Injective (columnTuple : (Fin L → ι) → (ι × Fin L) →₀ ℕ) := by
  intro f g h
  funext n
  have hs := congrArg (fun d => columnSlice d n) h
  change columnSlice (columnTuple f) n = columnSlice (columnTuple g) n at hs
  rw [columnSlice_columnTuple, columnSlice_columnTuple] at hs
  by_contra hne
  have hv := congrFun (congrArg DFunLike.coe hs) (f n)
  simpa [Finsupp.single_apply, hne] using hv

theorem eq_columnTuple_of_columnDegree_eq_one {L : ℕ}
    (d : (ι × Fin L) →₀ ℕ) (h : ∀ n : Fin L, columnDegree d n = 1) :
    ∃ f : Fin L → ι, d = columnTuple f := by
  choose f hf using fun n => exists_columnSlice_eq_single_of_columnDegree_eq_one d n (h n)
  refine ⟨f, ?_⟩
  ext jk
  have hjk := congrFun (congrArg DFunLike.coe (hf jk.2)) jk.1
  rw [columnSlice_apply] at hjk
  rw [columnTuple_apply]
  simpa [Finsupp.single_apply, eq_comm] using hjk

theorem monomialValue_powerGrid_columnTuple {L : ℕ} (q : ι → ℂ)
    (m : Fin L → ℕ) (f : Fin L → ι) :
    monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) (columnTuple f) =
      ∏ n : Fin L, q (f n) ^ m n := by
  rw [monomialValue_powerGrid]
  apply Finset.prod_congr rfl
  intro n _
  rw [columnMonomialValue_of_columnSlice_eq_single q (columnTuple f) n (f n)
    (columnSlice_columnTuple f n)]

/-- A polynomial whose nonzero monomials have degree one in every column is the finite sum of its
`columnTuple` monomials. -/
theorem eq_sum_monomial_columnTuple_of_columnDegree_eq_one {L : ℕ}
    (Q : MvPolynomial (ι × Fin L) ℂ)
    (hlinear : ∀ d : (ι × Fin L) →₀ ℕ, MvPolynomial.coeff d Q ≠ 0 →
      ∀ n : Fin L, columnDegree d n = 1) :
    Q = ∑ f : Fin L → ι,
      MvPolynomial.monomial (columnTuple f)
        (MvPolynomial.coeff (columnTuple f) Q) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hex : ∃ f : Fin L → ι, columnTuple f = d
  · obtain ⟨f, hf⟩ := hex
    rw [← hf]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single f]
    · simp
    · intro g _ hgf
      simp [show columnTuple g ≠ columnTuple f from
        fun h => hgf (columnTuple_injective h)]
    · simp
  · have hd : MvPolynomial.coeff d Q = 0 := by
      by_contra hd
      obtain ⟨f, hf⟩ := eq_columnTuple_of_columnDegree_eq_one d (hlinear d hd)
      exact hex ⟨f, hf.symm⟩
    rw [hd]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    symm
    apply Finset.sum_eq_zero
    intro f _
    simp [show columnTuple f ≠ d from fun h => hex ⟨f, h⟩]

/-- The tensor power grid is separating on the component that is linear in every column. -/
theorem columnMultilinear_powerGrid_zero {L : ℕ} (q : ι → ℂ)
    (hq : Function.Injective q) (Q : MvPolynomial (ι × Fin L) ℂ)
    (hlinear : ∀ d : (ι × Fin L) →₀ ℕ, MvPolynomial.coeff d Q ≠ 0 →
      ∀ n : Fin L, columnDegree d n = 1)
    (hgrid : ∀ m : Fin L → ℕ,
      MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2) Q = 0) :
    Q = 0 := by
  let c : (Fin L → ι) → ℂ := fun f => MvPolynomial.coeff (columnTuple f) Q
  have hcgrid : ∀ m : Fin L → ℕ,
      ∑ f : Fin L → ι, c f * ∏ n : Fin L, q (f n) ^ m n = 0 := by
    intro m
    have hm := hgrid m
    rw [eq_sum_monomial_columnTuple_of_columnDegree_eq_one Q hlinear] at hm
    simp only [map_sum, MvPolynomial.eval_monomial] at hm
    change (∑ f : Fin L → ι,
      MvPolynomial.coeff (columnTuple f) Q *
        monomialValue (fun jk : ι × Fin L => q jk.1 ^ m jk.2) (columnTuple f)) = 0 at hm
    simpa only [c, monomialValue_powerGrid_columnTuple] using hm
  have hc : c = 0 := tensor_power_sum_coeff_zero q hq L c hcgrid
  rw [eq_sum_monomial_columnTuple_of_columnDegree_eq_one Q hlinear]
  apply Finset.sum_eq_zero
  intro f _
  have hf := congrFun hc f
  simp only [c, Pi.zero_apply] at hf
  rw [hf, MvPolynomial.monomial_zero]

theorem support_columnDifferenceSet_subset {L : ℕ} (q : ι → ℂ)
    (S : Finset (Fin L)) (P : MvPolynomial (ι × Fin L) ℂ) :
    (columnDifferenceSet q S P).support ⊆ P.support := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  rw [coeff_columnDifferenceSet] at hd
  exact fun h => hd (by rw [h, zero_mul])

theorem totalDegree_columnDifferenceSet_le {L : ℕ} (q : ι → ℂ)
    (S : Finset (Fin L)) (P : MvPolynomial (ι × Fin L) ℂ) :
    (columnDifferenceSet q S P).totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset
    (support_columnDifferenceSet_subset q S P)

/-- **Multicolumn top-degree separator.**  If a polynomial has total degree at most the number of
independently powered columns, then taking one finite difference in every column kills it.  The only
input on the power nodes is pairwise distinctness; higher multiplicative resonances are irrelevant. -/
theorem columnDifferenceSet_univ_eq_zero_of_totalDegree_le {L : ℕ}
    (q : ι → ℂ) (hq : Function.Injective q)
    (P : MvPolynomial (ι × Fin L) ℂ) (hdeg : P.totalDegree ≤ L)
    (hgrid : ∀ m : Fin L → ℕ,
      MvPolynomial.eval (fun jk : ι × Fin L => q jk.1 ^ m jk.2) P = 0) :
    columnDifferenceSet q Finset.univ P = 0 := by
  apply columnMultilinear_powerGrid_zero q hq
  · intro d hd
    apply columnDegree_eq_one_of_coeff_columnDifferenceSet_univ_ne_zero q P d _ hd
    exact (MvPolynomial.le_totalDegree
      ((support_columnDifferenceSet_subset q Finset.univ P)
        (MvPolynomial.mem_support_iff.mpr hd))).trans hdeg
  · exact columnDifferenceSet_grid_zero q P hgrid Finset.univ

end

end HurwitzJointOrbit
