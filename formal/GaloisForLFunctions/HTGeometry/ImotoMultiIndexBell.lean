import GaloisForLFunctions.HTGeometry.PhaseGraphSobolevBlindness
import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Multi-indices used by the finite-input recursion of Imoto, arXiv:2609.03768. -/
abbrev FiniteMultiIndex (d : Type*) := d → ℕ

def finiteMultiIndexDegree (alpha : FiniteMultiIndex d) : ℕ := ∑ i, alpha i

def finiteMultiIndexIic (alpha : FiniteMultiIndex d) : Finset (FiniteMultiIndex d) :=
  Fintype.piFinset fun i => Finset.range (alpha i + 1)

@[simp] theorem mem_finiteMultiIndexIic (alpha beta : FiniteMultiIndex d) :
    beta ∈ finiteMultiIndexIic alpha ↔ ∀ i, beta i ≤ alpha i := by
  simp [finiteMultiIndexIic]

def IsMultiIndexDownwardClosed (A : Finset (FiniteMultiIndex d)) : Prop :=
  ∀ (alpha : FiniteMultiIndex d), alpha ∈ A →
    ∀ (beta : FiniteMultiIndex d), (∀ i, beta i ≤ alpha i) → beta ∈ A

def finiteMultiIndexDownwardClosure (A : Finset (FiniteMultiIndex d)) :
    Finset (FiniteMultiIndex d) :=
  A.biUnion finiteMultiIndexIic

@[simp] theorem mem_finiteMultiIndexDownwardClosure
    (A : Finset (FiniteMultiIndex d)) (beta : FiniteMultiIndex d) :
    beta ∈ finiteMultiIndexDownwardClosure A ↔
      ∃ alpha ∈ A, ∀ i, beta i ≤ alpha i := by
  simp [finiteMultiIndexDownwardClosure]

theorem finiteMultiIndexDownwardClosure_isDownwardClosed
    (A : Finset (FiniteMultiIndex d)) :
    IsMultiIndexDownwardClosed (finiteMultiIndexDownwardClosure A) := by
  intro alpha halpha beta hbeta
  obtain ⟨gamma, hgamma, halphaGamma⟩ :=
    (mem_finiteMultiIndexDownwardClosure A alpha).mp halpha
  exact (mem_finiteMultiIndexDownwardClosure A beta).mpr
    ⟨gamma, hgamma, fun i => (hbeta i).trans (halphaGamma i)⟩

theorem subset_finiteMultiIndexDownwardClosure (A : Finset (FiniteMultiIndex d)) :
    A ⊆ finiteMultiIndexDownwardClosure A := by
  intro alpha halpha
  exact (mem_finiteMultiIndexDownwardClosure A alpha).mpr
    ⟨alpha, halpha, fun _ => le_rfl⟩

theorem finiteMultiIndexDownwardClosure_minimal
    (A B : Finset (FiniteMultiIndex d))
    (hAB : A ⊆ B) (hB : IsMultiIndexDownwardClosed B) :
    finiteMultiIndexDownwardClosure A ⊆ B := by
  intro beta hbeta
  obtain ⟨alpha, halpha, hle⟩ :=
    (mem_finiteMultiIndexDownwardClosure A beta).mp hbeta
  exact hB alpha (hAB halpha) beta hle

theorem finiteMultiIndexDownwardClosure_idempotent
    (A : Finset (FiniteMultiIndex d)) :
    finiteMultiIndexDownwardClosure (finiteMultiIndexDownwardClosure A) =
      finiteMultiIndexDownwardClosure A := by
  apply Finset.Subset.antisymm
  · exact finiteMultiIndexDownwardClosure_minimal _ _ (fun _ h => h)
      (finiteMultiIndexDownwardClosure_isDownwardClosed A)
  · exact subset_finiteMultiIndexDownwardClosure _

theorem multiIndexSet_isDownwardClosed (k : ℕ) :
    IsMultiIndexDownwardClosed (multiIndexSet d k) := by
  intro alpha halpha beta hbeta
  rw [multiIndexSet, Finset.mem_filter] at halpha ⊢
  refine ⟨?_, ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hai := Finset.mem_range.mp ((Fintype.mem_piFinset.mp halpha.1) i)
    exact lt_of_le_of_lt (hbeta i) hai
  · exact (Finset.sum_le_sum fun i _ => hbeta i).trans halpha.2

theorem multiIndexSet_downwardClosure (k : ℕ) :
    finiteMultiIndexDownwardClosure (multiIndexSet d k) = multiIndexSet d k := by
  apply Finset.Subset.antisymm
  · exact finiteMultiIndexDownwardClosure_minimal _ _ (fun _ h => h)
      (multiIndexSet_isDownwardClosed k)
  · exact subset_finiteMultiIndexDownwardClosure _

abbrev MultiIndexAtMost (d : Type*) [Fintype d] (k : ℕ) :=
  {alpha : d → ℕ // ∑ i, alpha i ≤ k}

abbrev MultiIndexExact (d : Type*) [Fintype d] (k : ℕ) :=
  {alpha : d → ℕ // ∑ i, alpha i = k}

/-- Slack-coordinate form of stars and bars: order-at-most `k` in `d` variables is exact order
`k` after adding one coordinate. -/
def multiIndexAtMostEquivExact (k : ℕ) :
    MultiIndexAtMost d k ≃ MultiIndexExact (Option d) k where
  toFun alpha :=
    ⟨fun i => match i with
      | none => k - ∑ j, alpha.1 j
      | some j => alpha.1 j,
      by
        rw [Fintype.sum_option]
        simp only
        exact Nat.sub_add_cancel alpha.2⟩
  invFun alpha :=
    ⟨fun i => alpha.1 (some i), by
      change ∑ i, alpha.1 (some i) ≤ k
      have h : alpha.1 none + ∑ i, alpha.1 (some i) = k := by
        simpa only [Fintype.sum_option] using alpha.2
      omega⟩
  left_inv alpha := by
    apply Subtype.ext
    funext i
    rfl
  right_inv alpha := by
    apply Subtype.ext
    funext i
    cases i with
    | some i => rfl
    | none =>
        change k - (∑ i, alpha.1 (some i)) = alpha.1 none
        have h : alpha.1 none + ∑ i, alpha.1 (some i) = k := by
          simpa only [Fintype.sum_option] using alpha.2
        omega

def multiIndexSetEquivAtMost (k : ℕ) :
    {alpha // alpha ∈ multiIndexSet d k} ≃ MultiIndexAtMost d k where
  toFun alpha := ⟨alpha.1, (Finset.mem_filter.mp alpha.2).2⟩
  invFun alpha := ⟨alpha.1, by
    rw [multiIndexSet, Finset.mem_filter]
    refine ⟨?_, alpha.2⟩
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    exact lt_of_le_of_lt
      (Finset.single_le_sum (s := Finset.univ) (f := alpha.1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      (Nat.lt_succ_of_le alpha.2)⟩
  left_inv alpha := by rfl
  right_inv alpha := by rfl

def multiIndexSetEquivSym (k : ℕ) :
    {alpha // alpha ∈ multiIndexSet d k} ≃ Sym (Option d) k :=
  (multiIndexSetEquivAtMost (d := d) k).trans
    ((multiIndexAtMostEquivExact (d := d) k).trans
      (Sym.equivNatSumOfFintype (Option d) k).symm)

/-- Dense order-`k` mixed-derivative count, `choose (d+k) k`. -/
theorem card_multiIndexSet (k : ℕ) :
    (multiIndexSet d k).card = (Fintype.card d + k).choose k := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (multiIndexSetEquivSym (d := d) k)]
  rw [Sym.card_sym_eq_choose]
  simp

def finiteMultiIndexChoose (alpha beta : FiniteMultiIndex d) : ℕ :=
  ∏ i, (alpha i).choose (beta i)

def finiteMultiIndexSub (alpha beta : FiniteMultiIndex d) : FiniteMultiIndex d :=
  fun i => alpha i - beta i

omit [Fintype d] [DecidableEq d] in
@[simp] theorem finiteMultiIndexSub_self (alpha : FiniteMultiIndex d) :
    finiteMultiIndexSub alpha alpha = 0 := by
  funext i
  simp [finiteMultiIndexSub]

def finiteMultiIndexPositiveParts (alpha : FiniteMultiIndex d) :
    Finset (FiniteMultiIndex d) :=
  (finiteMultiIndexIic alpha).erase 0

@[simp] theorem finiteMultiIndexPositiveParts_zero :
    finiteMultiIndexPositiveParts (0 : FiniteMultiIndex d) = ∅ := by
  ext beta
  constructor
  · intro hbeta
    have hne : beta ≠ 0 := Finset.ne_of_mem_erase hbeta
    have hle : ∀ i, beta i ≤ 0 :=
      (mem_finiteMultiIndexIic (0 : FiniteMultiIndex d) beta).mp
        (Finset.mem_of_mem_erase hbeta)
    apply (hne (funext fun i => ?_)).elim
    have hi := hle i
    change beta i ≤ 0 at hi
    exact Nat.eq_zero_of_le_zero hi
  · simp

/-- Recursive multi-index partial Bell polynomial, equation (12) of arXiv:2609.03768. -/
def multiIndexPartialBell (alpha : FiniteMultiIndex d) :
    ℕ → MvPolynomial (FiniteMultiIndex d) ℚ
  | 0 => if alpha = 0 then 1 else 0
  | q + 1 => ((q + 1 : ℚ)⁻¹) •
      ∑ beta ∈ finiteMultiIndexPositiveParts alpha,
        C (finiteMultiIndexChoose alpha beta : ℚ) * X beta *
          multiIndexPartialBell (finiteMultiIndexSub alpha beta) q

@[simp] theorem multiIndexPartialBell_zero (alpha : FiniteMultiIndex d) :
    multiIndexPartialBell alpha 0 = if alpha = 0 then 1 else 0 := rfl

theorem multiIndexPartialBell_succ (alpha : FiniteMultiIndex d) (q : ℕ) :
    multiIndexPartialBell alpha (q + 1) = ((q + 1 : ℚ)⁻¹) •
      ∑ beta ∈ finiteMultiIndexPositiveParts alpha,
        C (finiteMultiIndexChoose alpha beta : ℚ) * X beta *
          multiIndexPartialBell (finiteMultiIndexSub alpha beta) q := rfl

theorem eval_multiIndexPartialBell_succ
    (s : FiniteMultiIndex d → ℚ) (alpha : FiniteMultiIndex d) (q : ℕ) :
    eval s (multiIndexPartialBell alpha (q + 1)) = ((q + 1 : ℚ)⁻¹) *
      ∑ beta ∈ finiteMultiIndexPositiveParts alpha,
        (finiteMultiIndexChoose alpha beta : ℚ) * s beta *
          eval s (multiIndexPartialBell (finiteMultiIndexSub alpha beta) q) := by
  simp [multiIndexPartialBell, Finset.mul_sum]

@[simp] theorem multiIndexPartialBell_zero_succ (q : ℕ) :
    multiIndexPartialBell (0 : FiniteMultiIndex d) (q + 1) = 0 := by
  simp [multiIndexPartialBell]

theorem multiIndexPartialBell_one
    (alpha : FiniteMultiIndex d) (halpha : alpha ≠ 0) :
    multiIndexPartialBell alpha 1 = X alpha := by
  rw [multiIndexPartialBell]
  norm_num only [Nat.cast_zero, zero_add, inv_one, one_smul]
  calc
    ∑ beta ∈ finiteMultiIndexPositiveParts alpha,
        C (finiteMultiIndexChoose alpha beta : ℚ) * X beta *
          multiIndexPartialBell (finiteMultiIndexSub alpha beta) 0 =
        C (finiteMultiIndexChoose alpha alpha : ℚ) * X alpha *
          multiIndexPartialBell (finiteMultiIndexSub alpha alpha) 0 := by
      apply Finset.sum_eq_single alpha
      · intro beta hbeta hne
        have hle : ∀ i, beta i ≤ alpha i :=
          (mem_finiteMultiIndexIic alpha beta).mp (Finset.mem_of_mem_erase hbeta)
        have hsub : finiteMultiIndexSub alpha beta ≠ 0 := by
          intro hz
          apply hne
          funext i
          have hi : alpha i - beta i = 0 := congrFun hz i
          change alpha i - beta i = 0 at hi
          exact Nat.le_antisymm (hle i) (Nat.sub_eq_zero_iff_le.mp hi)
        simp [multiIndexPartialBell, hsub]
      · intro hnot
        exact (hnot (by simp [finiteMultiIndexPositiveParts, halpha])).elim
    _ = X alpha := by
      simp [finiteMultiIndexChoose]

/-- The first nonzero Bell layer satisfies the paper's coefficient-derivative identity. -/
theorem pderiv_multiIndexPartialBell_one
    (alpha : FiniteMultiIndex d)
    (beta : {b // b ∈ finiteMultiIndexPositiveParts alpha}) :
    MvPolynomial.pderiv beta.1 (multiIndexPartialBell alpha 1) =
      C (finiteMultiIndexChoose alpha beta.1 : ℚ) *
        multiIndexPartialBell (finiteMultiIndexSub alpha beta.1) 0 := by
  have hbeta0 : beta.1 ≠ 0 := Finset.ne_of_mem_erase beta.2
  have halpha0 : alpha ≠ 0 := by
    intro ha
    subst alpha
    simpa using beta.2
  rw [multiIndexPartialBell_one alpha halpha0]
  by_cases h : beta.1 = alpha
  · have hleft : MvPolynomial.pderiv beta.1
        (X alpha : MvPolynomial (FiniteMultiIndex d) ℚ) = 1 := by
      simpa only [h] using
        (MvPolynomial.pderiv_X_self alpha :
          MvPolynomial.pderiv alpha
            (X alpha : MvPolynomial (FiniteMultiIndex d) ℚ) = 1)
    have hchoose : finiteMultiIndexChoose alpha beta.1 = 1 := by
      simp [finiteMultiIndexChoose, h]
    have hsub : finiteMultiIndexSub alpha beta.1 = 0 := by
      funext i
      simp [finiteMultiIndexSub, h]
    rw [hleft, hchoose, hsub]
    simp
  · have hle : ∀ i, beta.1 i ≤ alpha i :=
      (mem_finiteMultiIndexIic alpha beta.1).mp (Finset.mem_of_mem_erase beta.2)
    have hsub : finiteMultiIndexSub alpha beta.1 ≠ 0 := by
      intro hz
      apply h
      funext i
      have hi : alpha i - beta.1 i = 0 := congrFun hz i
      change alpha i - beta.1 i = 0 at hi
      exact Nat.le_antisymm (hle i) (Nat.sub_eq_zero_iff_le.mp hi)
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h)]
    simp [multiIndexPartialBell, hsub]

/-- Product seed used for residual terms with any finite number of factors. -/
def fullFactorProduct (r : Type*) [Fintype r] : MvPolynomial r ℚ :=
  ∏ i, X i

theorem pderiv_fullFactorProduct
    {r : Type*} [Fintype r] [DecidableEq r] (i : r) :
    MvPolynomial.pderiv i (fullFactorProduct r) =
      ∏ j ∈ (Finset.univ.erase i), X j := by
  classical
  rw [fullFactorProduct, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
  have hzero : MvPolynomial.pderiv i
      (∏ j ∈ (Finset.univ.erase i), (X j : MvPolynomial r ℚ)) = 0 := by
    have hzero_forall : ∀ (s : Finset r), i ∉ s →
        MvPolynomial.pderiv i (∏ j ∈ s, (X j : MvPolynomial r ℚ)) = 0 := by
      intro s hi
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
          have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j s)
          have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
          rw [Finset.prod_insert hj, MvPolynomial.pderiv_mul,
            MvPolynomial.pderiv_X_of_ne hji, ih his]
          simp
    exact hzero_forall _ (Finset.notMem_erase i _)
  rw [hzero]
  simp

/-- Product-rule seed for an arbitrary finite family of residual factors, equation (11). -/
theorem pderiv_finsetProduct
    {r theta : Type*} [DecidableEq r] (i : theta) (s : Finset r)
    (P : r → MvPolynomial theta ℚ) :
    MvPolynomial.pderiv i (∏ j ∈ s, P j) =
      ∑ j ∈ s, MvPolynomial.pderiv i (P j) * ∏ l ∈ s.erase j, P l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hself : (insert a s).erase a = s := Finset.erase_insert ha
      have hother : ∀ j ∈ s,
          MvPolynomial.pderiv i (P j) * ∏ l ∈ (insert a s).erase j, P l =
            P a * (MvPolynomial.pderiv i (P j) * ∏ l ∈ s.erase j, P l) := by
        intro j hj
        have haj : a ≠ j := fun h => ha (h ▸ hj)
        rw [Finset.erase_insert_of_ne haj,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul, Finset.sum_insert ha, hself,
        Finset.sum_congr rfl hother, ← Finset.mul_sum, ← ih]

theorem pderiv_fullProduct
    {r theta : Type*} [Fintype r] [DecidableEq r] (i : theta)
    (P : r → MvPolynomial theta ℚ) :
    MvPolynomial.pderiv i (∏ j, P j) =
      ∑ j, MvPolynomial.pderiv i (P j) * ∏ l ∈ Finset.univ.erase j, P l := by
  simpa using pderiv_finsetProduct i Finset.univ P

theorem pderiv_half_residual_sq
    {r : Type*} (i : r) (R : MvPolynomial r ℚ) :
    MvPolynomial.pderiv i (C (1 / 2 : ℚ) * R ^ 2) =
      R * MvPolynomial.pderiv i R := by
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow]
  norm_num
  have hc : (C (1 / 2 : ℚ) : MvPolynomial r ℚ) * 2 = 1 := by
    change C (1 / 2 : ℚ) * C (2 : ℚ) = C (1 : ℚ)
    rw [← MvPolynomial.C_mul]
    norm_num
  calc
    C (1 / 2 : ℚ) * (2 * R * MvPolynomial.pderiv i R) =
        (C (1 / 2 : ℚ) * 2) * (R * MvPolynomial.pderiv i R) := by ring
    _ = R * MvPolynomial.pderiv i R := by rw [hc, one_mul]

def polynomialLaplacian (p : MvPolynomial (Sum d d) ℚ) :
    MvPolynomial (Sum d d) ℚ :=
  ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)

def pairedHarmonicPolynomial : MvPolynomial (Sum d d) ℚ :=
  ∑ k, X (Sum.inl k) * X (Sum.inr k)

theorem pairedHarmonicPolynomial_laplacian :
    polynomialLaplacian (d := d) pairedHarmonicPolynomial = 0 := by
  classical
  have hterm (i : Sum d d) (k : d) :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (X (Sum.inl k) * X (Sum.inr k) : MvPolynomial (Sum d d) ℚ)) = 0 := by
    rcases i with i | i
    · by_cases h : i = k
      · subst k
        simp
      · simp [h]
    · by_cases h : i = k
      · subst k
        simp
      · simp [h]
  rw [polynomialLaplacian]
  apply Finset.sum_eq_zero
  intro i _
  rw [pairedHarmonicPolynomial, map_sum, map_sum]
  exact Finset.sum_eq_zero fun k _ => hterm i k

end

end GaloisForLFunctions.HTGeometry
