import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge
import GaloisForLFunctions.HTGeometry.RelationShapeCountable
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

/-!
# Expanding a family jet relation

Evaluating a differential relation of a finite family at a point separates into a power of the
spectral variable and a monomial in the jet variables: the jet index of a family is a sum type, and a
product over a sum type splits.

This is the shape in which a relation meets an expanded evaluation matrix, whose columns are exactly
pairs (jet monomial, power of the spectral variable).
-/

open BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The jet variables of a family, without the spectral variable. -/
abbrev FamilyJetVariables (m n : ℕ) : Type := Fin m × Fin (n + 1)

/-- **Evaluating a family jet relation splits the spectral variable from the jet monomial.** -/
theorem eval_familySplit_eq_sum {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ) (z : ℂ)
    (y : FamilyJetVariables m n → ℂ) :
    MvPolynomial.eval (Sum.elim (fun _ => z) y) P
      = ∑ s ∈ P.support, P.coeff s * (z ^ s (Sum.inl ()) * ∏ k, y k ^ s (Sum.inr k)) := by
  classical
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [Fintype.prod_sum_type]
  congr 1
  simp

/-- The evaluation of a relation at a jet vector of a family, in split form. -/
theorem eval_familyJetVec_eq_sum {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (g : Fin m → ℂ → ℂ) (z : ℂ) :
    MvPolynomial.eval (familyJetVec (n := n) g z) P
      = ∑ s ∈ P.support, P.coeff s *
          (z ^ s (Sum.inl ()) *
            ∏ k : FamilyJetVariables m n, iteratedDeriv (k.2 : ℕ) (g k.1) z ^ s (Sum.inr k)) := by
  have hvec : familyJetVec (n := n) g z
      = Sum.elim (fun _ => z) fun k : FamilyJetVariables m n =>
        iteratedDeriv (k.2 : ℕ) (g k.1) z := by
    funext s
    cases s with
    | inl a => cases a; rfl
    | inr k => rfl
  rw [hvec, eval_familySplit_eq_sum]

/-! ## Splitting and reassembling a monomial -/

/-- The jet part of a family jet monomial. -/
def jetPart {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) : FamilyJetVariables m n →₀ ℕ :=
  s.comapDomain Sum.inr Sum.inr_injective.injOn

@[simp]
theorem jetPart_apply {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) (k : FamilyJetVariables m n) :
    jetPart s k = s (Sum.inr k) := rfl

/-- Reassembling a family jet monomial from its spectral degree and its jet part. -/
def combineMonomial {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ) :
    FamilyJetIndex m n →₀ ℕ :=
  Finsupp.single (Sum.inl ()) d + Finsupp.mapDomain Sum.inr a

@[simp]
theorem combineMonomial_inl {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ) :
    combineMonomial d a (Sum.inl ()) = d := by
  have hnot : (Sum.inl () : FamilyJetIndex m n) ∉ Set.range (Sum.inr : _ → FamilyJetIndex m n) := by
    rintro ⟨k, hk⟩
    simp at hk
  rw [combineMonomial, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_notin_range _ _ hnot, add_zero]

@[simp]
theorem combineMonomial_inr {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ)
    (k : FamilyJetVariables m n) : combineMonomial d a (Sum.inr k) = a k := by
  rw [combineMonomial, Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp), zero_add,
    Finsupp.mapDomain_apply Sum.inr_injective]

/-- A family jet monomial is determined by its spectral degree and its jet part. -/
theorem combineMonomial_jetPart {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) :
    combineMonomial (s (Sum.inl ())) (jetPart s) = s := by
  ext t
  cases t with
  | inl a =>
      cases a
      rw [combineMonomial_inl]
  | inr k =>
      rw [combineMonomial_inr, jetPart_apply]

/-- The split is injective. -/
theorem familyMonomial_injective {m n : ℕ} {s s' : FamilyJetIndex m n →₀ ℕ}
    (hspec : s (Sum.inl ()) = s' (Sum.inl ())) (hjet : jetPart s = jetPart s') : s = s' := by
  rw [← combineMonomial_jetPart s, ← combineMonomial_jetPart s', hspec, hjet]

/-! ## Regrouping into a rectangle of shape data -/

/-- The jet exponents occurring in a relation. -/
def jetExponents {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    Finset (FamilyJetVariables m n →₀ ℕ) := P.support.image jetPart

/-- The largest spectral degree occurring in a relation. -/
def spectralBound {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ) : ℕ :=
  P.support.sup fun s => s (Sum.inl ())

/-- The coefficient of a relation at a (jet exponent, spectral degree) pair. -/
def relationCoeff {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (a : FamilyJetVariables m n →₀ ℕ) (d : ℕ) : ℂ :=
  P.coeff (combineMonomial d a)

/-- **A relation is its coefficient rectangle.**  Evaluating at a point is the double sum over jet
exponents and spectral degrees. -/
theorem eval_familySplit_eq_rectangle {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (z : ℂ) (y : FamilyJetVariables m n → ℂ) :
    MvPolynomial.eval (Sum.elim (fun _ => z) y) P
      = ∑ a ∈ jetExponents P, ∑ d ∈ Finset.range (spectralBound P + 1),
          relationCoeff P a d * (z ^ d * ∏ k, y k ^ a k) := by
  classical
  set g : (FamilyJetVariables m n →₀ ℕ) × ℕ → ℂ := fun p =>
    relationCoeff P p.1 p.2 * (z ^ p.2 * ∏ k, y k ^ p.1 k) with hg
  set Φ : (FamilyJetIndex m n →₀ ℕ) → (FamilyJetVariables m n →₀ ℕ) × ℕ := fun s =>
    (jetPart s, s (Sum.inl ())) with hΦ
  have hsub : P.support.image Φ ⊆ jetExponents P ×ˢ Finset.range (spectralBound P + 1) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    refine Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs, ?_⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := fun s => s (Sum.inl ())) hs
  have hzero : ∀ p ∈ jetExponents P ×ˢ Finset.range (spectralBound P + 1),
      p ∉ P.support.image Φ → g p = 0 := by
    intro p _ hp
    have hcoeff : P.coeff (combineMonomial p.2 p.1) = 0 := by
      by_contra hne
      refine hp (Finset.mem_image.mpr ⟨combineMonomial p.2 p.1, ?_, ?_⟩)
      · exact MvPolynomial.mem_support_iff.mpr hne
      · rw [hΦ]
        have h1 : jetPart (combineMonomial p.2 p.1) = p.1 := by
          ext k
          rw [jetPart_apply, combineMonomial_inr]
        have h2 : (combineMonomial p.2 p.1) (Sum.inl ()) = p.2 := combineMonomial_inl _ _
        simp only [h1, h2]
    rw [hg]
    simp only [relationCoeff, hcoeff, zero_mul]
  rw [← Finset.sum_product', ← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun s hs s' hs' hss => familyMonomial_injective
      (congrArg Prod.snd hss) (congrArg Prod.fst hss)),
    eval_familySplit_eq_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hg, hΦ]
  simp only [relationCoeff, combineMonomial_jetPart, jetPart_apply]

/-- **A nonzero relation has a nonzero coefficient in its rectangle.** -/
theorem exists_relationCoeff_ne_zero {m n : ℕ} {P : MvPolynomial (FamilyJetIndex m n) ℂ}
    (hP : P ≠ 0) : ∃ a ∈ jetExponents P, ∃ d ∈ Finset.range (spectralBound P + 1),
      relationCoeff P a d ≠ 0 := by
  classical
  have hne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hP (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨s, hs⟩ := hne
  refine ⟨jetPart s, Finset.mem_image_of_mem _ hs, s (Sum.inl ()), ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := fun s => s (Sum.inl ())) hs
  · rw [relationCoeff, combineMonomial_jetPart]
    exact MvPolynomial.mem_support_iff.mp hs

/-! ## Folding the jet variables into a single index -/

/-- Folding the (member, order) jet variables into a single index. -/
def foldExponent {m n : ℕ} (a : FamilyJetVariables m n →₀ ℕ) : Fin (m * (n + 1)) →₀ ℕ :=
  Finsupp.equivMapDomain finProdFinEquiv a

theorem foldExponent_apply {m n : ℕ} (a : FamilyJetVariables m n →₀ ℕ)
    (j : Fin (m * (n + 1))) : foldExponent a j = a (finProdFinEquiv.symm j) :=
  Finsupp.equivMapDomain_apply _ _ _

theorem foldExponent_injective {m n : ℕ} :
    Function.Injective (foldExponent (m := m) (n := n)) := by
  intro a b hab
  ext k
  have h := congrArg (fun v : Fin (m * (n + 1)) →₀ ℕ => v (finProdFinEquiv k)) hab
  simpa [foldExponent_apply] using h

/-- The jet monomial is unchanged by the fold. -/
theorem prod_foldExponent {m n : ℕ} (a : FamilyJetVariables m n →₀ ℕ)
    (y : FamilyJetVariables m n → ℂ) :
    ((foldExponent a).prod fun j e => y (finProdFinEquiv.symm j) ^ e)
      = ∏ k, y k ^ a k := by
  rw [foldExponent, Finsupp.prod_equivMapDomain]
  rw [show (a.prod fun k e => y (finProdFinEquiv.symm (finProdFinEquiv k)) ^ e)
      = a.prod fun k e => y k ^ e from
    Finsupp.prod_congr fun k _ => by rw [Equiv.symm_apply_apply]]
  exact Finsupp.prod_fintype a (fun k e => y k ^ e) fun k => pow_zero _

/-! ## Folding along an arbitrary identification -/

/-- Folding the jet variables along any identification with a single index. -/
def foldExponentEquiv {m n D : ℕ} (e : FamilyJetVariables m n ≃ Fin D)
    (a : FamilyJetVariables m n →₀ ℕ) : Fin D →₀ ℕ :=
  Finsupp.equivMapDomain e a

theorem foldExponentEquiv_apply {m n D : ℕ} (e : FamilyJetVariables m n ≃ Fin D)
    (a : FamilyJetVariables m n →₀ ℕ) (j : Fin D) :
    foldExponentEquiv e a j = a (e.symm j) :=
  Finsupp.equivMapDomain_apply _ _ _

theorem foldExponentEquiv_injective {m n D : ℕ} (e : FamilyJetVariables m n ≃ Fin D) :
    Function.Injective (foldExponentEquiv e) := by
  intro a b hab
  ext k
  have h := congrArg (fun v : Fin D →₀ ℕ => v (e k)) hab
  simpa [foldExponentEquiv_apply] using h

/-- The jet monomial is unchanged by any such fold. -/
theorem prod_foldExponentEquiv {m n D : ℕ} (e : FamilyJetVariables m n ≃ Fin D)
    (a : FamilyJetVariables m n →₀ ℕ) (y : FamilyJetVariables m n → ℂ) :
    ((foldExponentEquiv e a).prod fun j p => y (e.symm j) ^ p) = ∏ k, y k ^ a k := by
  rw [foldExponentEquiv, Finsupp.prod_equivMapDomain]
  rw [show (a.prod fun k p => y (e.symm (e k)) ^ p) = a.prod fun k p => y k ^ p from
    Finsupp.prod_congr fun k _ => by rw [Equiv.symm_apply_apply]]
  exact Finsupp.prod_fintype a (fun k p => y k ^ p) fun k => pow_zero _

/-- An identification of the jet variables of a nonempty family with a single index of the form
`Fin (d + 1)`, which is the form a relation shape carries. -/
def familyJetVariablesEquiv (m' n : ℕ) :
    FamilyJetVariables (m' + 1) n ≃ Fin (m' * (n + 1) + n + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-! ## The shape carried by a relation -/

/-- The shape of a relation of a nonempty family: its spectral degree, its jet depth, and the jet
exponents that actually occur. -/
def relationShapeOf {m' n : ℕ} (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ) :
    RelationShape where
  spectralDegree := spectralBound P
  depthPred := m' * (n + 1) + n
  monomialCount := (jetExponents P).card
  exponent := fun i =>
    foldExponentEquiv (familyJetVariablesEquiv m' n)
      (((jetExponents P).equivFin.symm i : {x // x ∈ jetExponents P}) : _)

/-- **The shape of a relation is reduced.**  Its jet exponents are pairwise distinct, since they
enumerate a finite set and the fold is injective. -/
theorem injective_relationShapeOf_exponent {m' n : ℕ}
    (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ) :
    Function.Injective (relationShapeOf P).exponent := by
  intro i j hij
  have h := foldExponentEquiv_injective (familyJetVariablesEquiv m' n) hij
  exact (jetExponents P).equivFin.symm.injective (Subtype.ext h)

/-! ## The coefficient vector of a relation -/

/-- The coefficient vector of a relation, indexed by the columns of its shape's evaluation
matrix. -/
def relationCoeffVector {m' n : ℕ} (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ) :
    Fin (relationShapeOf P).monomialCount ×
      Fin ((relationShapeOf P).spectralDegree + 1) → ℂ :=
  fun p =>
    relationCoeff P (((jetExponents P).equivFin.symm p.1 : {x // x ∈ jetExponents P}) : _)
      (p.2 : ℕ)

/-- **A nonzero relation has a nonzero coefficient vector.** -/
theorem relationCoeffVector_ne_zero {m' n : ℕ} {P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ}
    (hP : P ≠ 0) : relationCoeffVector P ≠ 0 := by
  classical
  obtain ⟨a, ha, d, hd, hne⟩ := exists_relationCoeff_ne_zero hP
  intro hzero
  have hval := congrFun hzero
    ((jetExponents P).equivFin ⟨a, ha⟩,
      ⟨d, show d < spectralBound P + 1 from Finset.mem_range.mp hd⟩)
  rw [relationCoeffVector] at hval
  simp only [Equiv.symm_apply_apply] at hval
  exact hne hval

/-! ## The relation as a row of the evaluation matrix -/

/-- **A relation is its coefficients against the entries of an evaluation matrix row.**  Each term is
a power of the node times the jet monomial in the folded coordinates -- exactly the entry of
`expandedDifferentialEvaluationMatrix` in that column. -/
theorem sum_rectangle_eq_eval {m' n D : ℕ} (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ)
    (e : FamilyJetVariables (m' + 1) n ≃ Fin D) (z : ℂ)
    (y : FamilyJetVariables (m' + 1) n → ℂ) :
    ∑ a ∈ jetExponents P, ∑ d ∈ Finset.range (spectralBound P + 1),
        (z ^ d * ((foldExponentEquiv e a).prod fun k p => y (e.symm k) ^ p)) * relationCoeff P a d
      = MvPolynomial.eval (Sum.elim (fun _ => z) y) P := by
  rw [eval_familySplit_eq_rectangle]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [prod_foldExponentEquiv]
  ring

/-- **Reindexing a rectangle sum.**  A sum over `Fin s.card × Fin (q+1)`, with the first coordinate
read through the canonical enumeration of a finite set, is the double sum over that set and the range
of degrees.  Keeping this step separate from any structure projection is what keeps the `Fintype`
instances of the two sides aligned. -/
theorem sum_fin_card_prod_eq {α : Type*} [DecidableEq α] (s : Finset α) (q : ℕ) (f : α → ℕ → ℂ) :
    ∑ p : Fin s.card × Fin (q + 1), f ((s.equivFin.symm p.1 : {x // x ∈ s}) : α) (p.2 : ℕ)
      = ∑ a ∈ s, ∑ d ∈ Finset.range (q + 1), f a d := by
  rw [Fintype.sum_prod_type,
    ← Finset.sum_coe_sort s fun a => ∑ d ∈ Finset.range (q + 1), f a d,
    ← Equiv.sum_comp s.equivFin.symm fun a : {x // x ∈ s} =>
      ∑ d ∈ Finset.range (q + 1), f (a : α) d]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range
    (fun d => f ((s.equivFin.symm i : {x // x ∈ s}) : α) d) (q + 1)

/-- **A relation is the evaluation matrix applied to its coefficient vector.**  At each row the
matrix product is the value of the relation at that row's node and jets. -/
theorem mulVec_relationCoeffVector_eq_eval {m' n : ℕ}
    (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ)
    {row : Type} [Fintype row] [DecidableEq row] (znodes : row → ℂ)
    (y : row → FamilyJetVariables (m' + 1) n → ℂ) (b : row) :
    (expandedDifferentialEvaluationMatrix (relationShapeOf P).spectralDegree
        ((relationShapeOf P).depthPred + 1) znodes (relationShapeOf P).exponent
        (fun p => y p.1 ((familyJetVariablesEquiv m' n).symm p.2))).mulVec
        (relationCoeffVector P) b
      = MvPolynomial.eval (Sum.elim (fun _ => znodes b) (y b)) P := by
  classical
  have h1 := sum_rectangle_eq_eval P (familyJetVariablesEquiv m' n) (znodes b) (y b)
  have h2 := sum_fin_card_prod_eq (jetExponents P) (spectralBound P)
    fun a d => (znodes b ^ d *
      ((foldExponentEquiv (familyJetVariablesEquiv m' n) a).prod
        fun k p => y b ((familyJetVariablesEquiv m' n).symm k) ^ p)) * relationCoeff P a d
  rw [← h1, ← h2]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [expandedDifferentialEvaluationMatrix_apply]
  rfl

end

end GaloisForLFunctions.HTGeometry
