import GaloisForLFunctions.HTGeometry.AffineJetPacketResidual

/-!
# Determinant avoidance is differential independence

A differential relation with polynomial coefficients among the affine pullbacks of one source
expands into a finite complex-linear combination of decorated monomials: a coordinate monomial
times a monomial in finitely many mixed jets.  Those data are exactly a finite decorated pattern,
so a source avoiding the pattern determinant makes the associated square evaluation matrix
invertible.  A relation vanishing identically therefore has a vanishing coefficient vector, i.e.
the relation itself is zero.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Jet variables of a differential relation on `n` affine frames. -/
abbrev RelationJetVar (d n : ℕ) := Fin n × (Fin d →₀ ℕ)

/-- The value of a differential relation with polynomial coefficients at a source and a point. -/
def affineJetRelationValue {d n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) (z : Fin d → ℂ) : ℂ :=
  eval₂ (eval z) (fun q => affineMultiIndexJetEvalCLM (frame q.1) z q.2 f) P

/-- A total order bound strictly exceeding every jet degree occurring in a relation. -/
def relationJetOrder {d n : ℕ}
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) : ℕ :=
  1 + P.support.sup fun m => m.support.sup fun q => Finsupp.degree q.2

theorem degree_lt_relationJetOrder {d n : ℕ}
    {P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)}
    {m : RelationJetVar d n →₀ ℕ} (hm : m ∈ P.support)
    {q : RelationJetVar d n} (hq : q ∈ m.support) :
    Finsupp.degree q.2 < relationJetOrder P := by
  have h1 : Finsupp.degree q.2 ≤ m.support.sup fun q => Finsupp.degree q.2 :=
    Finset.le_sup (f := fun q : RelationJetVar d n => Finsupp.degree q.2) hq
  have h2 : (m.support.sup fun q => Finsupp.degree q.2) ≤
      P.support.sup fun m => m.support.sup fun q => Finsupp.degree q.2 :=
    Finset.le_sup (f := fun m : RelationJetVar d n →₀ ℕ =>
      m.support.sup fun q : RelationJetVar d n => Finsupp.degree q.2) hm
  simp only [relationJetOrder]
  omega

/-- The bounded jet variables of a pattern inject into the relation jet variables. -/
def relationJetEmbedding (d n N : ℕ) :
    (Σ _ : Fin n, MultiIndexBelow d N) ↪ RelationJetVar d n where
  toFun s := (s.1, s.2.1)
  inj' := by
    rintro ⟨i, ⟨β, hβ⟩⟩ ⟨j, ⟨γ, hγ⟩⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
    rfl

@[simp] theorem relationJetEmbedding_apply (d n N : ℕ) (s : Σ _ : Fin n, MultiIndexBelow d N) :
    relationJetEmbedding d n N s = (s.1, s.2.1) := rfl

/-- The distinct decorated monomials occurring in a relation. -/
def relationDecoratedSupport {d n : ℕ}
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) :
    Finset ((Fin d →₀ ℕ) × ((RelationJetVar d n) →₀ ℕ)) :=
  P.support.biUnion fun m => (P.coeff m).support.image fun α => (α, m)

theorem mem_relationDecoratedSupport {d n : ℕ}
    {P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)}
    {p : (Fin d →₀ ℕ) × ((RelationJetVar d n) →₀ ℕ)} :
    p ∈ relationDecoratedSupport P ↔
      p.2 ∈ P.support ∧ p.1 ∈ (P.coeff p.2).support := by
  constructor
  · intro hp
    rw [relationDecoratedSupport, Finset.mem_biUnion] at hp
    obtain ⟨m, hm, hp⟩ := hp
    rw [Finset.mem_image] at hp
    obtain ⟨α, hα, rfl⟩ := hp
    exact ⟨hm, hα⟩
  · intro hp
    rw [relationDecoratedSupport, Finset.mem_biUnion]
    exact ⟨p.2, hp.1, Finset.mem_image.mpr ⟨p.1, hp.2, rfl⟩⟩

theorem relationDecoratedSupport_nonempty {d n : ℕ}
    {P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)} (hP : P ≠ 0) :
    (relationDecoratedSupport P).Nonempty := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hP
  have hcoeff : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  obtain ⟨α, hα⟩ := MvPolynomial.support_nonempty.mpr hcoeff
  exact ⟨(α, m), mem_relationDecoratedSupport.mpr ⟨hm, hα⟩⟩

/-- A relation is the finite complex-linear combination of its decorated monomials. -/
theorem affineJetRelationValue_eq_sum {d n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) (z : Fin d → ℂ) :
    affineJetRelationValue frame f P z =
      ∑ p ∈ relationDecoratedSupport P,
        coeff p.1 (coeff p.2 P) * (p.1.prod fun i k => z i ^ k) *
          (p.2.prod fun q k => affineMultiIndexJetEvalCLM (frame q.1) z q.2 f ^ k) := by
  classical
  rw [affineJetRelationValue, eval₂_eq, relationDecoratedSupport]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).1)]
    rw [eval_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α hα => rfl
  · intro m hm m' hm' hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro p ⟨α, hα, rfl⟩ ⟨α', hα', h⟩
    exact hne (congrArg Prod.snd h).symm

/-- Every jet variable occurring in a decorated monomial of a relation is a bounded pattern jet
variable. -/
theorem support_subset_range_relationJetEmbedding {d n : ℕ}
    {P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)}
    {p : (Fin d →₀ ℕ) × ((RelationJetVar d n) →₀ ℕ)} (hp : p ∈ relationDecoratedSupport P) :
    ↑(p.2.support) ⊆ Set.range (relationJetEmbedding d n (relationJetOrder P)) := by
  intro q hq
  exact ⟨⟨q.1, ⟨q.2, degree_lt_relationJetOrder (mem_relationDecoratedSupport.mp hp).1
    (Finset.mem_coe.mp hq)⟩⟩, rfl⟩

/-- The finite decorated pattern carried by a differential relation. -/
def relationPattern {d : ℕ} {Λ : Type*} {n : ℕ} (lab : Fin n → Λ) (hlab : Function.Injective lab)
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) :
    FiniteMultivariateAffineJetPattern Λ d where
  frameCount := n
  frameCode := lab
  orders := fun _ => relationJetOrder P
  monomialCount := (relationDecoratedSupport P).card
  coordinateExponent := fun b => ((relationDecoratedSupport P).equivFin.symm b).1.1
  jetExponent := fun b =>
    Finsupp.comapDomain (relationJetEmbedding d n (relationJetOrder P))
      ((relationDecoratedSupport P).equivFin.symm b).1.2
      (Set.injOn_of_injective (relationJetEmbedding d n (relationJetOrder P)).injective)
  frameCode_injective := hlab
  decoratedExponent_injective := by
    intro b b' hbb
    dsimp only at hbb
    have h1 := congrArg Prod.fst hbb
    have h2 := congrArg Prod.snd hbb
    dsimp only at h1 h2
    have hrec : ∀ b : Fin (relationDecoratedSupport P).card,
        Finsupp.embDomain (relationJetEmbedding d n (relationJetOrder P))
          (Finsupp.comapDomain (relationJetEmbedding d n (relationJetOrder P))
            ((relationDecoratedSupport P).equivFin.symm b).1.2
            (Set.injOn_of_injective
              (relationJetEmbedding d n (relationJetOrder P)).injective)) =
          ((relationDecoratedSupport P).equivFin.symm b).1.2 := fun b =>
      Finsupp.embDomain_comapDomain
        (support_subset_range_relationJetEmbedding
          ((relationDecoratedSupport P).equivFin.symm b).2)
    have h3 : ((relationDecoratedSupport P).equivFin.symm b).1.2 =
        ((relationDecoratedSupport P).equivFin.symm b').1.2 := by
      rw [← hrec b, ← hrec b', h2]
    have h4 : ((relationDecoratedSupport P).equivFin.symm b) =
        ((relationDecoratedSupport P).equivFin.symm b') :=
      Subtype.ext (Prod.ext h1 h3)
    exact (relationDecoratedSupport P).equivFin.symm.injective h4

/-- **Determinant avoidance is differential independence.**  A source avoiding every finite
decorated determinant of a noncolliding countable affine family satisfies no nonzero differential
relation with polynomial coefficients among its pullbacks along distinct frames. -/
theorem exists_affineJetRelationValue_ne_zero {d : ℕ} (hd : 0 < d) {Λ : Type*} [Countable Λ]
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    {f : MultivariateEntire d} (hf : f ∈ affineJetPacketGenericSet hd frame hframe)
    {n : ℕ} (lab : Fin n → Λ) (hlab : Function.Injective lab)
    {P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)} (hP : P ≠ 0) :
    ∃ z : Fin d → ℂ, affineJetRelationValue (fun i => frame (lab i)) f P z ≠ 0 := by
  classical
  by_contra hcon
  have hzero : ∀ z : Fin d → ℂ, affineJetRelationValue (fun i => frame (lab i)) f P z = 0 :=
    fun z => not_not.mp fun h => hcon ⟨z, h⟩
  set S := relationDecoratedSupport P with hS
  set pat := relationPattern lab hlab P with hpat
  set wit := affineJetPacketWitness hd frame hframe pat with hwit
  set enum := S.equivFin.symm with henum
  have hdet := hf pat
  rw [multivariateAffinePatternDefect, Set.mem_setOf_eq,
    eval_multivariateCoefficientPatternDeterminant] at hdet
  set base := wit.base with hbase
  set obs := multivariateAffinePatternObservationCLM frame pat base f with hobs
  set M : Matrix (Fin S.card) (Fin S.card) ℂ := Matrix.of fun a b =>
    (pat.coordinateExponent b).prod (fun i k => base a i ^ k) *
      (pat.jetExponent b).prod (fun s k => obs (a, s) ^ k) with hM
  set c : Fin S.card → ℂ := fun b => coeff (enum b).1.1 (coeff (enum b).1.2 P) with hc
  have hjet : ∀ (a b : Fin S.card),
      (pat.jetExponent b).prod (fun s k => obs (a, s) ^ k) =
        ((enum b).1.2).prod (fun q k =>
          affineMultiIndexJetEvalCLM (frame (lab q.1)) (base a) q.2 f ^ k) := by
    intro a b
    have hemb : Finsupp.embDomain (relationJetEmbedding d n (relationJetOrder P))
        (pat.jetExponent b) = (enum b).1.2 :=
      Finsupp.embDomain_comapDomain
        (support_subset_range_relationJetEmbedding (enum b).2)
    rw [← hemb, Finsupp.prod_embDomain]
    rfl
  have hmul : M.mulVec c = 0 := by
    funext a
    have hz := hzero (base a)
    rw [affineJetRelationValue_eq_sum] at hz
    show ∑ b : Fin S.card, M a b * c b = 0
    have hreindex : ∑ p ∈ S, coeff p.1 (coeff p.2 P) *
          (p.1.prod fun i k => base a i ^ k) *
          (p.2.prod fun q k =>
            affineMultiIndexJetEvalCLM (frame (lab q.1)) (base a) q.2 f ^ k) =
        ∑ b : Fin S.card, M a b * c b := by
      rw [← Finset.sum_coe_sort S]
      rw [← Equiv.sum_comp enum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hce : pat.coordinateExponent b = (enum b).1.1 := rfl
      simp only [hM, hc, Matrix.of_apply, hce]
      rw [hjet a b]
      ring
    rw [← hreindex]
    exact hz
  have hczero : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  obtain ⟨p₀, hp₀⟩ := relationDecoratedSupport_nonempty hP
  have hb₀ : c (S.equivFin ⟨p₀, hp₀⟩) ≠ 0 := by
    have : enum (S.equivFin ⟨p₀, hp₀⟩) = ⟨p₀, hp₀⟩ := S.equivFin.symm_apply_apply _
    rw [hc]
    simp only [this]
    exact MvPolynomial.mem_support_iff.mp (mem_relationDecoratedSupport.mp hp₀).2
  exact hb₀ (by rw [hczero]; rfl)

end

end GaloisForLFunctions.HTGeometry
