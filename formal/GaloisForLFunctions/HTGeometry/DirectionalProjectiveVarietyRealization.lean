import GaloisForLFunctions.HTGeometry.AlgebraicIndependentDisjointLinearForms
import GaloisForLFunctions.HTGeometry.DirectionalJetWordPolynomial
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Ordered-word realization of nonlinear projective law horizons

The law pencil remains linear, but its noncommuting ordered words can store arbitrary homogeneous
equations.  A free prefix tree propagates one observable until a prescribed depth; at that depth
the tree collapses onto terminal generators with arbitrary word coefficients.  The resulting top
directional jet is exactly the corresponding family of homogeneous law polynomials.

This module constructs the rational differential field and proves the exact jet formulas.  The
finite-packet algebraic-independence theorem below is the converse engine for the classification
of finite-order directional dependence loci.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι] [Fintype η]

/-- A length-indexed noncommutative word. -/
abbrev ProjectiveWordState (ι : Type*) := Σ n : ℕ, Fin n → ι

/-- Prefix-tree generators together with independent terminal generators. -/
abbrev ProjectiveWordGenerator (ι η : Type*) := ProjectiveWordState ι ⊕ η

/-- The free ordered-word polynomial algebra. -/
abbrev ProjectiveWordPolynomial (K ι η : Type*) [Field K] :=
  MvPolynomial (ProjectiveWordGenerator ι η) K

/-- Its rational function field. -/
abbrev ProjectiveWordField (K ι η : Type*) [Field K] :=
  FractionRing (ProjectiveWordPolynomial K ι η)

/-- Canonical embedding of the free word algebra into its fraction field. -/
def projectiveWordEmbedding :
    ProjectiveWordPolynomial K ι η →ₐ[K] ProjectiveWordField K ι η :=
  IsScalarTower.toAlgHom K (ProjectiveWordPolynomial K ι η)
    (ProjectiveWordField K ι η)

omit [Fintype ι] [Fintype η] in
theorem projectiveWordEmbedding_injective :
    Function.Injective (projectiveWordEmbedding (K := K) (ι := ι) (η := η)) :=
  IsFractionRing.injective (ProjectiveWordPolynomial K ι η)
    (ProjectiveWordField K ι η)

omit [Fintype ι] [Fintype η] in
@[simp]
theorem projectiveWordEmbedding_apply (p : ProjectiveWordPolynomial K ι η) :
    projectiveWordEmbedding (K := K) (ι := ι) (η := η) p =
      algebraMap (ProjectiveWordPolynomial K ι η)
        (ProjectiveWordField K ι η) p := rfl

/-- The free coordinate attached to an ordered prefix word. -/
def projectiveWordAncestor (n : ℕ) (w : Fin n → ι) : ProjectiveWordField K ι η :=
  projectiveWordEmbedding (K := K) (ι := ι) (η := η)
    (MvPolynomial.X (Sum.inl ⟨n, w⟩))

/-- An independent terminal coordinate storing one homogeneous equation. -/
def projectiveWordTerminal (j : η) : ProjectiveWordField K ι η :=
  projectiveWordEmbedding (K := K) (ι := ι) (η := η)
    (MvPolynomial.X (Sum.inr j))

/-- The root observable, before any law direction has been selected. -/
def projectiveWordRoot : ProjectiveWordField K ι η :=
  projectiveWordAncestor (K := K) (η := η) 0 Fin.elim0

/-- The homogeneous law polynomial obtained by commutatively collapsing ordered-word
coefficients at depth `n`. -/
def projectiveWordPolynomialValue
    (a : η → ProjectiveWordState ι → K) (j : η) (c : ι → K) (n : ℕ) : K :=
  ∑ w : Fin n → ι, (∏ r, c (w r)) * a j ⟨n, w⟩

/-- The actual homogeneous law-coordinate polynomial encoded by one terminal sector. -/
def projectiveWordLawPolynomial
    (a : η → ProjectiveWordState ι → K) (j : η) (n : ℕ) : MvPolynomial ι K :=
  ∑ w : Fin n → ι,
    MvPolynomial.C (a j ⟨n, w⟩) * ∏ r, MvPolynomial.X (w r)

omit [Fintype η] in
/-- Evaluation of the encoded law polynomial is the terminal coefficient used by the differential
realization. -/
@[simp]
theorem eval_projectiveWordLawPolynomial
    (a : η → ProjectiveWordState ι → K) (j : η) (c : ι → K) (n : ℕ) :
    MvPolynomial.eval c (projectiveWordLawPolynomial a j n) =
      projectiveWordPolynomialValue a j c n := by
  simp [projectiveWordLawPolynomial, projectiveWordPolynomialValue, mul_comm]

omit [Fintype η] in
/-- Every encoded terminal law is homogeneous of the collapse depth. -/
theorem projectiveWordLawPolynomial_isHomogeneous
    (a : η → ProjectiveWordState ι → K) (j : η) (n : ℕ) :
    MvPolynomial.IsHomogeneous (projectiveWordLawPolynomial a j n) n := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro w hw
  have hp : MvPolynomial.IsHomogeneous
      (∏ r, MvPolynomial.X (w r) : MvPolynomial ι K) (∑ _ : Fin n, 1) :=
    MvPolynomial.IsHomogeneous.prod Finset.univ (fun r ↦ MvPolynomial.X (w r))
      (fun _ ↦ 1) (fun r _ ↦ MvPolynomial.isHomogeneous_X K (w r))
  simpa using (MvPolynomial.isHomogeneous_C ι (a j ⟨n, w⟩)).mul hp

/-- Polynomial-level prefix-tree derivation.  Prefixes propagate freely below depth `d`; the
next step at depth `d` collapses onto the prescribed terminal linear combination. -/
def projectiveWordPolynomialDerivation
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) :
    Derivation K (ProjectiveWordPolynomial K ι η) (ProjectiveWordField K ι η) :=
  MvPolynomial.mkDerivation K fun g ↦
    match g with
    | Sum.inl ⟨n, w⟩ =>
        if n + 1 < d then
          algebraMap (ProjectiveWordPolynomial K ι η) (ProjectiveWordField K ι η)
            (MvPolynomial.X (Sum.inl ⟨n + 1, Fin.cons i w⟩))
        else if n + 1 = d then
          algebraMap (ProjectiveWordPolynomial K ι η) (ProjectiveWordField K ι η)
            (∑ j, MvPolynomial.C (a j ⟨n + 1, Fin.cons i w⟩) *
              MvPolynomial.X (Sum.inr j))
        else 0
    | Sum.inr _ => 0

/-- Quotient-rule extension to the rational word field. -/
def projectiveWordDerivation
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) :
    Derivation K (ProjectiveWordField K ι η) (ProjectiveWordField K ι η) :=
  fractionRingDerivation (projectiveWordPolynomialDerivation a d i)

omit [Fintype ι] in
/-- Below the collapse depth, a basis derivation prepends its law letter to the free word. -/
theorem projectiveWordDerivation_ancestor_of_lt
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (i : ι)
    (w : Fin n → ι) (h : n + 1 < d) :
    projectiveWordDerivation a d i (projectiveWordAncestor (K := K) (η := η) n w) =
      projectiveWordAncestor (K := K) (η := η) (n + 1) (Fin.cons i w) := by
  rw [projectiveWordDerivation, projectiveWordAncestor, projectiveWordEmbedding_apply,
    fractionRingDerivation_algebraMap, projectiveWordPolynomialDerivation,
    MvPolynomial.mkDerivation_X]
  simp [h, projectiveWordAncestor]

omit [Fintype ι] in
/-- At the collapse depth, a basis derivation writes the arbitrary ordered-word coefficients
onto the terminal coordinates. -/
theorem projectiveWordDerivation_ancestor_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (i : ι)
    (w : Fin n → ι) (h : n + 1 = d) :
    projectiveWordDerivation a d i (projectiveWordAncestor (K := K) (η := η) n w) =
      ∑ j, a j ⟨n + 1, Fin.cons i w⟩ • projectiveWordTerminal (K := K) (ι := ι) j := by
  rw [projectiveWordDerivation, projectiveWordAncestor, projectiveWordEmbedding_apply,
    fractionRingDerivation_algebraMap, projectiveWordPolynomialDerivation,
    MvPolynomial.mkDerivation_X]
  simp [h, projectiveWordTerminal, Algebra.smul_def,
    IsScalarTower.algebraMap_apply K (ProjectiveWordPolynomial K ι η)
      (ProjectiveWordField K ι η)]

omit [Fintype ι] in
/-- Terminal coordinates are stationary after the prescribed finite packet. -/
@[simp]
theorem projectiveWordDerivation_terminal
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) (j : η) :
    projectiveWordDerivation a d i (projectiveWordTerminal (K := K) (ι := ι) j) = 0 := by
  rw [projectiveWordDerivation, projectiveWordTerminal, projectiveWordEmbedding_apply,
    fractionRingDerivation_algebraMap, projectiveWordPolynomialDerivation,
    MvPolynomial.mkDerivation_X]

omit [Fintype ι] in
/-- Every ordered derivative below the collapse depth is the matching free prefix coordinate. -/
theorem directionalWordDerivative_projectiveWordRoot_of_lt
    (a : η → ProjectiveWordState ι → K) (d : ℕ) :
    ∀ (n : ℕ) (_h : n < d) (w : Fin n → ι),
      directionalWordDerivative (projectiveWordDerivation a d)
          (projectiveWordRoot (K := K) (ι := ι) (η := η)) w =
        projectiveWordAncestor (K := K) (η := η) n w := by
  intro n
  induction n with
  | zero =>
      intro h w
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      simp [hw, directionalWordDerivative, projectiveWordRoot]
  | succ n ih =>
      intro h w
      rw [← Fin.cons_self_tail w, directionalWordDerivative_cons,
        ih (by omega) (Fin.tail w)]
      exact projectiveWordDerivation_ancestor_of_lt a d n (w 0) (Fin.tail w) h

omit [Fintype ι] in
/-- At the collapse step, every ordered derivative is the prescribed terminal linear form. -/
theorem directionalWordDerivative_projectiveWordRoot_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n + 1 = d)
    (w : Fin (n + 1) → ι) :
    directionalWordDerivative (projectiveWordDerivation a d)
        (projectiveWordRoot (K := K) (ι := ι) (η := η)) w =
      ∑ j, a j ⟨n + 1, w⟩ • projectiveWordTerminal (K := K) (ι := ι) j := by
  rw [← Fin.cons_self_tail w, directionalWordDerivative_cons,
    directionalWordDerivative_projectiveWordRoot_of_lt a d n (by omega) (Fin.tail w),
    projectiveWordDerivation_ancestor_of_eq a d n (w 0) (Fin.tail w) h]

omit [Fintype ι] [Fintype η] in
/-- The complete free generator family remains algebraically independent in the rational word
field. -/
theorem projectiveWordGenerator_algebraicIndependent :
    AlgebraicIndependent K
      (fun g : ProjectiveWordGenerator ι η ↦
        projectiveWordEmbedding (K := K) (ι := ι) (η := η) (MvPolynomial.X g)) := by
  simpa only [Function.comp_apply] using
    (MvPolynomial.algebraicIndependent_X (ProjectiveWordGenerator ι η) K).map'
      (projectiveWordEmbedding_injective (K := K) (ι := ι) (η := η))

/-- The `n`-th directional jet below the collapse depth is the nonzero word-block linear form
with monomial law coefficients. -/
theorem directionalJet_projectiveWordRoot_of_lt
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n < d) (c : ι → K) :
    directionalJet (projectiveWordDerivation a d) c n
        (projectiveWordRoot (K := K) (ι := ι) (η := η)) =
      ∑ w : Fin n → ι, (∏ r, c (w r)) •
        projectiveWordAncestor (K := K) (η := η) n w := by
  rw [directionalJet_eq_sum_words]
  simp_rw [directionalWordDerivative_projectiveWordRoot_of_lt a d n h]

/-- **Arbitrary homogeneous top jet.**  At the collapse depth, the terminal coefficients are
exactly the prescribed homogeneous law polynomials. -/
theorem directionalJet_projectiveWordRoot_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n + 1 = d) (c : ι → K) :
    directionalJet (projectiveWordDerivation a d) c (n + 1)
        (projectiveWordRoot (K := K) (ι := ι) (η := η)) =
      ∑ j, projectiveWordPolynomialValue a j c (n + 1) •
        projectiveWordTerminal (K := K) (ι := ι) j := by
  rw [directionalJet_eq_sum_words]
  simp_rw [directionalWordDerivative_projectiveWordRoot_of_eq a d n h]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp [projectiveWordPolynomialValue, smul_smul, Finset.sum_smul]

/-- The first `n + 1` free jets together with the collapse jet. -/
def projectiveFiniteJetPacket
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K) :
    Fin (n + 1) ⊕ Unit → ProjectiveWordField K ι η
  | Sum.inl r => directionalJet (projectiveWordDerivation a (n + 1)) c r
      (projectiveWordRoot (K := K) (ι := ι) (η := η))
  | Sum.inr _ => directionalJet (projectiveWordDerivation a (n + 1)) c (n + 1)
      (projectiveWordRoot (K := K) (ι := ι) (η := η))

/-- **Finite projective realization, independence direction.**  At a nonzero law direction, if at
least one prescribed homogeneous top coefficient survives, the entire finite packet is
algebraically independent. -/
theorem projectiveFiniteJetPacket_algebraicIndependent
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0)
    (hP : ∃ j, projectiveWordPolynomialValue a j c (n + 1) ≠ 0) :
    AlgebraicIndependent K (projectiveFiniteJetPacket a n c) := by
  classical
  let τ := Fin (n + 1) ⊕ Unit
  let σ : τ → Type v :=
    Sum.elim (fun r : Fin (n + 1) ↦ Fin (r : ℕ) → ι) (fun _ ↦ η)
  letI : ∀ t, Fintype (σ t) := fun t ↦ by
    cases t <;> dsimp [σ] <;> infer_instance
  letI : ∀ t, DecidableEq (σ t) := fun t ↦ by
    cases t <;> dsimp [σ] <;> infer_instance
  let prefixEmbedding :
      (Σ r : Fin (n + 1), Fin (r : ℕ) → ι) ↪ ProjectiveWordState ι :=
    ⟨Sigma.map (fun r : Fin (n + 1) ↦ (r : ℕ)) (fun _ w ↦ w),
      Fin.val_injective.sigma_map (fun _ ↦ fun _ _ h ↦ h)⟩
  let terminalEquiv : (Σ _ : Unit, η) ≃ η := Equiv.uniqueSigma (fun _ : Unit ↦ η)
  let generatorEmbedding : (Σ t, σ t) ↪ ProjectiveWordGenerator ι η :=
    (Equiv.sumSigmaDistrib σ).toEmbedding.trans
      (Function.Embedding.sumMap prefixEmbedding terminalEquiv.toEmbedding)
  let x : (Σ t, σ t) → ProjectiveWordField K ι η := fun p ↦
    projectiveWordEmbedding (K := K) (ι := ι) (η := η)
      (MvPolynomial.X (generatorEmbedding p))
  have hx : AlgebraicIndependent K x := by
    simpa [x, Function.comp_def] using
      (projectiveWordGenerator_algebraicIndependent (K := K) (ι := ι) (η := η)).comp
        generatorEmbedding generatorEmbedding.injective
  let u : ∀ t, σ t → K := fun t ↦
    match t with
    | Sum.inl r => fun w ↦ ∏ q, c (w q)
    | Sum.inr _ => fun j ↦ projectiveWordPolynomialValue a j c (n + 1)
  have hu : ∀ t, ∃ s, u t s ≠ 0 := by
    intro t
    cases t with
    | inl r =>
        obtain ⟨i, hi⟩ := hc
        refine ⟨fun _ ↦ i, ?_⟩
        simpa [u] using pow_ne_zero (r : ℕ) hi
    | inr z =>
        obtain ⟨j, hj⟩ := hP
        exact ⟨j, by simpa [u] using hj⟩
  have hforms := algebraicIndependent_disjointBlockLinearForms u hu x hx
  have hpacket :
      (fun t ↦ ∑ s, algebraMap K (ProjectiveWordField K ι η) (u t s) * x ⟨t, s⟩) =
        projectiveFiniteJetPacket a n c := by
    funext t
    cases t with
    | inl r =>
        simpa [projectiveFiniteJetPacket, σ, u, x, generatorEmbedding, prefixEmbedding,
          terminalEquiv, Algebra.smul_def] using
          (directionalJet_projectiveWordRoot_of_lt a (n + 1) (r : ℕ) r.isLt c).symm
    | inr z =>
        have hz : z = () := Subsingleton.elim _ _
        subst z
        simpa [projectiveFiniteJetPacket, σ, u, x, generatorEmbedding, prefixEmbedding,
          terminalEquiv, Algebra.smul_def] using
          (directionalJet_projectiveWordRoot_of_eq a (n + 1) n rfl c).symm
  rw [← hpacket]
  exact hforms

/-- **Exact finite nonlinear horizon theorem.**  At every nonzero law direction, the constructed
finite jet packet is algebraically independent exactly when at least one prescribed homogeneous
equation is nonzero. -/
theorem projectiveFiniteJetPacket_algebraicIndependent_iff
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    AlgebraicIndependent K (projectiveFiniteJetPacket a n c) ↔
      ∃ j, projectiveWordPolynomialValue a j c (n + 1) ≠ 0 := by
  constructor
  · intro hindependent
    by_contra hnone
    push Not at hnone
    have htop : projectiveFiniteJetPacket a n c (Sum.inr ()) = 0 := by
      rw [projectiveFiniteJetPacket,
        directionalJet_projectiveWordRoot_of_eq a (n + 1) n rfl c]
      simp [hnone]
    exact hindependent.ne_zero (Sum.inr ()) htop
  · exact projectiveFiniteJetPacket_algebraicIndependent a n c hc

/-- Dependence is therefore the simultaneous zero locus of the arbitrary homogeneous terminal
equations. -/
theorem projectiveFiniteJetPacket_dependent_iff
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    (¬ AlgebraicIndependent K (projectiveFiniteJetPacket a n c)) ↔
      ∀ j, projectiveWordPolynomialValue a j c (n + 1) = 0 := by
  rw [projectiveFiniteJetPacket_algebraicIndependent_iff a n c hc]
  push Not
  rfl

/-- Polynomial form of the exact horizon theorem: the finite differential-dependence locus is the
common zero locus of the encoded homogeneous law polynomials. -/
theorem projectiveFiniteJetPacket_dependent_iff_lawPolynomials_zero
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    (¬ AlgebraicIndependent K (projectiveFiniteJetPacket a n c)) ↔
      ∀ j, MvPolynomial.eval c (projectiveWordLawPolynomial a j (n + 1)) = 0 := by
  simpa using projectiveFiniteJetPacket_dependent_iff a n c hc

end

end GaloisForLFunctions.HTGeometry
