import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity
import GaloisForLFunctions.HTGeometry.FreeDifferentialJetField

/-!
# The capacity spectrum is unbounded but never attained

A finite-palette observable disperses differential capacity: `N + 1` observations mixed from `N`
differentially independent sources are never differentially independent, while an invertible `N × N`
packet realizes exactly `N`.  Both halves are already in the corpus.  This file supplies the two
things that turn them into the capacity dichotomy itself.

* A **specialization certificate** for the observation matrix: if some ring homomorphism carries the
  matrix to the identity, its determinant is nonzero.  This is the exact shape produced by an
  interpolating family — the observation matrix of the translation orbit is the identity at the base
  point — so the analytic construction never has to compute a determinant.
* An **unbounded supply of sources**: in the free differential field on countably many generators
  the generators are differentially independent, so every finite palette size occurs.

Together: for every `n` there is a palette of `n` differentially independent sources whose invertible
recombinations are `n` differentially independent observations, and no observation family larger than
its own palette is ever differentially independent.  The capacity spectrum is unbounded, and no
single finite palette attains an infinite value.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix GaloisForLFunctions

noncomputable section

/-! ### A specialization certificate for the observation matrix -/

/-- **An identity specialization certifies an invertible observation packet.**  Determinants commute
with ring homomorphisms, so a matrix carried to the identity by some ring map has nonzero
determinant. -/
theorem det_ne_zero_of_map_eq_one {C R : Type*} [CommRing C] [CommRing R] [Nontrivial R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (ev : C →+* R) (h : M.map ev = 1) : M.det ≠ 0 := by
  intro hdet
  have h1 : ev M.det = (1 : R) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h, Matrix.det_one]
  rw [hdet, map_zero] at h1
  exact zero_ne_one h1

/-- **Capacity realization from an identity specialization.**  An observation packet which some ring
map carries to the identity transfers every source direction. -/
theorem finiteShadow_realizes_capacity_of_map_eq_one
    {C K R : Type*} [Field C] [CommRing K] [Algebra C K] [Differential K]
    [CommRing R] [Nontrivial R] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C) (ev : C →+* R) (hev : M.map ev = 1)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : Fin n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) :=
  finiteShadow_fullRank_realizes_capacity n M (det_ne_zero_of_map_eq_one M ev hev) hMconst x hx

/-- **A regular-point evaluation certifies an invertible observation packet.**  The entries of an
observation matrix of functions need not be evaluable everywhere; it is enough that they lie in a
subring carrying an evaluation, and that the evaluated matrix is the identity.  This is the shape an
interpolating family produces: every entry is regular at the base point, and there the matrix is the
identity. -/
theorem det_ne_zero_of_subring_map_eq_one {C R : Type*} [CommRing C] [CommRing R] [Nontrivial R]
    {A : Subring C} (ev : A →+* R) {n : ℕ} (M : Matrix (Fin n) (Fin n) A)
    (hev : M.map ev = 1) : (M.map A.subtype).det ≠ 0 := by
  have hA : M.det ≠ 0 := det_ne_zero_of_map_eq_one M ev hev
  intro hzero
  refine hA ?_
  have hmap : (M.map A.subtype).det = A.subtype M.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [hmap] at hzero
  exact Subtype.val_injective (by simpa using hzero)

/-- **Capacity realization from a regular-point evaluation.** -/
theorem finiteShadow_realizes_capacity_of_subring_map_eq_one
    {C K R : Type*} [Field C] [CommRing K] [Algebra C K] [Differential K]
    [CommRing R] [Nontrivial R] {A : Subring C} (ev : A →+* R) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) A) (hev : M.map ev = 1)
    (hMconst : ∀ i j, (algebraMap C K ((M i j : A) : C))′ = 0)
    (x : Fin n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms (M.map A.subtype) x) :=
  finiteShadow_fullRank_realizes_capacity n (M.map A.subtype)
    (det_ne_zero_of_subring_map_eq_one ev M hev) hMconst x hx

/-! ### An unbounded supply of differentially independent sources -/

namespace JetField

variable {C : Type*} [Field C] {ι : Type*}

/-- The differential jets of a generator are its own higher jet coordinates. -/
theorem differentialJet_jet_of_zero (j : ι) (m : ℕ) :
    differentialJet m (jet (j, 0) : JetField C ι) = jet (j, m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [differentialJet_succ, ih, deriv_jet]

/-- The jet coordinates of the free differential field are algebraically independent. -/
theorem algebraicIndependent_jet_free :
    AlgebraicIndependent C (fun p : ι × ℕ => (jet p : JetField C ι)) := by
  have hX : AlgebraicIndependent C (fun p : ι × ℕ => (MvPolynomial.X p : JetPoly C ι)) :=
    MvPolynomial.algebraicIndependent_X (ι × ℕ) C
  have hinj : Function.Injective
      (IsScalarTower.toAlgHom C (JetPoly C ι) (JetField C ι)) :=
    IsFractionRing.injective (JetPoly C ι) (JetField C ι)
  have h := (AlgHom.algebraicIndependent_iff
    (IsScalarTower.toAlgHom C (JetPoly C ι) (JetField C ι)) hinj).2 hX
  exact h

/-- **The generators of the free differential field are differentially independent.** -/
theorem differentialIndependent_jet :
    DifferentialIndependent C (fun j : ι => (jet (j, 0) : JetField C ι)) := by
  have hfun : (fun p : ι × ℕ =>
      differentialJet p.2 ((fun j : ι => (jet (j, 0) : JetField C ι)) p.1))
        = fun p : ι × ℕ => (jet p : JetField C ι) := by
    funext p
    exact differentialJet_jet_of_zero p.1 p.2
  show AlgebraicIndependent C _
  rw [hfun]
  exact algebraicIndependent_jet_free

/-- Coefficients of the free differential field are differential constants. -/
@[simp]
theorem deriv_algebraMap (c : C) : ((algebraMap C (JetField C ι)) c)′ = 0 := by
  rw [deriv_eq]
  exact Derivation.map_algebraMap _ c

end JetField

/-! ### The dichotomy -/

/-- **Every finite palette size occurs.**  The first `n` generators of the free differential field
are `n` differentially independent sources. -/
theorem exists_differentialIndependent_fin (C : Type*) [Field C] (n : ℕ) :
    ∃ x : Fin n → JetField C ℕ, DifferentialIndependent C x := by
  refine ⟨fun i => JetField.jet ((i : ℕ), 0), ?_⟩
  have hbase : AlgebraicIndependent C (fun p : ℕ × ℕ => (JetField.jet p : JetField C ℕ)) :=
    JetField.algebraicIndependent_jet_free
  have hinj : Function.Injective (fun p : Fin n × ℕ => ((p.1 : ℕ), p.2)) := by
    rintro ⟨i, m⟩ ⟨j, k⟩ h
    simp only [Prod.mk.injEq, Fin.val_inj] at h
    simp [h.1, h.2]
  have hcomp := hbase.comp _ hinj
  have hfun : (fun p : Fin n × ℕ =>
      differentialJet p.2 ((fun i : Fin n => (JetField.jet ((i : ℕ), 0) : JetField C ℕ)) p.1))
        = (fun p : ℕ × ℕ => (JetField.jet p : JetField C ℕ))
            ∘ (fun p : Fin n × ℕ => ((p.1 : ℕ), p.2)) := by
    funext p
    exact JetField.differentialJet_jet_of_zero (p.1 : ℕ) p.2
  show AlgebraicIndependent C _
  rw [hfun]
  exact hcomp

/-- **The capacity spectrum of the free differential field is unbounded but never attained.**  For
every `n` there is a palette of `n` differentially independent sources; every invertible
recombination of it is again `n` differentially independent observations, and no family of `n + 1`
observations mixed from that palette is differentially independent. -/
theorem capacity_spectrum_free (C : Type*) [Field C] (n : ℕ) :
    ∃ x : Fin n → JetField C ℕ, DifferentialIndependent C x ∧
      (∀ M : Matrix (Fin n) (Fin n) C, M.det ≠ 0 →
        DifferentialIndependent C (matrixLinearForms M x)) ∧
      (∀ M : Matrix (Fin (n + 1)) (Fin n) C,
        ¬ DifferentialIndependent C (matrixLinearForms M x)) := by
  obtain ⟨x, hx⟩ := exists_differentialIndependent_fin C n
  refine ⟨x, hx, ?_, ?_⟩
  · intro M hdet
    exact finiteShadow_fullRank_realizes_capacity n M hdet
      (fun i j => JetField.deriv_algebraMap (M i j)) x hx
  · intro M
    exact finiteShadow_moreObservablesThanSources_not_differentialIndependent n M
      (fun i j => JetField.deriv_algebraMap (M i j)) x hx

end

end GaloisForLFunctions.HTGeometry
