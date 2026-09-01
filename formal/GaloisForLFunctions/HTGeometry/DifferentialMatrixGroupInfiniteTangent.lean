import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupNonzeroTangent
import GaloisForLFunctions.HTGeometry.MatrixZeroTangentOperatorSpan
import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import GaloisForLFunctions.HTGeometry.MatrixTranslationZeroSet
import GaloisForLFunctions.HTGeometry.RightInverseMonoidGroup

/-!
# Infinite differential matrix groups cannot have zero tangent

The extension-valued identity tangent constructed from a differential generic point annihilates
every linearized defining equation.  If the coefficient-field tangent were zero, those operator
rows would span the whole free Ore module and force the extension-valued tangent to vanish.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u v

variable {C L : Type u} {κ : Type v} [Field C] [Field L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]
  [Fintype κ] [DecidableEq κ]

/-- Extension-valued evaluation of a linearized operator row. -/
theorem fieldPairingOver_linearisationDiffOpRow (p : κ → C)
    (P : DifferentialPolynomial κ C) (X : κ → L) :
    DiffOp.fieldPairingOver X (linearisationDiffOpRow p P) =
      ∑ v ∈ P.vars,
        algebraMap C L
            (differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v P)) *
          differentialJet v.2 (X v.1) := by
  classical
  have hmap (s : Finset (κ × ℕ)) (f : κ × ℕ → DiffOp C) :
      DiffOp.mapCoeffs (algebraMap C L) (∑ v ∈ s, f v) =
        ∑ v ∈ s, DiffOp.mapCoeffs (algebraMap C L) (f v) := by
    induction s using Finset.induction_on with
    | empty => simp [DiffOp.mapCoeffs_zero]
    | insert a s ha ih =>
        simp [ha, ih, DiffOp.mapCoeffs_add]
  rw [DiffOp.fieldPairingOver_apply]
  simp_rw [linearisationDiffOpRow]
  simp_rw [hmap]
  simp_rw [DiffOp.fieldApply_finset_sum_op]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.sum_eq_single v.1]
  · simp [DiffOp.mapCoeffs_mono, DiffOp.fieldApply_mono]
  · intro i _ hi
    simp [Ne.symm hi, DiffOp.mapCoeffs_zero, DiffOp.fieldApply_zero_op]
  · simp

/-- Evaluated gradient over a commutative algebra, with finite support supplied by polynomial
variables. -/
def mvPolynomialGradientEvalComm
    {ι K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ι → A) (P : MvPolynomial ι K) : ι →₀ A :=
  Finsupp.onFinset P.vars
    (fun i => MvPolynomial.aeval x (MvPolynomial.pderiv i P))
    (fun i hi => by
      change MvPolynomial.aeval x (MvPolynomial.pderiv i P) ≠ 0 at hi
      by_contra hnot
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot, map_zero] at hi
      exact hi rfl)

@[simp] theorem mvPolynomialGradientEvalComm_apply
    {ι K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ι → A) (P : MvPolynomial ι K) (i : ι) :
    mvPolynomialGradientEvalComm x P i =
      MvPolynomial.aeval x (MvPolynomial.pderiv i P) := by
  exact Finsupp.onFinset_apply

@[simp] theorem mvPolynomialGradientEvalComm_C
    {ι K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ι → A) (c : K) :
    mvPolynomialGradientEvalComm x (MvPolynomial.C c) = 0 := by
  ext i
  simp

theorem mvPolynomialGradientEvalComm_add
    {ι K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ι → A) (P Q : MvPolynomial ι K) :
    mvPolynomialGradientEvalComm x (P + Q) =
      mvPolynomialGradientEvalComm x P + mvPolynomialGradientEvalComm x Q := by
  ext i
  simp

theorem mvPolynomialGradientEvalComm_mul_X
    {ι K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ι → A) (P : MvPolynomial ι K) (k : ι) :
    mvPolynomialGradientEvalComm x (P * MvPolynomial.X k) =
      x k • mvPolynomialGradientEvalComm x P +
        Finsupp.single k (MvPolynomial.aeval x P) := by
  classical
  ext i
  simp only [mvPolynomialGradientEvalComm_apply, MvPolynomial.pderiv_mul,
    map_add, map_mul, MvPolynomial.aeval_X, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : k = i
  · subst i
    simp
    ring
  · simp [h]
    ring

/-- Multivariate chain rule for a derivation into a module, without a field assumption on the
source algebra. -/
theorem derivation_aeval_eq_gradient_comm
    {ι K A M : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
    (D : Derivation K A M) (x : ι → A) (P : MvPolynomial ι K) :
    D (MvPolynomial.aeval x P) =
      Finsupp.linearCombination A (fun i => D (x i))
        (mvPolynomialGradientEvalComm x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [map_add (MvPolynomial.aeval x) P Q]
      rw [D.map_add, hP, hQ, mvPolynomialGradientEvalComm_add, map_add]
  | mul_X P k hP =>
      rw [map_mul (MvPolynomial.aeval x) P (MvPolynomial.X k),
        MvPolynomial.aeval_X]
      rw [Derivation.leibniz, hP, mvPolynomialGradientEvalComm_mul_X,
        map_add]
      simp [Finsupp.linearCombination_single, map_smul]
      exact add_comm _ _

namespace DifferentialMatrixGroupRepresentation

variable {G : Type u} [Group G]
variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance infiniteTangentAmbientDifferential : Differential (G → C) :=
  pointwiseFunctionDifferential G

local instance infiniteTangentCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- Zeroth matrix coordinate as an element of the differential coordinate algebra. -/
def coordinateElement (q : Fin 2 × Fin 2) : r.coordinateAlgebra :=
  ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
    funext g
    exact (differentialJet_zero _).symm⟩⟩

/-- A matrix-coordinate jet as an element of the differential coordinate algebra. -/
def coordinateJetElement (v : (Fin 2 × Fin 2) × ℕ) : r.coordinateAlgebra :=
  ⟨r.coordinateJet v.1 v.2, Algebra.subset_adjoin ⟨v, rfl⟩⟩

theorem coordinateJetElement_eq_differentialJet (q : Fin 2 × Fin 2) (n : ℕ) :
    r.coordinateJetElement (q, n) = differentialJet n (r.coordinateElement q) := by
  exact r.coordinateJet_element_eq_differentialJet q n

/-- Evaluating at the coordinate-algebra jet generators is the represented matrix evaluation,
pointwise on the group. -/
theorem coordinateAlgebra_eval_eq (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    ((MvPolynomial.aeval r.coordinateJetElement P : r.coordinateAlgebra) : G → C) =
      differentialPolynomialEvalOver (K := C) r.coordinate P := by
  have hpointwise (f : G → C) (n : ℕ) (g : G) :
      differentialJet n f g = differentialJet n (f g) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ]
        rw [pointwiseFunctionDifferential_apply, ih]
  have hhom : (r.coordinateAlgebra.val).comp
        (MvPolynomial.aeval r.coordinateJetElement) =
      differentialPolynomialEvalOver (K := C) r.coordinate := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X,
      differentialPolynomialEvalOver_X]
    funext g
    exact (hpointwise (r.coordinate v.1) v.2 g).symm
  exact DFunLike.congr_fun hhom P

/-- Every represented-group relation evaluates to zero in its differential coordinate algebra. -/
theorem coordinateAlgebra_eval_eq_zero_of_mem_matrixVanishingIdeal
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C}
    (hP : P ∈ matrixVanishingIdeal (Set.range r.matrix)) :
    MvPolynomial.aeval r.coordinateJetElement P = 0 := by
  apply Subtype.ext
  rw [r.coordinateAlgebra_eval_eq P]
  funext g
  let ev : (G → C) →ₐ[C] C :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hpointwise (f : G → C) (n : ℕ) :
      ev (differentialJet n f) = differentialJet n (f g) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ]
        change Differential.deriv (differentialJet n f) g =
          Differential.deriv (differentialJet n (f g))
        change differentialJet n f g = differentialJet n (f g) at ih
        rw [pointwiseFunctionDifferential_apply, ih]
  have heval : ev.comp (differentialPolynomialEvalOver (K := C) r.coordinate) =
      differentialPolynomialEvalOver (K := C)
        (fun q : Fin 2 × Fin 2 => r.matrix g q.1 q.2) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, differentialPolynomialEvalOver_X,
      differentialPolynomialEvalOver_X, hpointwise]
    rfl
  have hevalP := DFunLike.congr_fun heval P
  change (ev.comp (differentialPolynomialEvalOver (K := C) r.coordinate)) P = 0
  rw [hevalP]
  exact hP (r.matrix g) ⟨g, rfl⟩

/-- An extension-valued derivation at the identity annihilates every linearized relation of the
represented group. -/
theorem identityTangent_fieldPairingOver_eq_zero
    (ell : r.coordinateAlgebra →ₗ[C] L)
    (hellMul : ∀ a b, ell (a * b) =
      r.tangentIdentityCharacter a * ell b +
        r.tangentIdentityCharacter b * ell a)
    (hellδ : ∀ a, ell (Differential.deriv a) = Differential.deriv (ell a))
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C}
    (hP : P ∈ matrixVanishingIdeal (Set.range r.matrix)) :
    DiffOp.fieldPairingOver (fun q => ell (r.coordinateElement q))
        (linearisationDiffOpRow
          (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2) P) = 0 := by
  classical
  let p : Fin 2 × Fin 2 → C := fun q =>
    (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2
  let X : Fin 2 × Fin 2 → L := fun q => ell (r.coordinateElement q)
  letI : Algebra r.coordinateAlgebra L := r.tangentIdentityAlgebra
  let E : Derivation C r.coordinateAlgebra L :=
    Derivation.mk' ell fun a b => by
      rw [hellMul]
      rfl
  have hcounitδ (a : r.coordinateAlgebra) :
      r.coordinateCounit (Differential.deriv a) =
        Differential.deriv (r.coordinateCounit a) := by
    change Differential.deriv (a : G → C) 1 = Differential.deriv (a.1 1)
    rw [pointwiseFunctionDifferential_apply]
  have hcharδ (a : r.coordinateAlgebra) :
      r.tangentIdentityCharacter (L := L) (Differential.deriv a) =
        Differential.deriv (r.tangentIdentityCharacter (L := L) a) := by
    change algebraMap C L (r.coordinateCounit (Differential.deriv a)) =
      Differential.deriv (algebraMap C L (r.coordinateCounit a))
    rw [hcounitδ, DifferentialAlgebra.deriv_algebraMap]
  have hcharJet (a : r.coordinateAlgebra) (n : ℕ) :
      r.tangentIdentityCharacter (L := L) (differentialJet n a) =
        differentialJet n (r.tangentIdentityCharacter (L := L) a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ, hcharδ, ih]
  have halgebraMapJet (c : C) (n : ℕ) :
      algebraMap C L (differentialJet n c) = differentialJet n (algebraMap C L c) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ,
          ← DifferentialAlgebra.deriv_algebraMap, ih]
  have hidentityEval :
      (r.tangentIdentityCharacter (L := L)).comp
          (MvPolynomial.aeval r.coordinateJetElement) =
        (Algebra.ofId C L).comp (differentialPolynomialEvalOver (K := C) p) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.comp_apply,
      differentialPolynomialEvalOver_X,
      r.coordinateJetElement_eq_differentialJet, hcharJet]
    have hc : r.tangentIdentityCharacter (L := L) (r.coordinateElement v.1) =
        algebraMap C L (p v.1) := by
      change algebraMap C L (r.coordinateCounit (r.coordinateElement v.1)) =
        algebraMap C L (p v.1)
      apply congrArg (algebraMap C L)
      simpa [coordinateElement, p] using r.coordinateCounit_coordinate v.1
    rw [hc, ← halgebraMapJet]
    rfl
  have hcoeff (Q : DifferentialPolynomial (Fin 2 × Fin 2) C) :
      r.tangentIdentityCharacter (L := L) (MvPolynomial.aeval r.coordinateJetElement Q) =
        algebraMap C L (differentialPolynomialEvalOver (K := C) p Q) := by
    exact DFunLike.congr_fun hidentityEval Q
  have hellJet (a : r.coordinateAlgebra) (n : ℕ) :
      ell (differentialJet n a) = differentialJet n (ell a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ, hellδ, ih]
  have hEjet (v : (Fin 2 × Fin 2) × ℕ) :
      E (r.coordinateJetElement v) = differentialJet v.2 (X v.1) := by
    change ell (r.coordinateJetElement v) = differentialJet v.2 (ell (r.coordinateElement v.1))
    rw [show r.coordinateJetElement v = differentialJet v.2 (r.coordinateElement v.1) by
      exact r.coordinateJetElement_eq_differentialJet v.1 v.2, hellJet]
  have hrelation : MvPolynomial.aeval r.coordinateJetElement P = 0 :=
    r.coordinateAlgebra_eval_eq_zero_of_mem_matrixVanishingIdeal hP
  have hchain := derivation_aeval_eq_gradient_comm E r.coordinateJetElement P
  rw [hrelation, map_zero] at hchain
  have hlinear : Finsupp.linearCombination r.coordinateAlgebra
      (fun v => E (r.coordinateJetElement v))
      (mvPolynomialGradientEvalComm r.coordinateJetElement P) = 0 := hchain.symm
  let grad := mvPolynomialGradientEvalComm r.coordinateJetElement P
  have hsupport : grad.support ⊆ P.vars := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv
    by_contra hnot
    apply hv
    rw [mvPolynomialGradientEvalComm_apply,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot, map_zero]
  have hsum : Finsupp.linearCombination r.coordinateAlgebra
        (fun v => E (r.coordinateJetElement v)) grad =
      ∑ v ∈ P.vars,
        algebraMap C L
            (differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v P)) *
          differentialJet v.2 (X v.1) := by
    rw [Finsupp.linearCombination_apply]
    change (∑ v ∈ grad.support, grad v • E (r.coordinateJetElement v)) = _
    rw [Finset.sum_subset hsupport]
    · refine Finset.sum_congr rfl fun v hv => ?_
      change r.tangentIdentityCharacter (L := L) (grad v) *
          E (r.coordinateJetElement v) = _
      rw [show grad v = MvPolynomial.aeval r.coordinateJetElement
          (MvPolynomial.pderiv v P) by
        exact mvPolynomialGradientEvalComm_apply _ _ _, hcoeff, hEjet]
    · intro v hv hvsupp
      have hgv : grad v = 0 := by
        by_contra hne
        exact hvsupp (Finsupp.mem_support_iff.mpr hne)
      rw [hgv]
      simp
  change DiffOp.fieldPairingOver X (linearisationDiffOpRow p P) = 0
  rw [fieldPairingOver_linearisationDiffOpRow]
  change (∑ v ∈ P.vars,
      algebraMap C L
          (differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v P)) *
        differentialJet v.2 (X v.1)) = 0
  exact hsum.symm.trans (by simpa [grad] using hlinear)

/-- A derivation-compatible identity tangent is determined by its four zeroth coordinates. -/
theorem identityTangent_eq_zero_of_coordinates_eq_zero
    (ell : r.coordinateAlgebra →ₗ[C] L)
    (hellMul : ∀ a b, ell (a * b) =
      r.tangentIdentityCharacter a * ell b +
        r.tangentIdentityCharacter b * ell a)
    (hellδ : ∀ a, ell (Differential.deriv a) = Differential.deriv (ell a))
    (hcoord : ∀ q : Fin 2 × Fin 2, ell (r.coordinateElement q) = 0) :
    ell = 0 := by
  have hellOne : ell 1 = 0 := by
    have h : ell 1 = ell 1 + ell 1 := by
      simpa using hellMul 1 1
    apply add_left_cancel (a := ell 1)
    rw [add_zero]
    exact h.symm
  have hellJet (a : r.coordinateAlgebra) (n : ℕ) :
      ell (differentialJet n a) = differentialJet n (ell a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ, hellδ, ih]
  apply LinearMap.ext
  intro a
  change ell a = 0
  refine Algebra.adjoin_induction (p := fun f _ =>
      ell ⟨f, by assumption⟩ = 0) ?_ ?_ ?_ ?_ a.2
  · intro f hf
    obtain ⟨v, rfl⟩ := hf
    change ell (r.coordinateJetElement v) = 0
    rw [show r.coordinateJetElement v = differentialJet v.2 (r.coordinateElement v.1) by
      exact r.coordinateJetElement_eq_differentialJet v.1 v.2,
      hellJet, hcoord, differentialJet_eq_zero_zero]
  · intro c
    change ell (algebraMap C r.coordinateAlgebra c) = 0
    have h := ell.map_smul c (1 : r.coordinateAlgebra)
    rw [hellOne, smul_zero] at h
    simpa [Algebra.smul_def] using h
  · intro f g hf hg hfe hge
    change ell (⟨f, hf⟩ + ⟨g, hg⟩) = 0
    rw [map_add, hfe, hge, add_zero]
  · intro f g hf hg hfe hge
    change ell (⟨f, hf⟩ * ⟨g, hg⟩) = 0
    rw [hellMul, hfe, hge, mul_zero, mul_zero, add_zero]

/-- **An infinite injectively represented differential matrix group has nonzero coefficient-field
tangent.**  The conclusion is over the original differentially closed coefficient field; the
extension-valued generic tangent only serves to rule out the zero branch. -/
theorem matrixTangentM_ne_bot_of_infinite_representation
    [CharZero C] [Algebra ℚ C] [IsDifferentiallyClosed C] [Infinite G]
    (hinj : Function.Injective r.matrix) :
    let H : Set (Matrix (Fin 2) (Fin 2) C) := Set.range r.matrix
    let hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈
        matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
      subset_matrixZeroSet_vanishingIdeal H ⟨1, r.matrix.map_one⟩
    matrixTangentM (matrixVanishingIdeal H) hone ≠ ⊥ := by
  classical
  dsimp only
  let H : Set (Matrix (Fin 2) (Fin 2) C) := Set.range r.matrix
  have hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H := ⟨1, r.matrix.map_one⟩
  let hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈
      matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
    subset_matrixZeroSet_vanishingIdeal H hHone
  intro hzero
  obtain ⟨L, hLfield, hLrat, hLC, hLdiff, hLdiffAlg,
      ell, hellNe, hellMul, hellδ⟩ := r.exists_nonzero_identity_tangent_of_infinite hinj
  letI : Field L := hLfield
  letI : Algebra ℚ L := hLrat
  letI : Algebra C L := hLC
  letI : Differential L := hLdiff
  letI : DifferentialAlgebra C L := hLdiffAlg
  letI : Module (DiffOp C) L := DiffOp.extensionModule
  let X : Fin 2 × Fin 2 → L := fun q => ell (r.coordinateElement q)
  have hXne : X ≠ 0 := by
    intro hX
    apply hellNe
    apply r.identityTangent_eq_zero_of_coordinates_eq_zero ell hellMul hellδ
    intro q
    exact congrFun hX q
  let p : Fin 2 × Fin 2 → C := fun q =>
    (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2
  let N := linearisationDiffOpSpan p (matrixVanishingIdeal H)
  have hNtop : N = ⊤ := by
    exact linearisationDiffOpSpan_eq_top_of_matrixTangentM_eq_bot
      (matrixVanishingIdeal H) hone hzero
  have hcommon : ∀ w ∈ N, DiffOp.fieldPairingOver X w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨P, rfl⟩ := hw
        exact r.identityTangent_fieldPairingOver_eq_zero ell hellMul hellδ P.2
    | zero => exact map_zero (DiffOp.fieldPairingOver X)
    | add a b _ _ ha hb =>
        rw [map_add, ha, hb, add_zero]
    | smul c a _ ha =>
        rw [map_smul, ha, smul_zero]
  apply hXne
  funext q
  have hunit : Pi.single q (1 : DiffOp C) ∈ N := by
    rw [hNtop]
    trivial
  have hpair := hcommon (Pi.single q (1 : DiffOp C)) hunit
  rw [DiffOp.fieldPairingOver_single_operator,
    DiffOp.mapCoeffs_one, DiffOp.fieldApply_one] at hpair
  exact hpair

end DifferentialMatrixGroupRepresentation

/-- An infinite determinant-one matrix set closed under multiplication and internal right inverses
has nonzero coefficient-field identity tangent. -/
theorem matrixTangentM_ne_bot_of_infinite_matrixSet
    {C : Type u} [Field C] [Algebra ℚ C] [CharZero C] [Differential C]
    [IsDifferentiallyClosed C]
    (H : Set (Matrix (Fin 2) (Fin 2) C))
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hdet : ∀ a ∈ H, a.det = 1)
    (hinv : ∀ a ∈ H, ∃ b ∈ H, a * b = 1)
    (hInfinite : H.Infinite) :
    matrixTangentM (matrixVanishingIdeal H)
        (subset_matrixZeroSet_vanishingIdeal H hone) ≠ ⊥ := by
  classical
  let S : Submonoid (Matrix (Fin 2) (Fin 2) C) :=
    { carrier := H
      one_mem' := hone
      mul_mem' := fun ha hb => hmul _ ha _ hb }
  have hright : ∀ x : S, ∃ y : S, x * y = 1 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hinv x x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  letI : Group S := groupOfRightInverses hright
  haveI : Infinite S := by
    change Infinite {a : Matrix (Fin 2) (Fin 2) C // a ∈ H}
    exact Set.infinite_coe_iff.mpr hInfinite
  let r : DifferentialMatrixGroupRepresentation (C := C) (G := S) :=
    { matrix := S.subtype
      det_eq_one := fun g => hdet g g.property }
  have hinjective : Function.Injective r.matrix := fun a b hab => Subtype.ext hab
  have hRange : Set.range r.matrix = H := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact g.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have htangent := r.matrixTangentM_ne_bot_of_infinite_representation hinjective
  simpa only [hRange] using htangent

end

end GaloisForLFunctions.HTGeometry
