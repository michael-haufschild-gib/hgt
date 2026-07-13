import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Partial evaluation of differential polynomials and the differential Steinitz exchange

The differential-transcendence matroid needs the exchange property.  Its mechanism is a *partial*
evaluation of a two-family differential polynomial: substitute the jets of the right family `y` into
the right variables and keep the left variables `X` formal, landing in the differential polynomial
ring in the left variables over `K`.

The construction factors as the isomorphism splitting the left/right variables followed by
`MvPolynomial.map` of the jet evaluation at `y`; hence it is injective exactly when `y` is
differentially transcendental (the jet evaluation is injective).  This injectivity is the crux: a
nonzero two-family relation stays nonzero after substituting a differentially transcendental `y`.
-/

namespace GaloisForLFunctions

open MvPolynomial

variable {L R k K : Type*} [CommRing k] [CommRing K] [Algebra k K] [Differential K]

/-- Split the left and right jet variables: `k{L ⊔ R}` as differential polynomials in the left
variables with coefficients differential polynomials in the right variables. -/
noncomputable def diffPolySumSplit (L R k : Type*) [CommRing k] :
    DifferentialPolynomial (L ⊕ R) k ≃ₐ[k]
      MvPolynomial (L × ℕ) (DifferentialPolynomial R k) :=
  (MvPolynomial.renameEquiv k (Equiv.sumProdDistrib L R ℕ)).trans
    (MvPolynomial.sumAlgEquiv k (L × ℕ) (R × ℕ))

/-- Partial evaluation: substitute the right variables with the jets of `y`, keep the left variables
formal. -/
noncomputable def diffPolyEvalRight (y : R → K) :
    DifferentialPolynomial (L ⊕ R) k →+* DifferentialPolynomial L K :=
  (MvPolynomial.map (differentialPolynomialEval (C := k) y).toRingHom).comp
    (diffPolySumSplit L R k).toRingHom

/-- When `y` is differentially transcendental, substituting it into the right variables is injective:
a nonzero two-family relation cannot vanish. -/
theorem diffPolyEvalRight_injective (y : R → K) (hy : DifferentialIndependent k y) :
    Function.Injective (diffPolyEvalRight (L := L) (k := k) y) := by
  have hmap : Function.Injective
      ⇑(MvPolynomial.map (σ := L × ℕ) (differentialPolynomialEval (C := k) y).toRingHom) := by
    apply MvPolynomial.map_injective
    intro a b hab
    exact hy hab
  have hsplit : Function.Injective ⇑(diffPolySumSplit L R k).toRingHom :=
    (diffPolySumSplit L R k).injective
  rw [diffPolyEvalRight, RingHom.coe_comp]
  exact hmap.comp hsplit

theorem diffPolySumSplit_X_inl (i : L) (n : ℕ) :
    diffPolySumSplit L R k (MvPolynomial.X (Sum.inl i, n)) = MvPolynomial.X (i, n) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.sumProdDistrib_apply_left]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_Xl]

theorem diffPolySumSplit_X_inr (j : R) (n : ℕ) :
    diffPolySumSplit L R k (MvPolynomial.X (Sum.inr j, n)) =
      MvPolynomial.C (MvPolynomial.X (j, n)) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.sumProdDistrib_apply_right]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_Xr]

theorem diffPolySumSplit_C (c : k) :
    diffPolySumSplit L R k (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_C]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_C]

@[simp] theorem diffPolyEvalRight_X_inl (y : R → K) (i : L) (n : ℕ) :
    diffPolyEvalRight (k := k) y (MvPolynomial.X (Sum.inl i, n)) = MvPolynomial.X (i, n) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.X (Sum.inl i, n))) = _
  rw [diffPolySumSplit_X_inl, map_X]

@[simp] theorem diffPolyEvalRight_X_inr (y : R → K) (j : R) (n : ℕ) :
    diffPolyEvalRight (L := L) (k := k) y (MvPolynomial.X (Sum.inr j, n)) =
      MvPolynomial.C (differentialJet n (y j)) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.X (Sum.inr j, n))) = _
  rw [diffPolySumSplit_X_inr, map_C]
  congr 1
  simp [differentialPolynomialEval]

@[simp] theorem diffPolyEvalRight_C (y : R → K) (c : k) :
    diffPolyEvalRight (L := L) (k := k) y (MvPolynomial.C c) =
      MvPolynomial.C (algebraMap k K c) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.C c)) = _
  rw [diffPolySumSplit_C, map_C]
  congr 1
  simp [differentialPolynomialEval]

/-- Evaluating the surviving left variables at `x` after substituting `y` recovers the full
evaluation of the two-family relation at `(x, y)`. -/
theorem diffPolyEvalRight_eval (x : L → K) (y : R → K) (P : DifferentialPolynomial (L ⊕ R) k) :
    differentialPolynomialEval (C := K) x (diffPolyEvalRight (k := k) y P) =
      differentialPolynomialEval (C := k) (Sum.elim x y) P := by
  have hring :
      ((differentialPolynomialEval (C := K) x).toRingHom.comp
          (diffPolyEvalRight (L := L) (k := k) y)) =
        (differentialPolynomialEval (C := k) (Sum.elim x y)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [differentialPolynomialEval]
    · rintro ⟨a | a, n⟩ <;>
        simp [differentialPolynomialEval_X]
  exact RingHom.congr_fun hring P

/-- Base change of jet evaluation: evaluating a differential polynomial with coefficients in an
intermediate ring `C'` at a point of `K` is the same as first pushing the coefficients into `K` and
then evaluating.  Coefficients are constants under evaluation, so no derivation compatibility is
needed. -/
theorem differentialPolynomialEval_map {L C' K' : Type*} [CommRing C'] [CommRing K']
    [Algebra C' K'] [Differential K'] (x : L → K') (Q : DifferentialPolynomial L C') :
    differentialPolynomialEval (C := C') x Q =
      differentialPolynomialEval (C := K') x (MvPolynomial.map (algebraMap C' K') Q) := by
  have hring :
      (differentialPolynomialEval (C := C') x).toRingHom =
        (differentialPolynomialEval (C := K') x).toRingHom.comp
          (MvPolynomial.map (algebraMap C' K')) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [differentialPolynomialEval]
    · rintro ⟨i, n⟩; simp [differentialPolynomialEval_X]
  exact RingHom.congr_fun hring Q

/-- Jets commute with a derivation-preserving algebra map. -/
theorem differentialJet_algebraMap {F K' : Type*} [CommRing F] [CommRing K'] [Algebra F K']
    [Differential F] [Differential K'] [DifferentialAlgebra F K'] (n : ℕ) (z : F) :
    algebraMap F K' (differentialJet n z) = differentialJet n (algebraMap F K' z) := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [differentialJet_succ, ← deriv_algebraMap, ih, ← differentialJet_succ]

/-- Differential independence reflects along a derivation-preserving field embedding: if the images
of a family are differentially independent, so is the family. -/
theorem DifferentialIndependent.of_algebraMap {k F K' σ : Type*}
    [CommRing k] [CommRing F] [CommRing K'] [Algebra k F] [Algebra F K'] [Algebra k K']
    [IsScalarTower k F K'] [Differential F] [Differential K'] [DifferentialAlgebra F K']
    {x : σ → F}
    (h : DifferentialIndependent k (fun i => algebraMap F K' (x i))) :
    DifferentialIndependent k x := by
  unfold DifferentialIndependent at h ⊢
  have hj : (fun p : σ × ℕ => differentialJet p.2 (algebraMap F K' (x p.1)))
      = (algebraMap F K') ∘ (fun p : σ × ℕ => differentialJet p.2 (x p.1)) := by
    funext p
    exact (differentialJet_algebraMap p.2 (x p.1)).symm
  rw [hj] at h
  exact h.of_comp (IsScalarTower.toAlgHom k F K')

/-- The `y`-substitution commutes with a derivation-preserving field embedding of the coefficients. -/
theorem map_diffPolyEvalRight {F K' : Type*} [CommRing F] [CommRing K']
    [Algebra F K'] [Algebra k F] [Algebra k K'] [IsScalarTower k F K']
    [Differential F] [Differential K'] [DifferentialAlgebra F K'] (y : R → F)
    (P : DifferentialPolynomial (L ⊕ R) k) :
    MvPolynomial.map (algebraMap F K') (diffPolyEvalRight (L := L) (k := k) (K := F) y P) =
      diffPolyEvalRight (L := L) (k := k) (K := K') (fun i => algebraMap F K' (y i)) P := by
  have hrh : (algebraMap F K').comp (differentialPolynomialEval (C := k) y).toRingHom =
      (differentialPolynomialEval (C := k) (fun i => algebraMap F K' (y i))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [differentialPolynomialEval, IsScalarTower.algebraMap_apply k F K']
    · rintro ⟨j, n⟩
      simp [differentialPolynomialEval_X, differentialJet_algebraMap]
  show MvPolynomial.map (algebraMap F K')
      ((MvPolynomial.map _) (diffPolySumSplit L R k P)) = _
  rw [MvPolynomial.map_map, hrh]
  rfl

/-- **Differential Steinitz exchange.**  If a pair `(x, y)` satisfies a nonzero differential
polynomial relation over the differential field `k`, and `y` is differentially transcendental over
`k`, then `x` is differentially algebraic over `k⟨y⟩`.  This is the exchange property of the
differential-dependence closure. -/
theorem differentialExchange {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Differential k] [Differential K] [DifferentialAlgebra k K] (x y : K)
    (hdep : ∃ P : DifferentialPolynomial (Unit ⊕ Unit) k, P ≠ 0 ∧
      differentialPolynomialEval (C := k) (Sum.elim (fun _ => x) (fun _ => y)) P = 0)
    (hy : DifferentialIndependent k (fun _ : Unit => y)) :
    ¬ DifferentialIndependent (differentialAdjoin k ({y} : Set K)) (fun _ : Unit => x) := by
  set F := differentialAdjoin k ({y} : Set K) with hF
  haveI : DifferentialAlgebra F K :=
    ⟨fun c => (derivationClosedDifferential_apply _ (derivationClosed_differentialAdjoin k _) c)⟩
  have hymem : y ∈ F := subset_differentialAdjoin k ({y} : Set K) rfl
  set y' : Unit → F := fun _ => ⟨y, hymem⟩ with hy'def
  have hcoe : (fun i : Unit => algebraMap F K (y' i)) = (fun _ : Unit => y) := rfl
  have hy' : DifferentialIndependent k y' := by
    apply DifferentialIndependent.of_algebraMap (K' := K)
    rw [hcoe]; exact hy
  obtain ⟨P, hP0, hPeval⟩ := hdep
  set Q' := diffPolyEvalRight (L := Unit) (k := k) (K := F) y' P with hQ'
  have hQ0 : Q' ≠ 0 := fun h => hP0 (diffPolyEvalRight_injective (L := Unit) y' hy' (by
    rw [hQ'] at h; rw [h, map_zero]))
  rw [differentialIndependent_iff_relationIdeal_eq_bot]
  intro hbot
  apply hQ0
  have hmem : Q' ∈ differentialRelationIdeal (C := F) (fun _ : Unit => x) := by
    rw [mem_differentialRelationIdeal_iff]
    rw [hQ', differentialPolynomialEval_map (K' := K),
      map_diffPolyEvalRight (L := Unit) (k := k) (K' := K) y' P, hcoe,
      diffPolyEvalRight_eval]
    exact hPeval
  rw [← Ideal.mem_bot, ← hbot]
  exact hmem

/-- **Family form of the differential exchange / closure membership.**  If `x` together with a
differentially independent family `y` satisfies a nonzero differential relation over `k`, then `x`
is differentially algebraic over `k⟨y⟩`.  Taking `y` to enumerate an independent set `I` and the
relation to witness the dependence of `insert x I`, this says exactly that adjoining a dependent
element lands it in the differential closure of `I`. -/
theorem differentialExchange_family {k K ι : Type*} [Field k] [Field K] [Algebra k K]
    [Differential k] [Differential K] [DifferentialAlgebra k K] (x : K) (y : ι → K)
    (hdep : ∃ P : DifferentialPolynomial (Unit ⊕ ι) k, P ≠ 0 ∧
      differentialPolynomialEval (C := k) (Sum.elim (fun _ => x) y) P = 0)
    (hy : DifferentialIndependent k y) :
    ¬ DifferentialIndependent (differentialAdjoin k (Set.range y)) (fun _ : Unit => x) := by
  set F := differentialAdjoin k (Set.range y) with hF
  haveI : DifferentialAlgebra F K :=
    ⟨fun c => (derivationClosedDifferential_apply _ (derivationClosed_differentialAdjoin k _) c)⟩
  set y' : ι → F := fun i => ⟨y i, subset_differentialAdjoin k (Set.range y) ⟨i, rfl⟩⟩ with hy'def
  have hcoe : (fun i : ι => algebraMap F K (y' i)) = y := rfl
  have hy' : DifferentialIndependent k y' := by
    apply DifferentialIndependent.of_algebraMap (K' := K)
    rw [hcoe]; exact hy
  obtain ⟨P, hP0, hPeval⟩ := hdep
  set Q' := diffPolyEvalRight (L := Unit) (k := k) (K := F) y' P with hQ'
  have hQ0 : Q' ≠ 0 := fun h => hP0 (diffPolyEvalRight_injective (L := Unit) y' hy' (by
    rw [hQ'] at h; rw [h, map_zero]))
  rw [differentialIndependent_iff_relationIdeal_eq_bot]
  intro hbot
  apply hQ0
  have hmem : Q' ∈ differentialRelationIdeal (C := F) (fun _ : Unit => x) := by
    rw [mem_differentialRelationIdeal_iff]
    rw [hQ', differentialPolynomialEval_map (K' := K),
      map_diffPolyEvalRight (L := Unit) (k := k) (K' := K) y' P, hcoe,
      diffPolyEvalRight_eval]
    exact hPeval
  rw [← Ideal.mem_bot, ← hbot]
  exact hmem

end GaloisForLFunctions
