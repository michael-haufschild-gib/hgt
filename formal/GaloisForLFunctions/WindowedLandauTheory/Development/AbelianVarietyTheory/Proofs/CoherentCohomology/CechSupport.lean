import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Order.Interval.Set.Defs

/-! Truncating an alternating Čech datum to order-convex subsets of its
intersection indices gives the support sequences for comparing covers. -/

noncomputable section

open CategoryTheory

namespace HTGeometry.FinsetCechDatum

variable {R ι : Type} [CommRing R]
  (D : FinsetCechDatum.{0} ι) [∀ s, Module R (D.obj s)]

/-- Keep a coefficient on its support and require it to be zero elsewhere. -/
def supportCoeff (P : Set (Finset ι)) (s : Finset ι) : Submodule R (D.obj s) where
  carrier := {x | s ∉ P → x = 0}
  zero_mem' := fun _ => rfl
  add_mem' hx hy h := by rw [hx h, hy h, add_zero]
  smul_mem' a _ hx h := by rw [hx h, smul_zero]

open Classical in
private def supportRes (P : Set (Finset ι)) {s t : Finset ι} (h : s ⊆ t) :
    D.supportCoeff (R := R) P s →+ D.supportCoeff (R := R) P t where
  toFun x := ⟨if t ∈ P then D.res h x.1 else 0, fun ht => if_neg ht⟩
  map_zero' := Subtype.ext (by
    change (if t ∈ P then D.res h 0 else 0) = 0
    simp only [map_zero, ite_self])
  map_add' x y := Subtype.ext (by
    by_cases ht : t ∈ P <;> simp only [ht, if_true, if_false, Submodule.coe_add, map_add, add_zero])

/-- Intermediates between supported indices are supported, so the truncated
restrictions compose. -/
def truncate (P : Set (Finset ι)) (hP : P.OrdConnected) : FinsetCechDatum.{0} ι where
  obj s := D.supportCoeff (R := R) P s
  grp _ := inferInstance
  res := D.supportRes P
  res_refl s x := Subtype.ext (by
    classical
    change (if s ∈ P then D.res (Finset.Subset.refl s) x.1 else 0) = x.1
    by_cases hs : s ∈ P
    · rw [if_pos hs, D.res_refl]
    · exact (if_neg hs).trans (x.2 hs).symm)
  res_res h₁ h₂ x := Subtype.ext (by
    classical
    rename_i s t u
    change (if u ∈ P then D.res h₂ (if t ∈ P then D.res h₁ x.1 else 0) else 0) =
      if u ∈ P then D.res (h₁.trans h₂) x.1 else 0
    by_cases hu : u ∈ P
    · rw [if_pos hu, if_pos hu]
      by_cases ht : t ∈ P
      · rw [if_pos ht, D.res_res]
      · have hs : s ∉ P := fun hs => ht (hP.out' hs hu ⟨h₁, h₂⟩)
        rw [if_neg ht, x.2 hs, map_zero, map_zero]
    · rw [if_neg hu, if_neg hu])

instance (P : Set (Finset ι)) (hP : P.OrdConnected) (s : Finset ι) :
    Module R ((D.truncate (R := R) P hP).obj s) :=
  inferInstanceAs (Module R (D.supportCoeff P s))

theorem subsingleton_truncate_obj (P : Set (Finset ι)) (hP : P.OrdConnected)
    (s : Finset ι) (hs : s ∉ P) : Subsingleton ((D.truncate (R := R) P hP).obj s) :=
  ⟨fun x y => Subtype.ext ((x.2 hs).trans (y.2 hs).symm)⟩

open Classical in
theorem truncate_res_value (P : Set (Finset ι)) (hP : P.OrdConnected)
    {s t : Finset ι} (h : s ⊆ t) (x : (D.truncate (R := R) P hP).obj s) :
    ((D.truncate P hP).res h x).1 = if t ∈ P then D.res h x.1 else 0 := rfl

/-- When every index lies in the support, truncation preserves all coefficients. -/
def toTruncateOfAll (P : Set (Finset ι)) (hP : P.OrdConnected) (h : ∀ s, s ∈ P) :
    D.Hom (D.truncate (R := R) P hP) where
  app s :=
    { toFun := fun x => ⟨x, fun hs => (hs (h s)).elim⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  comm {s t} hst x := Subtype.ext (by
    rw [D.truncate_res_value (R := R), if_pos (h t)]
    rfl)

theorem toTruncateOfAll_bijective (P : Set (Finset ι)) (hP : P.OrdConnected) (h : ∀ s, s ∈ P)
    (s : Finset ι) : Function.Bijective ((D.toTruncateOfAll (R := R) P hP h).app s) :=
  ⟨fun _ _ hx => congrArg Subtype.val hx, fun y => ⟨y.1, Subtype.ext rfl⟩⟩

theorem truncate_linear (P : Set (Finset ι)) (hP : P.OrdConnected)
    (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    {s t : Finset ι} (h : s ⊆ t) (r : R) (x : (D.truncate (R := R) P hP).obj s) :
    (D.truncate P hP).res h (r • x) = r • (D.truncate P hP).res h x := by
  classical
  refine Subtype.ext ?_
  change (if t ∈ P then D.res h (r • x.1) else 0) =
    r • (if t ∈ P then D.res h x.1 else 0)
  split_ifs <;> simp only [hD, smul_zero]

variable {P Q : Set (Finset ι)} (hP : P.OrdConnected) (hQ : Q.OrdConnected)
  (hPQ : P ⊆ Q) (hupper : ∀ ⦃s t⦄, s ∈ P → t ∈ Q → s ⊆ t → t ∈ P)

include hQ hupper in
/-- Removing an upper subset preserves order-convexity. -/
theorem supportDiff_ordConnected :
    (Q \ P).OrdConnected := by
  constructor
  intro s hs t ht z hz
  exact ⟨hQ.out' hs.1 ht.1 hz, fun hp => ht.2 (hupper hp ht.1 hz.2)⟩

private def supportIncl :
    (D.truncate (R := R) P hP).Hom (D.truncate (R := R) Q hQ) where
  app _ :=
    { toFun := fun x => ⟨x.1, fun hn => x.2 (fun hp => hn (hPQ hp))⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  comm {s t} h x := by
    classical
    refine Subtype.ext ?_
    change (if t ∈ Q then D.res h x.1 else 0) = if t ∈ P then D.res h x.1 else 0
    by_cases hp : t ∈ P
    · rw [if_pos hp, if_pos (hPQ hp)]
    · rw [if_neg hp]
      by_cases hq : t ∈ Q
      · rw [if_pos hq, x.2 (fun hs => hp (hupper hs hq h)), map_zero]
      · rw [if_neg hq]

open Classical in
private def supportProj :
    (D.truncate (R := R) Q hQ).Hom (D.truncate (R := R) (Q \ P) (supportDiff_ordConnected hQ hupper)) where
  app s :=
    { toFun := fun x => ⟨if s ∈ Q \ P then x.1 else 0, fun hn => if_neg hn⟩
      map_zero' := Subtype.ext (by
        change (if s ∈ Q \ P then (0 : D.obj s) else 0) = 0
        simp only [ite_self])
      map_add' x y := Subtype.ext (by
        change (if s ∈ Q \ P then x.1 + y.1 else 0) =
          (if s ∈ Q \ P then x.1 else 0) + (if s ∈ Q \ P then y.1 else 0)
        by_cases hs : s ∈ Q \ P <;> simp only [hs, if_true, if_false, add_zero]) }
  comm {s t} h x := by
    refine Subtype.ext ?_
    change (if t ∈ Q \ P then D.res h (if s ∈ Q \ P then x.1 else 0) else 0) =
      if t ∈ Q \ P then (if t ∈ Q then D.res h x.1 else 0) else 0
    by_cases ht : t ∈ Q \ P
    · rw [if_pos ht, if_pos ht, if_pos ht.1]
      by_cases hs : s ∈ Q \ P
      · rw [if_pos hs]
      · have hs' : s ∉ Q := fun hq => hs ⟨hq, fun hp => ht.2 (hupper hp ht.1 h)⟩
        rw [if_neg hs, x.2 hs', map_zero]
    · rw [if_neg ht, if_neg ht]

variable [DecidableEq ι] [LinearOrder ι]

include hPQ in
/-- The support sequence splits in each coefficient module. -/
theorem shortExact_truncate
    (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x) :
    ∃ S : ShortComplex (CochainComplex (ModuleCat R) ℕ),
      S.ShortExact ∧
        S.X₁ = (D.truncate (R := R) P hP).linearComplex (D.truncate_linear P hP hD) ∧
        S.X₂ = (D.truncate Q hQ).linearComplex (D.truncate_linear Q hQ hD) ∧
        S.X₃ = (D.truncate (Q \ P) (supportDiff_ordConnected hQ hupper)).linearComplex
          (D.truncate_linear (Q \ P) (supportDiff_ordConnected hQ hupper) hD) := by
  classical
  let φ := D.supportIncl hP hQ hPQ hupper
  let ψ := D.supportProj hQ hupper
  have hφ (s : Finset ι) (r : R) (x : (D.truncate P hP).obj s) :
      φ.app s (r • x) = r • φ.app s x := rfl
  have hψ (s : Finset ι) (r : R) (x : (D.truncate Q hQ).obj s) :
      ψ.app s (r • x) = r • ψ.app s x := by
    refine Subtype.ext ?_
    change (if s ∈ Q \ P then r • x.1 else 0) = r • (if s ∈ Q \ P then x.1 else 0)
    split_ifs <;> simp only [smul_zero]
  have hc (s : Finset ι) (x : (D.truncate P hP).obj s) : ψ.app s (φ.app s x) = 0 := by
    refine Subtype.ext ?_
    change (if s ∈ Q \ P then x.1 else 0) = 0
    split_ifs with hs
    · exact x.2 hs.2
    · rfl
  have hi (s : Finset ι) : Function.Injective (φ.app s) := fun _ _ h =>
    Subtype.ext (congrArg Subtype.val h)
  have he (s : Finset ι) : Function.Exact (φ.app s) (ψ.app s) := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x.1, fun hp => ?_⟩, rfl⟩
      by_cases hq : s ∈ Q
      · have e : (if s ∈ Q \ P then x.1 else 0) = 0 := congrArg Subtype.val hx
        exact (if_pos (show s ∈ Q \ P from ⟨hq, hp⟩)).symm.trans e
      · exact x.2 hq
    · rintro ⟨x, rfl⟩
      exact hc s x
  have hs (s : Finset ι) : Function.Surjective (ψ.app s) := by
    intro x
    refine ⟨⟨x.1, fun hq => x.2 (fun h => hq h.1)⟩, Subtype.ext ?_⟩
    change (if s ∈ Q \ P then x.1 else 0) = x.1
    split_ifs with h
    · rfl
    · exact (x.2 h).symm
  exact ⟨_, shortExact_linearCochainMap _ _ _ φ hφ ψ hψ hc (fun s _ => hi s)
    (fun s _ => he s) (fun s _ => hs s), rfl, rfl, rfl⟩

include hPQ in
/-- If the middle support is acyclic, the connecting isomorphism shifts the
cohomology of the remaining lower support by one. -/
theorem nonempty_homology_equiv_truncate_succ
    (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (hacyc : ((D.truncate (R := R) Q hQ).linearComplex (D.truncate_linear Q hQ hD)).Acyclic)
    (n : ℕ) :
    Nonempty (((D.truncate (Q \ P) (supportDiff_ordConnected hQ hupper)).linearComplex
      (D.truncate_linear (Q \ P) (supportDiff_ordConnected hQ hupper) hD)).homology n ≃ₗ[R]
      ((D.truncate P hP).linearComplex (D.truncate_linear P hP hD)).homology (n + 1)) := by
  obtain ⟨S, hS, h₁, h₂, h₃⟩ := D.shortExact_truncate hP hQ hPQ hupper hD
  have hA : S.X₂.Acyclic := h₂.symm ▸ hacyc
  have hz (i : ℕ) : Limits.IsZero (S.X₂.homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hA i)
  rw [← h₁, ← h₃]
  exact ⟨(hS.δIso n (n + 1) (by simp) (hz n) (hz (n + 1))).toLinearEquiv⟩

end HTGeometry.FinsetCechDatum
