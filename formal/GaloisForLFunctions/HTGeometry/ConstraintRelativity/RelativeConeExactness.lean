import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ObserverDescentDuality

/-!
# The mapping cone of a comparison of cochain complexes

For a comparison `Φ : C → X` of `ℤ`-graded cochain complexes of `k`-vector spaces the mapping cone
`Cone(Φ)ⁿ = Xⁿ ⊕ Cⁿ⁺¹`, `d(x, c) = (d_X x − Φ c, −d_C c)`, sits in an exact segment

`Hⁿ(X) → Hⁿ(Cone Φ) → Hⁿ⁺¹(C) → Hⁿ⁺¹(X)`,

which is what identifies the relative-law space with the kernel of the comparison.
-/

namespace HTGeometry.ConstraintRelativity

/-- A `ℤ`-graded cochain complex of `k`-vector spaces. -/
structure ZCochain (k : Type*) [Field k] (M : ℤ → Type*) [∀ n, AddCommGroup (M n)]
    [∀ n, Module k (M n)] where
  /-- The differential, raising the degree by one. -/
  d : ∀ n, M n →ₗ[k] M (n + 1)
  /-- Consecutive differentials compose to zero. -/
  d_squared : ∀ (n : ℤ) (x : M n), d (n + 1) (d n x) = 0

namespace ZCochain

variable {k : Type*} [Field k] {M : ℤ → Type*} [∀ n, AddCommGroup (M n)]
  [∀ n, Module k (M n)]

/-- The cocycles in degree `n + 1`. -/
def cocycles (C : ZCochain k M) (n : ℤ) : Submodule k (M (n + 1)) :=
  LinearMap.ker (C.d (n + 1))

/-- The coboundaries in degree `n + 1`. -/
def coboundaries (C : ZCochain k M) (n : ℤ) : Submodule k (M (n + 1)) :=
  LinearMap.range (C.d n)

theorem mem_cocycles_iff (C : ZCochain k M) {n : ℤ} {x : M (n + 1)} :
    x ∈ C.cocycles n ↔ C.d (n + 1) x = 0 := Iff.rfl

theorem coboundaries_le_cocycles (C : ZCochain k M) (n : ℤ) :
    C.coboundaries n ≤ C.cocycles n := by
  rintro _ ⟨x, rfl⟩
  exact C.d_squared n x

/-- The cohomology in degree `n + 1`. -/
abbrev cohomology (C : ZCochain k M) (n : ℤ) : Type _ :=
  ↥(C.cocycles n) ⧸ Submodule.comap (C.cocycles n).subtype (C.coboundaries n)

/-- The class of a cocycle. -/
def cls (C : ZCochain k M) {n : ℤ} (x : C.cocycles n) : C.cohomology n :=
  Submodule.Quotient.mk x

theorem cls_surjective (C : ZCochain k M) (n : ℤ) :
    Function.Surjective (C.cls (n := n)) := Submodule.Quotient.mk_surjective _

theorem cls_eq_zero_iff (C : ZCochain k M) {n : ℤ} (x : C.cocycles n) :
    C.cls x = 0 ↔ (x : M (n + 1)) ∈ C.coboundaries n := by
  rw [cls, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

end ZCochain

/-- A comparison of `ℤ`-graded cochain complexes. -/
structure ZCochainMap {k : Type*} [Field k] {M N : ℤ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module k (M n)] [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]
    (C : ZCochain k M) (X : ZCochain k N) where
  /-- The degreewise components. -/
  f : ∀ n, M n →ₗ[k] N n
  /-- Compatibility with the differentials. -/
  comm : ∀ (n : ℤ) (x : M n), f (n + 1) (C.d n x) = X.d n (f n x)

namespace ZCochainMap

variable {k : Type*} [Field k] {M N : ℤ → Type*} [∀ n, AddCommGroup (M n)]
  [∀ n, Module k (M n)] [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]
  {C : ZCochain k M} {X : ZCochain k N} (F : ZCochainMap C X)

theorem mapsTo_cocycles {n : ℤ} {x : M (n + 1)} (hx : x ∈ C.cocycles n) :
    F.f (n + 1) x ∈ X.cocycles n := by
  have hx' : C.d (n + 1) x = 0 := hx
  show X.d (n + 1) (F.f (n + 1) x) = 0
  rw [← F.comm]
  show F.f (n + 1 + 1) (C.d (n + 1) x) = 0
  rw [hx', map_zero]

/-- The induced map on cocycles. -/
def cocyclesMap (n : ℤ) : C.cocycles n →ₗ[k] X.cocycles n where
  toFun x := ⟨F.f (n + 1) x, F.mapsTo_cocycles x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The induced map on cohomology. -/
noncomputable def cohomologyMap (n : ℤ) : C.cohomology n →ₗ[k] X.cohomology n := by
  refine Submodule.mapQ _ _ (F.cocyclesMap n) ?_
  rintro y hy
  have hy' : (y : M (n + 1)) ∈ C.coboundaries n := hy
  obtain ⟨z, hz⟩ := hy'
  show ((F.cocyclesMap n y : X.cocycles n) : N (n + 1)) ∈ X.coboundaries n
  refine ⟨F.f n z, ?_⟩
  show X.d n (F.f n z) = F.f (n + 1) (y : M (n + 1))
  rw [← F.comm, hz]

@[simp] theorem cohomologyMap_cls (n : ℤ) (x : C.cocycles n) :
    F.cohomologyMap n (C.cls x) = X.cls (F.cocyclesMap n x) := rfl

end ZCochainMap

/-! ## The mapping cone -/

section Cone

variable {k : Type*} [Field k] {M N : ℤ → Type*} [∀ n, AddCommGroup (M n)]
  [∀ n, Module k (M n)] [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]
  {C : ZCochain k M} {X : ZCochain k N} (Φ : ZCochainMap C X)

/-- The mapping cone of a comparison: `Cone(Φ)ⁿ = Xⁿ ⊕ Cⁿ⁺¹` with
`d(x, c) = (d_X x − Φ c, −d_C c)`. -/
noncomputable def coneComplex : ZCochain k (fun n => N n × M (n + 1)) where
  d n := LinearMap.prod
    ((X.d n).comp (LinearMap.fst k (N n) (M (n + 1)))
      - (Φ.f (n + 1)).comp (LinearMap.snd k (N n) (M (n + 1))))
    (-((C.d (n + 1)).comp (LinearMap.snd k (N n) (M (n + 1)))))
  d_squared n y := by
    refine Prod.ext ?_ ?_
    · show X.d (n + 1) (X.d n y.1 - Φ.f (n + 1) y.2)
        - Φ.f (n + 1 + 1) (-(C.d (n + 1) y.2)) = 0
      rw [map_sub, X.d_squared, map_neg, Φ.comm]
      abel
    · show -(C.d (n + 1 + 1) (-(C.d (n + 1) y.2))) = 0
      rw [map_neg, C.d_squared, neg_neg]

theorem coneComplex_d_apply (n : ℤ) (y : N n × M (n + 1)) :
    (coneComplex Φ).d n y
      = (X.d n y.1 - Φ.f (n + 1) y.2, -(C.d (n + 1) y.2)) := rfl

/-- The inclusion of the target complex into its mapping cone. -/
noncomputable def coneInc : ZCochainMap X (coneComplex Φ) where
  f n := LinearMap.inl k (N n) (M (n + 1))
  comm n x := by
    refine Prod.ext ?_ ?_
    · show X.d n x = X.d n x - Φ.f (n + 1) 0
      rw [map_zero, sub_zero]
    · show (0 : M (n + 1 + 1)) = -(C.d (n + 1) 0)
      rw [map_zero, neg_zero]

theorem conePr_mapsTo {n : ℤ} {y : N (n + 1) × M (n + 1 + 1)}
    (hy : y ∈ (coneComplex Φ).cocycles n) : y.2 ∈ C.cocycles (n + 1) := by
  have hy' : (coneComplex Φ).d (n + 1) y = 0 := hy
  rw [coneComplex_d_apply] at hy'
  have h2 := congrArg Prod.snd hy'
  show C.d (n + 1 + 1) y.2 = 0
  have : -(C.d (n + 1 + 1) y.2) = 0 := h2
  rw [neg_eq_zero] at this
  exact this

theorem conePr_fst {n : ℤ} {y : N (n + 1) × M (n + 1 + 1)}
    (hy : y ∈ (coneComplex Φ).cocycles n) :
    X.d (n + 1) y.1 = Φ.f (n + 1 + 1) y.2 := by
  have hy' : (coneComplex Φ).d (n + 1) y = 0 := hy
  rw [coneComplex_d_apply] at hy'
  have h1 := congrArg Prod.fst hy'
  have : X.d (n + 1) y.1 - Φ.f (n + 1 + 1) y.2 = 0 := h1
  linear_combination (norm := abel) this

/-- The projection of a cone cocycle to its source component. -/
noncomputable def conePrCocycles (n : ℤ) :
    (coneComplex Φ).cocycles n →ₗ[k] C.cocycles (n + 1) where
  toFun y := ⟨(y : N (n + 1) × M (n + 1 + 1)).2, conePr_mapsTo Φ y.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The projection from the cohomology of the cone to the source cohomology. -/
noncomputable def conePr (n : ℤ) :
    (coneComplex Φ).cohomology n →ₗ[k] C.cohomology (n + 1) := by
  refine Submodule.mapQ _ _ (conePrCocycles Φ n) ?_
  rintro y hy
  have hy' : (y : N (n + 1) × M (n + 1 + 1)) ∈ (coneComplex Φ).coboundaries n := hy
  obtain ⟨w, hw⟩ := hy'
  show ((conePrCocycles Φ n y : C.cocycles (n + 1)) : M (n + 1 + 1)) ∈ C.coboundaries (n + 1)
  refine ⟨-w.2, ?_⟩
  show C.d (n + 1) (-w.2) = (y : N (n + 1) × M (n + 1 + 1)).2
  rw [map_neg, ← congrArg Prod.snd hw, coneComplex_d_apply]

@[simp] theorem conePr_cls (n : ℤ) (y : (coneComplex Φ).cocycles n) :
    conePr Φ n ((coneComplex Φ).cls y) = C.cls (conePrCocycles Φ n y) := rfl

/-- A cone class whose source projection is a nonzero source class is itself nonzero: a degree-zero
cone boundary has source coordinate a source coboundary. -/
theorem cone_cls_ne_zero_of_conePr_ne_zero (n : ℤ) (y : (coneComplex Φ).cocycles n)
    (h : C.cls (conePrCocycles Φ n y) ≠ 0) : (coneComplex Φ).cls y ≠ 0 := by
  intro hz
  exact h (by rw [← conePr_cls, hz, map_zero])

/-- **Card `(ROD.9)`, exactness at the cone.**  The image of the target cohomology is exactly the
kernel of the projection. -/
theorem cone_exact_left (n : ℤ) :
    LinearMap.range ((coneInc Φ).cohomologyMap n) = LinearMap.ker (conePr Φ n) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := X.cls_surjective n u
    rw [LinearMap.mem_ker, ZCochainMap.cohomologyMap_cls, conePr_cls,
      ZCochain.cls_eq_zero_iff]
    show (0 : M (n + 1 + 1)) ∈ C.coboundaries (n + 1)
    exact zero_mem _
  · intro z hz
    obtain ⟨y, rfl⟩ := (coneComplex Φ).cls_surjective n z
    rw [LinearMap.mem_ker, conePr_cls, ZCochain.cls_eq_zero_iff] at hz
    obtain ⟨b, hb⟩ := hz
    have hb' : C.d (n + 1) b = (y : N (n + 1) × M (n + 1 + 1)).2 := hb
    have hfst := conePr_fst Φ y.2
    have hx : X.d (n + 1) ((y : N (n + 1) × M (n + 1 + 1)).1 - Φ.f (n + 1) b) = 0 := by
      rw [map_sub, hfst, ← hb', Φ.comm]
      exact sub_self _
    refine ⟨X.cls ⟨(y : N (n + 1) × M (n + 1 + 1)).1 - Φ.f (n + 1) b, hx⟩, ?_⟩
    rw [ZCochainMap.cohomologyMap_cls]
    refine (Submodule.Quotient.eq _).2 ?_
    show ((coneInc Φ).cocyclesMap n
        ⟨(y : N (n + 1) × M (n + 1 + 1)).1 - Φ.f (n + 1) b, hx⟩ : N (n + 1) × M (n + 1 + 1))
      - (y : N (n + 1) × M (n + 1 + 1)) ∈ (coneComplex Φ).coboundaries n
    refine ⟨(0, b), ?_⟩
    rw [coneComplex_d_apply]
    refine Prod.ext ?_ ?_
    · show X.d n 0 - Φ.f (n + 1) b
        = ((y : N (n + 1) × M (n + 1 + 1)).1 - Φ.f (n + 1) b)
          - (y : N (n + 1) × M (n + 1 + 1)).1
      rw [map_zero]
      abel
    · show -(C.d (n + 1) b) = (0 : M (n + 1 + 1)) - (y : N (n + 1) × M (n + 1 + 1)).2
      rw [hb']
      abel

/-- **Card `(ROD.9)`, exactness at the source.**  The image of the projection is exactly the
kernel of the comparison. -/
theorem cone_exact_right (n : ℤ) :
    LinearMap.range (conePr Φ n) = LinearMap.ker (Φ.cohomologyMap (n + 1)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := (coneComplex Φ).cls_surjective n z
    rw [LinearMap.mem_ker, conePr_cls, ZCochainMap.cohomologyMap_cls,
      ZCochain.cls_eq_zero_iff]
    exact ⟨(y : N (n + 1) × M (n + 1 + 1)).1, conePr_fst Φ y.2⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := C.cls_surjective (n + 1) z
    rw [LinearMap.mem_ker, ZCochainMap.cohomologyMap_cls, ZCochain.cls_eq_zero_iff] at hz
    obtain ⟨x, hx⟩ := hz
    have hcoc : ((x, (c : M (n + 1 + 1))) : N (n + 1) × M (n + 1 + 1))
        ∈ (coneComplex Φ).cocycles n := by
      show (coneComplex Φ).d (n + 1) (x, (c : M (n + 1 + 1))) = 0
      rw [coneComplex_d_apply]
      refine Prod.ext ?_ ?_
      · show X.d (n + 1) x - Φ.f (n + 1 + 1) (c : M (n + 1 + 1)) = 0
        rw [hx]
        exact sub_self _
      · show -(C.d (n + 1 + 1) (c : M (n + 1 + 1))) = 0
        have : C.d (n + 1 + 1) (c : M (n + 1 + 1)) = 0 := c.2
        rw [this, neg_zero]
    refine ⟨(coneComplex Φ).cls ⟨(x, (c : M (n + 1 + 1))), hcoc⟩, ?_⟩
    rw [conePr_cls]
    congr 1

/-- **Card `(ROD.10)`, boxed.**  The relative-law space of the comparison is the kernel of the
comparison on cohomology.  No exactness is assumed: it is supplied by the mapping cone. -/
noncomputable def coneRelativeLawEquiv (n : ℤ) :
    ((coneComplex Φ).cohomology n ⧸ LinearMap.range ((coneInc Φ).cohomologyMap n))
      ≃ₗ[k] LinearMap.ker (Φ.cohomologyMap (n + 1)) :=
  relativeLawEquiv ((coneInc Φ).cohomologyMap n) (conePr Φ n) (Φ.cohomologyMap (n + 1))
    (cone_exact_left Φ n) (cone_exact_right Φ n)

/-- **Card `(ROD.11)`, boxed.**  The observer-descent quotient of the comparison is the dual of
its relative-law space. -/
noncomputable def coneRelativeObserverDuality (V : Type*) [AddCommGroup V] [Module k V]
    (n : ℤ) :
    ((C.cohomology (n + 1) →ₗ[k] V) ⧸
        LinearMap.range (pullback (V := V) (Φ.cohomologyMap (n + 1))))
      ≃ₗ[k] (((coneComplex Φ).cohomology n ⧸
        LinearMap.range ((coneInc Φ).cohomologyMap n)) →ₗ[k] V) :=
  relativeObserverDuality ((coneInc Φ).cohomologyMap n) (conePr Φ n) (Φ.cohomologyMap (n + 1))
    (cone_exact_left Φ n) (cone_exact_right Φ n)

/-! ## Cone characters -/

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- A functional on the source that kills coboundaries descends to source cohomology. -/
noncomputable def sourceCharacter (n : ℤ) (P : M (n + 1) →ₗ[k] V)
    (hP : ∀ b : M n, P (C.d n b) = 0) : C.cohomology n →ₗ[k] V := by
  refine Submodule.liftQ _ (P.comp (C.cocycles n).subtype) ?_
  rintro c hc
  have hc' : (c : M (n + 1)) ∈ C.coboundaries n := hc
  obtain ⟨b, hb⟩ := hc'
  show P (c : M (n + 1)) = 0
  rw [← hb]
  exact hP b

@[simp] theorem sourceCharacter_cls (n : ℤ) (P : M (n + 1) →ₗ[k] V)
    (hP : ∀ b : M n, P (C.d n b) = 0) (c : C.cocycles n) :
    sourceCharacter (C := C) n P hP (C.cls c) = P (c : M (n + 1)) := rfl

/-- The same functional read on the mapping cone: a cone class is sent to the value of `P` on its
source coordinate. -/
noncomputable def coneCharacter (n : ℤ) (P : M (n + 1 + 1) →ₗ[k] V)
    (hP : ∀ b : M (n + 1), P (C.d (n + 1) b) = 0) :
    (coneComplex Φ).cohomology n →ₗ[k] V := by
  refine Submodule.liftQ _
    (P.comp ((LinearMap.snd k (N (n + 1)) (M (n + 1 + 1))).comp
      ((coneComplex Φ).cocycles n).subtype)) ?_
  rintro y hy
  have hy' : (y : N (n + 1) × M (n + 1 + 1)) ∈ (coneComplex Φ).coboundaries n := hy
  obtain ⟨w, hw⟩ := hy'
  show P (y : N (n + 1) × M (n + 1 + 1)).2 = 0
  rw [← congrArg Prod.snd hw, coneComplex_d_apply]
  show P (-(C.d (n + 1) w.2)) = 0
  rw [map_neg, hP, neg_zero]

@[simp] theorem coneCharacter_cls (n : ℤ) (P : M (n + 1 + 1) →ₗ[k] V)
    (hP : ∀ b : M (n + 1), P (C.d (n + 1) b) = 0) (y : (coneComplex Φ).cocycles n) :
    coneCharacter Φ n P hP ((coneComplex Φ).cls y)
      = P (y : N (n + 1) × M (n + 1 + 1)).2 := rfl

/-- A cone character reads the source coordinate only: it annihilates every class coming from the
target complex, so it never sees the chosen primitive. -/
theorem coneCharacter_coneInc (n : ℤ) (P : M (n + 1 + 1) →ₗ[k] V)
    (hP : ∀ b : M (n + 1), P (C.d (n + 1) b) = 0) (u : X.cohomology n) :
    coneCharacter Φ n P hP ((coneInc Φ).cohomologyMap n u) = 0 := by
  obtain ⟨x, rfl⟩ := X.cls_surjective n u
  rw [ZCochainMap.cohomologyMap_cls, coneCharacter_cls]
  show P (0 : M (n + 1 + 1)) = 0
  exact map_zero _

/-- Consequently the character descends to the relative-law space. -/
noncomputable def coneCharacterRel (n : ℤ) (P : M (n + 1 + 1) →ₗ[k] V)
    (hP : ∀ b : M (n + 1), P (C.d (n + 1) b) = 0) :
    ((coneComplex Φ).cohomology n ⧸ LinearMap.range ((coneInc Φ).cohomologyMap n)) →ₗ[k] V :=
  Submodule.liftQ _ (coneCharacter Φ n P hP)
    (by
      rintro _ ⟨u, rfl⟩
      exact coneCharacter_coneInc Φ n P hP u)

/-- **Card `(ROD.12)`, `(ROD.17)`–`(ROD.18)` shape.**  Pairing a cone character with a relative-law
class computes the source character on the class that the relative law names in `ker f`. -/
theorem coneCharacterRel_eq (n : ℤ) (P : M (n + 1 + 1) →ₗ[k] V)
    (hP : ∀ b : M (n + 1), P (C.d (n + 1) b) = 0)
    (z : (coneComplex Φ).cohomology n ⧸ LinearMap.range ((coneInc Φ).cohomologyMap n)) :
    coneCharacterRel Φ n P hP z
      = sourceCharacter (C := C) (n + 1) P hP
        ((coneRelativeLawEquiv Φ n z : C.cohomology (n + 1))) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := (coneComplex Φ).cls_surjective n w
  show coneCharacter Φ n P hP ((coneComplex Φ).cls y) = _
  rw [coneRelativeLawEquiv, relativeLawEquiv_mk, conePr_cls, coneCharacter_cls,
    sourceCharacter_cls]
  rfl

end Cone

end HTGeometry.ConstraintRelativity
