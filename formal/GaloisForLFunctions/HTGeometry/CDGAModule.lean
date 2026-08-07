import GaloisForLFunctions.HTGeometry.CDGA
import Mathlib.Tactic.Abel

/-!
# Differential graded modules over a commutative differential graded algebra

A differential graded module over a commutative differential graded algebra is a family of modules
indexed by the nonnegative degrees, with a bilinear action of the algebra that adds degrees, and a
differential raising the degree by one, squaring to zero and satisfying the Leibniz rule for the
action.  Its cohomology in each degree is the cocycles modulo the coboundaries, a morphism induces a
map on cohomology, and a quasi-isomorphism is a morphism inducing isomorphisms in every degree.

This is the layer the derived tensor product is built on: an algebra is a module over itself, a
degreewise isomorphism is a quasi-isomorphism, and quasi-isomorphisms compose — so the notion of
"the same up to quasi-isomorphism" is available for modules, not only for algebras.

* `CDGAModuleStructure` : the structure.
* `CDGAModuleStructure.cohomology` : the cohomology in a degree.
* `CDGAModuleHom`, `CDGAModuleHom.cohomologyMap` : morphisms and the induced map.
* `CDGAModuleHom.IsQuasiIso` : a morphism inducing isomorphisms on cohomology.
* `CDGAStructure.selfModule` : an algebra is a module over itself.
-/

universe u v w w'

namespace GaloisForLFunctions.HTGeometry

/-- **A differential graded module** over a commutative differential graded algebra, in nonnegative
degrees, on a given family of modules. -/
structure CDGAModuleStructure {R : Type u} [CommRing R] {X : ℕ → Type v}
    [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)] (A : CDGAStructure R X) (M : ℕ → Type w)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)] where
  /-- The action of the algebra, adding degrees. -/
  act : ∀ {a b n : ℕ}, a + b = n → X a → M b → M n
  /-- The differential, raising the degree by one. -/
  d : ∀ n : ℕ, M n → M (n + 1)
  act_add_left : ∀ {a b n : ℕ} (h : a + b = n) (x x' : X a) (m : M b),
    act h (x + x') m = act h x m + act h x' m
  act_add_right : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (m m' : M b),
    act h x (m + m') = act h x m + act h x m'
  act_smul_left : ∀ {a b n : ℕ} (h : a + b = n) (c : R) (x : X a) (m : M b),
    act h (c • x) m = c • act h x m
  act_smul_right : ∀ {a b n : ℕ} (h : a + b = n) (c : R) (x : X a) (m : M b),
    act h x (c • m) = c • act h x m
  act_assoc : ∀ {a b k m' m'' n : ℕ} (h₁ : a + b = m') (h₂ : m' + k = n) (h₃ : b + k = m'')
    (h₄ : a + m'' = n) (x : X a) (y : X b) (m : M k),
    act h₂ (A.mul h₁ x y) m = act h₄ x (act h₃ y m)
  d_add : ∀ (n : ℕ) (m m' : M n), d n (m + m') = d n m + d n m'
  d_smul : ∀ (n : ℕ) (c : R) (m : M n), d n (c • m) = c • d n m
  d_d : ∀ (n : ℕ) (m : M n), d (n + 1) (d n m) = 0
  d_act : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (m : M b),
    d n (act h x m) = act (show a + 1 + b = n + 1 by omega) (A.d a x) m +
      ((-1 : R)) ^ a • act (show a + (b + 1) = n + 1 by omega) x (d b m)

namespace CDGAModuleStructure

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] (P : CDGAModuleStructure A M)

/-- The differential as a linear map. -/
def dₗ (n : ℕ) : M n →ₗ[R] M (n + 1) where
  toFun := P.d n
  map_add' := P.d_add n
  map_smul' := P.d_smul n

@[simp] theorem dₗ_apply (n : ℕ) (m : M n) : P.dₗ n m = P.d n m := rfl

/-- The action of a fixed element of the algebra, as a linear map. -/
def actₗ {b i n : ℕ} (h : b + i = n) (x : X b) : M i →ₗ[R] M n where
  toFun m := P.act h x m
  map_add' := P.act_add_right h x
  map_smul' := fun c m => P.act_smul_right h c x m

@[simp] theorem actₗ_apply {b i n : ℕ} (h : b + i = n) (x : X b) (m : M i) :
    P.actₗ h x m = P.act h x m := rfl

/-- The cocycles in a degree. -/
def cocycles (n : ℕ) : Submodule R (M n) := LinearMap.ker (P.dₗ n)

@[simp] theorem mem_cocycles {n : ℕ} {m : M n} : m ∈ P.cocycles n ↔ P.d n m = 0 := Iff.rfl

/-- The coboundaries inside the cocycles of the next degree. -/
def coboundaries (n : ℕ) : Submodule R (P.cocycles (n + 1)) where
  carrier := {y | ∃ m : M n, (y : M (n + 1)) = P.d n m}
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨m', hm'⟩
    exact ⟨m + m', by rw [P.d_add, ← hm, ← hm']; rfl⟩
  zero_mem' := ⟨0, by
    have h : P.d n 0 = 0 := (P.dₗ n).map_zero
    rw [h]
    rfl⟩
  smul_mem' := by
    rintro c a ⟨m, hm⟩
    exact ⟨c • m, by rw [P.d_smul, ← hm]; rfl⟩

@[simp] theorem mem_coboundaries {n : ℕ} {y : P.cocycles (n + 1)} :
    y ∈ P.coboundaries n ↔ ∃ m : M n, (y : M (n + 1)) = P.d n m := Iff.rfl

/-- The cohomology in a degree. -/
abbrev cohomology (n : ℕ) := (↥(P.cocycles (n + 1))) ⧸ (P.coboundaries n)

end CDGAModuleStructure

/-- **A morphism of differential graded modules**: a degree-wise linear map commuting with the
action of the algebra and with the differential. -/
structure CDGAModuleHom {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
    [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
    [∀ n, Module R (M n)] {N : ℕ → Type w'} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
    (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) where
  /-- The underlying degree-wise map. -/
  toFun : ∀ n : ℕ, M n → N n
  map_add : ∀ (n : ℕ) (m m' : M n), toFun n (m + m') = toFun n m + toFun n m'
  map_smul : ∀ (n : ℕ) (c : R) (m : M n), toFun n (c • m) = c • toFun n m
  map_act : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (m : M b),
    toFun n (P.act h x m) = Q.act h x (toFun b m)
  map_d : ∀ (n : ℕ) (m : M n), toFun (n + 1) (P.d n m) = Q.d n (toFun n m)

namespace CDGAModuleHom

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] {N : ℕ → Type w'} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N} (φ : CDGAModuleHom P Q)

/-- The underlying map in a degree, as a linear map. -/
def mapₗ (n : ℕ) : M n →ₗ[R] N n where
  toFun := φ.toFun n
  map_add' := φ.map_add n
  map_smul' := φ.map_smul n

@[simp] theorem mapₗ_apply (n : ℕ) (m : M n) : φ.mapₗ n m = φ.toFun n m := rfl

theorem map_mem_cocycles {n : ℕ} {m : M n} (hm : m ∈ P.cocycles n) :
    φ.toFun n m ∈ Q.cocycles n := by
  have h : Q.d n (φ.toFun n m) = φ.toFun (n + 1) (P.d n m) := (φ.map_d n m).symm
  have hm' : P.d n m = 0 := hm
  rw [CDGAModuleStructure.mem_cocycles, h, hm']
  exact (φ.mapₗ (n + 1)).map_zero

/-- The induced map on cocycles. -/
def cocyclesMap (n : ℕ) : P.cocycles n →ₗ[R] Q.cocycles n where
  toFun m := ⟨φ.toFun n m, φ.map_mem_cocycles m.2⟩
  map_add' _ _ := Subtype.ext (φ.map_add n _ _)
  map_smul' _ _ := Subtype.ext (φ.map_smul n _ _)

@[simp] theorem cocyclesMap_coe (n : ℕ) (m : P.cocycles n) :
    ((φ.cocyclesMap n m : Q.cocycles n) : N n) = φ.toFun n m := rfl

/-- The induced map on cohomology. -/
def cohomologyMap (n : ℕ) : P.cohomology n →ₗ[R] Q.cohomology n :=
  Submodule.mapQ _ _ (φ.cocyclesMap (n + 1)) (by
    rintro y ⟨m, hm⟩
    exact ⟨φ.toFun n m, by
      show φ.toFun (n + 1) (y : M (n + 1)) = _
      rw [hm, φ.map_d n m]⟩)

@[simp] theorem cohomologyMap_mk (n : ℕ) (m : P.cocycles (n + 1)) :
    φ.cohomologyMap n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (φ.cocyclesMap (n + 1) m) := rfl

/-- A morphism of differential graded modules is a quasi-isomorphism when it induces isomorphisms
on cohomology in every degree. -/
def IsQuasiIso : Prop := ∀ n : ℕ, Function.Bijective (φ.cohomologyMap n)

/-- The identity morphism. -/
def id (P : CDGAModuleStructure A M) : CDGAModuleHom P P where
  toFun _ m := m
  map_add _ _ _ := rfl
  map_smul _ _ _ := rfl
  map_act _ _ _ := rfl
  map_d _ _ := rfl

/-- The composite of two morphisms. -/
def comp {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} (ψ : CDGAModuleHom Q S) (φ : CDGAModuleHom P Q) :
    CDGAModuleHom P S where
  toFun n m := ψ.toFun n (φ.toFun n m)
  map_add n m m' := by rw [φ.map_add, ψ.map_add]
  map_smul n c m := by rw [φ.map_smul, ψ.map_smul]
  map_act h x m := by rw [φ.map_act, ψ.map_act]
  map_d n m := by rw [φ.map_d, ψ.map_d]

/-- Two morphisms with the same underlying degreewise maps are equal. -/
theorem hom_ext {φ χ : CDGAModuleHom P Q} (h : ∀ (n : ℕ) (m : M n), φ.toFun n m = χ.toFun n m) :
    φ = χ := by
  cases φ
  cases χ
  congr 1
  funext n m
  exact h n m

@[simp] theorem comp_toFun {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} (ψ : CDGAModuleHom Q S) (φ : CDGAModuleHom P Q) (n : ℕ)
    (m : M n) : (ψ.comp φ).toFun n m = ψ.toFun n (φ.toFun n m) := rfl

theorem cohomologyMap_id (P : CDGAModuleStructure A M) (n : ℕ) (y : P.cohomology n) :
    (CDGAModuleHom.id P).cohomologyMap n y = y := by
  refine Quotient.inductionOn' y fun m => ?_
  rfl

theorem cohomologyMap_comp {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} (ψ : CDGAModuleHom Q S) (φ : CDGAModuleHom P Q) (n : ℕ)
    (y : P.cohomology n) :
    (ψ.comp φ).cohomologyMap n y = ψ.cohomologyMap n (φ.cohomologyMap n y) := by
  refine Quotient.inductionOn' y fun m => ?_
  rfl

/-- **Quasi-isomorphisms compose.** -/
theorem IsQuasiIso.comp {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} {ψ : CDGAModuleHom Q S} {φ : CDGAModuleHom P Q}
    (hψ : ψ.IsQuasiIso) (hφ : φ.IsQuasiIso) : (ψ.comp φ).IsQuasiIso := by
  intro n
  constructor
  · intro a b hab
    refine (hφ n).1 ((hψ n).1 ?_)
    rw [← cohomologyMap_comp, ← cohomologyMap_comp]
    exact hab
  · intro c
    obtain ⟨b, hb⟩ := (hψ n).2 c
    obtain ⟨a, ha⟩ := (hφ n).2 b
    exact ⟨a, by rw [cohomologyMap_comp, ha, hb]⟩

/-- A degreewise bijective morphism sends cocycles onto cocycles bijectively. -/
theorem cocyclesMap_bijective {φ : CDGAModuleHom P Q} (hφ : ∀ n, Function.Bijective (φ.toFun n))
    (n : ℕ) : Function.Bijective (φ.cocyclesMap n) := by
  constructor
  · intro a b hab
    exact Subtype.ext ((hφ n).1 (congrArg Subtype.val hab))
  · intro y
    obtain ⟨m, hm⟩ := (hφ n).2 (y : Q.cocycles n)
    have hcoc : m ∈ P.cocycles n := by
      show P.d n m = 0
      refine (hφ (n + 1)).1 ?_
      rw [φ.map_d n m, hm]
      have hy : Q.d n (y : Q.cocycles n) = 0 := y.2
      rw [hy]
      exact ((φ.mapₗ (n + 1)).map_zero).symm
    exact ⟨⟨m, hcoc⟩, Subtype.ext hm⟩

/-- **A degreewise bijective morphism is a quasi-isomorphism.**  This is how a quasi-isomorphism is
transported along an identification of differential graded modules. -/
theorem IsQuasiIso.of_bijective {φ : CDGAModuleHom P Q}
    (hφ : ∀ n, Function.Bijective (φ.toFun n)) : φ.IsQuasiIso := by
  intro n
  constructor
  · refine fun a b => Quotient.inductionOn₂' a b fun u v huv => ?_
    obtain ⟨w, hw⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 huv)
    obtain ⟨w', hw'⟩ := (hφ n).2 w
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨w', ?_⟩)
    refine (hφ (n + 1)).1 ?_
    rw [φ.map_d n w', hw']
    have hsub : φ.toFun (n + 1) ((u : M (n + 1)) - (v : M (n + 1)))
        = φ.toFun (n + 1) (u : M (n + 1)) - φ.toFun (n + 1) (v : M (n + 1)) :=
      map_sub (φ.mapₗ (n + 1)) _ _
    show φ.toFun (n + 1) ((u : M (n + 1)) - (v : M (n + 1))) = Q.d n w
    rw [hsub]
    exact hw
  · refine fun c => Quotient.inductionOn' c fun u => ?_
    obtain ⟨m, hm⟩ := (cocyclesMap_bijective hφ (n + 1)).2 u
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    show Submodule.Quotient.mk (φ.cocyclesMap (n + 1) m) = _
    rw [hm]
    rfl

/-- **Two out of three, left**: if a composite and its first factor are quasi-isomorphisms, so is
the second factor. -/
theorem IsQuasiIso.of_comp_left {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} {ψ : CDGAModuleHom Q S} {φ : CDGAModuleHom P Q}
    (hcomp : (ψ.comp φ).IsQuasiIso) (hφ : φ.IsQuasiIso) : ψ.IsQuasiIso := by
  intro n
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := (hφ n).2 x
    obtain ⟨b, hb⟩ := (hφ n).2 y
    have hab : (ψ.comp φ).cohomologyMap n a = (ψ.comp φ).cohomologyMap n b := by
      rw [cohomologyMap_comp, cohomologyMap_comp, ha, hb, hxy]
    rw [← ha, ← hb, (hcomp n).1 hab]
  · intro c
    obtain ⟨a, ha⟩ := (hcomp n).2 c
    exact ⟨φ.cohomologyMap n a, by rw [← cohomologyMap_comp]; exact ha⟩

/-- **Two out of three, right**: if a composite and its second factor are quasi-isomorphisms, so is
the first factor. -/
theorem IsQuasiIso.of_comp_right {L : ℕ → Type w'} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {S : CDGAModuleStructure A L} {ψ : CDGAModuleHom Q S} {φ : CDGAModuleHom P Q}
    (hcomp : (ψ.comp φ).IsQuasiIso) (hψ : ψ.IsQuasiIso) : φ.IsQuasiIso := by
  intro n
  constructor
  · intro x y hxy
    refine (hcomp n).1 ?_
    rw [cohomologyMap_comp, cohomologyMap_comp, hxy]
  · intro b
    obtain ⟨a, ha⟩ := (hcomp n).2 (ψ.cohomologyMap n b)
    refine ⟨a, (hψ n).1 ?_⟩
    rw [← cohomologyMap_comp]
    exact ha

/-- **The identity is a quasi-isomorphism.** -/
theorem isQuasiIso_id (P : CDGAModuleStructure A M) : (CDGAModuleHom.id P).IsQuasiIso := fun n => by
  constructor
  · intro a b hab
    rw [← cohomologyMap_id P n a, ← cohomologyMap_id P n b, hab]
  · intro c
    exact ⟨c, cohomologyMap_id P n c⟩

end CDGAModuleHom

namespace CDGAStructure

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] (A : CDGAStructure R X)

/-- **An algebra is a module over itself.** -/
def selfModule : CDGAModuleStructure A X where
  act h x y := A.mul h x y
  d := A.d
  act_add_left h x x' y := A.mul_add_left h x x' y
  act_add_right h x y y' := A.mul_add_right h x y y'
  act_smul_left h c x y := A.mul_smul_left h c x y
  act_smul_right h c x y := A.mul_smul_right h c x y
  act_assoc h₁ h₂ h₃ h₄ x y z := A.mul_assoc h₁ h₂ h₃ h₄ x y z
  d_add := A.d_add
  d_smul := A.d_smul
  d_d := A.d_d
  d_act h x y := A.d_mul h x y

@[simp] theorem selfModule_d (n : ℕ) (x : X n) : A.selfModule.d n x = A.d n x := rfl

@[simp] theorem selfModule_cocycles (n : ℕ) : A.selfModule.cocycles n = A.cocycles n := rfl

end CDGAStructure


namespace CDGAModuleStructure

section Prod

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **The direct sum of two differential graded modules**, degreewise. -/
def prod (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) :
    CDGAModuleStructure A (fun n => M n × N n) where
  act h x m := (P.act h x m.1, Q.act h x m.2)
  d n m := (P.d n m.1, Q.d n m.2)
  act_add_left h x x' m := by
    refine Prod.ext ?_ ?_
    · exact P.act_add_left h x x' m.1
    · exact Q.act_add_left h x x' m.2
  act_add_right h x m m' := by
    refine Prod.ext ?_ ?_
    · exact P.act_add_right h x m.1 m'.1
    · exact Q.act_add_right h x m.2 m'.2
  act_smul_left h c x m := by
    refine Prod.ext ?_ ?_
    · exact P.act_smul_left h c x m.1
    · exact Q.act_smul_left h c x m.2
  act_smul_right h c x m := by
    refine Prod.ext ?_ ?_
    · exact P.act_smul_right h c x m.1
    · exact Q.act_smul_right h c x m.2
  act_assoc h₁ h₂ h₃ h₄ x y m := by
    refine Prod.ext ?_ ?_
    · exact P.act_assoc h₁ h₂ h₃ h₄ x y m.1
    · exact Q.act_assoc h₁ h₂ h₃ h₄ x y m.2
  d_add n m m' := by
    refine Prod.ext ?_ ?_
    · exact P.d_add n m.1 m'.1
    · exact Q.d_add n m.2 m'.2
  d_smul n c m := by
    refine Prod.ext ?_ ?_
    · exact P.d_smul n c m.1
    · exact Q.d_smul n c m.2
  d_d n m := by
    refine Prod.ext ?_ ?_
    · exact P.d_d n m.1
    · exact Q.d_d n m.2
  d_act h x m := by
    refine Prod.ext ?_ ?_
    · exact P.d_act h x m.1
    · exact Q.d_act h x m.2

@[simp] theorem prod_d (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (m : M n × N n) : (P.prod Q).d n m = (P.d n m.1, Q.d n m.2) := rfl

theorem mem_prod_cocycles {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N} {n : ℕ}
    {m : M n × N n} : m ∈ (P.prod Q).cocycles n ↔ m.1 ∈ P.cocycles n ∧ m.2 ∈ Q.cocycles n := by
  constructor
  · intro hm
    have h : (P.d n m.1, Q.d n m.2) = (0, 0) := hm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    have e1 : P.d n m.1 = 0 := h1
    have e2 : Q.d n m.2 = 0 := h2
    show (P.d n m.1, Q.d n m.2) = 0
    rw [e1, e2]
    rfl

/-- The first component of a cocycle of a direct sum. -/
def prodFst (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {n : ℕ}
    (u : (P.prod Q).cocycles n) : P.cocycles n :=
  ⟨(u : M n × N n).1, (mem_prod_cocycles.1 u.2).1⟩

/-- The second component of a cocycle of a direct sum. -/
def prodSnd (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {n : ℕ}
    (u : (P.prod Q).cocycles n) : Q.cocycles n :=
  ⟨(u : M n × N n).2, (mem_prod_cocycles.1 u.2).2⟩

@[simp] theorem prodFst_coe (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {n : ℕ}
    (u : (P.prod Q).cocycles n) : ((prodFst P Q u : P.cocycles n) : M n) = (u : M n × N n).1 := rfl

@[simp] theorem prodSnd_coe (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {n : ℕ}
    (u : (P.prod Q).cocycles n) : ((prodSnd P Q u : Q.cocycles n) : N n) = (u : M n × N n).2 := rfl

end Prod

end CDGAModuleStructure

namespace CDGAModuleHom

section Prod

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N}
  {P' : CDGAModuleStructure A M'} {Q' : CDGAModuleStructure A N'}

/-- **The direct sum of two morphisms.** -/
def prodMap (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q') :
    CDGAModuleHom (P.prod Q) (P'.prod Q') where
  toFun n m := (φ.toFun n m.1, ψ.toFun n m.2)
  map_add n m m' := by
    refine Prod.ext ?_ ?_
    · exact φ.map_add n m.1 m'.1
    · exact ψ.map_add n m.2 m'.2
  map_smul n c m := by
    refine Prod.ext ?_ ?_
    · exact φ.map_smul n c m.1
    · exact ψ.map_smul n c m.2
  map_act h x m := by
    refine Prod.ext ?_ ?_
    · exact φ.map_act h x m.1
    · exact ψ.map_act h x m.2
  map_d n m := by
    refine Prod.ext ?_ ?_
    · exact φ.map_d n m.1
    · exact ψ.map_d n m.2

@[simp] theorem prodMap_toFun (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q') (n : ℕ)
    (m : M n × N n) : (φ.prodMap ψ).toFun n m = (φ.toFun n m.1, ψ.toFun n m.2) := rfl

/-- **A direct sum of quasi-isomorphisms is a quasi-isomorphism.**  A pair is a coboundary exactly
when both of its components are, so injectivity and surjectivity on cohomology are componentwise. -/
theorem IsQuasiIso.prodMap {φ : CDGAModuleHom P P'} {ψ : CDGAModuleHom Q Q'}
    (hφ : φ.IsQuasiIso) (hψ : ψ.IsQuasiIso) : (φ.prodMap ψ).IsQuasiIso := by
  intro n
  constructor
  · refine fun a b => Quotient.inductionOn₂' a b fun u v huv => ?_
    obtain ⟨w, hw⟩ := (Submodule.Quotient.eq _).1 huv
    have h1 : Submodule.Quotient.mk
        (φ.cocyclesMap (n + 1) (CDGAModuleStructure.prodFst P Q u))
        = Submodule.Quotient.mk
          (φ.cocyclesMap (n + 1) (CDGAModuleStructure.prodFst P Q v)) :=
      (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2
        ⟨w.1, by simpa using congrArg Prod.fst hw⟩)
    have h2 : Submodule.Quotient.mk
        (ψ.cocyclesMap (n + 1) (CDGAModuleStructure.prodSnd P Q u))
        = Submodule.Quotient.mk
          (ψ.cocyclesMap (n + 1) (CDGAModuleStructure.prodSnd P Q v)) :=
      (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2
        ⟨w.2, by simpa using congrArg Prod.snd hw⟩)
    obtain ⟨s, hs⟩ := (CDGAModuleStructure.mem_coboundaries _).1
      ((Submodule.Quotient.eq _).1 ((hφ n).1 h1))
    obtain ⟨t, ht⟩ := (CDGAModuleStructure.mem_coboundaries _).1
      ((Submodule.Quotient.eq _).1 ((hψ n).1 h2))
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨(s, t), ?_⟩)
    refine Prod.ext ?_ ?_
    · simpa using hs
    · simpa using ht
  · refine fun c => Quotient.inductionOn' c fun u => ?_
    obtain ⟨a, ha⟩ := (hφ n).2 (Submodule.Quotient.mk (CDGAModuleStructure.prodFst P' Q' u))
    obtain ⟨b, hb⟩ := (hψ n).2 (Submodule.Quotient.mk (CDGAModuleStructure.prodSnd P' Q' u))
    obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ b
    rw [← hm₁] at ha
    rw [← hm₂] at hb
    obtain ⟨s, hs⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 ha)
    obtain ⟨t, ht⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 hb)
    refine ⟨Submodule.Quotient.mk ⟨((m₁ : M (n + 1)), (m₂ : N (n + 1))),
      CDGAModuleStructure.mem_prod_cocycles.2 ⟨m₁.2, m₂.2⟩⟩, ?_⟩
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨(s, t), ?_⟩)
    refine Prod.ext ?_ ?_
    · simpa using hs
    · simpa using ht

end Prod

end CDGAModuleHom


/-- **A twisting cochain**: a degree-one map from one differential graded module to another which
is linear over the algebra up to the Koszul sign and anticommutes with the differentials.  This is
the attaching datum of a cell. -/
structure CDGATwist {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
    [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
    [∀ n, Module R (M n)] {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
    (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) where
  /-- The twisting map, raising the degree by one. -/
  τ : ∀ n : ℕ, N n → M (n + 1)
  τ_add : ∀ (n : ℕ) (c c' : N n), τ n (c + c') = τ n c + τ n c'
  τ_smul : ∀ (n : ℕ) (r : R) (c : N n), τ n (r • c) = r • τ n c
  τ_act : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (c : N b),
    τ n (Q.act h x c) = ((-1 : R)) ^ a • P.act (show a + (b + 1) = n + 1 by omega) x (τ b c)
  τ_d : ∀ (n : ℕ) (c : N n), P.d (n + 1) (τ n c) + τ (n + 1) (Q.d n c) = 0

namespace CDGATwist

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N}

/-- The twisting cochain as a linear map. -/
def τₗ (t : CDGATwist P Q) (n : ℕ) : N n →ₗ[R] M (n + 1) where
  toFun := t.τ n
  map_add' := t.τ_add n
  map_smul' := fun c m => t.τ_smul n c m

@[simp] theorem τₗ_apply (t : CDGATwist P Q) (n : ℕ) (c : N n) : t.τₗ n c = t.τ n c := rfl

end CDGATwist

namespace CDGAModuleStructure

section Twisted

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N}

theorem CDGATwist.τ_zero (t : CDGATwist P Q) (n : ℕ) : t.τ n 0 = 0 := by
  have h := t.τ_add n 0 0
  rw [add_zero] at h
  simpa using h.symm

/-- **The cell attached to a differential graded module along a twisting cochain**: the direct sum,
with the differential deformed by the attaching map. -/
def twisted (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (t : CDGATwist P Q) :
    CDGAModuleStructure A (fun n => M n × N n) where
  act h x m := (P.act h x m.1, Q.act h x m.2)
  d n m := (P.d n m.1 + t.τ n m.2, Q.d n m.2)
  act_add_left h x x' m := Prod.ext (P.act_add_left h x x' m.1) (Q.act_add_left h x x' m.2)
  act_add_right h x m m' := Prod.ext (P.act_add_right h x m.1 m'.1) (Q.act_add_right h x m.2 m'.2)
  act_smul_left h c x m := Prod.ext (P.act_smul_left h c x m.1) (Q.act_smul_left h c x m.2)
  act_smul_right h c x m := Prod.ext (P.act_smul_right h c x m.1) (Q.act_smul_right h c x m.2)
  act_assoc h₁ h₂ h₃ h₄ x y m :=
    Prod.ext (P.act_assoc h₁ h₂ h₃ h₄ x y m.1) (Q.act_assoc h₁ h₂ h₃ h₄ x y m.2)
  d_add n m m' := by
    refine Prod.ext ?_ (Q.d_add n m.2 m'.2)
    show P.d n (m.1 + m'.1) + t.τ n (m.2 + m'.2)
      = (P.d n m.1 + t.τ n m.2) + (P.d n m'.1 + t.τ n m'.2)
    rw [P.d_add, t.τ_add]
    abel
  d_smul n c m := by
    refine Prod.ext ?_ (Q.d_smul n c m.2)
    show P.d n (c • m.1) + t.τ n (c • m.2) = c • (P.d n m.1 + t.τ n m.2)
    rw [P.d_smul, t.τ_smul, smul_add]
  d_d n m := by
    refine Prod.ext ?_ (Q.d_d n m.2)
    show P.d (n + 1) (P.d n m.1 + t.τ n m.2) + t.τ (n + 1) (Q.d n m.2) = 0
    rw [P.d_add, P.d_d, zero_add, t.τ_d]
  d_act h x m := by
    refine Prod.ext ?_ (Q.d_act h x m.2)
    show P.d _ (P.act h x m.1) + t.τ _ (Q.act h x m.2)
      = P.act (show _ + 1 + _ = _ + 1 by omega) (A.d _ x) m.1
        + ((-1 : R)) ^ _ • P.act (show _ + (_ + 1) = _ + 1 by omega) x
            (P.d _ m.1 + t.τ _ m.2)
    rw [P.d_act h x m.1, t.τ_act h x m.2, P.act_add_right, smul_add]
    abel

@[simp] theorem twisted_d (t : CDGATwist P Q) (n : ℕ) (m : M n × N n) :
    (twisted P Q t).d n m = (P.d n m.1 + t.τ n m.2, Q.d n m.2) := rfl

end Twisted

end CDGAModuleStructure

namespace CDGAModuleHom

section Twisted

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)] {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N} (t : CDGATwist P Q)

/-- The inclusion of the base into a cell attachment. -/
def twistedIncl : CDGAModuleHom P (CDGAModuleStructure.twisted P Q t) where
  toFun _ m := (m, 0)
  map_add n m m' := by
    refine Prod.ext rfl ?_
    show (0 : N n) = 0 + 0
    rw [add_zero]
  map_smul n c m := by
    refine Prod.ext rfl ?_
    show (0 : N n) = c • (0 : N n)
    rw [smul_zero]
  map_act h x m := by
    refine Prod.ext rfl ?_
    have h0 := Q.act_add_right h x (0 : N _) 0
    rw [add_zero] at h0
    have h1 : Q.act h x (0 : N _) = 0 := by
      simpa using h0
    show (0 : N _) = Q.act h x 0
    rw [h1]
  map_d n m := by
    refine Prod.ext ?_ ?_
    · show P.d n m = P.d n m + t.τ n 0
      rw [CDGAModuleStructure.CDGATwist.τ_zero, add_zero]
    · show (0 : N (n + 1)) = Q.d n 0
      have h0 := Q.d_add n (0 : N n) 0
      rw [add_zero] at h0
      have h1 : Q.d n (0 : N n) = 0 := by simpa using h0
      rw [h1]

@[simp] theorem twistedIncl_toFun (n : ℕ) (m : M n) :
    (twistedIncl t).toFun n m = (m, 0) := rfl

/-- The projection of a cell attachment onto the cell. -/
def twistedProj : CDGAModuleHom (CDGAModuleStructure.twisted P Q t) Q where
  toFun _ m := m.2
  map_add _ _ _ := rfl
  map_smul _ _ _ := rfl
  map_act _ _ _ := rfl
  map_d _ _ := rfl

@[simp] theorem twistedProj_toFun (n : ℕ) (m : M n × N n) :
    (twistedProj t).toFun n m = m.2 := rfl

/-- **The cell attachment is an extension of the cell by the base**: the inclusion is degreewise
injective, the projection degreewise surjective, and their composite is zero. -/
theorem twistedProj_comp_incl (n : ℕ) (m : M n) :
    (twistedProj t).toFun n ((twistedIncl t).toFun n m) = 0 := rfl

theorem twistedIncl_injective (n : ℕ) : Function.Injective ((twistedIncl t).toFun n) :=
  fun _ _ h => congrArg Prod.fst h

theorem twistedProj_surjective (n : ℕ) : Function.Surjective ((twistedProj t).toFun n) :=
  fun c => ⟨(0, c), rfl⟩

theorem twistedProj_eq_zero_iff {n : ℕ} {m : M n × N n} :
    (twistedProj t).toFun n m = 0 ↔ ∃ m' : M n, m = (twistedIncl t).toFun n m' := by
  constructor
  · intro h
    exact ⟨m.1, Prod.ext rfl h⟩
  · rintro ⟨m', rfl⟩
    rfl

/-- A cocycle whose image is a coboundary is a coboundary, when the map is a quasi-isomorphism. -/
theorem exists_eq_d_of_map_eq_d {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)]
    [∀ n, Module R (M' n)] {P' : CDGAModuleStructure A M'} {φ : CDGAModuleHom P P'}
    (hφ : φ.IsQuasiIso) (n : ℕ) (y : P.cocycles (n + 1)) (p : M' n)
    (h : φ.toFun (n + 1) (y : M (n + 1)) = P'.d n p) :
    ∃ q : M n, (y : M (n + 1)) = P.d n q := by
  have h0 : Submodule.Quotient.mk (φ.cocyclesMap (n + 1) y) = (0 : P'.cohomology n) := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact (CDGAModuleStructure.mem_coboundaries _).2 ⟨p, h⟩
  have h1 : Submodule.Quotient.mk y = (0 : P.cohomology n) := by
    refine (hφ n).1 ?_
    rw [map_zero]
    exact h0
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact (CDGAModuleStructure.mem_coboundaries _).1 h1

/-- Every cohomology class downstairs is hit, up to a coboundary, by a cocycle upstairs. -/
theorem exists_cocycle_sub_eq_d {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)]
    [∀ n, Module R (M' n)] {P' : CDGAModuleStructure A M'} {φ : CDGAModuleHom P P'}
    (hφ : φ.IsQuasiIso) (n : ℕ) (y' : P'.cocycles (n + 1)) :
    ∃ (y : P.cocycles (n + 1)) (w : M' n),
      φ.toFun (n + 1) (y : M (n + 1)) - (y' : M' (n + 1)) = P'.d n w := by
  obtain ⟨a, ha⟩ := (hφ n).2 (Submodule.Quotient.mk y')
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ a
  rw [← hy] at ha
  obtain ⟨w, hw⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 ha)
  exact ⟨y, w, by simpa using hw⟩

end Twisted

end CDGAModuleHom


namespace CDGAModuleHom

section Invariance

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'} {Q : CDGAModuleStructure A N}

/-- **The map of cell attachments induced by a map of bases** compatible with the twists. -/
def twistedMap (t : CDGATwist P Q) (t' : CDGATwist P' Q) (φ : CDGAModuleHom P P')
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n c) :
    CDGAModuleHom (CDGAModuleStructure.twisted P Q t) (CDGAModuleStructure.twisted P' Q t') where
  toFun n m := (φ.toFun n m.1, m.2)
  map_add n m m' := Prod.ext (φ.map_add n m.1 m'.1) rfl
  map_smul n c m := Prod.ext (φ.map_smul n c m.1) rfl
  map_act h x m := Prod.ext (φ.map_act h x m.1) rfl
  map_d n m := by
    refine Prod.ext ?_ rfl
    show φ.toFun (n + 1) (P.d n m.1 + t.τ n m.2) = P'.d n (φ.toFun n m.1) + t'.τ n m.2
    rw [φ.map_add, φ.map_d, hcompat]

@[simp] theorem twistedMap_toFun (t : CDGATwist P Q) (t' : CDGATwist P' Q)
    (φ : CDGAModuleHom P P')
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n c) (n : ℕ)
    (m : M n × N n) : (twistedMap t t' φ hcompat).toFun n m = (φ.toFun n m.1, m.2) := rfl

/-- A cocycle of a cell attachment that maps to a coboundary is a coboundary. -/
theorem twisted_mem_coboundaries {t : CDGATwist P Q} {t' : CDGATwist P' Q}
    {φ : CDGAModuleHom P P'}
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n c) (hφ : φ.IsQuasiIso)
    (n : ℕ) (u : (CDGAModuleStructure.twisted P Q t).cocycles (n + 1))
    (hu : (twistedMap t t' φ hcompat).cocyclesMap (n + 1) u
      ∈ (CDGAModuleStructure.twisted P' Q t').coboundaries n) :
    u ∈ (CDGAModuleStructure.twisted P Q t).coboundaries n := by
  obtain ⟨pq, hpq⟩ := (CDGAModuleStructure.mem_coboundaries _).1 hu
  have hp : φ.toFun (n + 1) (u : M (n + 1) × N (n + 1)).1 = P'.d n pq.1 + t'.τ n pq.2 :=
    congrArg Prod.fst hpq
  have hq : (u : M (n + 1) × N (n + 1)).2 = Q.d n pq.2 := congrArg Prod.snd hpq
  have hucoc : P.d (n + 1) (u : M (n + 1) × N (n + 1)).1
      + t.τ (n + 1) (u : M (n + 1) × N (n + 1)).2 = 0 := congrArg Prod.fst u.2
  have hdm : P.d (n + 1) (u : M (n + 1) × N (n + 1)).1
      = -t.τ (n + 1) (u : M (n + 1) × N (n + 1)).2 := eq_neg_iff_add_eq_zero.2 hucoc
  have hdt : P.d (n + 1) (t.τ n pq.2) = -t.τ (n + 1) (Q.d n pq.2) :=
    eq_neg_iff_add_eq_zero.2 (t.τ_d n pq.2)
  have hycoc : ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2) ∈ P.cocycles (n + 1) := by
    show P.d (n + 1) ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2) = 0
    have hsub := map_sub (P.dₗ (n + 1)) (u : M (n + 1) × N (n + 1)).1 (t.τ n pq.2)
    show P.d (n + 1) ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2) = 0
    rw [show P.d (n + 1) ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2)
        = P.d (n + 1) (u : M (n + 1) × N (n + 1)).1 - P.d (n + 1) (t.τ n pq.2) from hsub,
      hdm, hdt, ← hq]
    abel
  have hφy : φ.toFun (n + 1) ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2) = P'.d n pq.1 := by
    have hsub := map_sub (φ.mapₗ (n + 1)) (u : M (n + 1) × N (n + 1)).1 (t.τ n pq.2)
    rw [show φ.toFun (n + 1) ((u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2)
        = φ.toFun (n + 1) (u : M (n + 1) × N (n + 1)).1 - φ.toFun (n + 1) (t.τ n pq.2) from hsub,
      hp, hcompat]
    abel
  obtain ⟨p₀, hp₀⟩ :=
    exists_eq_d_of_map_eq_d hφ n ⟨_, hycoc⟩ pq.1 hφy
  refine (CDGAModuleStructure.mem_coboundaries _).2 ⟨(p₀, pq.2), ?_⟩
  refine Prod.ext ?_ hq
  show (u : M (n + 1) × N (n + 1)).1 = P.d n p₀ + t.τ n pq.2
  have hsimp : (u : M (n + 1) × N (n + 1)).1 - t.τ n pq.2 = P.d n p₀ := hp₀
  rw [← hsimp]
  abel

/-- **Attaching a cell preserves quasi-isomorphisms.**  A quasi-isomorphism of bases compatible with
the twists induces a quasi-isomorphism of the cell attachments.  The proof is a direct chase rather
than a long exact sequence: a cocycle of an attachment is a pair whose base component differs from a
twist of the cell component by a cocycle of the base, and each half of the hypothesis on the base is
used exactly once. -/
theorem IsQuasiIso.twistedMap {t : CDGATwist P Q} {t' : CDGATwist P' Q} {φ : CDGAModuleHom P P'}
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n c) (hφ : φ.IsQuasiIso) :
    (CDGAModuleHom.twistedMap t t' φ hcompat).IsQuasiIso := by
  intro n
  constructor
  · refine fun a b => Quotient.inductionOn₂' a b fun u v hab => ?_
    have h2 := (Submodule.Quotient.eq _).1 hab
    have h3 : (CDGAModuleHom.twistedMap t t' φ hcompat).cocyclesMap (n + 1) (u - v)
        ∈ (CDGAModuleStructure.twisted P' Q t').coboundaries n := by
      rw [map_sub]
      exact h2
    exact (Submodule.Quotient.eq _).2 (twisted_mem_coboundaries hcompat hφ n (u - v) h3)
  · refine fun cl => Quotient.inductionOn' cl fun u' => ?_
    have hcoc1 : P'.d (n + 1) (u' : M' (n + 1) × N (n + 1)).1
        + t'.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2 = 0 := congrArg Prod.fst u'.2
    have hcoc2 : Q.d (n + 1) (u' : M' (n + 1) × N (n + 1)).2 = 0 := congrArg Prod.snd u'.2
    have htcoc : t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2 ∈ P.cocycles (n + 1 + 1) := by
      show P.d (n + 1 + 1) (t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2) = 0
      rw [eq_neg_iff_add_eq_zero.2 (t.τ_d (n + 1) (u' : M' (n + 1) × N (n + 1)).2), hcoc2,
        CDGAModuleStructure.CDGATwist.τ_zero, neg_zero]
    have hφt : φ.toFun (n + 1 + 1) (t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2)
        = P'.d (n + 1) (-(u' : M' (n + 1) × N (n + 1)).1) := by
      rw [hcompat, show P'.d (n + 1) (-(u' : M' (n + 1) × N (n + 1)).1)
          = -P'.d (n + 1) (u' : M' (n + 1) × N (n + 1)).1
        from map_neg (P'.dₗ (n + 1)) _]
      exact (neg_eq_iff_add_eq_zero.2 hcoc1).symm
    obtain ⟨q₀, hq₀⟩ :=
      exists_eq_d_of_map_eq_d hφ (n + 1) ⟨_, htcoc⟩ (-(u' : M' (n + 1) × N (n + 1)).1) hφt
    have hdiff : (φ.toFun (n + 1) (-q₀) - (u' : M' (n + 1) × N (n + 1)).1)
        ∈ P'.cocycles (n + 1) := by
      show P'.d (n + 1) (φ.toFun (n + 1) (-q₀) - (u' : M' (n + 1) × N (n + 1)).1) = 0
      rw [show P'.d (n + 1) (φ.toFun (n + 1) (-q₀) - (u' : M' (n + 1) × N (n + 1)).1)
          = P'.d (n + 1) (φ.toFun (n + 1) (-q₀)) - P'.d (n + 1) (u' : M' (n + 1) × N (n + 1)).1
        from map_sub (P'.dₗ (n + 1)) _ _, ← φ.map_d (n + 1) (-q₀),
        show P.d (n + 1) (-q₀) = -P.d (n + 1) q₀ from map_neg (P.dₗ (n + 1)) q₀, ← hq₀,
        show φ.toFun (n + 1 + 1) (-t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2)
          = -φ.toFun (n + 1 + 1) (t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2)
        from map_neg (φ.mapₗ (n + 1 + 1)) _, hcompat,
        (neg_eq_iff_add_eq_zero.2 hcoc1).symm]
      abel
    obtain ⟨y, wcorr, hyw⟩ := exists_cocycle_sub_eq_d hφ n ⟨_, hdiff⟩
    have hnew : ((-q₀ - (y : M (n + 1)), (u' : M' (n + 1) × N (n + 1)).2) : M (n + 1) × N (n + 1))
        ∈ (CDGAModuleStructure.twisted P Q t).cocycles (n + 1) := by
      refine Prod.ext ?_ hcoc2
      show P.d (n + 1) (-q₀ - (y : M (n + 1)))
        + t.τ (n + 1) (u' : M' (n + 1) × N (n + 1)).2 = 0
      rw [show P.d (n + 1) (-q₀ - (y : M (n + 1)))
          = P.d (n + 1) (-q₀) - P.d (n + 1) (y : M (n + 1)) from map_sub (P.dₗ (n + 1)) _ _,
        show P.d (n + 1) (y : M (n + 1)) = 0 from y.2,
        show P.d (n + 1) (-q₀) = -P.d (n + 1) q₀ from map_neg (P.dₗ (n + 1)) q₀, ← hq₀]
      abel
    refine ⟨Submodule.Quotient.mk ⟨_, hnew⟩, ?_⟩
    show Submodule.Quotient.mk
      ((CDGAModuleHom.twistedMap t t' φ hcompat).cocyclesMap (n + 1) ⟨_, hnew⟩) = _
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2
      ⟨(-wcorr, 0), ?_⟩)
    refine Prod.ext ?_ ?_
    · show φ.toFun (n + 1) (-q₀ - (y : M (n + 1))) - (u' : M' (n + 1) × N (n + 1)).1
        = P'.d n (-wcorr) + t'.τ n 0
      rw [show φ.toFun (n + 1) (-q₀ - (y : M (n + 1)))
          = φ.toFun (n + 1) (-q₀) - φ.toFun (n + 1) (y : M (n + 1))
        from map_sub (φ.mapₗ (n + 1)) _ _,
        show P'.d n (-wcorr) = -P'.d n wcorr from map_neg (P'.dₗ n) wcorr,
        CDGAModuleStructure.CDGATwist.τ_zero, add_zero]
      have hyw' : φ.toFun (n + 1) (y : M (n + 1))
          - (φ.toFun (n + 1) (-q₀) - (u' : M' (n + 1) × N (n + 1)).1) = P'.d n wcorr := hyw
      rw [← hyw']
      abel
    · show (u' : M' (n + 1) × N (n + 1)).2 - (u' : M' (n + 1) × N (n + 1)).2 = Q.d n 0
      rw [sub_self]
      have h0 := Q.d_add n (0 : N n) 0
      rw [add_zero] at h0
      have h1 : Q.d n (0 : N n) = 0 := by simpa using h0
      rw [h1]

end Invariance

end CDGAModuleHom



namespace CDGAModuleStructure

section Pi

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {ι : Type*}
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]

/-- **The product of a family of differential graded modules**, degreewise. -/
def pi (P : ∀ i, CDGAModuleStructure A (M i)) :
    CDGAModuleStructure A (fun n => ∀ i, M i n) where
  act h x m := fun i => (P i).act h x (m i)
  d n m := fun i => (P i).d n (m i)
  act_add_left h x x' m := funext fun i => (P i).act_add_left h x x' (m i)
  act_add_right h x m m' := funext fun i => (P i).act_add_right h x (m i) (m' i)
  act_smul_left h c x m := funext fun i => (P i).act_smul_left h c x (m i)
  act_smul_right h c x m := funext fun i => (P i).act_smul_right h c x (m i)
  act_assoc h₁ h₂ h₃ h₄ x y m := funext fun i => (P i).act_assoc h₁ h₂ h₃ h₄ x y (m i)
  d_add n m m' := funext fun i => (P i).d_add n (m i) (m' i)
  d_smul n c m := funext fun i => (P i).d_smul n c (m i)
  d_d n m := funext fun i => (P i).d_d n (m i)
  d_act h x m := funext fun i => (P i).d_act h x (m i)

@[simp] theorem pi_d (P : ∀ i, CDGAModuleStructure A (M i)) (n : ℕ) (m : ∀ i, M i n) :
    (pi P).d n m = fun i => (P i).d n (m i) := rfl

theorem mem_pi_cocycles {P : ∀ i, CDGAModuleStructure A (M i)} {n : ℕ} {m : ∀ i, M i n} :
    m ∈ (pi P).cocycles n ↔ ∀ i, m i ∈ (P i).cocycles n := by
  constructor
  · intro hm i
    have h : (fun j => (P j).d n (m j)) = 0 := hm
    exact congrFun h i
  · intro hm
    show (fun j => (P j).d n (m j)) = 0
    funext i
    exact hm i

/-- The `i`-th component of a cocycle of a product. -/
def piComp (P : ∀ i, CDGAModuleStructure A (M i)) {n : ℕ} (u : (pi P).cocycles n) (i : ι) :
    (P i).cocycles n := ⟨(u : ∀ j, M j n) i, mem_pi_cocycles.1 u.2 i⟩

@[simp] theorem piComp_coe (P : ∀ i, CDGAModuleStructure A (M i)) {n : ℕ}
    (u : (pi P).cocycles n) (i : ι) :
    ((piComp P u i : (P i).cocycles n) : M i n) = (u : ∀ j, M j n) i := rfl

end Pi

end CDGAModuleStructure

namespace CDGAModuleHom

section Pi

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {ι : Type*}
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)} {Q : ∀ i, CDGAModuleStructure A (N i)}

/-- **The product of a family of morphisms.** -/
def piMap (φ : ∀ i, CDGAModuleHom (P i) (Q i)) :
    CDGAModuleHom (CDGAModuleStructure.pi P) (CDGAModuleStructure.pi Q) where
  toFun n m := fun i => (φ i).toFun n (m i)
  map_add n m m' := funext fun i => (φ i).map_add n (m i) (m' i)
  map_smul n c m := funext fun i => (φ i).map_smul n c (m i)
  map_act h x m := funext fun i => (φ i).map_act h x (m i)
  map_d n m := funext fun i => (φ i).map_d n (m i)

@[simp] theorem piMap_toFun (φ : ∀ i, CDGAModuleHom (P i) (Q i)) (n : ℕ) (m : ∀ i, M i n) :
    (piMap φ).toFun n m = fun i => (φ i).toFun n (m i) := rfl

/-- **A product of quasi-isomorphisms is a quasi-isomorphism.**  A family is a coboundary exactly
when each of its components is, so both halves are read off componentwise; the primitives are chosen
with the axiom of choice. -/
theorem IsQuasiIso.piMap {φ : ∀ i, CDGAModuleHom (P i) (Q i)}
    (hφ : ∀ i, (φ i).IsQuasiIso) : (CDGAModuleHom.piMap φ).IsQuasiIso := by
  classical
  intro n
  constructor
  · refine fun a b => Quotient.inductionOn₂' a b fun u v huv => ?_
    obtain ⟨w, hw⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 huv)
    have hcomp : ∀ i, (Submodule.Quotient.mk
        ((φ i).cocyclesMap (n + 1) (CDGAModuleStructure.piComp P u i)) : (Q i).cohomology n)
        = Submodule.Quotient.mk
          ((φ i).cocyclesMap (n + 1) (CDGAModuleStructure.piComp P v i)) := by
      intro i
      exact (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2
        ⟨w i, by simpa using congrFun hw i⟩)
    have hstep : ∀ i, ∃ s : M i n,
        ((CDGAModuleStructure.piComp P u i : (P i).cocycles (n + 1)) : M i (n + 1))
          - ((CDGAModuleStructure.piComp P v i : (P i).cocycles (n + 1)) : M i (n + 1))
          = (P i).d n s := by
      intro i
      obtain ⟨s, hs⟩ := (CDGAModuleStructure.mem_coboundaries _).1
        ((Submodule.Quotient.eq _).1 ((hφ i n).1 (hcomp i)))
      exact ⟨s, by simpa using hs⟩
    choose s hs using hstep
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨s, ?_⟩)
    funext i
    simpa using hs i
  · refine fun cl => Quotient.inductionOn' cl fun u => ?_
    have hstep : ∀ i, ∃ (y : (P i).cocycles (n + 1)) (t : N i n),
        (φ i).toFun (n + 1) ((y : (P i).cocycles (n + 1)) : M i (n + 1))
          - ((CDGAModuleStructure.piComp Q u i : (Q i).cocycles (n + 1)) : N i (n + 1))
          = (Q i).d n t := by
      intro i
      obtain ⟨a, ha⟩ := (hφ i n).2 (Submodule.Quotient.mk (CDGAModuleStructure.piComp Q u i))
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective ((P i).coboundaries n) a
      rw [← hy] at ha
      obtain ⟨t, ht⟩ := (CDGAModuleStructure.mem_coboundaries _).1 ((Submodule.Quotient.eq _).1 ha)
      exact ⟨y, t, by simpa using ht⟩
    choose y t ht using hstep
    refine ⟨Submodule.Quotient.mk ⟨fun i => ((y i : (P i).cocycles (n + 1)) : M i (n + 1)),
      CDGAModuleStructure.mem_pi_cocycles.2 fun i => (y i).2⟩, ?_⟩
    refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨t, ?_⟩)
    funext i
    simpa using ht i

end Pi

end CDGAModuleHom

end GaloisForLFunctions.HTGeometry
