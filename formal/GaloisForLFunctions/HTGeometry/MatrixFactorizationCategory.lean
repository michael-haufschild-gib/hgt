import Mathlib

/-!
# The category of matrix factorizations of a ring element

A matrix factorization of `w` in a commutative ring `R` is a pair of square matrices over `R` whose
two products are both `w` times the identity.  With the evident morphisms these form a category, and
the construction is functorial in the pair `(R, w)`: a ring homomorphism carrying `w` to `w'`
induces a functor, and a ring isomorphism induces an equivalence of categories.

The equivalence is the algebraic content of "the local matrix-factorization category is invariant
under a change of coordinates": a coordinate change is a ring isomorphism of the local rings that
carries one potential to the other.

* `MatrixFactorization R w` — the objects, together with `MFHom` and the `Category` instance.
* `MatrixFactorization.map` — the functor induced by a ring homomorphism.
* `MatrixFactorization.mapEquivalence` — the equivalence induced by a ring isomorphism.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u v

/-- A matrix factorization of `w` in `R`: two square matrices of a common size whose two products
are both `w` times the identity. -/
structure MatrixFactorization (R : Type u) [CommRing R] (w : R) : Type u where
  /-- The common size of the two matrices. -/
  rank : ℕ
  /-- The first differential. -/
  d₀ : Matrix (Fin rank) (Fin rank) R
  /-- The second differential. -/
  d₁ : Matrix (Fin rank) (Fin rank) R
  /-- The first factorization identity. -/
  d₀_mul_d₁ : d₀ * d₁ = w • (1 : Matrix (Fin rank) (Fin rank) R)
  /-- The second factorization identity. -/
  d₁_mul_d₀ : d₁ * d₀ = w • (1 : Matrix (Fin rank) (Fin rank) R)

namespace MatrixFactorization

variable {R : Type u} [CommRing R] {w : R}

/-- A morphism of matrix factorizations: a pair of matrices intertwining the two differentials. -/
@[ext]
structure MFHom (X Y : MatrixFactorization R w) : Type u where
  /-- The component on the first summand. -/
  f₀ : Matrix (Fin Y.rank) (Fin X.rank) R
  /-- The component on the second summand. -/
  f₁ : Matrix (Fin Y.rank) (Fin X.rank) R
  /-- Compatibility with the first differential. -/
  comm₀ : Y.d₀ * f₁ = f₀ * X.d₀
  /-- Compatibility with the second differential. -/
  comm₁ : Y.d₁ * f₀ = f₁ * X.d₁

instance : Category (MatrixFactorization R w) where
  Hom X Y := MFHom X Y
  id X := ⟨1, 1, by simp, by simp⟩
  comp {X Y Z} f g :=
    { f₀ := g.f₀ * f.f₀
      f₁ := g.f₁ * f.f₁
      comm₀ := by
        rw [← Matrix.mul_assoc, g.comm₀, Matrix.mul_assoc, f.comm₀, ← Matrix.mul_assoc]
      comm₁ := by
        rw [← Matrix.mul_assoc, g.comm₁, Matrix.mul_assoc, f.comm₁, ← Matrix.mul_assoc] }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Matrix.mul_assoc]

@[ext]
theorem hom_ext {X Y : MatrixFactorization R w} {f g : X ⟶ Y}
    (h₀ : MFHom.f₀ f = MFHom.f₀ g) (h₁ : MFHom.f₁ f = MFHom.f₁ g) : f = g :=
  MFHom.ext h₀ h₁

@[simp] theorem id_f₀ (X : MatrixFactorization R w) : MFHom.f₀ (𝟙 X) = 1 := rfl
@[simp] theorem id_f₁ (X : MatrixFactorization R w) : MFHom.f₁ (𝟙 X) = 1 := rfl

@[simp] theorem comp_f₀ {X Y Z : MatrixFactorization R w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MFHom.f₀ (f ≫ g) = g.f₀ * f.f₀ := rfl

@[simp] theorem comp_f₁ {X Y Z : MatrixFactorization R w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MFHom.f₁ (f ≫ g) = g.f₁ * f.f₁ := rfl

/-! ### Functoriality in the ring -/

section Map

variable {S : Type v} [CommRing S] {w' : S}

/-- Entrywise image of `w • 1` under a ring homomorphism. -/
theorem map_smul_one {n : ℕ} (φ : R →+* S) (hw : φ w = w') :
    ((w • (1 : Matrix (Fin n) (Fin n) R)).map φ) = w' • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.map_apply, h, hw]

/-- A ring homomorphism carrying `w` to `w'` transports a matrix factorization of `w` to one of
`w'`. -/
@[simps rank d₀ d₁, reducible]
def mapObj (φ : R →+* S) (hw : φ w = w') (X : MatrixFactorization R w) :
    MatrixFactorization S w' where
  rank := X.rank
  d₀ := X.d₀.map φ
  d₁ := X.d₁.map φ
  d₀_mul_d₁ := by rw [← Matrix.map_mul, X.d₀_mul_d₁, map_smul_one φ hw]
  d₁_mul_d₀ := by rw [← Matrix.map_mul, X.d₁_mul_d₀, map_smul_one φ hw]

/-- The functor induced on matrix factorizations by a ring homomorphism carrying `w` to `w'`. -/
@[reducible]
def map (φ : R →+* S) (hw : φ w = w') :
    MatrixFactorization R w ⥤ MatrixFactorization S w' where
  obj X := mapObj φ hw X
  map {X Y} f :=
    { f₀ := f.f₀.map φ
      f₁ := f.f₁.map φ
      comm₀ := by
        show Y.d₀.map φ * f.f₁.map φ = f.f₀.map φ * X.d₀.map φ
        rw [← Matrix.map_mul, ← Matrix.map_mul, f.comm₀]
      comm₁ := by
        show Y.d₁.map φ * f.f₀.map φ = f.f₁.map φ * X.d₁.map φ
        rw [← Matrix.map_mul, ← Matrix.map_mul, f.comm₁] }
  map_id X := by
    refine hom_ext ?_ ?_ <;>
      · show (1 : Matrix (Fin X.rank) (Fin X.rank) R).map φ = 1
        exact Matrix.map_one _ φ.map_zero φ.map_one
  map_comp {X Y Z} f g := by
    refine hom_ext ?_ ?_
    · show (g.f₀ * f.f₀).map φ = g.f₀.map φ * f.f₀.map φ
      exact Matrix.map_mul
    · show (g.f₁ * f.f₁).map φ = g.f₁.map φ * f.f₁.map φ
      exact Matrix.map_mul

@[simp] theorem map_obj_rank (φ : R →+* S) (hw : φ w = w') (X : MatrixFactorization R w) :
    ((map φ hw).obj X).rank = X.rank := rfl

@[simp] theorem map_map_f₀ (φ : R →+* S) (hw : φ w = w') {X Y : MatrixFactorization R w}
    (f : X ⟶ Y) : ((map φ hw).map f).f₀ = f.f₀.map φ := rfl

@[simp] theorem map_map_f₁ (φ : R →+* S) (hw : φ w = w') {X Y : MatrixFactorization R w}
    (f : X ⟶ Y) : ((map φ hw).map f).f₁ = f.f₁.map φ := rfl

end Map

/-! ### Invariance under a ring isomorphism -/

section Equivalence

variable {S : Type v} [CommRing S] {w' : S}

/-- Round trip of a matrix through a ring isomorphism and back. -/
@[simp]
theorem map_map_symm {m n : ℕ} (φ : R ≃+* S) (A : Matrix (Fin m) (Fin n) R) :
    (A.map (φ : R →+* S)).map (φ.symm : S →+* R) = A := by
  ext i j
  simp

/-- Round trip of a matrix through the inverse of a ring isomorphism and back. -/
@[simp]
theorem map_symm_map {m n : ℕ} (φ : R ≃+* S) (A : Matrix (Fin m) (Fin n) S) :
    (A.map (φ.symm : S →+* R)).map (φ : R →+* S) = A := by
  ext i j
  simp

/-- The inverse isomorphism carries the second potential back to the first. -/
theorem ringEquiv_symm_potential (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    (φ.symm : S →+* R) w' = w := by
  simp only [RingEquiv.coe_toRingHom] at hw ⊢
  rw [← hw, RingEquiv.symm_apply_apply]

/-- The functor attached to a ring isomorphism is faithful: applying the inverse isomorphism
entrywise recovers each component. -/
instance mapFaithful (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    (map (φ : R →+* S) hw).Faithful where
  map_injective {X Y} f g h := by
    have h₀ : f.f₀.map (φ : R →+* S) = g.f₀.map (φ : R →+* S) := congrArg MFHom.f₀ h
    have h₁ : f.f₁.map (φ : R →+* S) = g.f₁.map (φ : R →+* S) := congrArg MFHom.f₁ h
    refine hom_ext ?_ ?_
    · have e := congrArg
        (fun A : Matrix (Fin Y.rank) (Fin X.rank) S => A.map (φ.symm : S →+* R)) h₀
      simp only [map_map_symm] at e
      exact e
    · have e := congrArg
        (fun A : Matrix (Fin Y.rank) (Fin X.rank) S => A.map (φ.symm : S →+* R)) h₁
      simp only [map_map_symm] at e
      exact e

/-- The functor attached to a ring isomorphism is full: a morphism between the images is the image
of the morphism obtained by applying the inverse isomorphism entrywise. -/
instance mapFull (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    (map (φ : R →+* S) hw).Full where
  map_surjective {X Y} g := by
    refine ⟨{ f₀ := g.f₀.map (φ.symm : S →+* R)
              f₁ := g.f₁.map (φ.symm : S →+* R)
              comm₀ := ?_
              comm₁ := ?_ }, ?_⟩
    · have h := congrArg
        (fun A : Matrix (Fin Y.rank) (Fin X.rank) S => A.map (φ.symm : S →+* R)) g.comm₀
      simp only [Matrix.map_mul, map_map_symm] at h
      exact h
    · have h := congrArg
        (fun A : Matrix (Fin Y.rank) (Fin X.rank) S => A.map (φ.symm : S →+* R)) g.comm₁
      simp only [Matrix.map_mul, map_map_symm] at h
      exact h
    · refine hom_ext ?_ ?_
      · show (g.f₀.map (φ.symm : S →+* R)).map (φ : R →+* S) = g.f₀
        exact map_symm_map φ g.f₀
      · show (g.f₁.map (φ.symm : S →+* R)).map (φ : R →+* S) = g.f₁
        exact map_symm_map φ g.f₁

/-- The functor attached to a ring isomorphism is essentially surjective: the inverse isomorphism
transports every matrix factorization of the second potential back to one of the first. -/
instance mapEssSurj (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    (map (φ : R →+* S) hw).EssSurj where
  mem_essImage Y := by
    refine ⟨mapObj (φ.symm : S →+* R) (ringEquiv_symm_potential φ hw) Y, ⟨?_⟩⟩
    refine
      { hom :=
          { f₀ := 1
            f₁ := 1
            comm₀ := by
              show Y.d₀ * (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                  = (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                    * (Y.d₀.map (φ.symm : S →+* R)).map (φ : R →+* S)
              rw [map_symm_map φ Y.d₀, Matrix.mul_one, Matrix.one_mul]
            comm₁ := by
              show Y.d₁ * (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                  = (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                    * (Y.d₁.map (φ.symm : S →+* R)).map (φ : R →+* S)
              rw [map_symm_map φ Y.d₁, Matrix.mul_one, Matrix.one_mul] }
        inv :=
          { f₀ := 1
            f₁ := 1
            comm₀ := by
              show (Y.d₀.map (φ.symm : S →+* R)).map (φ : R →+* S)
                    * (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                  = (1 : Matrix (Fin Y.rank) (Fin Y.rank) S) * Y.d₀
              rw [map_symm_map φ Y.d₀, Matrix.mul_one, Matrix.one_mul]
            comm₁ := by
              show (Y.d₁.map (φ.symm : S →+* R)).map (φ : R →+* S)
                    * (1 : Matrix (Fin Y.rank) (Fin Y.rank) S)
                  = (1 : Matrix (Fin Y.rank) (Fin Y.rank) S) * Y.d₁
              rw [map_symm_map φ Y.d₁, Matrix.mul_one, Matrix.one_mul] }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · refine hom_ext ?_ ?_ <;> exact Matrix.one_mul 1
    · refine hom_ext ?_ ?_ <;> exact Matrix.one_mul 1

instance mapIsEquivalence (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    (map (φ : R →+* S) hw).IsEquivalence where

/-- **A ring isomorphism carrying one potential to the other induces an equivalence of the two
categories of matrix factorizations.**  The induced functor is faithful and full because the
inverse isomorphism acts entrywise, and essentially surjective because the inverse isomorphism
transports objects back. -/
noncomputable def mapEquivalence (φ : R ≃+* S) (hw : (φ : R →+* S) w = w') :
    MatrixFactorization R w ≌ MatrixFactorization S w' :=
  (map (φ : R →+* S) hw).asEquivalence

end Equivalence

end MatrixFactorization

end GaloisForLFunctions.HTGeometry
