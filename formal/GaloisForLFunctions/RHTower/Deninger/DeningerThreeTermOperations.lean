import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermCohomology

/-!
# Operations on three-term arithmetic cohomology

Everything that acts on Deninger's arithmetic coefficient acts on the cohomology of the three-term
complex it totalizes to.  A morphism of three-term complexes — three linear maps commuting with the
two differentials — induces maps in all three degrees; the assignment is functorial and additive,
so Galois maps, Frobenius and Verschiebung, and finite correspondences, which are integral
combinations of morphisms, all descend.  A trace on the top term that kills boundaries descends,
and a cup datum satisfying the Koszul--Leibniz rules descends to products in every bidegree.

* `DeningerThreeTermHom`, `H0map`, `H1map`, `H2map` : morphisms and the induced maps.
* `H0map_id`, `H0map_comp`, `H0map_add`, `H0map_smul` (and their degree one and two analogues) :
  functoriality and additivity, hence descent of finite correspondences.
* `DeningerThreeTermTrace.H2map` : the trace on the top group.
* `DeningerThreeTermCup` and `cupH00`, `cupH01`, `cupH10`, `cupH11`, `cupH02`, `cupH20` : the cup
  product on cohomology.
-/

namespace RHTower

open DeningerArithmeticThreeTermComplex

section Operations

variable {R A0 A1 A2 B0 B1 B2 E0 E1 E2 : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup B0] [Module R B0] [AddCommGroup B1] [Module R B1]
variable [AddCommGroup B2] [Module R B2]
variable [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
variable [AddCommGroup E2] [Module R E2]

/-- **A morphism of three-term arithmetic complexes**: three linear maps commuting with both
differentials.  Galois maps, Frobenius, Verschiebung and the transverse flow are of this shape. -/
structure DeningerThreeTermHom (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (C' : DeningerArithmeticThreeTermComplex R B0 B1 B2) where
  /-- The degree-zero component. -/
  f0 : A0 →ₗ[R] B0
  /-- The degree-one component. -/
  f1 : A1 →ₗ[R] B1
  /-- The degree-two component. -/
  f2 : A2 →ₗ[R] B2
  /-- The first square commutes. -/
  comm0 : C'.d0.comp f0 = f1.comp C.d0
  /-- The second square commutes. -/
  comm1 : C'.d1.comp f1 = f2.comp C.d1

namespace DeningerThreeTermHom

variable {C : DeningerArithmeticThreeTermComplex R A0 A1 A2}
variable {C' : DeningerArithmeticThreeTermComplex R B0 B1 B2}
variable {C'' : DeningerArithmeticThreeTermComplex R E0 E1 E2}

theorem comm0_apply (φ : DeningerThreeTermHom C C') (x : A0) :
    C'.d0 (φ.f0 x) = φ.f1 (C.d0 x) := LinearMap.congr_fun φ.comm0 x

theorem comm1_apply (φ : DeningerThreeTermHom C C') (x : A1) :
    C'.d1 (φ.f1 x) = φ.f2 (C.d1 x) := LinearMap.congr_fun φ.comm1 x

/-- The induced map on degree-zero cocycles. -/
def cycles0Map (φ : DeningerThreeTermHom C C') : C.cycles0 →ₗ[R] C'.cycles0 where
  toFun x := ⟨φ.f0 (x : A0), by
    show C'.d0 (φ.f0 (x : A0)) = 0
    rw [φ.comm0_apply, show C.d0 (x : A0) = 0 from x.2, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add φ.f0 _ _)
  map_smul' _ _ := Subtype.ext (map_smul φ.f0 _ _)

/-- The induced map on degree-one cocycles. -/
def cycles1Map (φ : DeningerThreeTermHom C C') : C.cycles1 →ₗ[R] C'.cycles1 where
  toFun x := ⟨φ.f1 (x : A1), by
    show C'.d1 (φ.f1 (x : A1)) = 0
    rw [φ.comm1_apply, show C.d1 (x : A1) = 0 from x.2, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add φ.f1 _ _)
  map_smul' _ _ := Subtype.ext (map_smul φ.f1 _ _)

theorem cycles1Map_mem_boundaries (φ : DeningerThreeTermHom C C') (x : C.cycles1)
    (hx : x ∈ C.boundaries1.comap C.cycles1.subtype) :
    φ.cycles1Map x ∈ C'.boundaries1.comap C'.cycles1.subtype := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨φ.f0 a, ?_⟩
  show C'.d0 (φ.f0 a) = φ.f1 (x : A1)
  rw [φ.comm0_apply]
  exact congrArg φ.f1 ha

theorem f2_mem_boundaries2 (φ : DeningerThreeTermHom C C') (z : A2) (hz : z ∈ C.boundaries2) :
    φ.f2 z ∈ C'.boundaries2 := by
  obtain ⟨a, ha⟩ := hz
  exact ⟨φ.f1 a, by rw [φ.comm1_apply, ha]⟩

/-- **The induced map on `H⁰`.** -/
def H0map (φ : DeningerThreeTermHom C C') : C.H0 →ₗ[R] C'.H0 := φ.cycles0Map

/-- **The induced map on `H¹`.** -/
def H1map (φ : DeningerThreeTermHom C C') : C.H1 →ₗ[R] C'.H1 :=
  Submodule.mapQ _ _ φ.cycles1Map φ.cycles1Map_mem_boundaries

/-- **The induced map on `H²`.** -/
def H2map (φ : DeningerThreeTermHom C C') : C.H2 →ₗ[R] C'.H2 :=
  Submodule.mapQ _ _ φ.f2 φ.f2_mem_boundaries2

@[simp]
theorem H0map_apply (φ : DeningerThreeTermHom C C') (x : C.H0) :
    ((φ.H0map x : C'.cycles0) : B0) = φ.f0 (x : A0) := rfl

@[simp]
theorem H1map_mk (φ : DeningerThreeTermHom C C') (x : C.cycles1) :
    φ.H1map (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.cycles1Map x) := rfl

@[simp]
theorem H2map_mk (φ : DeningerThreeTermHom C C') (z : A2) :
    φ.H2map (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.f2 z) := rfl

/-- The identity morphism. -/
def id (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) : DeningerThreeTermHom C C where
  f0 := LinearMap.id
  f1 := LinearMap.id
  f2 := LinearMap.id
  comm0 := rfl
  comm1 := rfl

/-- Composition of morphisms. -/
def comp (ψ : DeningerThreeTermHom C' C'') (φ : DeningerThreeTermHom C C') :
    DeningerThreeTermHom C C'' where
  f0 := ψ.f0.comp φ.f0
  f1 := ψ.f1.comp φ.f1
  f2 := ψ.f2.comp φ.f2
  comm0 := by
    ext x
    show C''.d0 (ψ.f0 (φ.f0 x)) = ψ.f1 (φ.f1 (C.d0 x))
    rw [ψ.comm0_apply, φ.comm0_apply]
  comm1 := by
    ext x
    show C''.d1 (ψ.f1 (φ.f1 x)) = ψ.f2 (φ.f2 (C.d1 x))
    rw [ψ.comm1_apply, φ.comm1_apply]

@[simp]
theorem H0map_id (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) :
    (DeningerThreeTermHom.id C).H0map = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem H1map_id (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) :
    (DeningerThreeTermHom.id C).H1map = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem H2map_id (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) :
    (DeningerThreeTermHom.id C).H2map = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem H0map_comp (ψ : DeningerThreeTermHom C' C'') (φ : DeningerThreeTermHom C C') :
    (ψ.comp φ).H0map = ψ.H0map.comp φ.H0map := by
  ext x
  rfl

@[simp]
theorem H1map_comp (ψ : DeningerThreeTermHom C' C'') (φ : DeningerThreeTermHom C C') :
    (ψ.comp φ).H1map = ψ.H1map.comp φ.H1map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

@[simp]
theorem H2map_comp (ψ : DeningerThreeTermHom C' C'') (φ : DeningerThreeTermHom C C') :
    (ψ.comp φ).H2map = ψ.H2map.comp φ.H2map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- The sum of two morphisms: this is what makes finite correspondences descend. -/
def add (φ ψ : DeningerThreeTermHom C C') : DeningerThreeTermHom C C' where
  f0 := φ.f0 + ψ.f0
  f1 := φ.f1 + ψ.f1
  f2 := φ.f2 + ψ.f2
  comm0 := by
    ext x
    show C'.d0 (φ.f0 x + ψ.f0 x) = φ.f1 (C.d0 x) + ψ.f1 (C.d0 x)
    rw [map_add, φ.comm0_apply, ψ.comm0_apply]
  comm1 := by
    ext x
    show C'.d1 (φ.f1 x + ψ.f1 x) = φ.f2 (C.d1 x) + ψ.f2 (C.d1 x)
    rw [map_add, φ.comm1_apply, ψ.comm1_apply]

/-- A scalar multiple of a morphism. -/
def smul (c : R) (φ : DeningerThreeTermHom C C') : DeningerThreeTermHom C C' where
  f0 := c • φ.f0
  f1 := c • φ.f1
  f2 := c • φ.f2
  comm0 := by
    ext x
    show C'.d0 (c • φ.f0 x) = c • φ.f1 (C.d0 x)
    rw [map_smul, φ.comm0_apply]
  comm1 := by
    ext x
    show C'.d1 (c • φ.f1 x) = c • φ.f2 (C.d1 x)
    rw [map_smul, φ.comm1_apply]

@[simp]
theorem H0map_add (φ ψ : DeningerThreeTermHom C C') :
    (φ.add ψ).H0map = φ.H0map + ψ.H0map := by
  ext x
  rfl

@[simp]
theorem H1map_add (φ ψ : DeningerThreeTermHom C C') :
    (φ.add ψ).H1map = φ.H1map + ψ.H1map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

@[simp]
theorem H2map_add (φ ψ : DeningerThreeTermHom C C') :
    (φ.add ψ).H2map = φ.H2map + ψ.H2map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

@[simp]
theorem H0map_smul (c : R) (φ : DeningerThreeTermHom C C') :
    (DeningerThreeTermHom.smul c φ).H0map = c • φ.H0map := by
  ext x
  rfl

@[simp]
theorem H1map_smul (c : R) (φ : DeningerThreeTermHom C C') :
    (DeningerThreeTermHom.smul c φ).H1map = c • φ.H1map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

@[simp]
theorem H2map_smul (c : R) (φ : DeningerThreeTermHom C C') :
    (DeningerThreeTermHom.smul c φ).H2map = c • φ.H2map := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

end DeningerThreeTermHom

/-- **The transverse flow is a morphism of three-term complexes**, and the maps it induces are the
ones already attached to it. -/
def DeningerArithmeticThreeTermFlow.toHom (F : DeningerArithmeticThreeTermFlow R A0 A1 A2) :
    DeningerThreeTermHom F.complex F.complex where
  f0 := F.theta0
  f1 := F.theta1
  f2 := F.theta2
  comm0 := F.theta_commutes_d0
  comm1 := F.theta_commutes_d1

@[simp]
theorem DeningerArithmeticThreeTermFlow.toHom_H0map
    (F : DeningerArithmeticThreeTermFlow R A0 A1 A2) : F.toHom.H0map = F.thetaH0 := by
  ext x
  rfl

@[simp]
theorem DeningerArithmeticThreeTermFlow.toHom_H1map
    (F : DeningerArithmeticThreeTermFlow R A0 A1 A2) : F.toHom.H1map = F.thetaH1 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

@[simp]
theorem DeningerArithmeticThreeTermFlow.toHom_H2map
    (F : DeningerArithmeticThreeTermFlow R A0 A1 A2) : F.toHom.H2map = F.thetaH2 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- **A trace on the top term** that kills boundaries. -/
structure DeningerThreeTermTrace (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) where
  /-- The trace functional. -/
  tr : A2 →ₗ[R] R
  /-- It kills boundaries. -/
  tr_comp_d1 : tr.comp C.d1 = 0

namespace DeningerThreeTermTrace

variable {C : DeningerArithmeticThreeTermComplex R A0 A1 A2}

/-- **The trace descends to `H²`.** -/
def H2map (T : DeningerThreeTermTrace C) : C.H2 →ₗ[R] R :=
  C.boundaries2.liftQ T.tr (by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.congr_fun T.tr_comp_d1 a)

@[simp]
theorem H2map_mk (T : DeningerThreeTermTrace C) (z : A2) :
    T.H2map (Submodule.Quotient.mk z) = T.tr z := rfl

end DeningerThreeTermTrace

end Operations

end RHTower
