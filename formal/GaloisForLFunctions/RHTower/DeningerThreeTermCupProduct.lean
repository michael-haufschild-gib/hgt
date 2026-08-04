import GaloisForLFunctions.RHTower.DeningerThreeTermOperations

/-!
# The cup product on three-term arithmetic cohomology

A cup datum on three three-term complexes is a family of chain-level products obeying the
Koszul--Leibniz rule `d(x ∪ y) = dx ∪ y + (-1)^{|x|} x ∪ dy`.  Every such datum descends to
cohomology in each bidegree of total degree at most two: cocycles multiply to cocycles because the
Leibniz rule kills both terms, and a boundary in either variable produces a boundary, again by the
Leibniz rule.

* `DeningerThreeTermCup` : the chain-level cup datum.
* `cupH00`, `cupH01`, `cupH10`, `cupH11`, `cupH02`, `cupH20` : the descended products.
-/

namespace RHTower

open DeningerArithmeticThreeTermComplex

section CupProduct

variable {R A0 A1 A2 B0 B1 B2 E0 E1 E2 : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup B0] [Module R B0] [AddCommGroup B1] [Module R B1]
variable [AddCommGroup B2] [Module R B2]
variable [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
variable [AddCommGroup E2] [Module R E2]

theorem deningerQuotMk_add {M : Type*} [AddCommGroup M] [Module R M] (p : Submodule R M)
    (v w : M) : (Submodule.Quotient.mk (v + w) : M ⧸ p) =
      Submodule.Quotient.mk v + Submodule.Quotient.mk w := map_add p.mkQ v w

theorem deningerQuotMk_smul {M : Type*} [AddCommGroup M] [Module R M] (p : Submodule R M)
    (r : R) (v : M) : (Submodule.Quotient.mk (r • v) : M ⧸ p) =
      r • Submodule.Quotient.mk v := map_smul p.mkQ r v

/-- **A chain-level cup datum** on three three-term complexes: products in every bidegree of total
degree at most two, subject to the Koszul--Leibniz rules. -/
structure DeningerThreeTermCup (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (C' : DeningerArithmeticThreeTermComplex R B0 B1 B2)
    (C'' : DeningerArithmeticThreeTermComplex R E0 E1 E2) where
  /-- The product of two degree-zero cochains. -/
  cup00 : A0 →ₗ[R] B0 →ₗ[R] E0
  /-- The product of a degree-zero and a degree-one cochain. -/
  cup01 : A0 →ₗ[R] B1 →ₗ[R] E1
  /-- The product of a degree-one and a degree-zero cochain. -/
  cup10 : A1 →ₗ[R] B0 →ₗ[R] E1
  /-- The product of a degree-zero and a degree-two cochain. -/
  cup02 : A0 →ₗ[R] B2 →ₗ[R] E2
  /-- The product of two degree-one cochains. -/
  cup11 : A1 →ₗ[R] B1 →ₗ[R] E2
  /-- The product of a degree-two and a degree-zero cochain. -/
  cup20 : A2 →ₗ[R] B0 →ₗ[R] E2
  /-- Leibniz in total degree zero. -/
  leibniz00 : ∀ a b, C''.d0 (cup00 a b) = cup10 (C.d0 a) b + cup01 a (C'.d0 b)
  /-- Leibniz in bidegree `(0,1)`. -/
  leibniz01 : ∀ a b, C''.d1 (cup01 a b) = cup11 (C.d0 a) b + cup02 a (C'.d1 b)
  /-- Leibniz in bidegree `(1,0)`, with the Koszul sign. -/
  leibniz10 : ∀ a b, C''.d1 (cup10 a b) = cup20 (C.d1 a) b - cup11 a (C'.d0 b)

namespace DeningerThreeTermCup

variable {C : DeningerArithmeticThreeTermComplex R A0 A1 A2}
variable {C' : DeningerArithmeticThreeTermComplex R B0 B1 B2}
variable {C'' : DeningerArithmeticThreeTermComplex R E0 E1 E2}
variable (P : DeningerThreeTermCup C C' C'')

section Degree0

/-- The product of two degree-zero cocycles is a degree-zero cocycle. -/
def cupCycles00 (a : C.cycles0) : C'.cycles0 →ₗ[R] C''.cycles0 where
  toFun b := ⟨P.cup00 (a : A0) (b : B0), by
    show C''.d0 (P.cup00 (a : A0) (b : B0)) = 0
    rw [P.leibniz00, show C.d0 (a : A0) = 0 from a.2, show C'.d0 (b : B0) = 0 from b.2]
    simp⟩
  map_add' b b' := Subtype.ext (by simp)
  map_smul' r b := Subtype.ext (by simp)

/-- **The cup product `H⁰ × H⁰ → H⁰`.** -/
def cupH00 : C.H0 →ₗ[R] C'.H0 →ₗ[R] C''.H0 where
  toFun a := P.cupCycles00 a
  map_add' a a' := LinearMap.ext fun b => Subtype.ext (by simp [cupCycles00])
  map_smul' r a := LinearMap.ext fun b => Subtype.ext (by simp [cupCycles00])

@[simp]
theorem cupH00_val (a : C.H0) (b : C'.H0) :
    ((P.cupH00 a b : C''.cycles0) : E0) = P.cup00 (a : A0) (b : B0) := rfl

end Degree0

section Degree01

/-- The product of a degree-zero cocycle with a degree-one cocycle is a degree-one cocycle. -/
def cupCycles01 (a : C.cycles0) : C'.cycles1 →ₗ[R] C''.cycles1 where
  toFun y := ⟨P.cup01 (a : A0) (y : B1), by
    show C''.d1 (P.cup01 (a : A0) (y : B1)) = 0
    rw [P.leibniz01, show C.d0 (a : A0) = 0 from a.2, show C'.d1 (y : B1) = 0 from y.2]
    simp⟩
  map_add' y y' := Subtype.ext (by simp)
  map_smul' r y := Subtype.ext (by simp)

theorem cupCycles01_mem_boundaries (a : C.cycles0) (y : C'.cycles1)
    (hy : y ∈ C'.boundaries1.comap C'.cycles1.subtype) :
    P.cupCycles01 a y ∈ C''.boundaries1.comap C''.cycles1.subtype := by
  obtain ⟨b, hb⟩ := hy
  refine ⟨P.cup00 (a : A0) b, ?_⟩
  show C''.d0 (P.cup00 (a : A0) b) = P.cup01 (a : A0) (y : B1)
  rw [P.leibniz00, show C.d0 (a : A0) = 0 from a.2]
  have hb' : C'.d0 b = (y : B1) := hb
  rw [hb']
  simp

/-- **The cup product `H⁰ × H¹ → H¹`.** -/
def cupH01 : C.H0 →ₗ[R] C'.H1 →ₗ[R] C''.H1 where
  toFun a := Submodule.mapQ _ _ (P.cupCycles01 a) (P.cupCycles01_mem_boundaries a)
  map_add' a a' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact congrArg _ (Subtype.ext (by simp [cupCycles01]))
  map_smul' r a := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact congrArg _ (Subtype.ext (by simp [cupCycles01]))

@[simp]
theorem cupH01_mk (a : C.H0) (y : C'.cycles1) :
    P.cupH01 a (Submodule.Quotient.mk y) = Submodule.Quotient.mk (P.cupCycles01 a y) := rfl

end Degree01

section Degree10

/-- The product of a degree-one cocycle with a degree-zero cocycle is a degree-one cocycle. -/
def cupCycles10 (b : C'.cycles0) : C.cycles1 →ₗ[R] C''.cycles1 where
  toFun x := ⟨P.cup10 (x : A1) (b : B0), by
    show C''.d1 (P.cup10 (x : A1) (b : B0)) = 0
    rw [P.leibniz10, show C.d1 (x : A1) = 0 from x.2, show C'.d0 (b : B0) = 0 from b.2]
    simp⟩
  map_add' x x' := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

theorem cupCycles10_mem_boundaries (b : C'.cycles0) (x : C.cycles1)
    (hx : x ∈ C.boundaries1.comap C.cycles1.subtype) :
    P.cupCycles10 b x ∈ C''.boundaries1.comap C''.cycles1.subtype := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨P.cup00 a (b : B0), ?_⟩
  show C''.d0 (P.cup00 a (b : B0)) = P.cup10 (x : A1) (b : B0)
  rw [P.leibniz00, show C'.d0 (b : B0) = 0 from b.2]
  have ha' : C.d0 a = (x : A1) := ha
  rw [ha']
  simp

/-- **The cup product `H¹ × H⁰ → H¹`.** -/
def cupH10 : C.H1 →ₗ[R] C'.H0 →ₗ[R] C''.H1 where
  toFun q :=
    { toFun := fun b => Submodule.mapQ _ _ (P.cupCycles10 b) (P.cupCycles10_mem_boundaries b) q
      map_add' := by
        intro b b'
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact congrArg _ (Subtype.ext (by simp [cupCycles10]))
      map_smul' := by
        intro r b
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact congrArg _ (Subtype.ext (by simp [cupCycles10])) }
  map_add' q q' := by
    refine LinearMap.ext fun b => ?_
    exact map_add (Submodule.mapQ _ _ (P.cupCycles10 b) (P.cupCycles10_mem_boundaries b)) q q'
  map_smul' r q := by
    refine LinearMap.ext fun b => ?_
    exact map_smul (Submodule.mapQ _ _ (P.cupCycles10 b) (P.cupCycles10_mem_boundaries b)) r q

@[simp]
theorem cupH10_mk (x : C.cycles1) (b : C'.H0) :
    P.cupH10 (Submodule.Quotient.mk x) b = Submodule.Quotient.mk (P.cupCycles10 b x) := rfl

end Degree10

section Degree11

theorem cup11_mem_boundaries2_left (x : C.cycles1) (y : C'.cycles1)
    (hx : x ∈ C.boundaries1.comap C.cycles1.subtype) :
    P.cup11 (x : A1) (y : B1) ∈ C''.boundaries2 := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨P.cup01 a (y : B1), ?_⟩
  have ha' : C.d0 a = (x : A1) := ha
  rw [P.leibniz01, show C'.d1 (y : B1) = 0 from y.2, ha']
  simp

theorem cup11_mem_boundaries2_right (x : C.cycles1) (y : C'.cycles1)
    (hy : y ∈ C'.boundaries1.comap C'.cycles1.subtype) :
    P.cup11 (x : A1) (y : B1) ∈ C''.boundaries2 := by
  obtain ⟨b, hb⟩ := hy
  refine ⟨-P.cup10 (x : A1) b, ?_⟩
  have hb' : C'.d0 b = (y : B1) := hb
  rw [map_neg, P.leibniz10, show C.d1 (x : A1) = 0 from x.2, hb']
  simp

/-- The degree-one product with the right variable fixed, as a map out of the cocycles. -/
def cupCycles11Right (y : C'.cycles1) : C.cycles1 →ₗ[R] C''.H2 where
  toFun x := Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1))
  map_add' x x' := by
    show (Submodule.Quotient.mk (P.cup11 ((x + x' : C.cycles1) : A1) (y : B1)) : C''.H2) =
      Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1)) +
        Submodule.Quotient.mk (P.cup11 (x' : A1) (y : B1))
    rw [← deningerQuotMk_add C''.boundaries2]
    exact congrArg _ (by simp)
  map_smul' r x := by
    show (Submodule.Quotient.mk (P.cup11 ((r • x : C.cycles1) : A1) (y : B1)) : C''.H2) =
      r • Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1))
    rw [← deningerQuotMk_smul C''.boundaries2]
    exact congrArg _ (by simp)

/-- The degree-one product with the right variable fixed, descended in the left variable. -/
def cupH11Left (y : C'.cycles1) : C.H1 →ₗ[R] C''.H2 :=
  Submodule.liftQ _ (P.cupCycles11Right y) (by
    intro x hx
    show Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 (P.cup11_mem_boundaries2_left x y hx))

/-- **The cup product `H¹ × H¹ → H²`.** -/
def cupH11 : C'.H1 →ₗ[R] C.H1 →ₗ[R] C''.H2 :=
  Submodule.liftQ _
    { toFun := fun y => P.cupH11Left y
      map_add' := by
        intro y y'
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [LinearMap.add_apply]
        show (Submodule.Quotient.mk (P.cup11 (x : A1) ((y + y' : C'.cycles1) : B1)) : C''.H2) =
          Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1)) +
            Submodule.Quotient.mk (P.cup11 (x : A1) (y' : B1))
        rw [← deningerQuotMk_add C''.boundaries2]
        exact congrArg _ (by simp)
      map_smul' := by
        intro r y
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [RingHom.id_apply, LinearMap.smul_apply]
        show (Submodule.Quotient.mk (P.cup11 (x : A1) ((r • y : C'.cycles1) : B1)) : C''.H2) =
          r • Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1))
        rw [← deningerQuotMk_smul C''.boundaries2]
        exact congrArg _ (by simp) }
    (by
      intro y hy
      refine LinearMap.ext fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 (P.cup11_mem_boundaries2_right x y hy))

@[simp]
theorem cupH11_mk (x : C.cycles1) (y : C'.cycles1) :
    P.cupH11 (Submodule.Quotient.mk y) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.cup11 (x : A1) (y : B1)) := rfl

end Degree11

section Degree02

theorem cup02_mem_boundaries2 (a : C.cycles0) (z : B2) (hz : z ∈ C'.boundaries2) :
    P.cup02 (a : A0) z ∈ C''.boundaries2 := by
  obtain ⟨c, hc⟩ := hz
  refine ⟨P.cup01 (a : A0) c, ?_⟩
  rw [P.leibniz01, show C.d0 (a : A0) = 0 from a.2, hc]
  simp

/-- **The cup product `H⁰ × H² → H²`.** -/
def cupH02 : C.H0 →ₗ[R] C'.H2 →ₗ[R] C''.H2 where
  toFun a := Submodule.mapQ _ _ (P.cup02 (a : A0)) (P.cup02_mem_boundaries2 a)
  map_add' a a' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.add_apply]
    show (Submodule.Quotient.mk (P.cup02 ((a + a' : C.cycles0) : A0) z) : C''.H2) =
      Submodule.Quotient.mk (P.cup02 (a : A0) z) + Submodule.Quotient.mk (P.cup02 (a' : A0) z)
    rw [← deningerQuotMk_add C''.boundaries2]
    exact congrArg _ (by simp)
  map_smul' r a := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [RingHom.id_apply, LinearMap.smul_apply]
    show (Submodule.Quotient.mk (P.cup02 ((r • a : C.cycles0) : A0) z) : C''.H2) =
      r • Submodule.Quotient.mk (P.cup02 (a : A0) z)
    rw [← deningerQuotMk_smul C''.boundaries2]
    exact congrArg _ (by simp)

@[simp]
theorem cupH02_mk (a : C.H0) (z : B2) :
    P.cupH02 a (Submodule.Quotient.mk z) = Submodule.Quotient.mk (P.cup02 (a : A0) z) := rfl

end Degree02

section Degree20

theorem cup20_mem_boundaries2 (b : C'.cycles0) (z : A2) (hz : z ∈ C.boundaries2) :
    P.cup20 z (b : B0) ∈ C''.boundaries2 := by
  obtain ⟨a, ha⟩ := hz
  refine ⟨P.cup10 a (b : B0), ?_⟩
  rw [P.leibniz10, show C'.d0 (b : B0) = 0 from b.2, ha]
  simp

/-- **The cup product `H² × H⁰ → H²`.** -/
def cupH20 : C.H2 →ₗ[R] C'.H0 →ₗ[R] C''.H2 where
  toFun q :=
    { toFun := fun b => Submodule.mapQ _ _ (P.cup20.flip (b : B0)) (P.cup20_mem_boundaries2 b) q
      map_add' := by
        intro b b'
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show (Submodule.Quotient.mk (P.cup20 z ((b + b' : C'.cycles0) : B0)) : C''.H2) =
          Submodule.Quotient.mk (P.cup20 z (b : B0)) + Submodule.Quotient.mk (P.cup20 z (b' : B0))
        rw [← deningerQuotMk_add C''.boundaries2]
        exact congrArg _ (by simp)
      map_smul' := by
        intro r b
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show (Submodule.Quotient.mk (P.cup20 z ((r • b : C'.cycles0) : B0)) : C''.H2) =
          r • Submodule.Quotient.mk (P.cup20 z (b : B0))
        rw [← deningerQuotMk_smul C''.boundaries2]
        exact congrArg _ (by simp) }
  map_add' q q' := by
    refine LinearMap.ext fun b => ?_
    exact map_add (Submodule.mapQ _ _ (P.cup20.flip (b : B0)) (P.cup20_mem_boundaries2 b)) q q'
  map_smul' r q := by
    refine LinearMap.ext fun b => ?_
    exact map_smul (Submodule.mapQ _ _ (P.cup20.flip (b : B0)) (P.cup20_mem_boundaries2 b)) r q

@[simp]
theorem cupH20_mk (z : A2) (b : C'.H0) :
    P.cupH20 (Submodule.Quotient.mk z) b = Submodule.Quotient.mk (P.cup20 z (b : B0)) := rfl

end Degree20

end DeningerThreeTermCup

end CupProduct

end RHTower
