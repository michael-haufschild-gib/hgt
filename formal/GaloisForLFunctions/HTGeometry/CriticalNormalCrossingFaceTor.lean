import GaloisForLFunctions.HTGeometry.CofaceBoundaryReconstruction
import GaloisForLFunctions.HTGeometry.SourceFaceBaseChangeTransmutation

/-!
# Critical normal-crossing coordinate-face Tor

Normal form of the Hilbert--Burch resolution after a nonempty coordinate face is imposed.
`k` counts face coordinates after the distinguished base coordinate; `q` counts surviving
coordinates.  Thus face cardinality is `k + 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Finset

noncomputable section

variable {F : Type*} [Field F]

/-- Polynomial algebra on the coordinates surviving a face specialization. -/
abbrev criticalFaceRing (q : ℕ) := MvPolynomial (Fin q) F

/-- Product of all surviving coordinates. -/
def criticalFaceProduct (q : ℕ) : criticalFaceRing (F := F) q :=
  ∏ j, X j

/-- Degree-two and degree-one free terms in the relabelled face complex. -/
abbrev criticalFaceC2 (k q : ℕ) :=
  (Fin k ⊕ Fin q) → criticalFaceRing (F := F) q

abbrev criticalFaceC1 (k q : ℕ) :=
  (Fin (k + 1) ⊕ Fin q) → criticalFaceRing (F := F) q

/-- Base-changed Hilbert--Burch boundary. Face columns vanish; each surviving column is
multiplication by its own coordinate. -/
def criticalFaceBoundary (k q : ℕ) :
    criticalFaceC2 (F := F) k q →ₗ[criticalFaceRing (F := F) q]
      criticalFaceC1 (F := F) k q where
  toFun b
    | Sum.inl _ => 0
    | Sum.inr j => X j * b (Sum.inr j)
  map_add' b c := by
    funext i
    cases i <;> simp [mul_add]
  map_smul' a b := by
    funext i
    cases i <;> simp [mul_assoc, mul_comm a]

/-- Base-changed coface relation. On a one-coordinate face only the complementary product
survives; on a deeper face all coface generators vanish. -/
def criticalFaceRelation (k q : ℕ) :
    criticalFaceC1 (F := F) k q →ₗ[criticalFaceRing (F := F) q]
      criticalFaceRing (F := F) q where
  toFun a := if k = 0 then a (Sum.inl 0) * criticalFaceProduct q else 0
  map_add' a b := by
    by_cases hk : k = 0 <;> simp [hk, add_mul]
  map_smul' a b := by
    by_cases hk : k = 0 <;> simp [hk, mul_assoc]

@[simp]
theorem criticalFaceBoundary_apply_face (k q : ℕ)
    (b : criticalFaceC2 (F := F) k q) (i : Fin (k + 1)) :
    criticalFaceBoundary k q b (Sum.inl i) = 0 := rfl

@[simp]
theorem criticalFaceBoundary_apply_survivor (k q : ℕ)
    (b : criticalFaceC2 (F := F) k q) (j : Fin q) :
    criticalFaceBoundary k q b (Sum.inr j) = X j * b (Sum.inr j) := rfl

@[simp]
theorem criticalFaceRelation_boundary (k q : ℕ) :
    (criticalFaceRelation (F := F) k q).comp (criticalFaceBoundary k q) = 0 := by
  ext b
  by_cases hk : k = 0 <;> simp [criticalFaceRelation, hk]

/-- Boundary with codomain restricted to cycles. -/
def criticalFaceBoundaryToCycles (k q : ℕ) :
    criticalFaceC2 (F := F) k q →ₗ[criticalFaceRing (F := F) q]
      LinearMap.ker (criticalFaceRelation (F := F) k q) :=
  (criticalFaceBoundary k q).codRestrict _ (fun b => by
    rw [LinearMap.mem_ker]
    by_cases hk : k = 0 <;>
      simp [criticalFaceRelation, criticalFaceBoundary, hk])

/-- Homology of the exact length-two critical resolution after face base change. -/
abbrev criticalNormalCrossingFaceTor (k q : ℕ) : ℕ → Type _
  | 0 => criticalFaceRing (F := F) q ⧸
      LinearMap.range (criticalFaceRelation (F := F) k q)
  | 1 => LinearMap.ker (criticalFaceRelation (F := F) k q) ⧸
      LinearMap.range (criticalFaceBoundaryToCycles (F := F) k q)
  | 2 => LinearMap.ker (criticalFaceBoundary (F := F) k q)
  | _ + 3 => PUnit

/-- Quotient by an exact kernel, followed by a surjective map. -/
def quotientEquivOfKernelEqOfSurjective
    {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (g : V →ₗ[R] W) (P : Submodule R V) (hker : P = LinearMap.ker g)
    (hsurj : Function.Surjective g) : (V ⧸ P) ≃ₗ[R] W := by
  let gq : (V ⧸ P) →ₗ[R] W := P.liftQ g (by simpa [hker])
  apply LinearEquiv.ofBijective gq
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        apply (Submodule.Quotient.eq P).2
        rw [hker, LinearMap.mem_ker]
        change g (x - y) = 0
        rw [map_sub, sub_eq_zero]
        exact hxy
  · intro w
    obtain ⟨v, rfl⟩ := hsurj w
    exact ⟨P.mkQ v, rfl⟩

/-- Degree two consists exactly of the vanished non-base face columns. -/
def criticalFaceTorTwoEquiv (k q : ℕ) :
    criticalNormalCrossingFaceTor (F := F) k q 2 ≃ₗ[criticalFaceRing (F := F) q]
      (Fin k → criticalFaceRing (F := F) q) := by
  let forward : LinearMap.ker (criticalFaceBoundary (F := F) k q) →ₗ[
      criticalFaceRing (F := F) q] (Fin k → criticalFaceRing (F := F) q) := {
    toFun := fun b i => b.1 (Sum.inl i)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let backward : (Fin k → criticalFaceRing (F := F) q) →ₗ[
      criticalFaceRing (F := F) q]
      LinearMap.ker (criticalFaceBoundary (F := F) k q) := {
    toFun := fun a => ⟨fun i => match i with
      | Sum.inl j => a j
      | Sum.inr _ => 0, by
        rw [LinearMap.mem_ker]
        funext i
        cases i <;> simp⟩
    map_add' := by intros; apply Subtype.ext; funext i; cases i <;> simp
    map_smul' := by intros; apply Subtype.ext; funext i; cases i <;> simp }
  exact LinearEquiv.ofLinear forward backward (by
    apply LinearMap.ext
    intro a
    funext i
    rfl) (by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr j =>
      have hb := LinearMap.mem_ker.mp b.2
      have hj := congrFun hb (Sum.inr j)
      change X j * b.1 (Sum.inr j) = 0 at hj
      change (0 : criticalFaceRing (F := F) q) = b.1 (Sum.inr j)
      exact ((mul_eq_zero.mp hj).resolve_left (MvPolynomial.X_ne_zero j)).symm)

/-- On a one-coordinate face the degree-zero range is the principal product layer. -/
theorem range_criticalFaceRelation_zero (q : ℕ) :
    LinearMap.range (criticalFaceRelation (F := F) 0 q) =
      LinearMap.range (sourceFaceScalarMul (criticalFaceProduct (F := F) q)
        (criticalFaceRing (F := F) q)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a (Sum.inl 0), by simp [criticalFaceRelation, sourceFaceScalarMul,
      mul_comm]⟩
  · rintro ⟨a, rfl⟩
    let b : criticalFaceC1 (F := F) 0 q := fun i => match i with
      | Sum.inl _ => a
      | Sum.inr _ => 0
    exact ⟨b, by simp [criticalFaceRelation, sourceFaceScalarMul, b, mul_comm]⟩

/-- One-face degree zero is the lower normal-crossing hypersurface ring. -/
def criticalFaceTorZeroEquiv_oneFace (q : ℕ) :
    criticalNormalCrossingFaceTor (F := F) 0 q 0 ≃ₗ[criticalFaceRing (F := F) q]
      criticalFaceRing (F := F) q ⧸
        LinearMap.range (sourceFaceScalarMul (criticalFaceProduct (F := F) q)
          (criticalFaceRing (F := F) q)) :=
  sourceFaceQuotientEquivOfEq _ _ (range_criticalFaceRelation_zero (F := F) q)

/-- On every face of cardinality at least two the degree-one relation vanishes. -/
theorem criticalFaceRelation_succ (k q : ℕ) :
    criticalFaceRelation (F := F) (k + 1) q = 0 := by
  ext a
  simp [criticalFaceRelation]

/-- Explicit equivalence from a quotient by the zero submodule. -/
def quotientBotEquiv
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] :
    (V ⧸ (⊥ : Submodule R V)) ≃ₗ[R] V := by
  let f : (V ⧸ (⊥ : Submodule R V)) →ₗ[R] V :=
    Submodule.liftQ ⊥ LinearMap.id (by simp)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        apply (Submodule.Quotient.eq (⊥ : Submodule R V)).2
        change x = y at hxy
        simpa [hxy]
  · intro v
    exact ⟨(⊥ : Submodule R V).mkQ v, rfl⟩

/-- Every deeper face has the full face ring in degree zero. -/
def criticalFaceTorZeroEquiv_deeperFace (k q : ℕ) :
    criticalNormalCrossingFaceTor (F := F) (k + 1) q 0 ≃ₗ[
      criticalFaceRing (F := F) q] criticalFaceRing (F := F) q := by
  have hrange : LinearMap.range (criticalFaceRelation (F := F) (k + 1) q) = ⊥ := by
    rw [criticalFaceRelation_succ]
    exact LinearMap.range_zero
  exact (sourceFaceQuotientEquivOfEq _ _ hrange).trans quotientBotEquiv

/-! ## Degree-one profile -/

/-- Coordinate torsion summand attached to one surviving variable. -/
abbrev criticalFaceCoordinateQuotient (q : ℕ) (j : Fin q) :=
  criticalFaceRing (F := F) q ⧸
    LinearMap.range (sourceFaceScalarMul
      (X j : criticalFaceRing (F := F) q) (criticalFaceRing (F := F) q))

/-- Free face coordinates plus coordinate-torsion summands. -/
abbrev criticalFaceDegreeOneProfile (k q : ℕ) :=
  (Fin (k + 1) → criticalFaceRing (F := F) q) ×
    ((j : Fin q) → criticalFaceCoordinateQuotient (F := F) q j)

/-- Coordinate projection whose kernel is the base-changed boundary range. -/
def criticalFaceDegreeOneProjection (k q : ℕ) :
    criticalFaceC1 (F := F) k q →ₗ[criticalFaceRing (F := F) q]
      criticalFaceDegreeOneProfile (F := F) k q where
  toFun a :=
    (fun i => a (Sum.inl i),
      fun j => (LinearMap.range (sourceFaceScalarMul
        (X j : criticalFaceRing (F := F) q)
        (criticalFaceRing (F := F) q))).mkQ (a (Sum.inr j)))
  map_add' a b := by
    apply Prod.ext
    · funext i
      rfl
    · funext j
      exact map_add _ _ _
  map_smul' a b := by
    apply Prod.ext
    · funext i
      rfl
    · funext j
      rfl

/-- Every profile has a representative. -/
theorem criticalFaceDegreeOneProjection_surjective (k q : ℕ) :
    Function.Surjective (criticalFaceDegreeOneProjection (F := F) k q) := by
  rintro ⟨u, v⟩
  have hv : ∀ j : Fin q, ∃ x : criticalFaceRing (F := F) q,
      (LinearMap.range (sourceFaceScalarMul
        (X j : criticalFaceRing (F := F) q)
        (criticalFaceRing (F := F) q))).mkQ x = v j := by
    intro j
    exact Submodule.Quotient.mk_surjective _ (v j)
  choose x hx using hv
  let a : criticalFaceC1 (F := F) k q := fun i => match i with
    | Sum.inl j => u j
    | Sum.inr j => x j
  refine ⟨a, ?_⟩
  apply Prod.ext
  · funext i
    rfl
  · funext j
    exact hx j

/-- Exact diagonal boundary law. -/
theorem ker_criticalFaceDegreeOneProjection (k q : ℕ) :
    LinearMap.ker (criticalFaceDegreeOneProjection (F := F) k q) =
      LinearMap.range (criticalFaceBoundary (F := F) k q) := by
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    have hface : ∀ i : Fin (k + 1), a (Sum.inl i) = 0 := by
      intro i
      have h := congrArg (fun z => z.1 i) ha
      exact h
    have hsurvivor : ∀ j : Fin q, a (Sum.inr j) ∈
        LinearMap.range (sourceFaceScalarMul
          (X j : criticalFaceRing (F := F) q)
          (criticalFaceRing (F := F) q)) := by
      intro j
      apply (Submodule.Quotient.mk_eq_zero _).1
      have h := congrArg (fun z => z.2 j) ha
      exact h
    have hwitness : ∀ j : Fin q, ∃ x : criticalFaceRing (F := F) q,
        X j * x = a (Sum.inr j) := by
      intro j
      rcases hsurvivor j with ⟨x, hx⟩
      exact ⟨x, hx⟩
    choose x hx using hwitness
    let b : criticalFaceC2 (F := F) k q := fun i => match i with
      | Sum.inl _ => 0
      | Sum.inr j => x j
    refine ⟨b, ?_⟩
    funext i
    cases i with
    | inl i => exact (hface i).symm
    | inr j => exact hx j
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    apply Prod.ext
    · funext i
      rfl
    · funext j
      apply Submodule.Quotient.mk_eq_zero _ |>.2
      exact ⟨b (Sum.inr j), rfl⟩

/-- On a deeper face every degree-one chain is a cycle. -/
theorem ker_criticalFaceRelation_succ (k q : ℕ) :
    LinearMap.ker (criticalFaceRelation (F := F) (k + 1) q) = ⊤ := by
  rw [criticalFaceRelation_succ]
  exact LinearMap.ker_zero

/-- Degree-one projection restricted to deeper-face cycles. -/
def criticalDeeperFaceDegreeOneCycleProjection (k q : ℕ) :
    LinearMap.ker (criticalFaceRelation (F := F) (k + 1) q) →ₗ[
      criticalFaceRing (F := F) q]
      criticalFaceDegreeOneProfile (F := F) (k + 1) q :=
  (criticalFaceDegreeOneProjection (F := F) (k + 1) q).comp
    (LinearMap.ker (criticalFaceRelation (F := F) (k + 1) q)).subtype

theorem criticalDeeperFaceDegreeOneCycleProjection_surjective (k q : ℕ) :
    Function.Surjective (criticalDeeperFaceDegreeOneCycleProjection (F := F) k q) := by
  intro w
  obtain ⟨a, ha⟩ := criticalFaceDegreeOneProjection_surjective (F := F) (k + 1) q w
  refine ⟨⟨a, ?_⟩, ha⟩
  rw [LinearMap.mem_ker, criticalFaceRelation_succ]
  rfl

theorem ker_criticalDeeperFaceDegreeOneCycleProjection (k q : ℕ) :
    LinearMap.ker (criticalDeeperFaceDegreeOneCycleProjection (F := F) k q) =
      LinearMap.range (criticalFaceBoundaryToCycles (F := F) (k + 1) q) := by
  ext a
  constructor
  · intro ha
    have ha' : a.1 ∈ LinearMap.ker
        (criticalFaceDegreeOneProjection (F := F) (k + 1) q) := by
      exact ha
    rw [ker_criticalFaceDegreeOneProjection] at ha'
    rcases ha' with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact hb
  · rintro ⟨b, hb⟩
    rw [LinearMap.mem_ker]
    have hbval : (criticalFaceBoundary (F := F) (k + 1) q) b = a.1 :=
      congrArg Subtype.val hb
    change criticalFaceDegreeOneProjection (F := F) (k + 1) q a.1 = 0
    rw [← hbval]
    exact LinearMap.mem_ker.mp
      ((ker_criticalFaceDegreeOneProjection (F := F) (k + 1) q).symm ▸
        ⟨b, rfl⟩)

/-- Formula `(20)` in degree one: free summands for all killed coordinates and coordinate
quotients for all surviving coordinates. -/
def criticalFaceTorOneEquiv_deeperFace (k q : ℕ) :
    criticalNormalCrossingFaceTor (F := F) (k + 1) q 1 ≃ₗ[
      criticalFaceRing (F := F) q]
      criticalFaceDegreeOneProfile (F := F) (k + 1) q :=
  quotientEquivOfKernelEqOfSurjective
    (criticalDeeperFaceDegreeOneCycleProjection (F := F) k q)
    (LinearMap.range (criticalFaceBoundaryToCycles (F := F) (k + 1) q))
    (ker_criticalDeeperFaceDegreeOneCycleProjection (F := F) k q).symm
    (criticalDeeperFaceDegreeOneCycleProjection_surjective (F := F) k q)

/-- One-face degree-one profile, with no free face summand. -/
abbrev criticalOneFaceDegreeOneProfile (q : ℕ) :=
  (j : Fin q) → criticalFaceCoordinateQuotient (F := F) q j

def criticalOneFaceDegreeOneCycleProjection (q : ℕ) :
    LinearMap.ker (criticalFaceRelation (F := F) 0 q) →ₗ[
      criticalFaceRing (F := F) q]
      criticalOneFaceDegreeOneProfile (F := F) q where
  toFun a j := (LinearMap.range (sourceFaceScalarMul
    (X j : criticalFaceRing (F := F) q)
    (criticalFaceRing (F := F) q))).mkQ (a.1 (Sum.inr j))
  map_add' a b := by funext j; exact map_add _ _ _
  map_smul' a b := by funext j; rfl

theorem criticalFaceProduct_ne_zero (q : ℕ) :
    criticalFaceProduct (F := F) q ≠ 0 := by
  rw [criticalFaceProduct, Finset.prod_ne_zero_iff]
  intro j hj
  exact MvPolynomial.X_ne_zero j

theorem criticalOneFaceDegreeOneCycleProjection_surjective (q : ℕ) :
    Function.Surjective (criticalOneFaceDegreeOneCycleProjection (F := F) q) := by
  intro v
  have hv : ∀ j : Fin q, ∃ x : criticalFaceRing (F := F) q,
      (LinearMap.range (sourceFaceScalarMul
        (X j : criticalFaceRing (F := F) q)
        (criticalFaceRing (F := F) q))).mkQ x = v j := by
    intro j
    exact Submodule.Quotient.mk_surjective _ (v j)
  choose x hx using hv
  let a : criticalFaceC1 (F := F) 0 q := fun i => match i with
    | Sum.inl _ => 0
    | Sum.inr j => x j
  refine ⟨⟨a, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker]
    simp [criticalFaceRelation, a]
  · funext j
    exact hx j

theorem ker_criticalOneFaceDegreeOneCycleProjection (q : ℕ) :
    LinearMap.ker (criticalOneFaceDegreeOneCycleProjection (F := F) q) =
      LinearMap.range (criticalFaceBoundaryToCycles (F := F) 0 q) := by
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    have hsurvivor : ∀ j : Fin q, a.1 (Sum.inr j) ∈
        LinearMap.range (sourceFaceScalarMul
          (X j : criticalFaceRing (F := F) q)
          (criticalFaceRing (F := F) q)) := by
      intro j
      apply (Submodule.Quotient.mk_eq_zero _).1
      exact congrFun ha j
    have hwitness : ∀ j : Fin q, ∃ x : criticalFaceRing (F := F) q,
        X j * x = a.1 (Sum.inr j) := by
      intro j
      rcases hsurvivor j with ⟨x, hx⟩
      exact ⟨x, hx⟩
    choose x hx using hwitness
    have hbase : a.1 (Sum.inl (0 : Fin 1)) = 0 := by
      have hcycle := LinearMap.mem_ker.mp a.2
      change a.1 (Sum.inl (0 : Fin 1)) * criticalFaceProduct q = 0 at hcycle
      exact (mul_eq_zero.mp hcycle).resolve_right (criticalFaceProduct_ne_zero q)
    let b : criticalFaceC2 (F := F) 0 q := fun i => match i with
      | Sum.inl h => Fin.elim0 h
      | Sum.inr j => x j
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    cases i with
    | inl i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact hbase.symm
    | inr j => exact hx j
  · rintro ⟨b, hb⟩
    rw [LinearMap.mem_ker]
    funext j
    have hbval : (criticalFaceBoundary (F := F) 0 q) b = a.1 :=
      congrArg Subtype.val hb
    change (LinearMap.range (sourceFaceScalarMul
      (X j : criticalFaceRing (F := F) q)
      (criticalFaceRing (F := F) q))).mkQ (a.1 (Sum.inr j)) = 0
    rw [← hbval]
    apply Submodule.Quotient.mk_eq_zero _ |>.2
    exact ⟨b (Sum.inr j), rfl⟩

/-- Formula `(19)` in degree one. -/
def criticalFaceTorOneEquiv_oneFace (q : ℕ) :
    criticalNormalCrossingFaceTor (F := F) 0 q 1 ≃ₗ[
      criticalFaceRing (F := F) q]
      criticalOneFaceDegreeOneProfile (F := F) q :=
  quotientEquivOfKernelEqOfSurjective
    (criticalOneFaceDegreeOneCycleProjection (F := F) q)
    (LinearMap.range (criticalFaceBoundaryToCycles (F := F) 0 q))
    (ker_criticalOneFaceDegreeOneCycleProjection (F := F) q).symm
    (criticalOneFaceDegreeOneCycleProjection_surjective (F := F) q)

/-! ## One-face Jacobian correction -/

/-- The principal full-product layer in the lower coordinate algebra. -/
abbrev criticalFaceProductLayer (r : ℕ) :
    Submodule (criticalFaceRing (F := F) (r + 1))
      (criticalFaceRing (F := F) (r + 1)) :=
  LinearMap.range (sourceFaceScalarMul
    (criticalFaceProduct (F := F) (r + 1))
    (criticalFaceRing (F := F) (r + 1)))

/-- Send a one-face cycle to its lower Jacobian relation modulo the full product. -/
def criticalOneFaceJacobianCycleMap (r : ℕ) :
    LinearMap.ker (criticalFaceRelation (F := F) 0 (r + 1)) →ₗ[
      criticalFaceRing (F := F) (r + 1)]
      criticalFaceRing (F := F) (r + 1) ⧸ criticalFaceProductLayer (F := F) r where
  toFun a := (criticalFaceProductLayer (F := F) r).mkQ
    (GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
      (fun j => a.1 (Sum.inr j)))
  map_add' a b := by
    rw [← map_add]
    congr 1
    simp [GaloisForLFunctions.VeroneseIdeal.cofaceRelation, add_mul,
      Finset.sum_add_distrib]
  map_smul' a b := by
    rw [← map_smul]
    congr 1
    simp [GaloisForLFunctions.VeroneseIdeal.cofaceRelation, mul_assoc,
      Finset.mul_sum]

/-- Boundaries map to zero in the lower hypersurface quotient. -/
theorem criticalOneFaceJacobianCycleMap_boundary (r : ℕ)
    (b : criticalFaceC2 (F := F) 0 (r + 1)) :
    criticalOneFaceJacobianCycleMap (F := F) r
      (criticalFaceBoundaryToCycles (F := F) 0 (r + 1) b) = 0 := by
  apply Submodule.Quotient.mk_eq_zero _ |>.2
  refine ⟨∑ j : Fin (r + 1), b (Sum.inr j), ?_⟩
  rw [sourceFaceScalarMul_apply]
  rw [GaloisForLFunctions.VeroneseIdeal.cofaceRelation]
  calc
    criticalFaceProduct (F := F) (r + 1) *
        (∑ j : Fin (r + 1), b (Sum.inr j)) =
      ∑ j : Fin (r + 1),
        b (Sum.inr j) * criticalFaceProduct (F := F) (r + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j : Fin (r + 1),
        (X j * b (Sum.inr j)) *
          GaloisForLFunctions.VeroneseIdeal.cofaceMonomial r j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [criticalFaceProduct,
        ← GaloisForLFunctions.VeroneseIdeal.X_mul_cofaceMonomial r j]
      ring

/-- A one-face cycle has zero distinguished face coordinate. -/
theorem criticalOneFaceCycle_base_eq_zero (q : ℕ)
    (a : LinearMap.ker (criticalFaceRelation (F := F) 0 q)) :
    a.1 (Sum.inl (0 : Fin 1)) = 0 := by
  have hcycle := LinearMap.mem_ker.mp a.2
  change a.1 (Sum.inl (0 : Fin 1)) * criticalFaceProduct q = 0 at hcycle
  exact (mul_eq_zero.mp hcycle).resolve_right (criticalFaceProduct_ne_zero q)

/-- Exact kernel law behind `(21)`: a lower Jacobian relation vanishes modulo the product iff
its coefficient vector is a base-changed Hilbert--Burch boundary. -/
theorem ker_criticalOneFaceJacobianCycleMap (r : ℕ) :
    LinearMap.ker (criticalOneFaceJacobianCycleMap (F := F) r) =
      LinearMap.range (criticalFaceBoundaryToCycles (F := F) 0 (r + 1)) := by
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    have hproduct :
        GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
          (fun j => a.1 (Sum.inr j)) ∈ criticalFaceProductLayer (F := F) r :=
      (Submodule.Quotient.mk_eq_zero _).1 ha
    rcases hproduct with ⟨c, hc⟩
    have hc' : criticalFaceProduct (F := F) (r + 1) * c =
        GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
          (fun j => a.1 (Sum.inr j)) := by
      simpa only [sourceFaceScalarMul_apply, smul_eq_mul] using hc
    have hrel : GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
        (fun j => if j = 0 then a.1 (Sum.inr j) - c * X 0
          else a.1 (Sum.inr j)) = 0 := by
      calc
        GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
            (fun j => if j = 0 then a.1 (Sum.inr j) - c * X 0
              else a.1 (Sum.inr j)) =
          GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
              (fun j => a.1 (Sum.inr j)) -
            c * criticalFaceProduct (F := F) (r + 1) := by
              rw [GaloisForLFunctions.VeroneseIdeal.cofaceRelation,
                GaloisForLFunctions.VeroneseIdeal.cofaceRelation,
                Fin.sum_univ_succ, Fin.sum_univ_succ]
              simp only [↓reduceIte, Fin.succ_ne_zero]
              rw [criticalFaceProduct,
                ← GaloisForLFunctions.VeroneseIdeal.X_mul_cofaceMonomial r 0]
              ring
        _ = 0 := by
          rw [← hc']
          ring
    obtain ⟨d, hd⟩ :=
      (GaloisForLFunctions.VeroneseIdeal.cofaceRelation_eq_zero_iff r
        (fun j => if j = 0 then a.1 (Sum.inr j) - c * X 0
          else a.1 (Sum.inr j))).mp hrel
    have hwitness : ∀ j : Fin (r + 1), ∃ x : criticalFaceRing (F := F) (r + 1),
        X j * x = a.1 (Sum.inr j) := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · refine ⟨c - ∑ i : Fin r, d i, ?_⟩
        have hzero := congrFun hd 0
        simp only [↓reduceIte,
          GaloisForLFunctions.VeroneseIdeal.cofaceBoundary,
          Fin.cases_zero] at hzero
        calc
          X 0 * (c - ∑ i : Fin r, d i) =
              c * X 0 - X 0 * ∑ i : Fin r, d i := by ring
          _ = c * X 0 + (-X 0 * ∑ i : Fin r, d i) := by ring
          _ = c * X 0 + (a.1 (Sum.inr 0) - c * X 0) := by rw [hzero]
          _ = a.1 (Sum.inr 0) := by ring
      · refine ⟨d i, ?_⟩
        have hi := congrFun hd i.succ
        simp only [Fin.succ_ne_zero, ↓reduceIte,
          GaloisForLFunctions.VeroneseIdeal.cofaceBoundary,
          Fin.cases_succ] at hi
        exact hi.symm
    choose x hx using hwitness
    let b : criticalFaceC2 (F := F) 0 (r + 1) := fun i => match i with
      | Sum.inl h => Fin.elim0 h
      | Sum.inr j => x j
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    cases i with
    | inl i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact (criticalOneFaceCycle_base_eq_zero (F := F) (r + 1) a).symm
    | inr j => exact hx j
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    exact criticalOneFaceJacobianCycleMap_boundary (F := F) r b

/-- Formula `(21)`, first form: one-face `Tor₁` is the image of the lower Jacobian ideal in the
lower hypersurface quotient, i.e. `J_F/(P_F)`. -/
def criticalFaceTorOneEquivJacobianImage (r : ℕ) :
    criticalNormalCrossingFaceTor (F := F) 0 (r + 1) 1 ≃ₗ[
      criticalFaceRing (F := F) (r + 1)]
      LinearMap.range (criticalOneFaceJacobianCycleMap (F := F) r) :=
  (sourceFaceQuotientEquivOfEq _ _
      (ker_criticalOneFaceJacobianCycleMap (F := F) r).symm).trans
    (LinearMap.quotKerEquivRange (criticalOneFaceJacobianCycleMap (F := F) r))

/-- Lower Jacobian ideal viewed as a submodule of the surviving polynomial algebra. -/
abbrev criticalFaceJacobianLayer (r : ℕ) :
    Submodule (criticalFaceRing (F := F) (r + 1))
      (criticalFaceRing (F := F) (r + 1)) :=
  GaloisForLFunctions.VeroneseIdeal.veroneseIdeal F (Fin (r + 1)) r

/-- The full product belongs to the lower Jacobian ideal. -/
theorem criticalFaceProductLayer_le_jacobianLayer (r : ℕ) :
    criticalFaceProductLayer (F := F) r ≤ criticalFaceJacobianLayer (F := F) r := by
  rintro z ⟨c, rfl⟩
  rw [sourceFaceScalarMul_apply, smul_eq_mul]
  have hm : GaloisForLFunctions.VeroneseIdeal.cofaceMonomial (F := F) r 0 ∈
      GaloisForLFunctions.VeroneseIdeal.veroneseIdeal F (Fin (r + 1)) r := by
    rw [← GaloisForLFunctions.VeroneseIdeal.cofaceMonomialIdeal_eq_veroneseIdeal]
    exact Ideal.subset_span ⟨0, rfl⟩
  rw [criticalFaceProduct,
    ← GaloisForLFunctions.VeroneseIdeal.X_mul_cofaceMonomial r 0]
  exact Ideal.mul_mem_right c _ (Ideal.mul_mem_left _ _ hm)

/-- Specialization from the lower normal-crossing hypersurface to its intrinsic critical
quotient. -/
def criticalFaceHypersurfaceToCriticalQuotient (r : ℕ) :
    (criticalFaceRing (F := F) (r + 1) ⧸ criticalFaceProductLayer (F := F) r) →ₗ[
      criticalFaceRing (F := F) (r + 1)]
      (criticalFaceRing (F := F) (r + 1) ⧸ criticalFaceJacobianLayer (F := F) r) :=
  (criticalFaceProductLayer (F := F) r).liftQ
    (criticalFaceJacobianLayer (F := F) r).mkQ (by
      intro z hz
      exact Submodule.Quotient.mk_eq_zero _ |>.2
        (criticalFaceProductLayer_le_jacobianLayer (F := F) r hz))

/-- Image of the Jacobian ideal in the hypersurface quotient is exactly the kernel of the
specialization to the critical quotient. -/
theorem ker_criticalFaceHypersurfaceToCriticalQuotient (r : ℕ) :
    LinearMap.ker (criticalFaceHypersurfaceToCriticalQuotient (F := F) r) =
      (criticalFaceJacobianLayer (F := F) r).map
        (criticalFaceProductLayer (F := F) r).mkQ := by
  ext z
  induction z using Quotient.inductionOn with
  | _ z =>
    constructor
    · intro hz
      rw [LinearMap.mem_ker] at hz
      have hzJ : z ∈ criticalFaceJacobianLayer (F := F) r :=
        (Submodule.Quotient.mk_eq_zero _).1 hz
      exact ⟨z, hzJ, rfl⟩
    · rintro ⟨w, hw, hzw⟩
      rw [LinearMap.mem_ker]
      change (criticalFaceJacobianLayer (F := F) r).mkQ z = 0
      apply Submodule.Quotient.mk_eq_zero _ |>.2
      have hwzP : w - z ∈ criticalFaceProductLayer (F := F) r :=
        (Submodule.Quotient.eq (criticalFaceProductLayer (F := F) r)).1 hzw
      have hwzJ : w - z ∈ criticalFaceJacobianLayer (F := F) r :=
        criticalFaceProductLayer_le_jacobianLayer (F := F) r hwzP
      simpa only [sub_sub_cancel] using
        (criticalFaceJacobianLayer (F := F) r).sub_mem hw hwzJ

/-- Jacobian relations produced by one-face cycles fill the entire Jacobian image modulo the
product. -/
theorem range_criticalOneFaceJacobianCycleMap (r : ℕ) :
    LinearMap.range (criticalOneFaceJacobianCycleMap (F := F) r) =
      (criticalFaceJacobianLayer (F := F) r).map
        (criticalFaceProductLayer (F := F) r).mkQ := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨GaloisForLFunctions.VeroneseIdeal.cofaceRelation r
      (fun j => a.1 (Sum.inr j)), ?_, rfl⟩
    exact (GaloisForLFunctions.VeroneseIdeal.mem_veroneseIdeal_iff_exists_cofaceRelation
      r _).2 ⟨fun j => a.1 (Sum.inr j), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨v, hv⟩ :=
      (GaloisForLFunctions.VeroneseIdeal.mem_veroneseIdeal_iff_exists_cofaceRelation
        r p).1 hp
    let a : criticalFaceC1 (F := F) 0 (r + 1) := fun i => match i with
      | Sum.inl _ => 0
      | Sum.inr j => v j
    have ha : a ∈ LinearMap.ker (criticalFaceRelation (F := F) 0 (r + 1)) := by
      rw [LinearMap.mem_ker]
      simp [criticalFaceRelation, a]
    refine ⟨⟨a, ha⟩, ?_⟩
    change (criticalFaceProductLayer (F := F) r).mkQ
      (GaloisForLFunctions.VeroneseIdeal.cofaceRelation r v) =
        (criticalFaceProductLayer (F := F) r).mkQ p
    rw [hv]

/-- Formula `(21)`, second form: `J_F/(P_F)` is precisely the kernel of the correction from
the lower hypersurface to the lower critical module. -/
def criticalFaceTorOneEquivCorrectionKernel (r : ℕ) :
    criticalNormalCrossingFaceTor (F := F) 0 (r + 1) 1 ≃ₗ[
      criticalFaceRing (F := F) (r + 1)]
      LinearMap.ker (criticalFaceHypersurfaceToCriticalQuotient (F := F) r) :=
  (criticalFaceTorOneEquivJacobianImage (F := F) r).trans <|
    LinearEquiv.ofEq _ _ <|
      (range_criticalOneFaceJacobianCycleMap (F := F) r).trans
        (ker_criticalFaceHypersurfaceToCriticalQuotient (F := F) r).symm

/-- Literal quotient `J_F/(P_F)`. -/
abbrev criticalFaceJacobianModuloProduct (r : ℕ) :=
  criticalFaceJacobianLayer (F := F) r ⧸
    (criticalFaceProductLayer (F := F) r).comap
      (criticalFaceJacobianLayer (F := F) r).subtype

/-- Include the Jacobian ideal into the hypersurface quotient. -/
def criticalFaceJacobianToHypersurface (r : ℕ) :
    criticalFaceJacobianLayer (F := F) r →ₗ[
      criticalFaceRing (F := F) (r + 1)]
      (criticalFaceRing (F := F) (r + 1) ⧸ criticalFaceProductLayer (F := F) r) :=
  (criticalFaceProductLayer (F := F) r).mkQ.comp
    (criticalFaceJacobianLayer (F := F) r).subtype

theorem ker_criticalFaceJacobianToHypersurface (r : ℕ) :
    LinearMap.ker (criticalFaceJacobianToHypersurface (F := F) r) =
      (criticalFaceProductLayer (F := F) r).comap
        (criticalFaceJacobianLayer (F := F) r).subtype := by
  ext z
  rw [LinearMap.mem_ker]
  exact Submodule.Quotient.mk_eq_zero _

theorem range_criticalFaceJacobianToHypersurface (r : ℕ) :
    LinearMap.range (criticalFaceJacobianToHypersurface (F := F) r) =
      (criticalFaceJacobianLayer (F := F) r).map
        (criticalFaceProductLayer (F := F) r).mkQ := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

/-- Canonical quotient interpretation of the Jacobian image. -/
def criticalFaceJacobianModuloProductEquivImage (r : ℕ) :
    criticalFaceJacobianModuloProduct (F := F) r ≃ₗ[
      criticalFaceRing (F := F) (r + 1)]
      LinearMap.range (criticalOneFaceJacobianCycleMap (F := F) r) :=
  (sourceFaceQuotientEquivOfEq _ _
      (ker_criticalFaceJacobianToHypersurface (F := F) r).symm).trans <|
    (LinearMap.quotKerEquivRange
      (criticalFaceJacobianToHypersurface (F := F) r)).trans <|
      LinearEquiv.ofEq _ _ <|
        (range_criticalFaceJacobianToHypersurface (F := F) r).trans
          (range_criticalOneFaceJacobianCycleMap (F := F) r).symm

/-- Formula `(21)` with literal left side `Tor₁` and right side `J_F/(P_F)`. -/
def criticalFaceTorOneEquivJacobianModuloProduct (r : ℕ) :
    criticalNormalCrossingFaceTor (F := F) 0 (r + 1) 1 ≃ₗ[
      criticalFaceRing (F := F) (r + 1)]
      criticalFaceJacobianModuloProduct (F := F) r :=
  (criticalFaceTorOneEquivJacobianImage (F := F) r).trans
    (criticalFaceJacobianModuloProductEquivImage (F := F) r).symm

/-! ## Source-resolution and all-degree certificates -/

/-- The one-face normal form starts from the already proved exact minimal resolution on `r + 2`
coordinates. -/
theorem criticalOneFace_sourceResolution_exact (r : ℕ) :
    GaloisForLFunctions.VeroneseIdeal.CofaceBoundaryResolutionCertificate
      (F := F) (r + 1) :=
  GaloisForLFunctions.VeroneseIdeal.cofaceBoundaryResolutionCertificate
    (F := F) (r + 1) (Nat.succ_pos r)

/-- A deeper face with `k + 2` killed and `q` surviving coordinates starts from the exact minimal
resolution on `k + q + 2` coordinates. -/
theorem criticalDeeperFace_sourceResolution_exact (k q : ℕ) :
    GaloisForLFunctions.VeroneseIdeal.CofaceBoundaryResolutionCertificate
      (F := F) (k + q + 1) :=
  GaloisForLFunctions.VeroneseIdeal.cofaceBoundaryResolutionCertificate
    (F := F) (k + q + 1) (Nat.succ_pos (k + q))

/-- Formula `(19)` in degree two: a one-coordinate face has no second Tor. -/
theorem criticalNormalCrossingFaceTor_two_subsingleton_oneFace (q : ℕ) :
    Subsingleton (criticalNormalCrossingFaceTor (F := F) 0 q 2) :=
  (criticalFaceTorTwoEquiv (F := F) 0 q).toEquiv.subsingleton

/-- The complex has no terms, hence no Tor, above degree two. -/
theorem criticalNormalCrossingFaceTor_subsingleton_of_three_le
    (k q i : ℕ) (hi : 3 ≤ i) :
    Subsingleton (criticalNormalCrossingFaceTor (F := F) k q i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa only [Nat.add_comm] using (inferInstance : Subsingleton PUnit)

/-- Complete one-face vanishing above degree one. -/
theorem criticalNormalCrossingFaceTor_subsingleton_oneFace_of_two_le
    (q i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (criticalNormalCrossingFaceTor (F := F) 0 q i) := by
  rcases Nat.eq_or_lt_of_le hi with rfl | hi3
  · exact criticalNormalCrossingFaceTor_two_subsingleton_oneFace (F := F) q
  · exact criticalNormalCrossingFaceTor_subsingleton_of_three_le
      (F := F) 0 q i hi3

end

end GaloisForLFunctions.HTGeometry
