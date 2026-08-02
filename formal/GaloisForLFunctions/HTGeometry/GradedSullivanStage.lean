import GaloisForLFunctions.HTGeometry.FreeGradedCommutativeAlgebra
import GaloisForLFunctions.HTGeometry.ExteriorOddDerivation
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Sullivan stages on generators of mixed degree

A stage of a Sullivan tower is a set of generators with assigned degrees together with a
degree-raising odd derivation determined by its values on those generators.  Attaching further
generators, each mapping to a cocycle of the stage, produces another stage whose differential
extends the old one and in which every attached class has become a coboundary.

Because the generators carry individual degrees, a generator of degree `n` may be attached to kill a
class in degree `n + 1`; the exterior-algebra model is the special case where every generator has
degree one and only degree-two classes can be killed.

* `DeningerGCAStage` : a stage, with its differential and `d² = 0`.
* `DeningerGCAAttachment` : the data attached at a successor step.
* `DeningerGCAStage.succ`, `succ_d_inl`, `succ_kills` : the successor stage.
* `DeningerGCAStage.iterate` : the tower obtained by iterating a choice of attachment.
-/

namespace HTGeometry

section Stage

variable (k : Type*) [CommRing k]

/-- **A Sullivan stage on generators of mixed degree.** -/
structure DeningerGCAStage where
  /-- The generators of the stage. -/
  gen : Type*
  /-- The degree of each generator. -/
  deg : gen → ℕ
  /-- The values of the differential on the generators. -/
  phi : gen → DeningerFreeGCA k gen deg
  /-- The generator values graded-commute as elements of degree one more than their generator. -/
  hphi : ∀ x y : gen, deningerGCAι k deg x * phi y =
    ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x)
  /-- The generator values transform under the involution as elements of that degree. -/
  hinv : ∀ x : gen, deningerGCAInvolute k deg (phi x) = ((-1 : k) ^ (deg x + 1)) • phi x
  /-- The differential kills its own generator values. -/
  hkill : ∀ x : gen, deningerGCAOddDerivation phi hphi (phi x) = 0

variable {k}

namespace DeningerGCAStage

/-- The differential of a stage. -/
def d (S : DeningerGCAStage k) :
    DeningerFreeGCA k S.gen S.deg →ₗ[k] DeningerFreeGCA k S.gen S.deg :=
  deningerGCAOddDerivation S.phi S.hphi

@[simp]
theorem d_ι (S : DeningerGCAStage k) (x : S.gen) :
    S.d (deningerGCAι k S.deg x) = S.phi x :=
  deningerGCAOddDerivation_ι _ _ x

/-- **The differential of a stage squares to zero.** -/
theorem d_comp_self (S : DeningerGCAStage k) (z : DeningerFreeGCA k S.gen S.deg) :
    S.d (S.d z) = 0 :=
  deningerGCAOddDerivation_comp_self _ _ S.hinv S.hkill z

/-- **The graded Leibniz rule of a stage.** -/
theorem d_leibniz (S : DeningerGCAStage k) (z w : DeningerFreeGCA k S.gen S.deg) :
    S.d (z * w) =
      deningerGCAInvolute k S.deg z * S.d w + S.d z * w :=
  deningerGCAOddDerivation_leibniz _ _ z w

end DeningerGCAStage

/-- **The data attached at a successor step**: new generators of prescribed degrees, each mapping to
a cocycle of the stage which transforms as an element of one degree higher, together with the
admissibility of the resulting generator assignment. -/
structure DeningerGCAAttachment (S : DeningerGCAStage k) where
  /-- The new generators. -/
  newGen : Type*
  /-- The degree of each new generator. -/
  newDeg : newGen → ℕ
  /-- The class each new generator is attached to kill. -/
  psi : newGen → DeningerFreeGCA k S.gen S.deg
  /-- The attached classes transform as elements of one degree higher. -/
  hpsiInv : ∀ n : newGen, deningerGCAInvolute k S.deg (psi n) =
    ((-1 : k) ^ (newDeg n + 1)) • psi n
  /-- **The attached classes are cocycles.** -/
  hpsiKill : ∀ n : newGen, S.d (psi n) = 0
  /-- The successor generator assignment is admissible. -/
  hphi' : ∀ u v : S.gen ⊕ newGen,
    deningerGCAι k (deningerGCASuccDeg S.deg newDeg) u *
        deningerGCASuccPhi S.deg newDeg S.phi psi v =
      ((-1 : k) ^ (deningerGCASuccDeg S.deg newDeg u *
        (deningerGCASuccDeg S.deg newDeg v + 1))) •
        (deningerGCASuccPhi S.deg newDeg S.phi psi v *
          deningerGCAι k (deningerGCASuccDeg S.deg newDeg) u)

namespace DeningerGCAStage

/-- **The successor of a stage.** -/
def succ (S : DeningerGCAStage k) (A : DeningerGCAAttachment S) : DeningerGCAStage k where
  gen := S.gen ⊕ A.newGen
  deg := deningerGCASuccDeg S.deg A.newDeg
  phi := deningerGCASuccPhi S.deg A.newDeg S.phi A.psi
  hphi := A.hphi'
  hinv := deningerGCASuccPhi_involute S.deg A.newDeg S.phi A.psi S.hinv A.hpsiInv
  hkill := deningerGCASuccPhi_kill S.deg A.newDeg S.phi A.psi S.hphi A.hphi' S.hkill A.hpsiKill

@[simp]
theorem succ_gen (S : DeningerGCAStage k) (A : DeningerGCAAttachment S) :
    (S.succ A).gen = (S.gen ⊕ A.newGen) := rfl

@[simp]
theorem succ_deg (S : DeningerGCAStage k) (A : DeningerGCAAttachment S) :
    (S.succ A).deg = deningerGCASuccDeg S.deg A.newDeg := rfl

/-- **The successor differential extends the stage differential.** -/
theorem succ_d_inl (S : DeningerGCAStage k) (A : DeningerGCAAttachment S)
    (z : DeningerFreeGCA k S.gen S.deg) :
    (S.succ A).d (deningerGCAInl S.deg A.newDeg z) =
      deningerGCAInl S.deg A.newDeg (S.d z) :=
  deningerGCASuccDerivation_inl S.deg A.newDeg S.phi A.psi S.hphi A.hphi' z

/-- **Every attached class becomes a coboundary at the successor stage.** -/
theorem succ_kills (S : DeningerGCAStage k) (A : DeningerGCAAttachment S) (n : A.newGen) :
    (S.succ A).d
        (deningerGCAι k (deningerGCASuccDeg S.deg A.newDeg) (Sum.inr n)) =
      deningerGCAInl S.deg A.newDeg (A.psi n) :=
  deningerGCASuccDerivation_new S.deg A.newDeg S.phi A.psi A.hphi' n

/-- **The base stage**: generators of prescribed degrees with vanishing differential.  This is the
algebra `P` with `d_P = 0` from which a relative Sullivan tower starts. -/
def base (k : Type*) [CommRing k] (G : Type*) (deg : G → ℕ) : DeningerGCAStage k where
  gen := G
  deg := deg
  phi := 0
  hphi := by
    intro x y
    show deningerGCAι k deg x * 0 = _ • (0 * deningerGCAι k deg x)
    rw [mul_zero, zero_mul, smul_zero]
  hinv := by
    intro x
    show deningerGCAInvolute k deg 0 = _ • (0 : DeningerFreeGCA k G deg)
    rw [map_zero, smul_zero]
  hkill := by
    intro x
    show deningerGCAOddDerivation (0 : G → DeningerFreeGCA k G deg) _ 0 = 0
    exact map_zero _

@[simp]
theorem base_gen (k : Type*) [CommRing k] (G : Type*) (deg : G → ℕ) :
    (base k G deg).gen = G := rfl

@[simp]
theorem base_phi (k : Type*) [CommRing k] (G : Type*) (deg : G → ℕ) :
    (base k G deg).phi = 0 := rfl

/-- **The degree-one base stage**: every generator has degree one, so the underlying algebra is the
exterior algebra and the stage is the starting point `P = Λ(V)`, `d_P = 0` of the statement. -/
def baseDegreeOne (k : Type*) [CommRing k] (G : Type*) : DeningerGCAStage k :=
  base k G (fun _ => 1)

/-- In the degree-one base stage the generators anticommute, as in an exterior algebra. -/
theorem baseDegreeOne_anticomm (k : Type*) [CommRing k] (G : Type*) (x y : G) :
    deningerGCAι k (fun _ : G => 1) x * deningerGCAι k (fun _ : G => 1) y =
      -(deningerGCAι k (fun _ : G => 1) y * deningerGCAι k (fun _ : G => 1) x) :=
  deningerGCA_anticomm_degreeOne k (fun _ : G => 1) rfl rfl

/-- **The tower** obtained by iterating a choice of attachment at every stage. -/
def iterate (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ℕ → DeningerGCAStage k
  | 0 => S
  | n + 1 => (iterate choose S n).succ (choose (iterate choose S n))

@[simp]
theorem iterate_zero (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : iterate choose S 0 = S := rfl

@[simp]
theorem iterate_succ (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) :
    iterate choose S (n + 1) =
      (iterate choose S n).succ (choose (iterate choose S n)) := rfl

/-- The inclusion of a stage of the tower into the next. -/
def iterateInl (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) :
    DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg →ₐ[k]
      DeningerFreeGCA k (iterate choose S (n + 1)).gen (iterate choose S (n + 1)).deg :=
  deningerGCAInl (iterate choose S n).deg (choose (iterate choose S n)).newDeg

/-- **Each stage of the tower includes into the next, compatibly with the differentials.**  The
tower is therefore a chain of differential extensions, not merely a sequence of stages. -/
theorem iterate_d_inl (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    (iterate choose S (n + 1)).d (iterateInl choose S n z) =
      iterateInl choose S n ((iterate choose S n).d z) :=
  (iterate choose S n).succ_d_inl _ z

/-- The inclusion of a stage of the tower into any later stage. -/
def iterateInlAdd (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) : ∀ j : ℕ,
      DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg →ₐ[k]
        DeningerFreeGCA k (iterate choose S (n + j)).gen (iterate choose S (n + j)).deg
  | 0 => AlgHom.id k _
  | j + 1 => (iterateInl choose S (n + j)).comp (iterateInlAdd choose S n j)

/-- **The differential is compatible with every inclusion along the tower.**  A stage therefore
embeds as a differential subalgebra of every later stage, which is what a colimit of the tower
would be built from. -/
theorem iterate_d_inlAdd (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) : ∀ (j : ℕ)
      (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg),
      (iterate choose S (n + j)).d (iterateInlAdd choose S n j z) =
        iterateInlAdd choose S n j ((iterate choose S n).d z)
  | 0, _ => rfl
  | j + 1, z => by
    show (iterate choose S (n + j + 1)).d
        (iterateInl choose S (n + j) (iterateInlAdd choose S n j z)) =
      iterateInl choose S (n + j) (iterateInlAdd choose S n j ((iterate choose S n).d z))
    rw [iterate_d_inl, iterate_d_inlAdd choose S n j z]

/-- **Cocycles persist along the tower.** -/
theorem iterate_cocycle_inlAdd (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n j : ℕ)
    {z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg}
    (hz : (iterate choose S n).d z = 0) :
    (iterate choose S (n + j)).d (iterateInlAdd choose S n j z) = 0 := by
  rw [iterate_d_inlAdd, hz, map_zero]

/-- **Coboundaries persist along the tower.** -/
theorem iterate_coboundary_inlAdd (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n j : ℕ)
    {x y : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg}
    (hxy : (iterate choose S n).d y = x) :
    (iterate choose S (n + j)).d (iterateInlAdd choose S n j y) =
      iterateInlAdd choose S n j x := by
  rw [iterate_d_inlAdd, hxy]

/-- All generators attached anywhere along the tower. -/
def iterateNewGen (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : Type _ :=
  Σ n : ℕ, (choose (iterate choose S n)).newGen

/-- **The generator set of the limit stage**: the original generators together with every generator
attached along the tower. -/
def iterateOmegaGen (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : Type _ :=
  S.gen ⊕ iterateNewGen choose S

/-- The degrees of the limit generators. -/
def iterateOmegaDeg (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : iterateOmegaGen choose S → ℕ :=
  Sum.elim S.deg (fun p => (choose (iterate choose S p.1)).newDeg p.2)

/-- The inclusion of the generators of a stage into the limit generator set. -/
def iterateGenToOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ∀ n : ℕ,
      (iterate choose S n).gen → iterateOmegaGen choose S
  | 0 => Sum.inl
  | n + 1 => fun x =>
      Sum.elim (iterateGenToOmega choose S n) (fun m => Sum.inr ⟨n, m⟩) x

/-- **The limit generator set preserves degrees.**  A generator of a stage keeps its degree in the
limit, so the limit algebra extends every stage compatibly with the grading. -/
theorem iterateGenToOmega_deg (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ∀ (n : ℕ) (x : (iterate choose S n).gen),
      iterateOmegaDeg choose S (iterateGenToOmega choose S n x) = (iterate choose S n).deg x
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y => exact iterateGenToOmega_deg choose S n y
    | inr m => rfl

theorem iterateToOmega_comm (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) (x y : (iterate choose S n).gen) :
    deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x) *
        deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n y) =
      ((-1 : k) ^ ((iterate choose S n).deg x * (iterate choose S n).deg y)) •
        (deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n y) *
          deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x)) := by
  rw [deningerGCA_comm, iterateGenToOmega_deg, iterateGenToOmega_deg]

theorem iterateToOmega_sq (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) (x : (iterate choose S n).gen)
    (hx : Odd ((iterate choose S n).deg x)) :
    deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x) *
      deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x) = 0 := by
  refine deningerGCA_sq_zero k (iterateOmegaDeg choose S) ?_
  rw [iterateGenToOmega_deg]
  exact hx

/-- **The map from a stage into the limit algebra.**  Every stage of the tower maps to the algebra
on the limit generator set, compatibly with the Koszul relations because degrees are preserved. -/
def iterateToOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) :
    DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg →ₐ[k]
      DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S) :=
  deningerGCALift
    (fun x => deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x))
    (iterateToOmega_comm choose S n) (iterateToOmega_sq choose S n)

@[simp]
theorem iterateToOmega_ι (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) (x : (iterate choose S n).gen) :
    iterateToOmega choose S n (deningerGCAι k (iterate choose S n).deg x) =
      deningerGCAι k (iterateOmegaDeg choose S) (iterateGenToOmega choose S n x) :=
  deningerGCALift_ι _ _ _ x

/-- **The limit maps are compatible with the tower's inclusions.**  Including a stage into the next
and then into the limit is the same as mapping into the limit directly, so the maps form a cocone
under the tower. -/
theorem iterateToOmega_comp_inl (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    iterateToOmega choose S (n + 1) (iterateInl choose S n z) =
      iterateToOmega choose S n z := by
  have h : (iterateToOmega choose S (n + 1)).comp (iterateInl choose S n) =
      iterateToOmega choose S n := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, iterateToOmega_ι]
    exact deningerGCALift_comp_inl _ _ _ _ _ x
  exact AlgHom.congr_fun h z

/-- **Every class attached at a stage of the tower dies at the next stage.** -/
theorem iterate_kills (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) (m : (choose (iterate choose S n)).newGen) :
    (iterate choose S (n + 1)).d
        (deningerGCAι k
          (deningerGCASuccDeg (iterate choose S n).deg
            (choose (iterate choose S n)).newDeg) (Sum.inr m)) =
      deningerGCAInl (iterate choose S n).deg (choose (iterate choose S n)).newDeg
        ((choose (iterate choose S n)).psi m) :=
  (iterate choose S n).succ_kills _ m

end DeningerGCAStage

end Stage

section ExteriorComparison

open ExteriorAlgebra

variable (k : Type*) [CommRing k] {G V : Type*} [AddCommGroup V] [Module k V]

theorem deningerGCAToExterior_comm (g : G → V) (x y : G) :
    ι k (g x) * ι k (g y) =
      ((-1 : k) ^ ((fun _ : G => 1) x * (fun _ : G => 1) y)) • (ι k (g y) * ι k (g x)) := by
  have h : ι k (g x) * ι k (g y) = -(ι k (g y) * ι k (g x)) :=
    add_eq_zero_iff_eq_neg.mp (ExteriorAlgebra.ι_add_mul_swap (g x) (g y))
  rw [h]
  show -(ι k (g y) * ι k (g x)) = ((-1 : k) ^ (1 * 1)) • (ι k (g y) * ι k (g x))
  rw [mul_one, pow_one]
  exact (neg_one_smul k (ι k (g y) * ι k (g x))).symm

theorem deningerGCAToExterior_sq (g : G → V) (x : G) (_ : Odd ((fun _ : G => 1) x)) :
    ι k (g x) * ι k (g x) = 0 :=
  ExteriorAlgebra.ι_sq_zero (g x)

/-- **The comparison map from the degree-one free graded-commutative algebra to an exterior
algebra**, sending each generator to the chosen vector.  This exhibits the exterior model used for
the first layers as the degree-one case of the general algebra. -/
def deningerGCAToExterior (g : G → V) :
    DeningerFreeGCA k G (fun _ : G => 1) →ₐ[k] ExteriorAlgebra k V :=
  deningerGCALift (fun x => ι k (g x)) (deningerGCAToExterior_comm k g)
    (deningerGCAToExterior_sq k g)

@[simp]
theorem deningerGCAToExterior_ι (g : G → V) (x : G) :
    deningerGCAToExterior k g (deningerGCAι k (fun _ : G => 1) x) = ι k (g x) :=
  deningerGCALift_ι _ _ _ x

/-- **The comparison map intertwines the two grading involutions.**  Both negate degree-one
generators, so the identification of the two models is compatible with the sign rule the
differentials run on. -/
theorem deningerGCAToExterior_involute (g : G → V)
    (z : DeningerFreeGCA k G (fun _ : G => 1)) :
    deningerGCAToExterior k g (deningerGCAInvolute k (fun _ : G => 1) z) =
      deningerExteriorInvolute k V (deningerGCAToExterior k g z) := by
  have h : (deningerGCAToExterior k g).comp (deningerGCAInvolute k (fun _ : G => 1)) =
      (deningerExteriorInvolute k V).comp (deningerGCAToExterior k g) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply,
      deningerGCAInvolute_ι_degreeOne k (fun _ : G => 1) (x := x) rfl,
      map_neg, deningerGCAToExterior_ι, deningerExteriorInvolute_ι]
  exact AlgHom.congr_fun h z

/-- **The comparison map is surjective when the generators span.**  Every exterior generator is in
the range, and the generators generate the exterior algebra, so the exterior model is a quotient of
the degree-one free graded-commutative algebra. -/
theorem deningerGCAToExterior_surjective (g : G → V)
    (hspan : Submodule.span k (Set.range g) = ⊤) :
    Function.Surjective (deningerGCAToExterior k g) := by
  have hsub : ∀ v : V, ι k v ∈ (deningerGCAToExterior k g).range := by
    have hmem : Submodule.span k (Set.range g) ≤
        Submodule.comap (ι k : V →ₗ[k] ExteriorAlgebra k V)
          (Subalgebra.toSubmodule (deningerGCAToExterior k g).range) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨deningerGCAι k (fun _ : G => 1) x, deningerGCAToExterior_ι k g x⟩
    intro v
    exact hmem (by rw [hspan]; exact Submodule.mem_top)
  have htop : (deningerGCAToExterior k g).range = ⊤ := by
    rw [eq_top_iff, ← CliffordAlgebra.adjoin_range_ι, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact hsub v
  rw [← AlgHom.range_eq_top]
  exact htop

/-- The linear map sending each basis vector to the corresponding generator. -/
noncomputable def deningerExteriorToGCAMap (B : Module.Basis G k V) :
    V →ₗ[k] DeningerFreeGCA k G (fun _ : G => 1) :=
  B.constr k (deningerGCAι k (fun _ : G => 1))

@[simp]
theorem deningerExteriorToGCAMap_basis (B : Module.Basis G k V) (x : G) :
    deningerExteriorToGCAMap k B (B x) = deningerGCAι k (fun _ : G => 1) x :=
  B.constr_basis k _ x

/-- **Every vector squares to zero** under the basis map, which is what the exterior algebra's
universal property requires. -/
theorem deningerExteriorToGCAMap_sq (B : Module.Basis G k V) (v : V) :
    deningerExteriorToGCAMap k B v * deningerExteriorToGCAMap k B v = 0 := by
  rw [deningerExteriorToGCAMap, Module.Basis.constr_apply, Finsupp.sum]
  exact deningerAnticommSmulSum_sq_zero _ _ _
    (fun i => deningerGCA_sq_zero k (fun _ : G => 1) (x := i) odd_one)
    (fun i j => deningerGCA_anticomm_degreeOne k (fun _ : G => 1) rfl rfl)

/-- **The inverse comparison map**, from an exterior algebra on a based module to the degree-one
free graded-commutative algebra on the basis. -/
noncomputable def deningerExteriorToGCA (B : Module.Basis G k V) :
    ExteriorAlgebra k V →ₐ[k] DeningerFreeGCA k G (fun _ : G => 1) :=
  ExteriorAlgebra.lift k ⟨deningerExteriorToGCAMap k B, deningerExteriorToGCAMap_sq k B⟩

@[simp]
theorem deningerExteriorToGCA_ι (B : Module.Basis G k V) (v : V) :
    deningerExteriorToGCA k B (ι k v) = deningerExteriorToGCAMap k B v :=
  ExteriorAlgebra.lift_ι_apply k (deningerExteriorToGCAMap k B)
    (deningerExteriorToGCAMap_sq k B) v

/-- **One composite of the comparison is the identity.**  Sending a generator to its basis vector
and back returns the generator, so the degree-one free graded-commutative algebra is a retract of
the exterior algebra on the based module. -/
theorem deningerExteriorToGCA_comp_toExterior (B : Module.Basis G k V) :
    (deningerExteriorToGCA k B).comp (deningerGCAToExterior k (fun x => B x)) =
      AlgHom.id k (DeningerFreeGCA k G (fun _ : G => 1)) := by
  refine deningerGCA_hom_ext fun x => ?_
  rw [AlgHom.comp_apply, deningerGCAToExterior_ι, deningerExteriorToGCA_ι,
    deningerExteriorToGCAMap_basis, AlgHom.id_apply]

/-- The comparison map from the degree-one free graded-commutative algebra is injective. -/
theorem deningerGCAToExterior_injective (B : Module.Basis G k V) :
    Function.Injective (deningerGCAToExterior k (fun x => B x)) := by
  intro a b hab
  have h := AlgHom.congr_fun (deningerExteriorToGCA_comp_toExterior k B)
  have ha := h a
  have hb := h b
  rw [AlgHom.comp_apply] at ha hb
  rw [AlgHom.id_apply] at ha hb
  rw [← ha, ← hb, hab]

/-- **The other composite is the identity.**  Sending a vector to its coordinates and back returns
the vector, so with the previous composite the two models are isomorphic on a based module. -/
theorem deningerGCAToExterior_comp_exteriorToGCA (B : Module.Basis G k V) :
    (deningerGCAToExterior k (fun x => B x)).comp (deningerExteriorToGCA k B) =
      AlgHom.id k (ExteriorAlgebra k V) := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  show deningerGCAToExterior k (fun x => B x) (deningerExteriorToGCA k B (ι k v)) = ι k v
  rw [deningerExteriorToGCA_ι, deningerExteriorToGCAMap, Module.Basis.constr_apply, Finsupp.sum,
    map_sum]
  have hterm : ∀ i ∈ (B.repr v).support,
      deningerGCAToExterior k (fun x => B x)
          ((B.repr v i) • deningerGCAι k (fun _ : G => 1) i) =
        (B.repr v i) • ι k (B i) := by
    intro i _
    rw [map_smul, deningerGCAToExterior_ι]
  rw [Finset.sum_congr rfl hterm]
  have hsum : ∑ i ∈ (B.repr v).support, (B.repr v i) • ι k (B i) =
      ι k (∑ i ∈ (B.repr v).support, (B.repr v i) • B i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul (ι k) _ _).symm
  have hrepr : (∑ i ∈ (B.repr v).support, (B.repr v) i • B i) = v := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using B.linearCombination_repr v
  rw [hsum, hrepr]

/-- **The two models are isomorphic on a based module.**  The exterior algebra on a module with a
basis is the degree-one free graded-commutative algebra on that basis. -/
noncomputable def deningerGCAExteriorEquiv (B : Module.Basis G k V) :
    DeningerFreeGCA k G (fun _ : G => 1) ≃ₐ[k] ExteriorAlgebra k V :=
  AlgEquiv.ofAlgHom (deningerGCAToExterior k (fun x => B x)) (deningerExteriorToGCA k B)
    (deningerGCAToExterior_comp_exteriorToGCA k B)
    (deningerExteriorToGCA_comp_toExterior k B)

@[simp]
theorem deningerGCAExteriorEquiv_ι (B : Module.Basis G k V) (x : G) :
    deningerGCAExteriorEquiv k B (deningerGCAι k (fun _ : G => 1) x) = ι k (B x) :=
  deningerGCAToExterior_ι k (fun x => B x) x

end ExteriorComparison

end HTGeometry
