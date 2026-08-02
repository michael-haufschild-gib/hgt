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

@[simp]
theorem d_algebraMap (S : DeningerGCAStage k) (r : k) :
    S.d (algebraMap k (DeningerFreeGCA k S.gen S.deg) r) = 0 :=
  deningerGCAOddDerivation_algebraMap _ _ r

/-- **The differential of a stage squares to zero.** -/
theorem d_comp_self (S : DeningerGCAStage k) (z : DeningerFreeGCA k S.gen S.deg) :
    S.d (S.d z) = 0 :=
  deningerGCAOddDerivation_comp_self _ _ S.hinv S.hkill z

/-- **The graded Leibniz rule of a stage.** -/
theorem d_leibniz (S : DeningerGCAStage k) (z w : DeningerFreeGCA k S.gen S.deg) :
    S.d (z * w) =
      deningerGCAInvolute k S.deg z * S.d w + S.d z * w :=
  deningerGCAOddDerivation_leibniz _ _ z w

/-- **A map of algebras matching on generators is a chain map.**  An algebra map intertwining the
grading involutions and carrying the generator values of one stage to the differentials of the
images of its generators commutes with the differentials everywhere; the twisted Leibniz rule
propagates the identity through products. -/
theorem d_map (S S' : DeningerGCAStage k)
    (F : DeningerFreeGCA k S.gen S.deg →ₐ[k] DeningerFreeGCA k S'.gen S'.deg)
    (hinv : ∀ z, F (deningerGCAInvolute k S.deg z) = deningerGCAInvolute k S'.deg (F z))
    (hgen : ∀ x : S.gen, F (S.phi x) = S'.d (F (deningerGCAι k S.deg x)))
    (z : DeningerFreeGCA k S.gen S.deg) : F (S.d z) = S'.d (F z) := by
  induction z using deningerGCA_induction with
  | algMap r => rw [S.d_algebraMap, map_zero, AlgHom.commutes, S'.d_algebraMap]
  | gen x =>
    rw [S.d_ι]
    exact hgen x
  | mul a b ha hb =>
    rw [S.d_leibniz, map_add, map_mul, map_mul, ha, hb, hinv, map_mul, S'.d_leibniz]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The differential of a stage raises weight by one** when its generator values are
homogeneous. -/
theorem d_homogeneous (S : DeningerGCAStage k)
    (hhom : ∀ x : S.gen, DeningerGCAHomogeneous k S.deg (S.deg x + 1) (S.phi x)) {n : ℕ}
    {z : DeningerFreeGCA k S.gen S.deg} (hz : DeningerGCAHomogeneous k S.deg n z) :
    DeningerGCAHomogeneous k S.deg (n + 1) (S.d z) :=
  deningerGCAHomogeneous_oddDerivation S.phi S.hphi hhom hz

/-- **The even part of a cocycle is a cocycle.** -/
theorem d_evenPart [Invertible (2 : k)] (S : DeningerGCAStage k)
    {z : DeningerFreeGCA k S.gen S.deg} (hz : S.d z = 0) :
    S.d (deningerGCAEvenPart k S.deg z) = 0 :=
  deningerGCAOddDerivation_evenPart S.phi S.hphi S.hinv hz

/-- **The odd part of a cocycle is a cocycle.** -/
theorem d_oddPart [Invertible (2 : k)] (S : DeningerGCAStage k)
    {z : DeningerFreeGCA k S.gen S.deg} (hz : S.d z = 0) :
    S.d (deningerGCAOddPart k S.deg z) = 0 :=
  deningerGCAOddDerivation_oddPart S.phi S.hphi S.hinv hz

/-- **A stage from its parity data alone.**  The admissibility hypothesis of a stage is a
consequence of the parity hypothesis, so a stage is determined by a generator assignment
transforming as an element of one degree higher together with the vanishing of its own
differential. -/
def ofInvolute {G : Type*} (deg : G → ℕ) (phi : G → DeningerFreeGCA k G deg)
    (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) = ((-1 : k) ^ (deg x + 1)) • phi x)
    (hkill : ∀ x : G,
      deningerGCAOddDerivation phi (deningerGCA_hphi_of_hinv deg phi hinv) (phi x) = 0) :
    DeningerGCAStage k where
  gen := G
  deg := deg
  phi := phi
  hphi := deningerGCA_hphi_of_hinv deg phi hinv
  hinv := hinv
  hkill := hkill

@[simp]
theorem ofInvolute_gen {G : Type*} (deg : G → ℕ) (phi : G → DeningerFreeGCA k G deg)
    (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) = ((-1 : k) ^ (deg x + 1)) • phi x)
    (hkill : ∀ x : G,
      deningerGCAOddDerivation phi (deningerGCA_hphi_of_hinv deg phi hinv) (phi x) = 0) :
    (ofInvolute deg phi hinv hkill).gen = G := rfl

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

namespace DeningerGCAAttachment

/-- **An attachment from its parity data alone.**  The admissibility of the successor generator
assignment is a consequence of the parities of the old and the attached classes, so attaching
generators requires only cocycles transforming as elements of one degree higher. -/
def of (S : DeningerGCAStage k) {N : Type*} (newDeg : N → ℕ)
    (psi : N → DeningerFreeGCA k S.gen S.deg)
    (hpsiInv : ∀ n : N, deningerGCAInvolute k S.deg (psi n) =
      ((-1 : k) ^ (newDeg n + 1)) • psi n)
    (hpsiKill : ∀ n : N, S.d (psi n) = 0) : DeningerGCAAttachment S where
  newGen := N
  newDeg := newDeg
  psi := psi
  hpsiInv := hpsiInv
  hpsiKill := hpsiKill
  hphi' := deningerGCA_hphi_of_hinv (deningerGCASuccDeg S.deg newDeg)
    (deningerGCASuccPhi S.deg newDeg S.phi psi)
    (deningerGCASuccPhi_involute S.deg newDeg S.phi psi S.hinv hpsiInv)

@[simp]
theorem of_newGen (S : DeningerGCAStage k) {N : Type*} (newDeg : N → ℕ)
    (psi : N → DeningerFreeGCA k S.gen S.deg)
    (hpsiInv : ∀ n : N, deningerGCAInvolute k S.deg (psi n) =
      ((-1 : k) ^ (newDeg n + 1)) • psi n)
    (hpsiKill : ∀ n : N, S.d (psi n) = 0) :
    (of S newDeg psi hpsiInv hpsiKill).newGen = N := rfl

@[simp]
theorem of_psi (S : DeningerGCAStage k) {N : Type*} (newDeg : N → ℕ)
    (psi : N → DeningerFreeGCA k S.gen S.deg)
    (hpsiInv : ∀ n : N, deningerGCAInvolute k S.deg (psi n) =
      ((-1 : k) ^ (newDeg n + 1)) • psi n)
    (hpsiKill : ∀ n : N, S.d (psi n) = 0) :
    (of S newDeg psi hpsiInv hpsiKill).psi = psi := rfl

end DeningerGCAAttachment

/-- **A class a stage can attach a generator to kill**: a cocycle transforming as an element of one
degree higher than the generator that will be attached to it. -/
structure DeningerGCACocycle (S : DeningerGCAStage k) where
  /-- The degree of the generator to be attached. -/
  degree : ℕ
  /-- The class to be killed. -/
  val : DeningerFreeGCA k S.gen S.deg
  /-- **The class is a cocycle.** -/
  hkill : S.d val = 0
  /-- The class transforms as an element of degree one more than the attached generator. -/
  hinv : deningerGCAInvolute k S.deg val = ((-1 : k) ^ (degree + 1)) • val

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

/-- **Every limit generator comes from a stage.** -/
theorem exists_iterateGenToOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u : iterateOmegaGen choose S) :
    ∃ (n : ℕ) (x : (iterate choose S n).gen), iterateGenToOmega choose S n x = u := by
  cases u with
  | inl x => exact ⟨0, x, rfl⟩
  | inr p => exact ⟨p.1 + 1, Sum.inr p.2, rfl⟩

/-- A generator of a stage is also a generator of every later stage, with the same image in the
limit. -/
theorem exists_iterateGenToOmega_ge (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) {n m : ℕ} (h : n ≤ m) (x : (iterate choose S n).gen) :
    ∃ y : (iterate choose S m).gen,
      iterateGenToOmega choose S m y = iterateGenToOmega choose S n x := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨x, rfl⟩
  | succ m _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨Sum.inl y, hy⟩

/-- **Any two limit generators already live at a common stage.** -/
theorem exists_common_stage (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u v : iterateOmegaGen choose S) :
    ∃ (m : ℕ) (x y : (iterate choose S m).gen),
      iterateGenToOmega choose S m x = u ∧ iterateGenToOmega choose S m y = v := by
  obtain ⟨a, x, hx⟩ := exists_iterateGenToOmega choose S u
  obtain ⟨b, y, hy⟩ := exists_iterateGenToOmega choose S v
  obtain ⟨x', hx'⟩ := exists_iterateGenToOmega_ge choose S (le_max_left a b) x
  obtain ⟨y', hy'⟩ := exists_iterateGenToOmega_ge choose S (le_max_right a b) y
  exact ⟨max a b, x', y', hx'.trans hx, hy'.trans hy⟩

/-- The limit maps are compatible with the inclusions into arbitrarily later stages. -/
theorem iterateToOmega_comp_inlAdd (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) : ∀ (j : ℕ)
      (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg),
      iterateToOmega choose S (n + j) (iterateInlAdd choose S n j z) =
        iterateToOmega choose S n z
  | 0, _ => rfl
  | j + 1, z => by
    have h : iterateToOmega choose S (n + j + 1)
        (iterateInl choose S (n + j) (iterateInlAdd choose S n j z)) =
        iterateToOmega choose S n z := by
      rw [iterateToOmega_comp_inl, iterateToOmega_comp_inlAdd choose S n j z]
    exact h

/-- **The limit maps intertwine the grading involutions.** -/
theorem iterateToOmega_involute (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    deningerGCAInvolute k (iterateOmegaDeg choose S) (iterateToOmega choose S n z) =
      iterateToOmega choose S n (deningerGCAInvolute k (iterate choose S n).deg z) := by
  have h : (deningerGCAInvolute k (iterateOmegaDeg choose S)).comp
        (iterateToOmega choose S n) =
      (iterateToOmega choose S n).comp (deningerGCAInvolute k (iterate choose S n).deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    simp only [AlgHom.comp_apply, iterateToOmega_ι, deningerGCAInvolute_ι, map_smul,
      iterateGenToOmega_deg]
  exact AlgHom.congr_fun h z

/-- **The generator assignment of the limit stage**: the original generators keep the differential
of the base stage, and every generator attached along the tower maps to the class it was attached
to kill, viewed in the limit. -/
noncomputable def iterateOmegaPhi (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : iterateOmegaGen choose S →
      DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S) :=
  Sum.elim (fun x => iterateToOmega choose S 0 (S.phi x))
    (fun p => iterateToOmega choose S p.1 ((choose (iterate choose S p.1)).psi p.2))

/-- **The limit generator assignment restricts to that of every stage.** -/
theorem iterateOmegaPhi_eq (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ∀ (n : ℕ) (x : (iterate choose S n).gen),
      iterateOmegaPhi choose S (iterateGenToOmega choose S n x) =
        iterateToOmega choose S n ((iterate choose S n).phi x)
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y =>
      refine (iterateOmegaPhi_eq choose S n y).trans ?_
      exact (iterateToOmega_comp_inl choose S n ((iterate choose S n).phi y)).symm
    | inr m =>
      exact (iterateToOmega_comp_inl choose S n ((choose (iterate choose S n)).psi m)).symm

/-- **The limit generator assignment is admissible.**  Any two limit generators live at a common
stage, where the stage's own admissibility applies. -/
theorem iterateOmegaPhi_hphi (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u v : iterateOmegaGen choose S) :
    deningerGCAι k (iterateOmegaDeg choose S) u * iterateOmegaPhi choose S v =
      ((-1 : k) ^ (iterateOmegaDeg choose S u * (iterateOmegaDeg choose S v + 1))) •
        (iterateOmegaPhi choose S v * deningerGCAι k (iterateOmegaDeg choose S) u) := by
  obtain ⟨m, x, y, rfl, rfl⟩ := exists_common_stage choose S u v
  have h := congrArg (iterateToOmega choose S m) ((iterate choose S m).hphi x y)
  simp only [map_mul, map_smul, iterateToOmega_ι] at h
  rw [iterateOmegaPhi_eq, iterateGenToOmega_deg, iterateGenToOmega_deg]
  exact h

/-- **The limit generator values transform as elements of one degree higher.** -/
theorem iterateOmegaPhi_hinv (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u : iterateOmegaGen choose S) :
    deningerGCAInvolute k (iterateOmegaDeg choose S) (iterateOmegaPhi choose S u) =
      ((-1 : k) ^ (iterateOmegaDeg choose S u + 1)) • iterateOmegaPhi choose S u := by
  obtain ⟨m, x, rfl⟩ := exists_iterateGenToOmega choose S u
  rw [iterateOmegaPhi_eq, iterateToOmega_involute, (iterate choose S m).hinv x, map_smul,
    iterateGenToOmega_deg]

/-- The odd derivation determined by the limit generator assignment. -/
noncomputable def iterateOmegaDerivation
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k) :
    DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S) →ₗ[k]
      DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S) :=
  deningerGCAOddDerivation (iterateOmegaPhi choose S) (iterateOmegaPhi_hphi choose S)

@[simp]
theorem iterateOmegaDerivation_ι (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u : iterateOmegaGen choose S) :
    iterateOmegaDerivation choose S (deningerGCAι k (iterateOmegaDeg choose S) u) =
      iterateOmegaPhi choose S u :=
  deningerGCAOddDerivation_ι _ _ u

theorem iterateOmegaDerivation_algebraMap
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (r : k) :
    iterateOmegaDerivation choose S
        (algebraMap k (DeningerFreeGCA k (iterateOmegaGen choose S)
          (iterateOmegaDeg choose S)) r) = 0 :=
  deningerGCAOddDerivation_algebraMap _ _ r

theorem iterateOmegaDerivation_leibniz
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (z w : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S)) :
    iterateOmegaDerivation choose S (z * w) =
      deningerGCAInvolute k (iterateOmegaDeg choose S) z * iterateOmegaDerivation choose S w +
        iterateOmegaDerivation choose S z * w :=
  deningerGCAOddDerivation_leibniz _ _ z w

/-- **The limit differential extends the differential of every stage.** -/
theorem iterateOmegaDerivation_toOmega
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    iterateOmegaDerivation choose S (iterateToOmega choose S n z) =
      iterateToOmega choose S n ((iterate choose S n).d z) := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes, iterateOmegaDerivation_algebraMap, d_algebraMap, map_zero]
  | gen x =>
    rw [iterateToOmega_ι, iterateOmegaDerivation_ι, iterateOmegaPhi_eq, d_ι]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, iterateOmegaDerivation_leibniz, ha, hb, iterateToOmega_involute,
      d_leibniz, map_add, map_mul, map_mul]

/-- **The limit differential kills its own generator values.** -/
theorem iterateOmegaPhi_hkill (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (u : iterateOmegaGen choose S) :
    iterateOmegaDerivation choose S (iterateOmegaPhi choose S u) = 0 := by
  obtain ⟨m, x, rfl⟩ := exists_iterateGenToOmega choose S u
  rw [iterateOmegaPhi_eq, iterateOmegaDerivation_toOmega]
  have h : (iterate choose S m).d ((iterate choose S m).phi x) = 0 :=
    (iterate choose S m).hkill x
  rw [h, map_zero]

/-- **The limit stage of the tower.**  Its generators are those of the base stage together with
every generator attached along the tower, and its differential restricts to the differential of
each stage. -/
noncomputable def iterateOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : DeningerGCAStage k where
  gen := iterateOmegaGen choose S
  deg := iterateOmegaDeg choose S
  phi := iterateOmegaPhi choose S
  hphi := iterateOmegaPhi_hphi choose S
  hinv := iterateOmegaPhi_hinv choose S
  hkill := iterateOmegaPhi_hkill choose S

@[simp]
theorem iterateOmega_gen (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : (iterateOmega choose S).gen = iterateOmegaGen choose S := rfl

@[simp]
theorem iterateOmega_deg (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : (iterateOmega choose S).deg = iterateOmegaDeg choose S := rfl

/-- **Every stage maps to the limit stage as a map of differential graded algebras.** -/
theorem iterateOmega_d_toOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    (iterateOmega choose S).d (iterateToOmega choose S n z) =
      iterateToOmega choose S n ((iterate choose S n).d z) :=
  iterateOmegaDerivation_toOmega choose S n z

/-- **Cocycles persist into the limit stage.** -/
theorem iterateOmega_cocycle (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    {z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg}
    (hz : (iterate choose S n).d z = 0) :
    (iterateOmega choose S).d (iterateToOmega choose S n z) = 0 := by
  rw [iterateOmega_d_toOmega, hz]
  exact map_zero _

/-- **Coboundaries persist into the limit stage.** -/
theorem iterateOmega_coboundary (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ)
    {z w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg}
    (hzw : (iterate choose S n).d w = z) :
    (iterateOmega choose S).d (iterateToOmega choose S n w) = iterateToOmega choose S n z := by
  rw [iterateOmega_d_toOmega, hzw]

/-- **Every class attached along the tower is a coboundary in the limit stage.** -/
theorem iterateOmega_kills (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) (m : (choose (iterate choose S n)).newGen) :
    (iterateOmega choose S).d
        (deningerGCAι k (iterateOmegaDeg choose S) (Sum.inr ⟨n, m⟩)) =
      iterateToOmega choose S n ((choose (iterate choose S n)).psi m) :=
  (iterateOmega choose S).d_ι _

/-- A generator of a stage is attached strictly before that stage. -/
theorem iterateGenToOmega_lt (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ∀ (n : ℕ) (x : (iterate choose S n).gen)
      (p : iterateNewGen choose S), iterateGenToOmega choose S n x = Sum.inr p → p.1 < n
  | 0, x, p, h => by
      have h' : (Sum.inl x : S.gen ⊕ iterateNewGen choose S) = Sum.inr p := h
      simp at h'
  | n + 1, x, p, h => by
      cases x with
      | inl y =>
        have hy : iterateGenToOmega choose S n y = Sum.inr p := h
        exact Nat.lt_succ_of_lt (iterateGenToOmega_lt choose S n y p hy)
      | inr m =>
        have hm : (Sum.inr ⟨n, m⟩ :
            S.gen ⊕ (j : ℕ) × (choose (iterate choose S j)).newGen) = Sum.inr p := h
        have hp : (⟨n, m⟩ : (j : ℕ) × (choose (iterate choose S j)).newGen) = p :=
          Sum.inr.inj hm
        rw [← hp]
        exact Nat.lt_succ_self n

/-- **Distinct generators of a stage stay distinct in the limit.** -/
theorem iterateGenToOmega_injective (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) : ∀ n : ℕ, Function.Injective (iterateGenToOmega choose S n)
  | 0 => fun x y h => by
      have h' : (Sum.inl x : S.gen ⊕ iterateNewGen choose S) = Sum.inl y := h
      simpa using h'
  | n + 1 => fun x y h => by
      cases x with
      | inl a =>
        cases y with
        | inl b =>
          have hab : iterateGenToOmega choose S n a = iterateGenToOmega choose S n b := h
          exact congrArg Sum.inl (iterateGenToOmega_injective choose S n hab)
        | inr b =>
          have hab : iterateGenToOmega choose S n a = Sum.inr ⟨n, b⟩ := h
          exact absurd (iterateGenToOmega_lt choose S n a _ hab) (lt_irrefl n)
      | inr a =>
        cases y with
        | inl b =>
          have hab : iterateGenToOmega choose S n b = Sum.inr ⟨n, a⟩ := h.symm
          exact absurd (iterateGenToOmega_lt choose S n b _ hab) (lt_irrefl n)
        | inr b =>
          have hab : (Sum.inr ⟨n, a⟩ :
              S.gen ⊕ (j : ℕ) × (choose (iterate choose S j)).newGen) = Sum.inr ⟨n, b⟩ := h
          have hb : a = b := by
            have hs : (⟨n, a⟩ : (j : ℕ) × (choose (iterate choose S j)).newGen) = ⟨n, b⟩ :=
              Sum.inr.inj hab
            simpa using hs
          exact congrArg Sum.inr hb

open Classical in
/-- The generator values of the retraction of the limit onto a stage: a generator of that stage is
kept and every other limit generator is sent to zero. -/
noncomputable def iterateOmegaRetractGen
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) : iterateOmegaGen choose S →
      DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg :=
  fun u => if h : ∃ x, iterateGenToOmega choose S n x = u then
    deningerGCAι k (iterate choose S n).deg h.choose else 0

theorem iterateOmegaRetractGen_eq_zero
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) {u : iterateOmegaGen choose S}
    (hu : ¬ ∃ x, iterateGenToOmega choose S n x = u) :
    iterateOmegaRetractGen choose S n u = 0 :=
  dif_neg hu

@[simp]
theorem iterateOmegaRetractGen_apply
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) (x : (iterate choose S n).gen) :
    iterateOmegaRetractGen choose S n (iterateGenToOmega choose S n x) =
      deningerGCAι k (iterate choose S n).deg x := by
  have h : ∃ y, iterateGenToOmega choose S n y = iterateGenToOmega choose S n x := ⟨x, rfl⟩
  have hval : iterateOmegaRetractGen choose S n (iterateGenToOmega choose S n x) =
      deningerGCAι k (iterate choose S n).deg h.choose := dif_pos h
  rw [hval, iterateGenToOmega_injective choose S n h.choose_spec]

theorem iterateOmegaRetractGen_comm
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) (u v : iterateOmegaGen choose S) :
    iterateOmegaRetractGen choose S n u * iterateOmegaRetractGen choose S n v =
      ((-1 : k) ^ (iterateOmegaDeg choose S u * iterateOmegaDeg choose S v)) •
        (iterateOmegaRetractGen choose S n v * iterateOmegaRetractGen choose S n u) := by
  by_cases hu : ∃ x, iterateGenToOmega choose S n x = u
  · by_cases hv : ∃ y, iterateGenToOmega choose S n y = v
    · obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hv
      rw [iterateOmegaRetractGen_apply, iterateOmegaRetractGen_apply, iterateGenToOmega_deg,
        iterateGenToOmega_deg, deningerGCA_comm]
    · rw [iterateOmegaRetractGen_eq_zero choose S n hv, mul_zero, zero_mul, smul_zero]
  · rw [iterateOmegaRetractGen_eq_zero choose S n hu, zero_mul, mul_zero, smul_zero]

theorem iterateOmegaRetractGen_sq
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) (u : iterateOmegaGen choose S) (hu : Odd (iterateOmegaDeg choose S u)) :
    iterateOmegaRetractGen choose S n u * iterateOmegaRetractGen choose S n u = 0 := by
  by_cases h : ∃ x, iterateGenToOmega choose S n x = u
  · obtain ⟨x, rfl⟩ := h
    rw [iterateOmegaRetractGen_apply]
    refine deningerGCA_sq_zero k (iterate choose S n).deg ?_
    rw [← iterateGenToOmega_deg choose S n x]
    exact hu
  · rw [iterateOmegaRetractGen_eq_zero choose S n h, mul_zero]

/-- **The retraction of the limit algebra onto a stage.** -/
noncomputable def iterateOmegaRetract
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) :
    DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S) →ₐ[k]
      DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg :=
  deningerGCALift (iterateOmegaRetractGen choose S n) (iterateOmegaRetractGen_comm choose S n)
    (iterateOmegaRetractGen_sq choose S n)

theorem iterateOmegaRetract_comp_toOmega
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    (n : ℕ) (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    iterateOmegaRetract choose S n (iterateToOmega choose S n z) = z := by
  have h : (iterateOmegaRetract choose S n).comp (iterateToOmega choose S n) =
      AlgHom.id k (DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, iterateToOmega_ι, AlgHom.id_apply]
    exact (deningerGCALift_ι _ _ _ _).trans (iterateOmegaRetractGen_apply choose S n x)
  exact AlgHom.congr_fun h z

/-- **Each stage embeds in the limit stage.**  The tower is therefore a genuine filtration of the
limit algebra, not merely a diagram mapping into it. -/
theorem iterateToOmega_injective (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) (n : ℕ) : Function.Injective (iterateToOmega choose S n) :=
  Function.LeftInverse.injective (iterateOmegaRetract_comp_toOmega choose S n)

/-- An element of a stage stays the same in the limit when pushed to a later stage. -/
theorem exists_iterateToOmega_ge (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k) {n m : ℕ} (h : n ≤ m)
    (z : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg) :
    ∃ w : DeningerFreeGCA k (iterate choose S m).gen (iterate choose S m).deg,
      iterateToOmega choose S m w = iterateToOmega choose S n z := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨z, rfl⟩
  | succ m _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨iterateInl choose S m w, (iterateToOmega_comp_inl choose S m w).trans hw⟩

/-- **The limit algebra is the union of the stages.**  Every element of the limit stage already
comes from a stage of the tower, so the limit is the filtered colimit of the tower. -/
theorem exists_iterateToOmega (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S)
    (S : DeningerGCAStage k)
    (z : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S)) :
    ∃ (n : ℕ) (w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg),
      iterateToOmega choose S n w = z := by
  induction z using deningerGCA_induction with
  | algMap r => exact ⟨0, algebraMap k _ r, AlgHom.commutes _ r⟩
  | gen u =>
    obtain ⟨n, x, rfl⟩ := exists_iterateGenToOmega choose S u
    exact ⟨n, deningerGCAι k (iterate choose S n).deg x, iterateToOmega_ι choose S n x⟩
  | mul a b ha hb =>
    obtain ⟨na, wa, hwa⟩ := ha
    obtain ⟨nb, wb, hwb⟩ := hb
    obtain ⟨wa', hwa'⟩ := exists_iterateToOmega_ge choose S (le_max_left na nb) wa
    obtain ⟨wb', hwb'⟩ := exists_iterateToOmega_ge choose S (le_max_right na nb) wb
    exact ⟨max na nb, wa' * wb', by rw [map_mul, hwa', hwb', hwa, hwb]⟩
  | add a b ha hb =>
    obtain ⟨na, wa, hwa⟩ := ha
    obtain ⟨nb, wb, hwb⟩ := hb
    obtain ⟨wa', hwa'⟩ := exists_iterateToOmega_ge choose S (le_max_left na nb) wa
    obtain ⟨wb', hwb'⟩ := exists_iterateToOmega_ge choose S (le_max_right na nb) wb
    exact ⟨max na nb, wa' + wb', by rw [map_add, hwa', hwb', hwa, hwb]⟩

/-- **A cocycle of the limit stage is the image of a cocycle of a stage.**  This is the first half
of the limit-stage comparison: the cohomology of the limit is generated by the cohomologies of the
stages. -/
theorem iterateOmega_cocycle_exists_stage
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    {z : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S)}
    (hz : (iterateOmega choose S).d z = 0) :
    ∃ (n : ℕ) (w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg),
      iterateToOmega choose S n w = z ∧ (iterate choose S n).d w = 0 := by
  obtain ⟨n, w, rfl⟩ := exists_iterateToOmega choose S z
  refine ⟨n, w, rfl, ?_⟩
  refine iterateToOmega_injective choose S n ?_
  rw [← iterateOmega_d_toOmega, hz]
  exact (map_zero _).symm

/-- **A class that becomes a coboundary in the limit already becomes one at a stage.**  This is the
second half of the limit-stage comparison: no cohomology class of a stage is killed by the passage
to the limit without being killed at a stage. -/
theorem iterateOmega_coboundary_exists_stage
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k)
    {n : ℕ} {w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg}
    {y : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S)}
    (hy : (iterateOmega choose S).d y = iterateToOmega choose S n w) :
    ∃ (m : ℕ) (v w' : DeningerFreeGCA k (iterate choose S m).gen (iterate choose S m).deg),
      n ≤ m ∧ (iterate choose S m).d v = w' ∧
        iterateToOmega choose S m w' = iterateToOmega choose S n w := by
  obtain ⟨a, v, rfl⟩ := exists_iterateToOmega choose S y
  obtain ⟨v', hv'⟩ := exists_iterateToOmega_ge choose S (le_max_right n a) v
  obtain ⟨w'', hw''⟩ := exists_iterateToOmega_ge choose S (le_max_left n a) w
  refine ⟨max n a, v', w'', le_max_left n a, ?_, hw''⟩
  refine iterateToOmega_injective choose S (max n a) ?_
  rw [← iterateOmega_d_toOmega, hv', hw'']
  exact hy

/-- **The limit-stage comparison.**  Cohomology of the limit stage of a tower is computed at the
stages: every cocycle of the limit comes from a cocycle of a stage, and a class of a stage that
becomes a coboundary in the limit becomes one at a later stage. -/
theorem iterateOmega_cohomology_computed_at_stages
    (choose : ∀ S : DeningerGCAStage k, DeningerGCAAttachment S) (S : DeningerGCAStage k) :
    (∀ z : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S),
        (iterateOmega choose S).d z = 0 →
        ∃ (n : ℕ) (w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg),
          iterateToOmega choose S n w = z ∧ (iterate choose S n).d w = 0) ∧
      (∀ (n : ℕ) (w : DeningerFreeGCA k (iterate choose S n).gen (iterate choose S n).deg)
          (y : DeningerFreeGCA k (iterateOmegaGen choose S) (iterateOmegaDeg choose S)),
          (iterateOmega choose S).d y = iterateToOmega choose S n w →
          ∃ (m : ℕ) (v w' : DeningerFreeGCA k (iterate choose S m).gen (iterate choose S m).deg),
            n ≤ m ∧ (iterate choose S m).d v = w' ∧
              iterateToOmega choose S m w' = iterateToOmega choose S n w) :=
  ⟨fun _ hz => iterateOmega_cocycle_exists_stage choose S hz,
    fun _ _ _ hy => iterateOmega_coboundary_exists_stage choose S hy⟩

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

section FullAttachment

universe u

variable {k : Type u} [CommRing k]

/-- **The attachment that kills every class a stage can kill**: one new generator for every
attachable cocycle, mapping to that cocycle. -/
def DeningerGCAStage.fullAttachment (S : DeningerGCAStage.{u, u} k) :
    DeningerGCAAttachment S :=
  DeningerGCAAttachment.of S (fun c : DeningerGCACocycle S => c.degree) (fun c => c.val)
    (fun c => c.hinv) (fun c => c.hkill)

/-- The choice of attachment that kills everything attachable, at every stage of the tower. -/
def deningerFullChoice (k : Type u) [CommRing k] :
    ∀ S : DeningerGCAStage.{u, u} k, DeningerGCAAttachment S :=
  fun S => S.fullAttachment

namespace DeningerGCAStage

/-- **Every attachable class of a stage is a coboundary at the next stage of the full tower.** -/
theorem fullChoice_kills (S : DeningerGCAStage.{u, u} k) (n : ℕ)
    (c : DeningerGCACocycle (iterate (deningerFullChoice k) S n)) :
    (iterate (deningerFullChoice k) S (n + 1)).d
        (deningerGCAι k (iterate (deningerFullChoice k) S (n + 1)).deg (Sum.inr c)) =
      iterateInl (deningerFullChoice k) S n c.val :=
  (iterate (deningerFullChoice k) S (n + 1)).d_ι _

/-- **The limit of the full tower is acyclic on classes of pure parity.**  If at every stage a
generator is attached to every attachable cocycle, then every cocycle of the limit that transforms
as an element of a definite degree is a coboundary.

This is the acyclicity that the successor attachments of a Sullivan factorization are designed to
produce, and it is obtained here with no transfinite induction: a cocycle of the limit already lives
at a stage, is attachable there, and is therefore killed one stage later. -/
theorem fullOmega_isCoboundary (S : DeningerGCAStage.{u, u} k) (p : ℕ)
    {z : DeningerFreeGCA k (iterateOmegaGen (deningerFullChoice k) S)
      (iterateOmegaDeg (deningerFullChoice k) S)}
    (hz : (iterateOmega (deningerFullChoice k) S).d z = 0)
    (hpar : deningerGCAInvolute k (iterateOmegaDeg (deningerFullChoice k) S) z =
      ((-1 : k) ^ (p + 1)) • z) :
    ∃ y, (iterateOmega (deningerFullChoice k) S).d y = z := by
  obtain ⟨n, w, rfl, hw⟩ := iterateOmega_cocycle_exists_stage (deningerFullChoice k) S hz
  have hinvw : deningerGCAInvolute k (iterate (deningerFullChoice k) S n).deg w =
      ((-1 : k) ^ (p + 1)) • w := by
    refine iterateToOmega_injective (deningerFullChoice k) S n ?_
    rw [← iterateToOmega_involute, hpar, map_smul]
  refine ⟨iterateToOmega (deningerFullChoice k) S (n + 1)
      (deningerGCAι k (iterate (deningerFullChoice k) S (n + 1)).deg
        (Sum.inr ⟨p, w, hw, hinvw⟩)), ?_⟩
  rw [iterateOmega_d_toOmega, fullChoice_kills, iterateToOmega_comp_inl]

/-- **A homogeneous cocycle of the limit of the full tower is a coboundary.**  Homogeneity supplies
the parity directly, so no invertibility of `2` is needed here. -/
theorem fullOmega_isCoboundary_of_homogeneous (S : DeningerGCAStage.{u, u} k) (n : ℕ)
    {z : DeningerFreeGCA k (iterateOmegaGen (deningerFullChoice k) S)
      (iterateOmegaDeg (deningerFullChoice k) S)}
    (hz : (iterateOmega (deningerFullChoice k) S).d z = 0)
    (hhom : DeningerGCAHomogeneous k (iterateOmegaDeg (deningerFullChoice k) S) (n + 1) z) :
    ∃ y, (iterateOmega (deningerFullChoice k) S).d y = z :=
  fullOmega_isCoboundary S n hz (deningerGCAHomogeneous_involute hhom)

/-- **The limit of the full tower is acyclic.**  With `2` invertible in the ground ring the grading
involution splits every element into an even and an odd part, each of pure parity and each a cocycle
when the element is; so the parity hypothesis disappears and the limit has no cohomology at all
beyond the scalars. -/
theorem fullOmega_isCoboundary' [Invertible (2 : k)] (S : DeningerGCAStage.{u, u} k)
    {z : DeningerFreeGCA k (iterateOmegaGen (deningerFullChoice k) S)
      (iterateOmegaDeg (deningerFullChoice k) S)}
    (hz : (iterateOmega (deningerFullChoice k) S).d z = 0) :
    ∃ y, (iterateOmega (deningerFullChoice k) S).d y = z := by
  obtain ⟨y₁, hy₁⟩ := fullOmega_isCoboundary S 1
    ((iterateOmega (deningerFullChoice k) S).d_evenPart hz) (deningerGCAEvenPart_parity z)
  obtain ⟨y₀, hy₀⟩ := fullOmega_isCoboundary S 0
    ((iterateOmega (deningerFullChoice k) S).d_oddPart hz) (deningerGCAOddPart_parity z)
  exact ⟨y₁ + y₀, by rw [map_add, hy₁, hy₀, deningerGCAEvenPart_add_oddPart]⟩

/-- **The limit of the full tower has no cohomology in any fixed parity.**  Stated as the two
halves together: a class of pure parity is a cocycle exactly when it is a coboundary. -/
theorem fullOmega_cocycle_iff_coboundary (S : DeningerGCAStage.{u, u} k) (p : ℕ)
    (z : DeningerFreeGCA k (iterateOmegaGen (deningerFullChoice k) S)
      (iterateOmegaDeg (deningerFullChoice k) S))
    (hpar : deningerGCAInvolute k (iterateOmegaDeg (deningerFullChoice k) S) z =
      ((-1 : k) ^ (p + 1)) • z) :
    (iterateOmega (deningerFullChoice k) S).d z = 0 ↔
      ∃ y, (iterateOmega (deningerFullChoice k) S).d y = z := by
  refine ⟨fun hz => fullOmega_isCoboundary S p hz hpar, ?_⟩
  rintro ⟨y, rfl⟩
  exact (iterateOmega (deningerFullChoice k) S).d_comp_self y

end DeningerGCAStage

end FullAttachment

end HTGeometry
