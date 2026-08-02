import GaloisForLFunctions.HTGeometry.FreeGradedCommutativeAlgebra

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

end HTGeometry
