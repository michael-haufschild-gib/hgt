import GaloisForLFunctions.HTGeometry.GradedSullivanStage
import GaloisForLFunctions.HTGeometry.GradedSullivanTower

/-!
# Augmented Sullivan stages and the relative attachment

A relative Sullivan factorization does not attach generators to every class: it attaches them to
exactly the classes that die in the target.  The bookkeeping for that is an augmentation, a map from
the stage to the target algebra which annihilates the differential — that is, a map of differential
graded algebras when the target carries the zero differential.

An augmentation extends over an attachment by sending the new generators to zero, and the extension
is again an augmentation precisely because the attached classes were chosen in its kernel.  So an
augmented stage has a canonical successor, and iterating it gives the relative tower.

* `deningerGCA_augmentation_comp_d` : an augmentation annihilates the differential as soon as it
  does so on generators.
* `DeningerGCAStage.cocycles` : the cocycles of a stage form a subalgebra.
* `DeningerGCAAugStage` : a stage with an augmentation, and `DeningerGCAAugCocycle` the classes it
  must kill.
* `DeningerGCAAugStage.succ`, `succ_kills` : the relative attachment and what it kills.
-/

namespace HTGeometry

section ZeroDerivation

variable {k G : Type*} [CommRing k] {deg : G → ℕ}

/-- **An odd derivation with vanishing generator values is zero.** -/
theorem deningerGCAOddDerivation_eq_zero (phi : G → DeningerFreeGCA k G deg)
    (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
      ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))
    (h0 : ∀ x : G, phi x = 0) (z : DeningerFreeGCA k G deg) :
    deningerGCAOddDerivation phi hphi z = 0 := by
  induction z using deningerGCA_induction with
  | algMap r => exact deningerGCAOddDerivation_algebraMap _ _ r
  | gen x =>
    rw [deningerGCAOddDerivation_ι]
    exact h0 x
  | mul a b ha hb =>
    rw [deningerGCAOddDerivation_leibniz, ha, hb, mul_zero, zero_mul, add_zero]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

end ZeroDerivation

section Augmented

universe u w

variable {k : Type u} {K : Type w} [CommRing k] [Ring K] [Algebra k K]

/-- **An augmentation annihilates the differential as soon as it annihilates it on generators.**
The Leibniz rule propagates the vanishing through products, so being a map of differential graded
algebras into a target with zero differential is a condition on the generators alone. -/
theorem deningerGCA_augmentation_comp_d (S : DeningerGCAStage k)
    (eps : DeningerFreeGCA k S.gen S.deg →ₐ[k] K)
    (hgen : ∀ x : S.gen, eps (S.phi x) = 0) (z : DeningerFreeGCA k S.gen S.deg) :
    eps (S.d z) = 0 := by
  induction z using deningerGCA_induction with
  | algMap r => rw [S.d_algebraMap, map_zero]
  | gen x =>
    rw [S.d_ι]
    exact hgen x
  | mul a b ha hb =>
    rw [S.d_leibniz, map_add, map_mul, map_mul, ha, hb, mul_zero, zero_mul, add_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

namespace DeningerGCAStage

@[simp]
theorem d_one (S : DeningerGCAStage k) : S.d 1 = 0 := by
  have h := S.d_algebraMap 1
  rwa [map_one] at h

/-- **The cocycles of a stage form a subalgebra.**  This is the graded Leibniz rule: a product of
closed elements is closed, because both terms of the rule vanish. -/
def cocycles (S : DeningerGCAStage k) : Subalgebra k (DeningerFreeGCA k S.gen S.deg) where
  carrier := {z | S.d z = 0}
  mul_mem' {a b} ha hb := by
    show S.d (a * b) = 0
    rw [S.d_leibniz, show S.d b = 0 from hb, show S.d a = 0 from ha, mul_zero, zero_mul, add_zero]
  one_mem' := S.d_one
  add_mem' {a b} ha hb := by
    show S.d (a + b) = 0
    rw [map_add, show S.d a = 0 from ha, show S.d b = 0 from hb, add_zero]
  zero_mem' := map_zero _
  algebraMap_mem' r := S.d_algebraMap r

@[simp]
theorem mem_cocycles {S : DeningerGCAStage k} {z : DeningerFreeGCA k S.gen S.deg} :
    z ∈ S.cocycles ↔ S.d z = 0 := Iff.rfl

/-- **The base stage has no differential**, so every element of it is closed. -/
@[simp]
theorem base_d {G : Type*} (deg : G → ℕ) (z : DeningerFreeGCA k G deg) :
    (base k G deg).d z = 0 :=
  deningerGCAOddDerivation_eq_zero _ _ (fun _ => rfl) z

/-- **Every element of the base stage is a cocycle.** -/
theorem base_cocycles {G : Type*} (deg : G → ℕ) : (base k G deg).cocycles = ⊤ :=
  le_antisymm le_top fun z _ => base_d deg z

end DeningerGCAStage

/-- **An augmented stage**: a Sullivan stage together with a map to a target algebra annihilating
the differential on generators.  The target carries the zero differential, so an augmentation is a
map of differential graded algebras. -/
structure DeningerGCAAugStage (k : Type u) (K : Type w) [CommRing k] [Ring K] [Algebra k K] where
  /-- The underlying stage. -/
  toStage : DeningerGCAStage.{u, u} k
  /-- The augmentation to the target. -/
  eps : DeningerFreeGCA k toStage.gen toStage.deg →ₐ[k] K
  /-- The augmentation annihilates the differential on generators. -/
  heps : ∀ x : toStage.gen, eps (toStage.phi x) = 0

namespace DeningerGCAAugStage

variable (A : DeningerGCAAugStage k K)

/-- **The augmentation of an augmented stage is a map of differential graded algebras.** -/
theorem eps_d (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) : A.eps (A.toStage.d z) = 0 :=
  deningerGCA_augmentation_comp_d A.toStage A.eps A.heps z

/-- **The cocycles of an augmented stage that die in the target.**  These are exactly the classes a
relative Sullivan factorization has to kill. -/
structure Cocycle (A : DeningerGCAAugStage k K) where
  /-- The degree of the generator to be attached. -/
  degree : ℕ
  /-- The class to be killed. -/
  val : DeningerFreeGCA k A.toStage.gen A.toStage.deg
  /-- **The class is a cocycle.** -/
  hkill : A.toStage.d val = 0
  /-- The class transforms as an element of degree one more than the attached generator. -/
  hinv : deningerGCAInvolute k A.toStage.deg val = ((-1 : k) ^ (degree + 1)) • val
  /-- **The class dies in the target.** -/
  hzero : A.eps val = 0

/-- **The relative attachment**: one new generator for every class of the stage that dies in the
target. -/
def attachment : DeningerGCAAttachment A.toStage :=
  DeningerGCAAttachment.of A.toStage (fun c : Cocycle A => c.degree) (fun c => c.val)
    (fun c => c.hinv) (fun c => c.hkill)

/-- The values of the extended augmentation on the generators of the successor: the old generators
keep their value and every new generator dies. -/
def epsSuccGen : A.toStage.gen ⊕ Cocycle A → K :=
  Sum.elim (fun x => A.eps (deningerGCAι k A.toStage.deg x)) (fun _ => 0)

theorem epsSuccGen_comm (u v : A.toStage.gen ⊕ Cocycle A) :
    A.epsSuccGen u * A.epsSuccGen v =
      ((-1 : k) ^ (deningerGCASuccDeg A.toStage.deg (fun c : Cocycle A => c.degree) u *
          deningerGCASuccDeg A.toStage.deg (fun c : Cocycle A => c.degree) v)) •
        (A.epsSuccGen v * A.epsSuccGen u) := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      show A.eps (deningerGCAι k A.toStage.deg x) * A.eps (deningerGCAι k A.toStage.deg y) =
        ((-1 : k) ^ (A.toStage.deg x * A.toStage.deg y)) •
          (A.eps (deningerGCAι k A.toStage.deg y) * A.eps (deningerGCAι k A.toStage.deg x))
      rw [← map_mul, deningerGCA_comm, map_smul, map_mul]
    | inr c =>
      show A.eps (deningerGCAι k A.toStage.deg x) * 0 =
        _ • ((0 : K) * A.eps (deningerGCAι k A.toStage.deg x))
      rw [mul_zero, zero_mul, smul_zero]
  | inr c =>
    show (0 : K) * A.epsSuccGen v = _ • (A.epsSuccGen v * 0)
    rw [zero_mul, mul_zero, smul_zero]

theorem epsSuccGen_sq (u : A.toStage.gen ⊕ Cocycle A)
    (hu : Odd (deningerGCASuccDeg A.toStage.deg (fun c : Cocycle A => c.degree) u)) :
    A.epsSuccGen u * A.epsSuccGen u = 0 := by
  cases u with
  | inl x =>
    have hx : Odd (A.toStage.deg x) := hu
    show A.eps (deningerGCAι k A.toStage.deg x) * A.eps (deningerGCAι k A.toStage.deg x) = 0
    rw [← map_mul, deningerGCA_sq_zero k A.toStage.deg hx, map_zero]
  | inr c =>
    show (0 : K) * 0 = 0
    rw [mul_zero]

/-- **The extended augmentation** on the successor of an augmented stage. -/
def epsSucc :
    DeningerFreeGCA k (A.toStage.succ A.attachment).gen (A.toStage.succ A.attachment).deg →ₐ[k] K :=
  deningerGCALift A.epsSuccGen (A.epsSuccGen_comm) (A.epsSuccGen_sq)

@[simp]
theorem epsSucc_ι (u : A.toStage.gen ⊕ Cocycle A) :
    A.epsSucc (deningerGCAι k (A.toStage.succ A.attachment).deg u) = A.epsSuccGen u :=
  deningerGCALift_ι _ _ _ u

/-- **The extended augmentation restricts to the old one.** -/
theorem epsSucc_comp_inl (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) :
    A.epsSucc (deningerGCAInl A.toStage.deg A.attachment.newDeg z) = A.eps z := by
  have h : A.epsSucc.comp (deningerGCAInl A.toStage.deg A.attachment.newDeg) = A.eps := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply]
    exact deningerGCALift_comp_inl _ _ _ _ _ x
  exact AlgHom.congr_fun h z

/-- **The extended augmentation is again an augmentation.**  On old generators this is the previous
augmentation condition; on the new generators it is exactly the requirement that the attached
classes die in the target. -/
theorem epsSucc_heps (u : (A.toStage.succ A.attachment).gen) :
    A.epsSucc ((A.toStage.succ A.attachment).phi u) = 0 := by
  cases u with
  | inl x =>
    show A.epsSucc (deningerGCAInl A.toStage.deg A.attachment.newDeg (A.toStage.phi x)) = 0
    rw [epsSucc_comp_inl]
    exact A.heps x
  | inr c =>
    show A.epsSucc (deningerGCAInl A.toStage.deg A.attachment.newDeg c.val) = 0
    rw [epsSucc_comp_inl]
    exact c.hzero

/-- **The successor of an augmented stage.** -/
def succ : DeningerGCAAugStage k K where
  toStage := A.toStage.succ A.attachment
  eps := A.epsSucc
  heps := A.epsSucc_heps

@[simp]
theorem succ_toStage : A.succ.toStage = A.toStage.succ A.attachment := rfl

@[simp]
theorem succ_eps : A.succ.eps = A.epsSucc := rfl

/-- **Every class dying in the target is a coboundary at the next augmented stage.** -/
theorem succ_kills (c : Cocycle A) :
    A.succ.toStage.d (deningerGCAι k A.succ.toStage.deg (Sum.inr c)) =
      deningerGCAInl A.toStage.deg A.attachment.newDeg c.val :=
  A.toStage.succ_kills A.attachment c

/-- **The relative tower**: iterate the relative attachment. -/
def iterate (B : DeningerGCAAugStage k K) : ℕ → DeningerGCAAugStage k K
  | 0 => B
  | n + 1 => (iterate B n).succ

@[simp]
theorem iterate_zero (B : DeningerGCAAugStage k K) : iterate B 0 = B := rfl

@[simp]
theorem iterate_succ (B : DeningerGCAAugStage k K) (n : ℕ) :
    iterate B (n + 1) = (iterate B n).succ := rfl

/-- The inclusion of a stage of the relative tower into the next. -/
def iterateInl (B : DeningerGCAAugStage k K) (n : ℕ) :
    DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg →ₐ[k]
      DeningerFreeGCA k (iterate B (n + 1)).toStage.gen (iterate B (n + 1)).toStage.deg :=
  deningerGCAInl (iterate B n).toStage.deg (iterate B n).attachment.newDeg

/-- **The inclusions of the relative tower commute with the differentials.** -/
theorem iterate_d_inl (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    (iterate B (n + 1)).toStage.d (iterateInl B n z) =
      iterateInl B n ((iterate B n).toStage.d z) :=
  (iterate B n).toStage.succ_d_inl _ z

/-- **The augmentations of the relative tower are compatible with its inclusions.**  Every stage of
the tower maps to the target, and the maps agree along the tower, so the tower has a single
augmentation to the target. -/
theorem iterate_eps_comp_inl (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    (iterate B (n + 1)).eps (iterateInl B n z) = (iterate B n).eps z :=
  (iterate B n).epsSucc_comp_inl z

/-- **At every stage of the relative tower, every class dying in the target is killed one stage
later.**  This is step 2 of the relative factorization: the attachments are exactly those the proof
prescribes, and nothing else is attached. -/
theorem iterate_kills (B : DeningerGCAAugStage k K) (n : ℕ) (c : Cocycle (iterate B n)) :
    (iterate B (n + 1)).toStage.d
        (deningerGCAι k (iterate B (n + 1)).toStage.deg (Sum.inr c)) =
      iterateInl B n c.val :=
  (iterate B n).succ_kills c

/-- **The differential of the relative tower never leaves the kernel of the augmentation.**  Every
class the tower kills was required to die in the target, so no class outside the kernel is
destroyed. -/
theorem iterate_eps_d (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    (iterate B n).eps ((iterate B n).toStage.d z) = 0 :=
  (iterate B n).eps_d z

/-- **Surjectivity of the augmentation propagates along the relative tower.** -/
theorem iterate_eps_surjective (B : DeningerGCAAugStage k K) (hsurj : Function.Surjective B.eps) :
    ∀ n : ℕ, Function.Surjective (iterate B n).eps
  | 0 => hsurj
  | n + 1 => by
    intro y
    obtain ⟨z, hz⟩ := iterate_eps_surjective B hsurj n y
    exact ⟨iterateInl B n z, by rw [iterate_eps_comp_inl, hz]⟩

/-- **The cohomology comparison of the relative tower is surjective at every stage.**  If the base
has no differential and its augmentation is onto the target, then at every stage of the tower every
element of the target is the image of a cocycle: the tower only ever has to make the comparison
injective. -/
theorem iterate_eps_cocycle_surjective (B : DeningerGCAAugStage k K)
    (hd : ∀ z : DeningerFreeGCA k B.toStage.gen B.toStage.deg, B.toStage.d z = 0)
    (hsurj : Function.Surjective B.eps) :
    ∀ (n : ℕ) (y : K), ∃ z, (iterate B n).toStage.d z = 0 ∧ (iterate B n).eps z = y
  | 0, y => by
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨z, hd z, hz⟩
  | n + 1, y => by
    obtain ⟨z, hzd, hze⟩ := iterate_eps_cocycle_surjective B hd hsurj n y
    refine ⟨iterateInl B n z, ?_, ?_⟩
    · rw [iterate_d_inl, hzd, map_zero]
    · rw [iterate_eps_comp_inl, hze]

/-! ### The limit of the relative tower -/

/-- All the generators attached anywhere along the relative tower. -/
def omegaNewGen (B : DeningerGCAAugStage k K) : Type u :=
  Σ n : ℕ, Cocycle (iterate B n)

/-- **The generator set of the limit of the relative tower**: the generators of the base together
with every generator attached along the tower. -/
def omegaGen (B : DeningerGCAAugStage k K) : Type u :=
  B.toStage.gen ⊕ omegaNewGen B

/-- The degrees of the limit generators. -/
def omegaDeg (B : DeningerGCAAugStage k K) : omegaGen B → ℕ :=
  Sum.elim B.toStage.deg fun p => p.2.degree

/-- The inclusion of a stage's generators into the limit generator set. -/
def genToOmega (B : DeningerGCAAugStage k K) : ∀ n : ℕ,
    (iterate B n).toStage.gen → omegaGen B
  | 0 => Sum.inl
  | n + 1 => fun x => Sum.elim (genToOmega B n) (fun c => Sum.inr ⟨n, c⟩) x

/-- **The limit generator set preserves degrees.** -/
theorem genToOmega_deg (B : DeningerGCAAugStage k K) : ∀ (n : ℕ) (x : (iterate B n).toStage.gen),
    omegaDeg B (genToOmega B n x) = (iterate B n).toStage.deg x
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y => exact genToOmega_deg B n y
    | inr c => rfl

theorem toOmega_comm (B : DeningerGCAAugStage k K) (n : ℕ) (x y : (iterate B n).toStage.gen) :
    deningerGCAι k (omegaDeg B) (genToOmega B n x) *
        deningerGCAι k (omegaDeg B) (genToOmega B n y) =
      ((-1 : k) ^ ((iterate B n).toStage.deg x * (iterate B n).toStage.deg y)) •
        (deningerGCAι k (omegaDeg B) (genToOmega B n y) *
          deningerGCAι k (omegaDeg B) (genToOmega B n x)) := by
  rw [deningerGCA_comm, genToOmega_deg, genToOmega_deg]

theorem toOmega_sq (B : DeningerGCAAugStage k K) (n : ℕ) (x : (iterate B n).toStage.gen)
    (hx : Odd ((iterate B n).toStage.deg x)) :
    deningerGCAι k (omegaDeg B) (genToOmega B n x) *
      deningerGCAι k (omegaDeg B) (genToOmega B n x) = 0 := by
  refine deningerGCA_sq_zero k (omegaDeg B) ?_
  rw [genToOmega_deg]
  exact hx

/-- **The map from a stage of the relative tower into the limit algebra.** -/
def toOmega (B : DeningerGCAAugStage k K) (n : ℕ) :
    DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg →ₐ[k]
      DeningerFreeGCA k (omegaGen B) (omegaDeg B) :=
  deningerGCALift (fun x => deningerGCAι k (omegaDeg B) (genToOmega B n x))
    (toOmega_comm B n) (toOmega_sq B n)

@[simp]
theorem toOmega_ι (B : DeningerGCAAugStage k K) (n : ℕ) (x : (iterate B n).toStage.gen) :
    toOmega B n (deningerGCAι k (iterate B n).toStage.deg x) =
      deningerGCAι k (omegaDeg B) (genToOmega B n x) :=
  deningerGCALift_ι _ _ _ x

/-- **The limit maps form a cocone under the relative tower.** -/
theorem toOmega_comp_inl (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    toOmega B (n + 1) (iterateInl B n z) = toOmega B n z := by
  have h : (toOmega B (n + 1)).comp (iterateInl B n) = toOmega B n := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, toOmega_ι]
    exact deningerGCALift_comp_inl _ _ _ _ _ x
  exact AlgHom.congr_fun h z

/-- **The limit maps intertwine the grading involutions.** -/
theorem toOmega_involute (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    deningerGCAInvolute k (omegaDeg B) (toOmega B n z) =
      toOmega B n (deningerGCAInvolute k (iterate B n).toStage.deg z) := by
  have h : (deningerGCAInvolute k (omegaDeg B)).comp (toOmega B n) =
      (toOmega B n).comp (deningerGCAInvolute k (iterate B n).toStage.deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    simp only [AlgHom.comp_apply, toOmega_ι, deningerGCAInvolute_ι, map_smul, genToOmega_deg]
  exact AlgHom.congr_fun h z

/-- **Every limit generator comes from a stage.** -/
theorem exists_genToOmega (B : DeningerGCAAugStage k K) (u : omegaGen B) :
    ∃ (n : ℕ) (x : (iterate B n).toStage.gen), genToOmega B n x = u := by
  cases u with
  | inl x => exact ⟨0, x, rfl⟩
  | inr p => exact ⟨p.1 + 1, Sum.inr p.2, rfl⟩

theorem exists_genToOmega_ge (B : DeningerGCAAugStage k K) {n m : ℕ} (h : n ≤ m)
    (x : (iterate B n).toStage.gen) :
    ∃ y : (iterate B m).toStage.gen, genToOmega B m y = genToOmega B n x := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨x, rfl⟩
  | succ m _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨Sum.inl y, hy⟩

/-- **Any two limit generators already live at a common stage.** -/
theorem exists_common_stage (B : DeningerGCAAugStage k K) (u v : omegaGen B) :
    ∃ (m : ℕ) (x y : (iterate B m).toStage.gen),
      genToOmega B m x = u ∧ genToOmega B m y = v := by
  obtain ⟨a, x, hx⟩ := exists_genToOmega B u
  obtain ⟨b, y, hy⟩ := exists_genToOmega B v
  obtain ⟨x', hx'⟩ := exists_genToOmega_ge B (le_max_left a b) x
  obtain ⟨y', hy'⟩ := exists_genToOmega_ge B (le_max_right a b) y
  exact ⟨max a b, x', y', hx'.trans hx, hy'.trans hy⟩

/-- **The generator assignment of the limit of the relative tower.** -/
def omegaPhi (B : DeningerGCAAugStage k K) :
    omegaGen B → DeningerFreeGCA k (omegaGen B) (omegaDeg B) :=
  Sum.elim (fun x => toOmega B 0 (B.toStage.phi x)) fun p => toOmega B p.1 p.2.val

/-- **The limit generator assignment restricts to that of every stage.** -/
theorem omegaPhi_eq (B : DeningerGCAAugStage k K) : ∀ (n : ℕ) (x : (iterate B n).toStage.gen),
    omegaPhi B (genToOmega B n x) = toOmega B n ((iterate B n).toStage.phi x)
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y =>
      refine (omegaPhi_eq B n y).trans ?_
      exact (toOmega_comp_inl B n ((iterate B n).toStage.phi y)).symm
    | inr c => exact (toOmega_comp_inl B n c.val).symm

theorem omegaPhi_hphi (B : DeningerGCAAugStage k K) (u v : omegaGen B) :
    deningerGCAι k (omegaDeg B) u * omegaPhi B v =
      ((-1 : k) ^ (omegaDeg B u * (omegaDeg B v + 1))) •
        (omegaPhi B v * deningerGCAι k (omegaDeg B) u) := by
  obtain ⟨m, x, y, rfl, rfl⟩ := exists_common_stage B u v
  have h := congrArg (toOmega B m) ((iterate B m).toStage.hphi x y)
  simp only [map_mul, map_smul, toOmega_ι] at h
  rw [omegaPhi_eq, genToOmega_deg, genToOmega_deg]
  exact h

theorem omegaPhi_hinv (B : DeningerGCAAugStage k K) (u : omegaGen B) :
    deningerGCAInvolute k (omegaDeg B) (omegaPhi B u) =
      ((-1 : k) ^ (omegaDeg B u + 1)) • omegaPhi B u := by
  obtain ⟨m, x, rfl⟩ := exists_genToOmega B u
  rw [omegaPhi_eq, toOmega_involute, (iterate B m).toStage.hinv x, map_smul, genToOmega_deg]

/-- The differential of the limit of the relative tower. -/
noncomputable def omegaDerivation (B : DeningerGCAAugStage k K) :
    DeningerFreeGCA k (omegaGen B) (omegaDeg B) →ₗ[k]
      DeningerFreeGCA k (omegaGen B) (omegaDeg B) :=
  deningerGCAOddDerivation (omegaPhi B) (omegaPhi_hphi B)

@[simp]
theorem omegaDerivation_ι (B : DeningerGCAAugStage k K) (u : omegaGen B) :
    omegaDerivation B (deningerGCAι k (omegaDeg B) u) = omegaPhi B u :=
  deningerGCAOddDerivation_ι _ _ u

theorem omegaDerivation_algebraMap (B : DeningerGCAAugStage k K) (r : k) :
    omegaDerivation B (algebraMap k (DeningerFreeGCA k (omegaGen B) (omegaDeg B)) r) = 0 :=
  deningerGCAOddDerivation_algebraMap _ _ r

theorem omegaDerivation_leibniz (B : DeningerGCAAugStage k K)
    (z w : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    omegaDerivation B (z * w) =
      deningerGCAInvolute k (omegaDeg B) z * omegaDerivation B w + omegaDerivation B z * w :=
  deningerGCAOddDerivation_leibniz _ _ z w

/-- **The limit differential extends the differential of every stage.** -/
theorem omegaDerivation_toOmega (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    omegaDerivation B (toOmega B n z) = toOmega B n ((iterate B n).toStage.d z) := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes, omegaDerivation_algebraMap, DeningerGCAStage.d_algebraMap, map_zero]
  | gen x => rw [toOmega_ι, omegaDerivation_ι, omegaPhi_eq, DeningerGCAStage.d_ι]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, omegaDerivation_leibniz, ha, hb, toOmega_involute,
      DeningerGCAStage.d_leibniz, map_add, map_mul, map_mul]

theorem omegaPhi_hkill (B : DeningerGCAAugStage k K) (u : omegaGen B) :
    omegaDerivation B (omegaPhi B u) = 0 := by
  obtain ⟨m, x, rfl⟩ := exists_genToOmega B u
  rw [omegaPhi_eq, omegaDerivation_toOmega]
  have h : (iterate B m).toStage.d ((iterate B m).toStage.phi x) = 0 :=
    (iterate B m).toStage.hkill x
  rw [h, map_zero]

/-- **The limit stage of the relative tower.** -/
noncomputable def omega (B : DeningerGCAAugStage k K) : DeningerGCAStage k where
  gen := omegaGen B
  deg := omegaDeg B
  phi := omegaPhi B
  hphi := omegaPhi_hphi B
  hinv := omegaPhi_hinv B
  hkill := omegaPhi_hkill B

@[simp]
theorem omega_deg (B : DeningerGCAAugStage k K) : (omega B).deg = omegaDeg B := rfl

/-- **Every stage of the relative tower maps to the limit as a map of differential graded
algebras.** -/
theorem omega_d_toOmega (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    (omega B).d (toOmega B n z) = toOmega B n ((iterate B n).toStage.d z) :=
  omegaDerivation_toOmega B n z

/-! ### The limit of the relative tower is a filtration -/

theorem genToOmega_lt (B : DeningerGCAAugStage k K) : ∀ (n : ℕ) (x : (iterate B n).toStage.gen)
    (p : omegaNewGen B), genToOmega B n x = Sum.inr p → p.1 < n
  | 0, x, p, h => by
      have h' : (Sum.inl x : B.toStage.gen ⊕ omegaNewGen B) = Sum.inr p := h
      simp at h'
  | n + 1, x, p, h => by
      cases x with
      | inl y =>
        have hy : genToOmega B n y = Sum.inr p := h
        exact Nat.lt_succ_of_lt (genToOmega_lt B n y p hy)
      | inr c =>
        have hm : (Sum.inr ⟨n, c⟩ :
            B.toStage.gen ⊕ (j : ℕ) × Cocycle (iterate B j)) = Sum.inr p := h
        have hp : (⟨n, c⟩ : (j : ℕ) × Cocycle (iterate B j)) = p := Sum.inr.inj hm
        rw [← hp]
        exact Nat.lt_succ_self n

/-- **Distinct generators of a stage stay distinct in the limit.** -/
theorem genToOmega_injective (B : DeningerGCAAugStage k K) :
    ∀ n : ℕ, Function.Injective (genToOmega B n)
  | 0 => fun x y h => by
      have h' : (Sum.inl x : B.toStage.gen ⊕ omegaNewGen B) = Sum.inl y := h
      simpa using h'
  | n + 1 => fun x y h => by
      cases x with
      | inl a =>
        cases y with
        | inl b =>
          have hab : genToOmega B n a = genToOmega B n b := h
          exact congrArg Sum.inl (genToOmega_injective B n hab)
        | inr b =>
          have hab : genToOmega B n a = Sum.inr ⟨n, b⟩ := h
          exact absurd (genToOmega_lt B n a _ hab) (lt_irrefl n)
      | inr a =>
        cases y with
        | inl b =>
          have hab : genToOmega B n b = Sum.inr ⟨n, a⟩ := h.symm
          exact absurd (genToOmega_lt B n b _ hab) (lt_irrefl n)
        | inr b =>
          have hab : (Sum.inr ⟨n, a⟩ :
              B.toStage.gen ⊕ (j : ℕ) × Cocycle (iterate B j)) = Sum.inr ⟨n, b⟩ := h
          have hs : (⟨n, a⟩ : (j : ℕ) × Cocycle (iterate B j)) = ⟨n, b⟩ := Sum.inr.inj hab
          have hb : a = b := by
            simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hs
            exact hs
          exact congrArg Sum.inr hb

open Classical in
/-- The generator values of the retraction of the limit onto a stage. -/
noncomputable def retractGen (B : DeningerGCAAugStage k K) (n : ℕ) :
    omegaGen B → DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg :=
  fun u => if h : ∃ x, genToOmega B n x = u then
    deningerGCAι k (iterate B n).toStage.deg h.choose else 0

theorem retractGen_eq_zero (B : DeningerGCAAugStage k K) (n : ℕ) {u : omegaGen B}
    (hu : ¬ ∃ x, genToOmega B n x = u) : retractGen B n u = 0 :=
  dif_neg hu

@[simp]
theorem retractGen_apply (B : DeningerGCAAugStage k K) (n : ℕ) (x : (iterate B n).toStage.gen) :
    retractGen B n (genToOmega B n x) = deningerGCAι k (iterate B n).toStage.deg x := by
  have h : ∃ y, genToOmega B n y = genToOmega B n x := ⟨x, rfl⟩
  have hval : retractGen B n (genToOmega B n x) =
      deningerGCAι k (iterate B n).toStage.deg h.choose := dif_pos h
  rw [hval, genToOmega_injective B n h.choose_spec]

theorem retractGen_comm (B : DeningerGCAAugStage k K) (n : ℕ) (u v : omegaGen B) :
    retractGen B n u * retractGen B n v =
      ((-1 : k) ^ (omegaDeg B u * omegaDeg B v)) • (retractGen B n v * retractGen B n u) := by
  by_cases hu : ∃ x, genToOmega B n x = u
  · by_cases hv : ∃ y, genToOmega B n y = v
    · obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hv
      rw [retractGen_apply, retractGen_apply, genToOmega_deg, genToOmega_deg, deningerGCA_comm]
    · rw [retractGen_eq_zero B n hv, mul_zero, zero_mul, smul_zero]
  · rw [retractGen_eq_zero B n hu, zero_mul, mul_zero, smul_zero]

theorem retractGen_sq (B : DeningerGCAAugStage k K) (n : ℕ) (u : omegaGen B)
    (hu : Odd (omegaDeg B u)) : retractGen B n u * retractGen B n u = 0 := by
  by_cases h : ∃ x, genToOmega B n x = u
  · obtain ⟨x, rfl⟩ := h
    rw [retractGen_apply]
    refine deningerGCA_sq_zero k (iterate B n).toStage.deg ?_
    rw [← genToOmega_deg B n x]
    exact hu
  · rw [retractGen_eq_zero B n h, mul_zero]

/-- **The retraction of the limit algebra onto a stage.** -/
noncomputable def retract (B : DeningerGCAAugStage k K) (n : ℕ) :
    DeningerFreeGCA k (omegaGen B) (omegaDeg B) →ₐ[k]
      DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg :=
  deningerGCALift (retractGen B n) (retractGen_comm B n) (retractGen_sq B n)

theorem retract_comp_toOmega (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    retract B n (toOmega B n z) = z := by
  have h : (retract B n).comp (toOmega B n) =
      AlgHom.id k (DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, toOmega_ι, AlgHom.id_apply]
    exact (deningerGCALift_ι _ _ _ _).trans (retractGen_apply B n x)
  exact AlgHom.congr_fun h z

/-- **Each stage of the relative tower embeds in its limit.** -/
theorem toOmega_injective (B : DeningerGCAAugStage k K) (n : ℕ) :
    Function.Injective (toOmega B n) :=
  Function.LeftInverse.injective (retract_comp_toOmega B n)

theorem exists_toOmega_ge (B : DeningerGCAAugStage k K) {n m : ℕ} (h : n ≤ m)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    ∃ w : DeningerFreeGCA k (iterate B m).toStage.gen (iterate B m).toStage.deg,
      toOmega B m w = toOmega B n z := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨z, rfl⟩
  | succ m _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨iterateInl B m w, (toOmega_comp_inl B m w).trans hw⟩

/-- **The limit of the relative tower is the union of its stages.** -/
theorem exists_toOmega (B : DeningerGCAAugStage k K)
    (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    ∃ (n : ℕ) (w : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg),
      toOmega B n w = z := by
  induction z using deningerGCA_induction with
  | algMap r => exact ⟨0, algebraMap k _ r, AlgHom.commutes _ r⟩
  | gen u =>
    obtain ⟨n, x, rfl⟩ := exists_genToOmega B u
    exact ⟨n, deningerGCAι k (iterate B n).toStage.deg x, toOmega_ι B n x⟩
  | mul a b ha hb =>
    obtain ⟨na, wa, hwa⟩ := ha
    obtain ⟨nb, wb, hwb⟩ := hb
    obtain ⟨wa', hwa'⟩ := exists_toOmega_ge B (le_max_left na nb) wa
    obtain ⟨wb', hwb'⟩ := exists_toOmega_ge B (le_max_right na nb) wb
    exact ⟨max na nb, wa' * wb', by rw [map_mul, hwa', hwb', hwa, hwb]⟩
  | add a b ha hb =>
    obtain ⟨na, wa, hwa⟩ := ha
    obtain ⟨nb, wb, hwb⟩ := hb
    obtain ⟨wa', hwa'⟩ := exists_toOmega_ge B (le_max_left na nb) wa
    obtain ⟨wb', hwb'⟩ := exists_toOmega_ge B (le_max_right na nb) wb
    exact ⟨max na nb, wa' + wb', by rw [map_add, hwa', hwb', hwa, hwb]⟩

/-- **A cocycle of the limit is the image of a cocycle of a stage.** -/
theorem omega_cocycle_exists_stage (B : DeningerGCAAugStage k K)
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0) :
    ∃ (n : ℕ) (w : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg),
      toOmega B n w = z ∧ (iterate B n).toStage.d w = 0 := by
  obtain ⟨n, w, rfl⟩ := exists_toOmega B z
  refine ⟨n, w, rfl, ?_⟩
  refine toOmega_injective B n ?_
  rw [← omega_d_toOmega, hz]
  exact (map_zero _).symm

/-- **The maps from the stages preserve homogeneity and its weight.** -/
theorem toOmega_homogeneous (B : DeningerGCAAugStage k K) (n : ℕ) {w : ℕ}
    {z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg}
    (hz : DeningerGCAHomogeneous k (iterate B n).toStage.deg w z) :
    DeningerGCAHomogeneous k (omegaDeg B) w (toOmega B n z) :=
  deningerGCAGenAlg_homogeneous (omegaDeg B) (genToOmega B n) (genToOmega_deg B n) hz

/-- **The tower's generator values are homogeneous** as soon as the base has no differential and
every attached class is homogeneous of one weight more than the generator attached to it.  This is
the hypothesis the degreewise cohomology comparison asks of the tower, reduced to a condition on the
attached classes. -/
theorem omegaPhi_homogeneous (B : DeningerGCAAugStage k K)
    (hbase : ∀ x : B.toStage.gen, B.toStage.phi x = 0)
    (hatt : ∀ (n : ℕ) (c : Cocycle (iterate B n)),
      DeningerGCAHomogeneous k (iterate B n).toStage.deg (c.degree + 1) c.val)
    (u : omegaGen B) :
    DeningerGCAHomogeneous k (omegaDeg B) (omegaDeg B u + 1) (omegaPhi B u) := by
  cases u with
  | inl x =>
    show DeningerGCAHomogeneous k (omegaDeg B) _ (toOmega B 0 (B.toStage.phi x))
    have h0 : toOmega B 0 (B.toStage.phi x) = 0 := by
      rw [hbase x]
      exact map_zero _
    rw [h0]
    exact deningerGCAHomogeneous_zero _
  | inr p =>
    show DeningerGCAHomogeneous k (omegaDeg B) (p.2.degree + 1) (toOmega B p.1 p.2.val)
    exact toOmega_homogeneous B p.1 (hatt p.1 p.2)

/-! ### The relative tower as a filtered Sullivan tower -/

/-- The level of a limit generator: the generators of the base sit at level `0`, and a generator
attached at step `n` sits at level `n + 1`. -/
def omegaLvl (B : DeningerGCAAugStage k K) : omegaGen B → ℕ :=
  Sum.elim (fun _ => 0) fun p => p.1 + 1

/-- **A generator of a stage has level at most that stage.** -/
theorem genToOmega_lvl_le (B : DeningerGCAAugStage k K) :
    ∀ (n : ℕ) (x : (iterate B n).toStage.gen), omegaLvl B (genToOmega B n x) ≤ n
  | 0, _ => le_rfl
  | n + 1, x => by
    cases x with
    | inl y => exact le_trans (genToOmega_lvl_le B n y) (Nat.le_succ n)
    | inr c => exact le_rfl

/-- **The image of a stage lies in the subalgebra generated by that stage's generators.** -/
theorem toOmega_mem_subalgebra (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    toOmega B n z ∈ deningerGCASubalgebra k (omegaDeg B) (Set.range (genToOmega B n)) := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | gen x =>
    rw [toOmega_ι]
    exact deningerGCASubalgebra_ι ⟨x, rfl⟩
  | mul a b ha hb =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb =>
    rw [map_add]
    exact Subalgebra.add_mem _ ha hb

/-- **The relative tower as a relative Sullivan tower indexed by the natural numbers.**  Its
generators are those of the limit, its base is the generator set of the starting algebra, and each
attached generator carries the step at which it was attached as its level.  Lower triangularity is
the statement that a generator attached at step `n` kills a class built from the generators
available before step `n`.

This is clauses 1 and 2 of the statement for the relative tower: the new generators carry a
well-ordered filtration, and the differential of a new generator lies in the subalgebra generated by
the base together with the strictly earlier stages. -/
noncomputable def augTower (B : DeningerGCAAugStage k K) : DeningerGCATower k ℕ where
  gen := omegaGen B
  deg := omegaDeg B
  lvl := omegaLvl B
  base := Set.range (Sum.inl : B.toStage.gen → omegaGen B)
  phi := omegaPhi B
  hphi := omegaPhi_hphi B
  hinv := omegaPhi_hinv B
  hkill := omegaPhi_hkill B
  base_lower := by
    rintro u ⟨x, rfl⟩
    exact toOmega_mem_subalgebra B 0 (B.toStage.phi x)
  lower := by
    rintro u hu
    cases u with
    | inl x => exact absurd ⟨x, rfl⟩ hu
    | inr p =>
      refine deningerGCASubalgebra_mono ?_ (toOmega_mem_subalgebra B p.1 p.2.val)
      rintro _ ⟨x, rfl⟩
      exact Or.inr (Nat.lt_succ_of_le (genToOmega_lvl_le B p.1 x))

@[simp]
theorem augTower_gen (B : DeningerGCAAugStage k K) : (augTower B).gen = omegaGen B := rfl

@[simp]
theorem augTower_deg (B : DeningerGCAAugStage k K) : (augTower B).deg = omegaDeg B := rfl

/-- **The filtered tower carries the differential of the limit stage.**  The two presentations of
the limit — as the union of the successor attachments, and as a single generator set with a level
function — are the same differential graded algebra. -/
theorem augTower_d (B : DeningerGCAAugStage k K)
    (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    (augTower B).d z = (omega B).d z := rfl

/-- **Clause 2 for the relative tower**, verbatim: the differential of an attached generator lies in
the subalgebra generated by the base and the generators of strictly smaller level. -/
theorem augTower_lower (B : DeningerGCAAugStage k K) (u : omegaGen B)
    (hu : u ∉ (augTower B).base) :
    (augTower B).phi u ∈ deningerGCASubalgebra k (omegaDeg B)
      ((augTower B).base ∪ {y | (augTower B).lvl y < (augTower B).lvl u}) :=
  (augTower B).lower u hu

/-- **Each stage of the relative tower lands in the corresponding stage of the level filtration.** -/
theorem toOmega_mem_augTower_stage (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    toOmega B n z ∈ (augTower B).stage n := by
  refine deningerGCASubalgebra_mono ?_ (toOmega_mem_subalgebra B n z)
  rintro _ ⟨x, rfl⟩
  exact Or.inr (genToOmega_lvl_le B n x)

/-! ### The augmentation of the limit -/

/-- The values of the limit augmentation on the generators: the base generators keep their value and
every attached generator dies. -/
def epsOmegaGen (B : DeningerGCAAugStage k K) : omegaGen B → K :=
  Sum.elim (fun x => B.eps (deningerGCAι k B.toStage.deg x)) fun _ => 0

theorem epsOmegaGen_comm (B : DeningerGCAAugStage k K) (u v : omegaGen B) :
    epsOmegaGen B u * epsOmegaGen B v =
      ((-1 : k) ^ (omegaDeg B u * omegaDeg B v)) • (epsOmegaGen B v * epsOmegaGen B u) := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      show B.eps (deningerGCAι k B.toStage.deg x) * B.eps (deningerGCAι k B.toStage.deg y) =
        ((-1 : k) ^ (B.toStage.deg x * B.toStage.deg y)) •
          (B.eps (deningerGCAι k B.toStage.deg y) * B.eps (deningerGCAι k B.toStage.deg x))
      rw [← map_mul, deningerGCA_comm, map_smul, map_mul]
    | inr c =>
      show B.eps (deningerGCAι k B.toStage.deg x) * 0 =
        _ • ((0 : K) * B.eps (deningerGCAι k B.toStage.deg x))
      rw [mul_zero, zero_mul, smul_zero]
  | inr c =>
    show (0 : K) * epsOmegaGen B v = _ • (epsOmegaGen B v * 0)
    rw [zero_mul, mul_zero, smul_zero]

theorem epsOmegaGen_sq (B : DeningerGCAAugStage k K) (u : omegaGen B) (hu : Odd (omegaDeg B u)) :
    epsOmegaGen B u * epsOmegaGen B u = 0 := by
  cases u with
  | inl x =>
    have hx : Odd (B.toStage.deg x) := hu
    show B.eps (deningerGCAι k B.toStage.deg x) * B.eps (deningerGCAι k B.toStage.deg x) = 0
    rw [← map_mul, deningerGCA_sq_zero k B.toStage.deg hx, map_zero]
  | inr c =>
    show (0 : K) * 0 = 0
    rw [mul_zero]

/-- **The augmentation of the limit of the relative tower.** -/
def epsOmega (B : DeningerGCAAugStage k K) :
    DeningerFreeGCA k (omegaGen B) (omegaDeg B) →ₐ[k] K :=
  deningerGCALift (epsOmegaGen B) (epsOmegaGen_comm B) (epsOmegaGen_sq B)

@[simp]
theorem epsOmega_ι (B : DeningerGCAAugStage k K) (u : omegaGen B) :
    epsOmega B (deningerGCAι k (omegaDeg B) u) = epsOmegaGen B u :=
  deningerGCALift_ι _ _ _ u

theorem epsOmegaGen_genToOmega (B : DeningerGCAAugStage k K) :
    ∀ (n : ℕ) (x : (iterate B n).toStage.gen), epsOmegaGen B (genToOmega B n x) =
      (iterate B n).eps (deningerGCAι k (iterate B n).toStage.deg x)
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y =>
      refine (epsOmegaGen_genToOmega B n y).trans ?_
      exact ((iterate B n).epsSucc_ι (Sum.inl y)).symm
    | inr c => exact ((iterate B n).epsSucc_ι (Sum.inr c)).symm

/-- **The limit augmentation restricts to the augmentation of every stage**, so the whole tower maps
to the target compatibly. -/
theorem epsOmega_comp_toOmega (B : DeningerGCAAugStage k K) (n : ℕ)
    (z : DeningerFreeGCA k (iterate B n).toStage.gen (iterate B n).toStage.deg) :
    epsOmega B (toOmega B n z) = (iterate B n).eps z := by
  have h : (epsOmega B).comp (toOmega B n) = (iterate B n).eps := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, toOmega_ι, epsOmega_ι]
    exact epsOmegaGen_genToOmega B n x
  exact AlgHom.congr_fun h z

/-- **The limit augmentation annihilates the limit differential**, so it is a map of differential
graded algebras out of the limit. -/
theorem epsOmega_d (B : DeningerGCAAugStage k K) (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    epsOmega B ((omega B).d z) = 0 := by
  obtain ⟨n, w, rfl⟩ := exists_toOmega B z
  rw [omega_d_toOmega, epsOmega_comp_toOmega]
  exact (iterate B n).eps_d w

/-- **The cohomology comparison of the relative tower is injective in the limit.**  A cocycle of the
limit which transforms as an element of a definite degree and dies in the target is a coboundary.

The proof is the whole point of the relative attachment: such a cocycle already lives at a stage,
and there it is a cocycle of pure parity lying in the kernel of that stage's augmentation — which is
exactly the data attached at the next stage. -/
theorem omega_isCoboundary_of_eps_eq_zero (B : DeningerGCAAugStage k K) (p : ℕ)
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0)
    (hpar : deningerGCAInvolute k (omegaDeg B) z = ((-1 : k) ^ (p + 1)) • z)
    (hzero : epsOmega B z = 0) :
    ∃ y, (omega B).d y = z := by
  obtain ⟨n, w, rfl, hw⟩ := omega_cocycle_exists_stage B hz
  have hinvw : deningerGCAInvolute k (iterate B n).toStage.deg w =
      ((-1 : k) ^ (p + 1)) • w := by
    refine toOmega_injective B n ?_
    rw [← toOmega_involute, hpar, map_smul]
  have hzw : (iterate B n).eps w = 0 := by
    rw [← epsOmega_comp_toOmega]
    exact hzero
  refine ⟨toOmega B (n + 1) (deningerGCAι k (iterate B (n + 1)).toStage.deg
      (Sum.inr ⟨p, w, hw, hinvw, hzw⟩)), ?_⟩
  rw [omega_d_toOmega, iterate_kills, toOmega_comp_inl]

/-- **The limit augmentation intertwines the grading involutions.**  The target must carry an
involution matching the augmentation on the base generators; the attached generators die, so nothing
has to be checked for them. -/
theorem epsOmega_involute (B : DeningerGCAAugStage k K) (sigmaK : K →ₐ[k] K)
    (hsig : ∀ x : B.toStage.gen, sigmaK (B.eps (deningerGCAι k B.toStage.deg x)) =
      ((-1 : k) ^ B.toStage.deg x) • B.eps (deningerGCAι k B.toStage.deg x))
    (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    epsOmega B (deningerGCAInvolute k (omegaDeg B) z) = sigmaK (epsOmega B z) := by
  have h : (epsOmega B).comp (deningerGCAInvolute k (omegaDeg B)) =
      sigmaK.comp (epsOmega B) := by
    refine deningerGCA_hom_ext fun u => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, deningerGCAInvolute_ι, map_smul, epsOmega_ι]
    cases u with
    | inl x => exact (hsig x).symm
    | inr p =>
      show ((-1 : k) ^ omegaDeg B (Sum.inr p)) • (0 : K) = sigmaK 0
      rw [smul_zero, map_zero]
  exact AlgHom.congr_fun h z

/-- **The cohomology comparison of the relative tower is injective in the limit, with no parity
hypothesis.**  With `2` invertible in the ground ring the grading involution splits every element
into an even and an odd part; both are cocycles when the element is, both die in the target when it
does, and each has pure parity. -/
theorem omega_isCoboundary_of_eps_eq_zero' [Invertible (2 : k)] (B : DeningerGCAAugStage k K)
    (sigmaK : K →ₐ[k] K)
    (hsig : ∀ x : B.toStage.gen, sigmaK (B.eps (deningerGCAι k B.toStage.deg x)) =
      ((-1 : k) ^ B.toStage.deg x) • B.eps (deningerGCAι k B.toStage.deg x))
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0)
    (hzero : epsOmega B z = 0) :
    ∃ y, (omega B).d y = z := by
  have he : epsOmega B (deningerGCAEvenPart k (omegaDeg B) z) = 0 := by
    rw [deningerGCAEvenPart, map_smul, map_add, hzero, epsOmega_involute B sigmaK hsig, hzero,
      map_zero, add_zero, smul_zero]
  have ho : epsOmega B (deningerGCAOddPart k (omegaDeg B) z) = 0 := by
    rw [deningerGCAOddPart, map_smul, map_sub, hzero, epsOmega_involute B sigmaK hsig, hzero,
      map_zero, sub_zero, smul_zero]
  obtain ⟨y₁, hy₁⟩ := omega_isCoboundary_of_eps_eq_zero B 1 ((omega B).d_evenPart hz)
    (deningerGCAEvenPart_parity z) he
  obtain ⟨y₀, hy₀⟩ := omega_isCoboundary_of_eps_eq_zero B 0 ((omega B).d_oddPart hz)
    (deningerGCAOddPart_parity z) ho
  exact ⟨y₁ + y₀, by rw [map_add, hy₁, hy₀, deningerGCAEvenPart_add_oddPart]⟩

/-- **Clause 3 for homogeneous classes.**  A cocycle of the limit which is homogeneous of weight
`n + 1` and dies in the target is a coboundary.  Homogeneity supplies the parity directly, so this
form needs neither the invertibility of `2` nor an involution on the target: it is the degreewise
injectivity of the cohomology comparison. -/
theorem omega_isCoboundary_of_homogeneous (B : DeningerGCAAugStage k K) (n : ℕ)
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0)
    (hhom : DeningerGCAHomogeneous k (omegaDeg B) (n + 1) z) (hzero : epsOmega B z = 0) :
    ∃ y, (omega B).d y = z :=
  omega_isCoboundary_of_eps_eq_zero B n hz (deningerGCAHomogeneous_involute hhom) hzero

/-- **Clause 3 for a homogeneous class of any weight.**  A cocycle of the limit homogeneous of
weight `i` and dying in the target is a coboundary; the parity the general form asks for is the
parity of the weight. -/
theorem omega_isCoboundary_of_homogeneous_weight (B : DeningerGCAAugStage k K) (i : ℕ)
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0)
    (hhom : DeningerGCAHomogeneous k (omegaDeg B) i z) (hzero : epsOmega B z = 0) :
    ∃ y, (omega B).d y = z := by
  refine omega_isCoboundary_of_eps_eq_zero B (i + 1) hz ?_ hzero
  rw [deningerGCAHomogeneous_involute hhom]
  congr 1
  rw [pow_succ, pow_succ]
  ring

/-- **The limit augmentation intertwines the weight actions**, given a target action matching the
augmentation on the base generators. -/
theorem epsOmega_weight (B : DeningerGCAAugStage k K) (sigma : k → (K →ₐ[k] K))
    (hsig : ∀ (t : k) (x : B.toStage.gen), sigma t (B.eps (deningerGCAι k B.toStage.deg x)) =
      (t ^ B.toStage.deg x) • B.eps (deningerGCAι k B.toStage.deg x))
    (t : k) (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)) :
    epsOmega B (deningerGCAWeight k (omegaDeg B) t z) = sigma t (epsOmega B z) := by
  have h : (epsOmega B).comp (deningerGCAWeight k (omegaDeg B) t) =
      (sigma t).comp (epsOmega B) := by
    refine deningerGCA_hom_ext fun u => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, deningerGCAWeight_ι, map_smul, epsOmega_ι]
    cases u with
    | inl x => exact (hsig t x).symm
    | inr p =>
      show ((t : k) ^ omegaDeg B (Sum.inr p)) • (0 : K) = sigma t 0
      rw [smul_zero, map_zero]
  exact AlgHom.congr_fun h z

/-- **The relative tower is a resolution of the target.**  If the base has no differential and its
augmentation is onto, then in the limit every element of the target is the image of a cocycle, and
every cocycle of pure parity dying in the target is a coboundary.  These are the two halves of the
statement that the limit augmentation is a quasi-isomorphism in the degrees the model reaches. -/
theorem omega_quasiIso (B : DeningerGCAAugStage k K)
    (hd : ∀ z : DeningerFreeGCA k B.toStage.gen B.toStage.deg, B.toStage.d z = 0)
    (hsurj : Function.Surjective B.eps) :
    (∀ y : K, ∃ z, (omega B).d z = 0 ∧ epsOmega B z = y) ∧
      (∀ (p : ℕ) (z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)), (omega B).d z = 0 →
        deningerGCAInvolute k (omegaDeg B) z = ((-1 : k) ^ (p + 1)) • z →
        epsOmega B z = 0 → ∃ y, (omega B).d y = z) := by
  refine ⟨fun y => ?_, fun p z hz hpar hzero => omega_isCoboundary_of_eps_eq_zero B p hz hpar hzero⟩
  obtain ⟨w, hwd, hwe⟩ := iterate_eps_cocycle_surjective B hd hsurj 0 y
  refine ⟨toOmega B 0 w, ?_, ?_⟩
  · rw [omega_d_toOmega, hwd]
    exact map_zero _
  · rw [epsOmega_comp_toOmega]
    exact hwe

/-- **The limit augmentation is surjective.** -/
theorem epsOmega_surjective (B : DeningerGCAAugStage k K)
    (hd : ∀ z : DeningerFreeGCA k B.toStage.gen B.toStage.deg, B.toStage.d z = 0)
    (hsurj : Function.Surjective B.eps) : Function.Surjective (epsOmega B) := by
  intro y
  obtain ⟨z, _, hz⟩ := (omega_quasiIso B hd hsurj).1 y
  exact ⟨z, hz⟩

/-- **Clause 3, with no parity hypothesis.**  Over a ground ring in which `2` is invertible, and for
a target carrying an involution matching the augmentation on the base generators, the limit
augmentation of the relative tower is a surjective quasi-isomorphism: every element of the target is
the image of a cocycle, and every cocycle dying in the target is a coboundary. -/
theorem omega_quasiIso' [Invertible (2 : k)] (B : DeningerGCAAugStage k K)
    (sigmaK : K →ₐ[k] K)
    (hsig : ∀ x : B.toStage.gen, sigmaK (B.eps (deningerGCAι k B.toStage.deg x)) =
      ((-1 : k) ^ B.toStage.deg x) • B.eps (deningerGCAι k B.toStage.deg x))
    (hd : ∀ z : DeningerFreeGCA k B.toStage.gen B.toStage.deg, B.toStage.d z = 0)
    (hsurj : Function.Surjective B.eps) :
    (∀ y : K, ∃ z, (omega B).d z = 0 ∧ epsOmega B z = y) ∧
      (∀ z : DeningerFreeGCA k (omegaGen B) (omegaDeg B), (omega B).d z = 0 →
        epsOmega B z = 0 → ∃ y, (omega B).d y = z) :=
  ⟨(omega_quasiIso B hd hsurj).1,
    fun _ hz hzero => omega_isCoboundary_of_eps_eq_zero' B sigmaK hsig hz hzero⟩

end DeningerGCAAugStage

/-- **The augmented base stage**: an algebra with no differential and any map to the target.  The
augmentation condition is vacuous because the differential of a base generator is zero. -/
def deningerGCAAugBase (k : Type u) (K : Type w) [CommRing k] [Ring K] [Algebra k K]
    {G : Type u} (deg : G → ℕ) (eps : DeningerFreeGCA k G deg →ₐ[k] K) :
    DeningerGCAAugStage k K where
  toStage := DeningerGCAStage.base k G deg
  eps := eps
  heps := fun x => by
    show eps (0 : DeningerFreeGCA k G deg) = 0
    exact map_zero _

@[simp]
theorem deningerGCAAugBase_toStage (k : Type u) (K : Type w) [CommRing k] [Ring K] [Algebra k K]
    {G : Type u} (deg : G → ℕ) (eps : DeningerFreeGCA k G deg →ₐ[k] K) :
    (deningerGCAAugBase k K deg eps).toStage = DeningerGCAStage.base k G deg := rfl

/-- **The augmentation of the base stage is surjective on cocycles as soon as it is surjective.**
The base has no differential, so every element of it is closed and the cohomology comparison is
surjective from the start; the tower only has to make it injective. -/
theorem deningerGCAAugBase_cocycle_surjective (k : Type u) (K : Type w) [CommRing k] [Ring K]
    [Algebra k K] {G : Type u} (deg : G → ℕ) (eps : DeningerFreeGCA k G deg →ₐ[k] K)
    (hsurj : Function.Surjective eps) (y : K) :
    ∃ z, (DeningerGCAStage.base k G deg).d z = 0 ∧ eps z = y := by
  obtain ⟨z, hz⟩ := hsurj y
  exact ⟨z, DeningerGCAStage.base_d deg z, hz⟩

end Augmented

section Functoriality

universe u w w' w''

variable {k : Type u} [CommRing k] {K : Type w} {K' : Type w'} {K'' : Type w''}
  [Ring K] [Algebra k K] [Ring K'] [Algebra k K'] [Ring K''] [Algebra k K'']

/-- **A morphism of augmented stages**: a degree-preserving map of generators together with a map of
targets, compatible with the differentials and with the augmentations. -/
structure DeningerGCAAugHom (A : DeningerGCAAugStage k K) (A' : DeningerGCAAugStage k K') where
  /-- The map on generators. -/
  gen : A.toStage.gen → A'.toStage.gen
  /-- It preserves degrees. -/
  hdeg : ∀ x : A.toStage.gen, A'.toStage.deg (gen x) = A.toStage.deg x
  /-- The map on targets. -/
  tgt : K →ₐ[k] K'
  /-- **The induced algebra map is a chain map on generators.** -/
  hphi : ∀ x : A.toStage.gen,
    deningerGCAGenAlg k A.toStage.deg A'.toStage.deg gen hdeg (A.toStage.phi x) =
      A'.toStage.phi (gen x)
  /-- **The induced algebra map is compatible with the augmentations on generators.** -/
  heps : ∀ x : A.toStage.gen, tgt (A.eps (deningerGCAι k A.toStage.deg x)) =
    A'.eps (deningerGCAι k A'.toStage.deg (gen x))

namespace DeningerGCAAugHom

variable {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
  (Φ : DeningerGCAAugHom A A')

/-- The algebra map induced by a morphism of augmented stages. -/
def alg : DeningerFreeGCA k A.toStage.gen A.toStage.deg →ₐ[k]
    DeningerFreeGCA k A'.toStage.gen A'.toStage.deg :=
  deningerGCAGenAlg k A.toStage.deg A'.toStage.deg Φ.gen Φ.hdeg

@[simp]
theorem alg_ι (x : A.toStage.gen) :
    Φ.alg (deningerGCAι k A.toStage.deg x) = deningerGCAι k A'.toStage.deg (Φ.gen x) :=
  deningerGCAGenAlg_ι _ _ _ _ x

theorem alg_involute (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) :
    Φ.alg (deningerGCAInvolute k A.toStage.deg z) =
      deningerGCAInvolute k A'.toStage.deg (Φ.alg z) :=
  deningerGCAGenAlg_involute _ _ _ _ z

/-- **A morphism of augmented stages is a chain map.** -/
theorem alg_d (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) :
    Φ.alg (A.toStage.d z) = A'.toStage.d (Φ.alg z) := by
  refine DeningerGCAStage.d_map A.toStage A'.toStage Φ.alg Φ.alg_involute ?_ z
  intro x
  rw [Φ.alg_ι, DeningerGCAStage.d_ι]
  exact Φ.hphi x

/-- **A morphism of augmented stages respects the augmentations.** -/
theorem alg_eps (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) :
    Φ.tgt (A.eps z) = A'.eps (Φ.alg z) := by
  have h : Φ.tgt.comp A.eps = A'.eps.comp Φ.alg := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Φ.alg_ι]
    exact Φ.heps x
  exact AlgHom.congr_fun h z

/-- **The classes an augmented stage must kill are carried along a morphism.**  This is what makes
the relative attachment functorial: the attachment is indexed by all attachable classes, so a
morphism of stages induces a map of attachments with no choices. -/
def cocycleMap (c : DeningerGCAAugStage.Cocycle A) : DeningerGCAAugStage.Cocycle A' where
  degree := c.degree
  val := Φ.alg c.val
  hkill := by rw [← Φ.alg_d, c.hkill, map_zero]
  hinv := by rw [← Φ.alg_involute, c.hinv, map_smul]
  hzero := by rw [← Φ.alg_eps, c.hzero, map_zero]

/-- **A class to be killed is determined by its degree and its value.** -/
theorem cocycleExt {B : DeningerGCAAugStage k K} {c c' : DeningerGCAAugStage.Cocycle B}
    (hd : c.degree = c'.degree) (hv : c.val = c'.val) : c = c' := by
  cases c
  cases c'
  cases hd
  cases hv
  rfl

/-- **A morphism carries the generator values to the generator values.** -/
theorem alg_phi (x : A.toStage.gen) :
    Φ.alg (A.toStage.phi x) = A'.toStage.phi (Φ.gen x) := Φ.hphi x

@[simp]
theorem cocycleMap_val (c : DeningerGCAAugStage.Cocycle A) :
    (Φ.cocycleMap c).val = Φ.alg c.val := rfl

@[simp]
theorem cocycleMap_degree (c : DeningerGCAAugStage.Cocycle A) :
    (Φ.cocycleMap c).degree = c.degree := rfl

/-- The generator map of the successor morphism. -/
def succGen : A.toStage.gen ⊕ DeningerGCAAugStage.Cocycle A →
    A'.toStage.gen ⊕ DeningerGCAAugStage.Cocycle A' :=
  Sum.elim (fun x => Sum.inl (Φ.gen x)) fun c => Sum.inr (Φ.cocycleMap c)

theorem succHdeg (u : A.succ.toStage.gen) :
    A'.succ.toStage.deg (Φ.succGen u) = A.succ.toStage.deg u := by
  cases u with
  | inl x => exact Φ.hdeg x
  | inr c => rfl

/-- The algebra map of the successor morphism. -/
def succAlg : DeningerFreeGCA k A.succ.toStage.gen A.succ.toStage.deg →ₐ[k]
    DeningerFreeGCA k A'.succ.toStage.gen A'.succ.toStage.deg :=
  deningerGCAGenAlg k A.succ.toStage.deg A'.succ.toStage.deg Φ.succGen Φ.succHdeg

/-- **The successor morphism restricts to the given one.** -/
theorem succAlg_inl (z : DeningerFreeGCA k A.toStage.gen A.toStage.deg) :
    Φ.succAlg (deningerGCAInl A.toStage.deg A.attachment.newDeg z) =
      deningerGCAInl A'.toStage.deg A'.attachment.newDeg (Φ.alg z) :=
  deningerGCAGenAlg_comp_inl A.toStage.deg A.attachment.newDeg A'.toStage.deg
    A'.attachment.newDeg Φ.gen (fun c => Φ.cocycleMap c) Φ.succHdeg Φ.hdeg z

/-- **The successor of a morphism of augmented stages.**  Because the relative attachment attaches a
generator to every attachable class, and those classes are carried along by the morphism, the
successor construction is functorial. -/
def succ : DeningerGCAAugHom A.succ A'.succ where
  gen := Φ.succGen
  hdeg := Φ.succHdeg
  tgt := Φ.tgt
  hphi := by
    intro u
    cases u with
    | inl x =>
      show Φ.succAlg (deningerGCAInl A.toStage.deg A.attachment.newDeg (A.toStage.phi x)) = _
      rw [Φ.succAlg_inl]
      exact congrArg (deningerGCAInl A'.toStage.deg A'.attachment.newDeg) (Φ.hphi x)
    | inr c =>
      show Φ.succAlg (deningerGCAInl A.toStage.deg A.attachment.newDeg c.val) = _
      rw [Φ.succAlg_inl]
      rfl
  heps := by
    intro u
    cases u with
    | inl x =>
      show Φ.tgt (A.epsSucc (deningerGCAι k A.succ.toStage.deg (Sum.inl x))) =
        A'.epsSucc (deningerGCAι k A'.succ.toStage.deg (Sum.inl (Φ.gen x)))
      have h1 : A.epsSucc (deningerGCAι k A.succ.toStage.deg (Sum.inl x)) =
          A.eps (deningerGCAι k A.toStage.deg x) := A.epsSucc_ι (Sum.inl x)
      have h2 : A'.epsSucc (deningerGCAι k A'.succ.toStage.deg (Sum.inl (Φ.gen x))) =
          A'.eps (deningerGCAι k A'.toStage.deg (Φ.gen x)) := A'.epsSucc_ι (Sum.inl (Φ.gen x))
      rw [h1, h2]
      exact Φ.heps x
    | inr c =>
      show Φ.tgt (A.epsSucc (deningerGCAι k A.succ.toStage.deg (Sum.inr c))) =
        A'.epsSucc (deningerGCAι k A'.succ.toStage.deg (Sum.inr (Φ.cocycleMap c)))
      have h1 : A.epsSucc (deningerGCAι k A.succ.toStage.deg (Sum.inr c)) = (0 : K) :=
        A.epsSucc_ι (Sum.inr c)
      have h2 : A'.epsSucc (deningerGCAι k A'.succ.toStage.deg
          (Sum.inr (Φ.cocycleMap c))) = (0 : K') := A'.epsSucc_ι (Sum.inr (Φ.cocycleMap c))
      rw [h1, h2]
      exact map_zero _

@[simp]
theorem succ_gen : Φ.succ.gen = Φ.succGen := rfl

@[simp]
theorem succ_tgt : Φ.succ.tgt = Φ.tgt := rfl

theorem succ_alg (z : DeningerFreeGCA k A.succ.toStage.gen A.succ.toStage.deg) :
    Φ.succ.alg z = Φ.succAlg z := rfl

/-- **The tower of a morphism of augmented stages.** -/
def iterate (Φ : DeningerGCAAugHom A A') : ∀ n : ℕ,
    DeningerGCAAugHom (DeningerGCAAugStage.iterate A n) (DeningerGCAAugStage.iterate A' n)
  | 0 => Φ
  | n + 1 => (iterate Φ n).succ

@[simp]
theorem iterate_zero : Φ.iterate 0 = Φ := rfl

@[simp]
theorem iterate_succ (n : ℕ) : Φ.iterate (n + 1) = (Φ.iterate n).succ := rfl

/-- **The tower of a morphism is compatible with the inclusions of the towers.**  This is the
naturality that makes the relative factorization functorial stage by stage. -/
theorem iterate_alg_inl (n : ℕ)
    (z : DeningerFreeGCA k (DeningerGCAAugStage.iterate A n).toStage.gen
      (DeningerGCAAugStage.iterate A n).toStage.deg) :
    (Φ.iterate (n + 1)).alg (DeningerGCAAugStage.iterateInl A n z) =
      DeningerGCAAugStage.iterateInl A' n ((Φ.iterate n).alg z) :=
  (Φ.iterate n).succAlg_inl z

/-- **The tower of a morphism commutes with the differentials at every stage.** -/
theorem iterate_alg_d (n : ℕ)
    (z : DeningerFreeGCA k (DeningerGCAAugStage.iterate A n).toStage.gen
      (DeningerGCAAugStage.iterate A n).toStage.deg) :
    (Φ.iterate n).alg ((DeningerGCAAugStage.iterate A n).toStage.d z) =
      (DeningerGCAAugStage.iterate A' n).toStage.d ((Φ.iterate n).alg z) :=
  (Φ.iterate n).alg_d z

/-- **The tower of a morphism respects the augmentations at every stage.** -/
theorem iterate_alg_eps (n : ℕ)
    (z : DeningerFreeGCA k (DeningerGCAAugStage.iterate A n).toStage.gen
      (DeningerGCAAugStage.iterate A n).toStage.deg) :
    Φ.tgt ((DeningerGCAAugStage.iterate A n).eps z) =
      (DeningerGCAAugStage.iterate A' n).eps ((Φ.iterate n).alg z) := by
  have htgt : ∀ m : ℕ, (Φ.iterate m).tgt = Φ.tgt := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => exact ih
  rw [← htgt n]
  exact (Φ.iterate n).alg_eps z

/-! ### The morphism induced on the limits -/

/-- The map on limit generators induced by a morphism of augmented stages. -/
def omegaGen : DeningerGCAAugStage.omegaGen A → DeningerGCAAugStage.omegaGen A' :=
  Sum.elim (fun x => Sum.inl (Φ.gen x)) fun p => Sum.inr ⟨p.1, (Φ.iterate p.1).cocycleMap p.2⟩

theorem omegaHdeg (u : DeningerGCAAugStage.omegaGen A) :
    DeningerGCAAugStage.omegaDeg A' (Φ.omegaGen u) = DeningerGCAAugStage.omegaDeg A u := by
  cases u with
  | inl x => exact Φ.hdeg x
  | inr p => rfl

/-- **The algebra map induced on the limits by a morphism of augmented stages.** -/
def omegaAlg : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A) (DeningerGCAAugStage.omegaDeg A)
    →ₐ[k] DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A')
      (DeningerGCAAugStage.omegaDeg A') :=
  deningerGCAGenAlg k (DeningerGCAAugStage.omegaDeg A) (DeningerGCAAugStage.omegaDeg A')
    Φ.omegaGen Φ.omegaHdeg

@[simp]
theorem omegaAlg_ι (u : DeningerGCAAugStage.omegaGen A) :
    Φ.omegaAlg (deningerGCAι k (DeningerGCAAugStage.omegaDeg A) u) =
      deningerGCAι k (DeningerGCAAugStage.omegaDeg A') (Φ.omegaGen u) :=
  deningerGCAGenAlg_ι _ _ _ _ u

/-- **The limit generator map agrees with the stage generator maps.** -/
theorem omegaGen_genToOmega (Φ : DeningerGCAAugHom A A') :
    ∀ (n : ℕ) (x : (DeningerGCAAugStage.iterate A n).toStage.gen),
      Φ.omegaGen (DeningerGCAAugStage.genToOmega A n x) =
        DeningerGCAAugStage.genToOmega A' n ((Φ.iterate n).gen x)
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | inl y => exact omegaGen_genToOmega Φ n y
    | inr c => rfl

/-- **The induced limit map is compatible with the maps from the stages.**  This is the naturality
of the limit construction: the square formed by a stage, its image, and the two limits commutes. -/
theorem omegaAlg_toOmega (n : ℕ)
    (z : DeningerFreeGCA k (DeningerGCAAugStage.iterate A n).toStage.gen
      (DeningerGCAAugStage.iterate A n).toStage.deg) :
    Φ.omegaAlg (DeningerGCAAugStage.toOmega A n z) =
      DeningerGCAAugStage.toOmega A' n ((Φ.iterate n).alg z) := by
  have h : Φ.omegaAlg.comp (DeningerGCAAugStage.toOmega A n) =
      (DeningerGCAAugStage.toOmega A' n).comp (Φ.iterate n).alg := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, DeningerGCAAugStage.toOmega_ι, Φ.omegaAlg_ι,
      alg_ι, DeningerGCAAugStage.toOmega_ι, Φ.omegaGen_genToOmega]
  exact AlgHom.congr_fun h z

theorem omegaAlg_involute (z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A)
    (DeningerGCAAugStage.omegaDeg A)) :
    Φ.omegaAlg (deningerGCAInvolute k (DeningerGCAAugStage.omegaDeg A) z) =
      deningerGCAInvolute k (DeningerGCAAugStage.omegaDeg A') (Φ.omegaAlg z) :=
  deningerGCAGenAlg_involute _ _ _ _ z

/-- **The induced limit map is a chain map.** -/
theorem omegaAlg_d (z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A)
    (DeningerGCAAugStage.omegaDeg A)) :
    Φ.omegaAlg ((DeningerGCAAugStage.omega A).d z) =
      (DeningerGCAAugStage.omega A').d (Φ.omegaAlg z) := by
  refine DeningerGCAStage.d_map (DeningerGCAAugStage.omega A) (DeningerGCAAugStage.omega A')
    Φ.omegaAlg Φ.omegaAlg_involute ?_ z
  intro u
  obtain ⟨n, x, rfl⟩ := DeningerGCAAugStage.exists_genToOmega A u
  have hR : (DeningerGCAAugStage.omega A').d
      (Φ.omegaAlg (deningerGCAι k (DeningerGCAAugStage.omegaDeg A)
        (DeningerGCAAugStage.genToOmega A n x))) =
      DeningerGCAAugStage.omegaPhi A'
        (Φ.omegaGen (DeningerGCAAugStage.genToOmega A n x)) := by
    rw [Φ.omegaAlg_ι]
    exact (DeningerGCAAugStage.omega A').d_ι _
  refine Eq.trans ?_ hR.symm
  show Φ.omegaAlg (DeningerGCAAugStage.omegaPhi A (DeningerGCAAugStage.genToOmega A n x)) =
    DeningerGCAAugStage.omegaPhi A' (Φ.omegaGen (DeningerGCAAugStage.genToOmega A n x))
  rw [DeningerGCAAugStage.omegaPhi_eq, Φ.omegaAlg_toOmega, alg_phi, Φ.omegaGen_genToOmega,
    DeningerGCAAugStage.omegaPhi_eq]

/-- **The induced limit map respects the limit augmentations.** -/
theorem omegaAlg_eps (z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A)
    (DeningerGCAAugStage.omegaDeg A)) :
    Φ.tgt (DeningerGCAAugStage.epsOmega A z) =
      DeningerGCAAugStage.epsOmega A' (Φ.omegaAlg z) := by
  have h : Φ.tgt.comp (DeningerGCAAugStage.epsOmega A) =
      (DeningerGCAAugStage.epsOmega A').comp Φ.omegaAlg := by
    refine deningerGCA_hom_ext fun u => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, DeningerGCAAugStage.epsOmega_ι, Φ.omegaAlg_ι,
      DeningerGCAAugStage.epsOmega_ι]
    cases u with
    | inl x => exact Φ.heps x
    | inr p =>
      show Φ.tgt (0 : K) = (0 : K')
      exact map_zero _
  exact AlgHom.congr_fun h z

/-! ### The identity and composition laws -/

/-- **The identity morphism of an augmented stage.** -/
def id (A : DeningerGCAAugStage k K) : DeningerGCAAugHom A A where
  gen := fun x => x
  hdeg := fun _ => rfl
  tgt := AlgHom.id k K
  hphi := fun x => deningerGCAGenAlg_eq_id _ _ _ (fun _ => rfl) (A.toStage.phi x)
  heps := fun _ => rfl

/-- **The composite of two morphisms of augmented stages.** -/
def comp {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
    {A'' : DeningerGCAAugStage k K''} (Ψ : DeningerGCAAugHom A' A'')
    (Φ : DeningerGCAAugHom A A') : DeningerGCAAugHom A A'' where
  gen := fun x => Ψ.gen (Φ.gen x)
  hdeg := fun x => (Ψ.hdeg (Φ.gen x)).trans (Φ.hdeg x)
  tgt := Ψ.tgt.comp Φ.tgt
  hphi := fun x => by
    have h := deningerGCAGenAlg_eq_comp (k := k) A.toStage.deg A'.toStage.deg A''.toStage.deg
      Φ.gen Ψ.gen (fun y => Ψ.gen (Φ.gen y)) Φ.hdeg Ψ.hdeg
      (fun y => (Ψ.hdeg (Φ.gen y)).trans (Φ.hdeg y)) (fun _ => rfl) (A.toStage.phi x)
    rw [h]
    show Ψ.alg (Φ.alg (A.toStage.phi x)) = _
    rw [Φ.alg_phi, Ψ.alg_phi]
  heps := fun x => by
    show Ψ.tgt (Φ.tgt (A.eps (deningerGCAι k A.toStage.deg x))) = _
    rw [Φ.heps x, Ψ.heps (Φ.gen x)]

@[simp]
theorem id_gen (A : DeningerGCAAugStage k K) (x : A.toStage.gen) :
    (DeningerGCAAugHom.id A).gen x = x := rfl

@[simp]
theorem comp_gen {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
    {A'' : DeningerGCAAugStage k K''} (Ψ : DeningerGCAAugHom A' A'')
    (Φ : DeningerGCAAugHom A A') (x : A.toStage.gen) :
    (Ψ.comp Φ).gen x = Ψ.gen (Φ.gen x) := rfl

/-- **The tower of the identity is the identity at every stage.** -/
theorem id_iterate_gen (A : DeningerGCAAugStage k K) :
    ∀ (n : ℕ) (x : (DeningerGCAAugStage.iterate A n).toStage.gen),
      ((DeningerGCAAugHom.id A).iterate n).gen x = x
  | 0, _ => rfl
  | n + 1, u => by
    cases u with
    | inl x => exact congrArg Sum.inl (id_iterate_gen A n x)
    | inr c =>
      refine congrArg Sum.inr (cocycleExt rfl ?_)
      exact deningerGCAGenAlg_eq_id _ _ _ (id_iterate_gen A n) c.val

/-- **The tower of a composite is the composite of the towers at every stage.** -/
theorem comp_iterate_gen {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
    {A'' : DeningerGCAAugStage k K''} (Ψ : DeningerGCAAugHom A' A'')
    (Φ : DeningerGCAAugHom A A') :
    ∀ (n : ℕ) (x : (DeningerGCAAugStage.iterate A n).toStage.gen),
      ((Ψ.comp Φ).iterate n).gen x = (Ψ.iterate n).gen ((Φ.iterate n).gen x)
  | 0, _ => rfl
  | n + 1, u => by
    cases u with
    | inl x => exact congrArg Sum.inl (comp_iterate_gen Ψ Φ n x)
    | inr c =>
      refine congrArg Sum.inr (cocycleExt rfl ?_)
      exact deningerGCAGenAlg_eq_comp _ _ _ _ _ _ _ _ _ (comp_iterate_gen Ψ Φ n) c.val

/-- **The identity induces the identity on the limit generators.** -/
theorem id_omegaGen (A : DeningerGCAAugStage k K) (u : DeningerGCAAugStage.omegaGen A) :
    (DeningerGCAAugHom.id A).omegaGen u = u := by
  cases u with
  | inl x => rfl
  | inr p =>
    have h : ((DeningerGCAAugHom.id A).iterate p.1).cocycleMap p.2 = p.2 :=
      cocycleExt rfl (deningerGCAGenAlg_eq_id _ _ _ (id_iterate_gen A p.1) p.2.val)
    show (Sum.inr ⟨p.1, ((DeningerGCAAugHom.id A).iterate p.1).cocycleMap p.2⟩ :
      DeningerGCAAugStage.omegaGen A) = Sum.inr p
    rw [h]
    rfl

/-- **A composite induces the composite on the limit generators.** -/
theorem comp_omegaGen {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
    {A'' : DeningerGCAAugStage k K''} (Ψ : DeningerGCAAugHom A' A'')
    (Φ : DeningerGCAAugHom A A') (u : DeningerGCAAugStage.omegaGen A) :
    (Ψ.comp Φ).omegaGen u = Ψ.omegaGen (Φ.omegaGen u) := by
  cases u with
  | inl x => rfl
  | inr p =>
    have h : ((Ψ.comp Φ).iterate p.1).cocycleMap p.2 =
        (Ψ.iterate p.1).cocycleMap ((Φ.iterate p.1).cocycleMap p.2) :=
      cocycleExt rfl (deningerGCAGenAlg_eq_comp _ _ _ _ _ _ _ _ _
        (comp_iterate_gen Ψ Φ p.1) p.2.val)
    show (Sum.inr ⟨p.1, ((Ψ.comp Φ).iterate p.1).cocycleMap p.2⟩ :
      DeningerGCAAugStage.omegaGen A'') = _
    rw [h]
    rfl

/-- **The identity induces the identity on the limit.** -/
theorem omegaAlg_id (A : DeningerGCAAugStage k K)
    (z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A) (DeningerGCAAugStage.omegaDeg A)) :
    (DeningerGCAAugHom.id A).omegaAlg z = z :=
  deningerGCAGenAlg_eq_id _ _ _ (id_omegaGen A) z

/-- **A composite induces the composite on the limit.**  With `omegaAlg_id` this is the
functoriality of the relative Sullivan factorization: the construction is a functor from augmented
stages to differential graded algebras over the target. -/
theorem omegaAlg_comp {A : DeningerGCAAugStage k K} {A' : DeningerGCAAugStage k K'}
    {A'' : DeningerGCAAugStage k K''} (Ψ : DeningerGCAAugHom A' A'')
    (Φ : DeningerGCAAugHom A A')
    (z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen A) (DeningerGCAAugStage.omegaDeg A)) :
    (Ψ.comp Φ).omegaAlg z = Ψ.omegaAlg (Φ.omegaAlg z) :=
  deningerGCAGenAlg_eq_comp _ _ _ _ _ _ _ _ _ (comp_omegaGen Ψ Φ) z

end DeningerGCAAugHom

end Functoriality

end HTGeometry
