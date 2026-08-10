import GaloisForLFunctions.HTGeometry.ConstitutivePromotionObservationExchange

/-!
# Coefficient-lift transgression

A coarse binary cocycle may fail to lift to a cocycle after coefficient refinement.  The
associator of any lift then lands in the coefficient kernel, satisfies the pentagon identity,
and is independent of the lift up to a ternary coboundary.  Its class vanishes exactly when a
strict refined cocycle lift exists.

The finite `((ZMod 2)^2, ZMod 4, ZMod 2)` cell proves this higher defect can be unavoidable.
A two-term linear cell verifies the same lift law without central-extension multiplication.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w x

/-- A binary compensator whose promotion differential vanishes. -/
def IsPromotionCocycle {M : Type u} {A : Type v} [Add M] [AddGroup A]
    (κ : M → M → A) : Prop :=
  ∀ a b c, PromotionAssociator κ a b c = 0

/-- A pointwise lift of a binary compensator through an additive coefficient observer. -/
def IsCompensatorLift {M : Type u} {A : Type v} {B : Type w}
    [AddGroup A] [AddGroup B]
    (q : A →+ B) (κA : M → M → A) (κB : M → M → B) : Prop :=
  ∀ a b, q (κA a b) = κB a b

/-- Change a fine compensator by a kernel-valued binary cochain. -/
def kernelCorrectedCompensator {M : Type u} {K : Type v} {A : Type w}
    [AddCommGroup K] [AddCommGroup A]
    (i : K →+ A) (κ : M → M → A) (β : M → M → K) (a b : M) : A :=
  κ a b + i (β a b)

/-- A kernel correction changes the fine associator by the image of its own associator. -/
theorem promotionAssociator_kernelCorrected
    {M : Type u} {K : Type v} {A : Type w}
    [AddSemigroup M] [AddCommGroup K] [AddCommGroup A]
    (i : K →+ A) (κ : M → M → A) (β : M → M → K) (a b c : M) :
    PromotionAssociator (kernelCorrectedCompensator i κ β) a b c =
      PromotionAssociator κ a b c + i (PromotionAssociator β a b c) := by
  simp [PromotionAssociator, kernelCorrectedCompensator]
  abel

/-- A coarse cocycle forces the associator of every fine lift into the coefficient kernel. -/
theorem exists_kernelHigherDefect
    {M : Type u} {K : Type v} {A : Type w} {B : Type x}
    [Add M] [AddCommGroup K] [AddCommGroup A] [AddCommGroup B]
    (i : K →+ A) (q : A →+ B)
    (hexact : ∀ a, q a = 0 → ∃ k, i k = a)
    (κA : M → M → A) (κB : M → M → B)
    (hlift : IsCompensatorLift q κA κB)
    (hcoc : IsPromotionCocycle κB) :
    ∃ h : M → M → M → K,
      ∀ a b c, i (h a b c) = PromotionAssociator κA a b c := by
  classical
  have hobserved : observedCompensator q κA = κB := by
    funext a b
    exact hlift a b
  have hkernel : ∀ a b c, q (PromotionAssociator κA a b c) = 0 := by
    intro a b c
    rw [← promotionAssociator_observed, hobserved]
    exact hcoc a b c
  choose h hh using fun a b c => hexact _ (hkernel a b c)
  exact ⟨h, hh⟩

/-- The kernel-valued defect born from a fine lift automatically satisfies pentagon coherence. -/
theorem kernelHigherDefect_pentagon
    {M : Type u} {K : Type v} {A : Type w}
    [AddSemigroup M] [AddCommGroup K] [AddCommGroup A]
    (i : K →+ A) (hi : Function.Injective i)
    (κ : M → M → A) (h : M → M → M → K)
    (hh : ∀ a b c, i (h a b c) = PromotionAssociator κ a b c)
    (w x y z : M) :
    h w x y + h w (x + y) z + h x y z =
      h (w + x) y z + h w x (y + z) := by
  apply hi
  simp only [map_add, hh]
  exact promotionAssociator_pentagon κ w x y z

/-- Vanishing of the higher defect by a kernel coboundary is exactly strict correction of the
chosen fine lift. -/
theorem kernelHigherDefect_trivial_iff_strict_lift
    {M : Type u} {K : Type v} {A : Type w}
    [AddMonoid M] [AddCommGroup K] [AddCommGroup A]
    (i : K →+ A) (hi : Function.Injective i)
    (κ : M → M → A) (h : M → M → M → K)
    (hh : ∀ a b c, i (h a b c) = PromotionAssociator κ a b c) :
    (∃ β : M → M → K,
      ∀ a b c, h a b c + PromotionAssociator β a b c = 0) ↔
      ∃ β : M → M → K,
        ∀ a b c,
          PromotionAssociator (kernelCorrectedCompensator i κ β) a b c = 0 := by
  constructor <;> rintro ⟨β, hβ⟩ <;> refine ⟨β, ?_⟩ <;> intro a b c
  · rw [promotionAssociator_kernelCorrected, ← hh, ← map_add, hβ, map_zero]
  · apply hi
    rw [map_add, hh, ← promotionAssociator_kernelCorrected, hβ, map_zero]

/-- **Strictification converse.**  The higher defect is a coboundary exactly when the coarse
cocycle has some strict fine cocycle lift. -/
theorem kernelHigherDefect_trivial_iff_exists_cocycle_lift
    {M : Type u} {K : Type v} {A : Type w} {B : Type x}
    [AddMonoid M] [AddCommGroup K] [AddCommGroup A] [AddCommGroup B]
    (i : K →+ A) (q : A →+ B)
    (hi : Function.Injective i)
    (hqi : ∀ k, q (i k) = 0)
    (hexact : ∀ a, q a = 0 → ∃ k, i k = a)
    (κA : M → M → A) (κB : M → M → B)
    (hlift : IsCompensatorLift q κA κB)
    (h : M → M → M → K)
    (hh : ∀ a b c, i (h a b c) = PromotionAssociator κA a b c) :
    (∃ β : M → M → K,
      ∀ a b c, h a b c + PromotionAssociator β a b c = 0) ↔
      ∃ κA' : M → M → A,
        IsCompensatorLift q κA' κB ∧ IsPromotionCocycle κA' := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨kernelCorrectedCompensator i κA β, ?_, ?_⟩
    · intro a b
      simp [kernelCorrectedCompensator, hlift a b, hqi]
    · intro a b c
      rw [promotionAssociator_kernelCorrected, ← hh, ← map_add, hβ, map_zero]
  · rintro ⟨κA', hlift', hcoc'⟩
    have hdiff : ∀ a b, q (κA' a b - κA a b) = 0 := by
      intro a b
      rw [map_sub, hlift' a b, hlift a b, sub_self]
    choose β hβ using fun a b => hexact _ (hdiff a b)
    have hfun : κA' = kernelCorrectedCompensator i κA β := by
      funext a b
      simp only [kernelCorrectedCompensator]
      rw [hβ]
      abel
    apply (kernelHigherDefect_trivial_iff_strict_lift i hi κA h hh).2
    refine ⟨β, ?_⟩
    intro a b c
    rw [← hfun]
    exact hcoc' a b c

/-- Defects computed from two fine lifts differ by a ternary coboundary. -/
theorem kernelHigherDefect_lift_independent
    {M : Type u} {K : Type v} {A : Type w} {B : Type x}
    [AddSemigroup M] [AddCommGroup K] [AddCommGroup A] [AddCommGroup B]
    (i : K →+ A) (q : A →+ B)
    (hi : Function.Injective i)
    (hexact : ∀ a, q a = 0 → ∃ k, i k = a)
    (κA κA' : M → M → A) (κB : M → M → B)
    (hlift : IsCompensatorLift q κA κB)
    (hlift' : IsCompensatorLift q κA' κB)
    (h h' : M → M → M → K)
    (hh : ∀ a b c, i (h a b c) = PromotionAssociator κA a b c)
    (hh' : ∀ a b c, i (h' a b c) = PromotionAssociator κA' a b c) :
    ∃ β : M → M → K,
      ∀ a b c, h' a b c = h a b c + PromotionAssociator β a b c := by
  have hdiff : ∀ a b, q (κA' a b - κA a b) = 0 := by
    intro a b
    rw [map_sub, hlift' a b, hlift a b, sub_self]
  choose β hβ using fun a b => hexact _ (hdiff a b)
  refine ⟨β, ?_⟩
  intro a b c
  apply hi
  rw [map_add, hh, hh']
  have hfun : κA' = kernelCorrectedCompensator i κA β := by
    funext x y
    simp only [kernelCorrectedCompensator]
    rw [hβ]
    abel
  rw [hfun, promotionAssociator_kernelCorrected]

/-- Split coefficient refinements cannot force higher birth: apply the additive section. -/
theorem splitCoefficient_cocycle_lift
    {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (s : B →+ A) (hs : ∀ b, q (s b) = b)
    (κB : M → M → B) (hcoc : IsPromotionCocycle κB) :
    IsCompensatorLift q (observedCompensator s κB) κB ∧
      IsPromotionCocycle (observedCompensator s κB) := by
  constructor
  · intro a b
    exact hs _
  · intro a b c
    rw [promotionAssociator_observed, hcoc a b c, map_zero]

/-! ## A finite nonliftable coefficient cell -/

/-- Reduction from the fine coefficient group `ZMod 4` to `ZMod 2`. -/
def quotientModTwo : ZMod 4 →+ ZMod 2 :=
  (ZMod.castHom (⟨2, rfl⟩ : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

/-- The asymmetric coarse cross-parity cocycle on `(ZMod 2)^2`. -/
def crossParityCarry (x y : ZMod 2 × ZMod 2) : ZMod 2 := x.1 * y.2

/-- Its binary-digit lift to `ZMod 4`. -/
def crossParityDigitLift (x y : ZMod 2 × ZMod 2) : ZMod 4 :=
  (crossParityCarry x y).val

theorem crossParityCarry_cocycle (x y z : ZMod 2 × ZMod 2) :
    PromotionAssociator crossParityCarry x y z = 0 := by
  apply (promotionAssociator_eq_zero_iff_cocycle crossParityCarry x y z).2
  simp [crossParityCarry]
  ring

theorem crossParityDigitLift_maps (x y : ZMod 2 × ZMod 2) :
    quotientModTwo (crossParityDigitLift x y) = crossParityCarry x y := by
  simp [quotientModTwo, crossParityDigitLift]

def parityE1 : ZMod 2 × ZMod 2 := (1, 0)
def parityE2 : ZMod 2 × ZMod 2 := (0, 1)

/-- The canonical fine lift already exposes a nonzero ternary defect. -/
theorem crossParityDigitLift_associator_witness :
    PromotionAssociator crossParityDigitLift parityE1 parityE2 parityE2 = 2 := by
  have he12 : parityE1 + parityE2 = (1, 1) := by
    ext <;> simp [parityE1, parityE2]
  have he22 : parityE2 + parityE2 = 0 := by
    apply Prod.ext
    · simp [parityE2]
    · exact ZMod.natCast_self 2
  simp only [PromotionAssociator]
  rw [he12, he22]
  simp [crossParityDigitLift, crossParityCarry, parityE1, parityE2]
  change (1 : ZMod 4) + 1 = 2
  rfl

/-- For a cocycle, commuting an order-two input with any other input has two-torsion defect. -/
theorem cocycle_commutator_two_torsion
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (κ : G → G → A) (x y : G)
    (hx : x + x = 0)
    (hcoc : ∀ a b c, PromotionAssociator κ a b c = 0) :
    2 • (κ x y - κ y x) = 0 := by
  have h0l : κ 0 0 = κ 0 y := by
    have h := (promotionAssociator_eq_zero_iff_cocycle κ 0 0 y).1 (hcoc 0 0 y)
    simpa using h
  have h0r : κ y 0 = κ 0 0 := by
    have h := (promotionAssociator_eq_zero_iff_cocycle κ y 0 0).1 (hcoc y 0 0)
    simpa using h
  have hA := (promotionAssociator_eq_zero_iff_cocycle κ x x y).1 (hcoc x x y)
  have hB := (promotionAssociator_eq_zero_iff_cocycle κ x y x).1 (hcoc x y x)
  have hC := (promotionAssociator_eq_zero_iff_cocycle κ y x x).1 (hcoc y x x)
  rw [hx, ← h0l] at hA
  rw [add_comm y x] at hB
  rw [add_comm y x, hx, h0r] at hC
  have hA' : κ x (x + y) = κ x x + κ 0 0 - κ x y := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hA.symm
  have hC' : κ (x + y) x = κ x x + κ 0 0 - κ y x := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hC
  rw [hA', hC'] at hB
  have hdiff :
      (κ x y + (κ x x + κ 0 0 - κ y x)) -
          (κ y x + (κ x x + κ 0 0 - κ x y)) = 0 :=
    sub_eq_zero.mpr hB
  rw [two_nsmul]
  calc
    (κ x y - κ y x) + (κ x y - κ y x) =
        (κ x y + (κ x x + κ 0 0 - κ y x)) -
          (κ y x + (κ x x + κ 0 0 - κ x y)) := by abel
    _ = 0 := hdiff

theorem quotientModTwo_eq_one_implies_two_mul_eq_two (a : ZMod 4)
    (ha : quotientModTwo a = 1) : 2 * a = 2 := by
  rw [show a = (a.val : ZMod 4) from (ZMod.natCast_zmod_val a).symm]
  have hodd : Odd a.val := by
    apply ZMod.natCast_eq_one_iff_odd.mp
    simpa [quotientModTwo, ZMod.castHom_apply] using ha
  obtain ⟨k, hk⟩ := hodd
  have hlt := a.val_lt
  have hval : a.val = 1 ∨ a.val = 3 := by omega
  rcases hval with h | h
  · rw [h]
    simp
  · rw [h]
    change (6 : ZMod 4) = 2
    calc
      (6 : ZMod 4) = 4 + 2 := by ring
      _ = 0 + 2 := by rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4]
      _ = 2 := zero_add 2

theorem zmodFour_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  intro hzero
  have hdiv := (ZMod.natCast_eq_zero_iff 2 4).mp hzero
  omega

/-- A linear two-term coefficient complex exhibits the same nonliftability. -/
theorem linearCoefficientLift_no_closed :
    ¬ ∃ a : ZMod 4, quotientModTwo a = 1 ∧ 2 * a = 0 := by
  rintro ⟨a, ha, hclosed⟩
  have htwo := quotientModTwo_eq_one_implies_two_mul_eq_two a ha
  rw [hclosed] at htwo
  exact zmodFour_two_ne_zero htwo.symm

/-- **Nonzero transgression.**  No fine `ZMod 4` cocycle lifts the coarse cross-parity law. -/
theorem crossParityCarry_no_cocycle_lift :
    ¬ ∃ κ : (ZMod 2 × ZMod 2) → (ZMod 2 × ZMod 2) → ZMod 4,
      (∀ x y, quotientModTwo (κ x y) = crossParityCarry x y) ∧
      ∀ x y z, PromotionAssociator κ x y z = 0 := by
  rintro ⟨κ, hlift, hcoc⟩
  have he1 : parityE1 + parityE1 = 0 := by
    apply Prod.ext
    · exact ZMod.natCast_self 2
    · simp [parityE1]
  have htors := cocycle_commutator_two_torsion κ parityE1 parityE2 he1 hcoc
  have hquot : quotientModTwo (κ parityE1 parityE2 - κ parityE2 parityE1) = 1 := by
    rw [map_sub, hlift, hlift]
    simp [crossParityCarry, parityE1, parityE2]
  have htwo := quotientModTwo_eq_one_implies_two_mul_eq_two _ hquot
  rw [two_nsmul] at htors
  rw [two_mul, htors] at htwo
  exact zmodFour_two_ne_zero htwo.symm

/-- Unconditional closed capstone: coarse closure, explicit higher birth, impossibility of every
strict fine lift, and an independent linear no-lift cell. -/
theorem coefficientLiftHigherBirth_closed :
    (∀ x y z, PromotionAssociator crossParityCarry x y z = 0) ∧
    quotientModTwo (crossParityDigitLift parityE1 parityE2) =
      crossParityCarry parityE1 parityE2 ∧
    PromotionAssociator crossParityDigitLift parityE1 parityE2 parityE2 = 2 ∧
    (¬ ∃ κ : (ZMod 2 × ZMod 2) → (ZMod 2 × ZMod 2) → ZMod 4,
      (∀ x y, quotientModTwo (κ x y) = crossParityCarry x y) ∧
      ∀ x y z, PromotionAssociator κ x y z = 0) ∧
    (¬ ∃ a : ZMod 4, quotientModTwo a = 1 ∧ 2 * a = 0) := by
  exact ⟨crossParityCarry_cocycle,
    crossParityDigitLift_maps _ _, crossParityDigitLift_associator_witness,
    crossParityCarry_no_cocycle_lift, linearCoefficientLift_no_closed⟩

end GaloisForLFunctions.HTGeometry
