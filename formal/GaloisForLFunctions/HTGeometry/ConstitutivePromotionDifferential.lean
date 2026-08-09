import GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion

/-!
# Promotion differential

A binary compensator closes as an associative central promotion exactly when its associator
residual vanishes.  Otherwise that residual is a coherent ternary law satisfying the pentagon
identity.  Unary gauge recalibration leaves the residual unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Binary compensation on an additive base, promoted into a central coefficient coordinate. -/
def promotedBinary {M : Type u} {A : Type v} [Add M] [Add A]
    (κ : M → M → A) : (M × A) → (M × A) → (M × A) :=
  fun p q => (p.1 + q.1, p.2 + q.2 + κ p.1 q.1)

/-- Exact residual between the two schedules for three promoted binary operations. -/
def PromotionAssociator {M : Type u} {A : Type v} [Add M] [AddGroup A]
    (κ : M → M → A) (x y z : M) : A :=
  κ x y + κ (x + y) z - κ y z - κ x (y + z)

theorem promotionAssociator_eq_zero_iff_cocycle
    {M : Type u} {A : Type v} [Add M] [AddCommGroup A]
    (κ : M → M → A) (x y z : M) :
    PromotionAssociator κ x y z = 0 ↔
      κ x y + κ (x + y) z = κ y z + κ x (y + z) := by
  simp only [PromotionAssociator]
  constructor
  · intro h
    have h' := congrArg (fun t => t + κ y z + κ x (y + z)) h
    abel_nf at h'
    exact h'
  · intro h
    rw [h]
    abel

theorem promotedBinary_associator_second
    {M : Type u} {A : Type v} [Add M] [AddCommGroup A]
    (κ : M → M → A) (x y z : M) (a b c : A) :
    (promotedBinary κ (promotedBinary κ (x, a) (y, b)) (z, c)).2 -
        (promotedBinary κ (x, a) (promotedBinary κ (y, b) (z, c))).2 =
      PromotionAssociator κ x y z := by
  simp only [promotedBinary, PromotionAssociator]
  abel

/-- Central promotion closes precisely when the promotion differential vanishes. -/
theorem promotedBinary_associative_iff_associator_zero
    {M : Type u} {A : Type v} [AddMonoid M] [AddCommGroup A]
    (κ : M → M → A) :
    (∀ p q s,
      promotedBinary κ (promotedBinary κ p q) s =
        promotedBinary κ p (promotedBinary κ q s)) ↔
      ∀ x y z, PromotionAssociator κ x y z = 0 := by
  constructor
  · intro hassoc x y z
    have hpairs := hassoc (x, 0) (y, 0) (z, 0)
    have hsecond := congrArg Prod.snd hpairs
    have hzero :
        (promotedBinary κ (promotedBinary κ (x, 0) (y, 0)) (z, 0)).2 -
            (promotedBinary κ (x, 0) (promotedBinary κ (y, 0) (z, 0))).2 = 0 :=
      sub_eq_zero.mpr hsecond
    rw [promotedBinary_associator_second] at hzero
    exact hzero
  · intro hzero p q s
    rcases p with ⟨x, a⟩
    rcases q with ⟨y, b⟩
    rcases s with ⟨z, c⟩
    apply Prod.ext
    · exact add_assoc x y z
    · apply sub_eq_zero.mp
      rw [promotedBinary_associator_second]
      exact hzero x y z

/-- The associator born from every binary compensator automatically satisfies the next pentagon
coherence law. -/
theorem promotionAssociator_pentagon
    {M : Type u} {A : Type v} [AddSemigroup M] [AddCommGroup A]
    (κ : M → M → A) (w x y z : M) :
    PromotionAssociator κ w x y +
          PromotionAssociator κ w (x + y) z +
          PromotionAssociator κ x y z =
      PromotionAssociator κ (w + x) y z +
        PromotionAssociator κ w x (y + z) := by
  simp only [PromotionAssociator, add_assoc]
  abel

/-- Unary recalibration of a binary compensator. -/
def promotionGaugeCoboundary {M : Type u} {A : Type v} [Add M] [AddGroup A]
    (b : M → A) (x y : M) : A :=
  b x + b y - b (x + y)

def gaugePromotedCompensator {M : Type u} {A : Type v} [Add M] [AddGroup A]
    (κ : M → M → A) (b : M → A) (x y : M) : A :=
  κ x y + promotionGaugeCoboundary b x y

/-- Promotion differential is invariant under unary splitting changes. -/
theorem promotionAssociator_gauge_invariant
    {M : Type u} {A : Type v} [AddSemigroup M] [AddCommGroup A]
    (κ : M → M → A) (b : M → A) (x y z : M) :
    PromotionAssociator (gaugePromotedCompensator κ b) x y z =
      PromotionAssociator κ x y z := by
  simp only [PromotionAssociator, gaugePromotedCompensator,
    promotionGaugeCoboundary, add_assoc]
  abel

theorem exchangeCarry_promotionAssociator_zero (u v w : ℤ × ℤ) :
    PromotionAssociator exchangeCarry u v w = 0 := by
  apply (promotionAssociator_eq_zero_iff_cocycle exchangeCarry u v w).2
  exact exchangeCarry_cocycle u v w

theorem exchangeCarry_promotedBinary_associative :
    ∀ p q s : (ℤ × ℤ) × ℤ,
      promotedBinary exchangeCarry (promotedBinary exchangeCarry p q) s =
        promotedBinary exchangeCarry p (promotedBinary exchangeCarry q s) := by
  exact (promotedBinary_associative_iff_associator_zero exchangeCarry).2
    exchangeCarry_promotionAssociator_zero

/-- A compensator whose binary promotion necessarily births a nonzero ternary associator. -/
def cubicPromotionCarry (x y : ℤ) : ℤ := x * x * y

theorem cubicPromotionCarry_associator_formula (x y z : ℤ) :
    PromotionAssociator cubicPromotionCarry x y z = 2 * x * y * z := by
  simp only [PromotionAssociator, cubicPromotionCarry]
  ring

theorem cubicPromotionCarry_associator_nonzero :
    PromotionAssociator cubicPromotionCarry 1 1 1 ≠ 0 := by
  rw [cubicPromotionCarry_associator_formula]
  simpa only [mul_one] using (two_ne_zero : (2 : ℤ) ≠ 0)

theorem cubicPromotionCarry_promotedBinary_not_associative :
    ¬ ∀ p q s : ℤ × ℤ,
      promotedBinary cubicPromotionCarry (promotedBinary cubicPromotionCarry p q) s =
        promotedBinary cubicPromotionCarry p (promotedBinary cubicPromotionCarry q s) := by
  intro hassoc
  have hzero :=
    (promotedBinary_associative_iff_associator_zero cubicPromotionCarry).1 hassoc 1 1 1
  exact cubicPromotionCarry_associator_nonzero hzero

theorem constitutivePromotionDifferentialMechanism_closed :
    ((∀ p q s : (ℤ × ℤ) × ℤ,
      promotedBinary exchangeCarry (promotedBinary exchangeCarry p q) s =
        promotedBinary exchangeCarry p (promotedBinary exchangeCarry q s)) ∧
    (¬ ∀ p q s : ℤ × ℤ,
      promotedBinary cubicPromotionCarry (promotedBinary cubicPromotionCarry p q) s =
        promotedBinary cubicPromotionCarry p (promotedBinary cubicPromotionCarry q s)) ∧
    (∀ w x y z : ℤ,
      PromotionAssociator cubicPromotionCarry w x y +
            PromotionAssociator cubicPromotionCarry w (x + y) z +
            PromotionAssociator cubicPromotionCarry x y z =
        PromotionAssociator cubicPromotionCarry (w + x) y z +
          PromotionAssociator cubicPromotionCarry w x (y + z))) := by
  exact ⟨exchangeCarry_promotedBinary_associative,
    cubicPromotionCarry_promotedBinary_not_associative,
    promotionAssociator_pentagon cubicPromotionCarry⟩

end GaloisForLFunctions.HTGeometry
