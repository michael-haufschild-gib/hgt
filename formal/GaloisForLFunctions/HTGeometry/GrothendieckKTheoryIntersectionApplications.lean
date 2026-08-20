import GaloisForLFunctions.HTGeometry.BiprojectiveChowRing
import GaloisForLFunctions.HTGeometry.MilnorWittCycles
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Grothendieck completion, K-theory, GRR, and intersection-theory applications

Mechanical applications of group completion to effective bidegrees and finitely supported cycles,
followed by the complete intersection-theory and GRR calculation for line bundles on `P¹ × P¹`.
-/

namespace GaloisForLFunctions.HTGeometry

open Algebra

attribute [local instance] Ideal.Quotient.field Classical.propDecidable

/-! ## Grothendieck completion of effective bidegrees -/

/-- Effective divisor bidegrees on `P¹ × P¹`. -/
abbrev P1xP1EffectiveBidegree := ℕ × ℕ

/-- Integral divisor bidegrees on `P¹ × P¹`. -/
abbrev P1xP1Bidegree := ℤ × ℤ

/-- Canonical inclusion of effective bidegrees into integral bidegrees. -/
def effectiveBidegreeToIntegral : P1xP1EffectiveBidegree →+ P1xP1Bidegree where
  toFun d := (d.1, d.2)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Abstract Grothendieck group of effective bidegrees. -/
abbrev P1xP1DivisorK0 := GrothendieckAddGroup P1xP1EffectiveBidegree

/-- Canonical class map from abstract completion to divisor lattice. -/
noncomputable def p1xp1DivisorK0Class : P1xP1DivisorK0 →+ P1xP1Bidegree :=
  GrothendieckAddGroup.lift effectiveBidegreeToIntegral

theorem p1xp1DivisorK0Class_of (d : P1xP1EffectiveBidegree) :
    p1xp1DivisorK0Class (GrothendieckAddGroup.of d) = effectiveBidegreeToIntegral d := by
  change ((GrothendieckAddGroup.lift
    (M := P1xP1EffectiveBidegree) (G := P1xP1Bidegree)).symm
      (GrothendieckAddGroup.lift effectiveBidegreeToIntegral)) d =
        effectiveBidegreeToIntegral d
  rw [Equiv.symm_apply_apply]

/-- Integral bidegrees as formal differences of effective ruling classes. -/
def integralBidegreeToDivisorK0 : P1xP1Bidegree →+ P1xP1DivisorK0 :=
  ((zmultiplesHom _ (GrothendieckAddGroup.of (1, 0))).comp
      (AddMonoidHom.fst ℤ ℤ)) +
    ((zmultiplesHom _ (GrothendieckAddGroup.of (0, 1))).comp
      (AddMonoidHom.snd ℤ ℤ))

theorem p1xp1DivisorK0Class_rightInverse (d : P1xP1Bidegree) :
    p1xp1DivisorK0Class (integralBidegreeToDivisorK0 d) = d := by
  rcases d with ⟨a, b⟩
  simp [integralBidegreeToDivisorK0]
  change a • p1xp1DivisorK0Class (GrothendieckAddGroup.of (1, 0)) +
    b • p1xp1DivisorK0Class (GrothendieckAddGroup.of (0, 1)) = (a, b)
  rw [p1xp1DivisorK0Class_of, p1xp1DivisorK0Class_of]
  ext <;> simp [effectiveBidegreeToIntegral]

theorem p1xp1DivisorK0Class_leftInverse (x : P1xP1DivisorK0) :
    integralBidegreeToDivisorK0 (p1xp1DivisorK0Class x) = x := by
  have hhom : integralBidegreeToDivisorK0.comp p1xp1DivisorK0Class =
      AddMonoidHom.id P1xP1DivisorK0 := by
    apply (GrothendieckAddGroup.lift
      (M := P1xP1EffectiveBidegree) (G := P1xP1DivisorK0)).symm.injective
    ext d
    rcases d with ⟨m, n⟩
    change (p1xp1DivisorK0Class (GrothendieckAddGroup.of (m, n))).1 •
        GrothendieckAddGroup.of (1, 0) +
      (p1xp1DivisorK0Class (GrothendieckAddGroup.of (m, n))).2 •
        GrothendieckAddGroup.of (0, 1) = GrothendieckAddGroup.of (m, n)
    rw [p1xp1DivisorK0Class_of]
    simp [effectiveBidegreeToIntegral, ← map_nsmul, ← map_add]
  exact DFunLike.congr_fun hhom x

/-- Grothendieck completion identifies effective bidegrees with divisor lattice `ℤ²`. -/
noncomputable def p1xp1DivisorK0Equiv : P1xP1DivisorK0 ≃+ P1xP1Bidegree where
  toFun := p1xp1DivisorK0Class
  invFun := integralBidegreeToDivisorK0
  left_inv := p1xp1DivisorK0Class_leftInverse
  right_inv := p1xp1DivisorK0Class_rightInverse
  map_add' := map_add p1xp1DivisorK0Class

/-! ## One-generator completion used by monoid Hopf envelopes -/

/-- Grothendieck group of natural multiplicities. -/
abbrev NaturalMultiplicityK0 := GrothendieckAddGroup ℕ

/-- Signed multiplicity of an abstract natural-multiplicity K-zero class. -/
noncomputable def naturalMultiplicityK0Class : NaturalMultiplicityK0 →+ ℤ :=
  GrothendieckAddGroup.lift (Nat.castAddMonoidHom ℤ)

theorem naturalMultiplicityK0Class_of (n : ℕ) :
    naturalMultiplicityK0Class (GrothendieckAddGroup.of n) = (n : ℤ) := by
  change ((GrothendieckAddGroup.lift (M := ℕ) (G := ℤ)).symm
    (GrothendieckAddGroup.lift (Nat.castAddMonoidHom ℤ))) n = (n : ℤ)
  rw [Equiv.symm_apply_apply]
  rfl

/-- Signed multiplicity represented inside abstract completion. -/
def integerToNaturalMultiplicityK0 : ℤ →+ NaturalMultiplicityK0 :=
  zmultiplesHom _ (GrothendieckAddGroup.of 1)

theorem naturalMultiplicityK0Class_rightInverse (n : ℤ) :
    naturalMultiplicityK0Class (integerToNaturalMultiplicityK0 n) = n := by
  simp [integerToNaturalMultiplicityK0]
  change n • naturalMultiplicityK0Class (GrothendieckAddGroup.of 1) = n
  rw [naturalMultiplicityK0Class_of]
  simp

theorem naturalMultiplicityK0Class_leftInverse (x : NaturalMultiplicityK0) :
    integerToNaturalMultiplicityK0 (naturalMultiplicityK0Class x) = x := by
  have hhom : integerToNaturalMultiplicityK0.comp naturalMultiplicityK0Class =
      AddMonoidHom.id NaturalMultiplicityK0 := by
    apply (GrothendieckAddGroup.lift (M := ℕ) (G := NaturalMultiplicityK0)).symm.injective
    apply AddMonoidHom.ext_nat
    change integerToNaturalMultiplicityK0
      (naturalMultiplicityK0Class (GrothendieckAddGroup.of 1)) =
        GrothendieckAddGroup.of 1
    rw [naturalMultiplicityK0Class_of]
    simp [integerToNaturalMultiplicityK0]
  exact DFunLike.congr_fun hhom x

/-- Canonical completion `K₀(ℕ) ≃ ℤ`, underlying Laurent/Hopf exponent passage. -/
noncomputable def naturalMultiplicityK0EquivInt : NaturalMultiplicityK0 ≃+ ℤ where
  toFun := naturalMultiplicityK0Class
  invFun := integerToNaturalMultiplicityK0
  left_inv := naturalMultiplicityK0Class_leftInverse
  right_inv := naturalMultiplicityK0Class_rightInverse
  map_add' := map_add naturalMultiplicityK0Class

/-! ## Divisor classes and intersection theory -/

/-- Chow class of divisor of integral bidegree `(a,b)` on `P¹ × P¹`. -/
noncomputable def p1xp1DivisorClass (a b : ℤ) : ChowProd 1 1 :=
  (a : ChowProd 1 1) * chowH₁ 1 1 + (b : ChowProd 1 1) * chowH₂ 1 1

theorem p1xp1_chowH₁_sq : chowH₁ 1 1 ^ 2 = 0 :=
  chowH₁_pow_eq_zero (by omega)

theorem p1xp1_chowH₂_sq : chowH₂ 1 1 ^ 2 = 0 :=
  chowH₂_pow_eq_zero (by omega)

/-- Top intersection of `m+n` equal divisors of bidegree `(a,b)` on `P^m × P^n`. -/
theorem chow_bidegree_divisor_pow (m n : ℕ) (a b : ℤ) :
    ((a : ChowProd m n) * chowH₁ m n + (b : ChowProd m n) * chowH₂ m n) ^ (m + n) =
      (((Nat.choose (m + n) m : ℤ) * a ^ m * b ^ n : ℤ) : ChowProd m n) *
        chowTop m n := by
  rw [add_pow, Finset.sum_eq_single m]
  · rw [Nat.add_sub_cancel_left]
    simp [mul_pow, chowTop]
    ring
  · intro k hk hkm
    rcases lt_or_gt_of_ne hkm with h | h
    · rw [Finset.mem_range] at hk
      rw [mul_pow, mul_pow,
        chowH₂_pow_eq_zero (m := m) (n := n) (k := m + n - k) (by omega)]
      simp
    · rw [mul_pow, chowH₁_pow_eq_zero (m := m) (n := n) (k := k) h]
      simp
  · intro hm
    exact absurd (Finset.mem_range.2 (by omega)) hm

/-- Intersection pairing on `P¹ × P¹`: `(a,b)·(c,d) = ad + bc`. -/
theorem p1xp1_divisor_intersection (a b c d : ℤ) :
    p1xp1DivisorClass a b * p1xp1DivisorClass c d =
      ((a * d + b * c : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  rw [p1xp1DivisorClass, p1xp1DivisorClass]
  ring_nf
  rw [p1xp1_chowH₁_sq, p1xp1_chowH₂_sq]
  simp [chowTop]
  ring

/-- Self-intersection of bidegree `(a,b)` is `2ab`. -/
theorem p1xp1_divisor_self_intersection (a b : ℤ) :
    p1xp1DivisorClass a b ^ 2 =
      ((2 * a * b : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  rw [pow_two, p1xp1_divisor_intersection]
  push_cast
  ring

/-- Canonical divisor class of `P¹ × P¹`. -/
noncomputable def p1xp1CanonicalClass : ChowProd 1 1 := p1xp1DivisorClass (-2) (-2)

/-- Adjunction intersection identity for a bidegree `(a,b)` divisor. -/
theorem p1xp1_adjunction_intersection (a b : ℤ) :
    p1xp1DivisorClass a b * (p1xp1DivisorClass a b + p1xp1CanonicalClass) =
      ((2 * ((a - 1) * (b - 1) - 1) : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  rw [p1xp1CanonicalClass]
  rw [show p1xp1DivisorClass a b + p1xp1DivisorClass (-2) (-2) =
      p1xp1DivisorClass (a - 2) (b - 2) by
    simp [p1xp1DivisorClass]
    ring]
  rw [p1xp1_divisor_intersection]
  push_cast
  ring

/-- Doubled surface Riemann--Roch correction `D·(D-K)`. -/
theorem p1xp1_riemannRoch_intersection (a b : ℤ) :
    p1xp1DivisorClass a b * (p1xp1DivisorClass a b - p1xp1CanonicalClass) =
      ((2 * ((a + 1) * (b + 1) - 1) : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  rw [p1xp1CanonicalClass]
  rw [show p1xp1DivisorClass a b - p1xp1DivisorClass (-2) (-2) =
      p1xp1DivisorClass (a + 2) (b + 2) by
    simp [p1xp1DivisorClass]
    ring]
  rw [p1xp1_divisor_intersection]
  push_cast
  ring

/-! ## GRR on projective lines and planes -/

/-- Chow ring of the projective line, represented as `P¹ × P⁰`. -/
abbrev P1Chow := ChowProd 1 0

/-- Hyperplane class on `P¹`. -/
noncomputable def p1Hyperplane : P1Chow := chowH₁ 1 0

theorem p1Hyperplane_sq : p1Hyperplane ^ 2 = 0 :=
  chowH₁_pow_eq_zero (by omega)

/-- Chern character of `O(d)` in the integral Chow ring of `P¹`. -/
noncomputable def p1LineChernCharacter (d : ℤ) : P1Chow :=
  1 + (d : P1Chow) * p1Hyperplane

/-- Todd class of `P¹`. -/
noncomputable def p1ToddClass : P1Chow := 1 + p1Hyperplane

/-- GRR for `O(d)` on `P¹`: the top component is `χ(O(d)) = d + 1`. -/
theorem p1_grr_lineBundle (d : ℤ) :
    p1LineChernCharacter d * p1ToddClass =
      1 + ((d + 1 : ℤ) : P1Chow) * p1Hyperplane := by
  simp only [p1LineChernCharacter, p1ToddClass]
  ring_nf
  rw [p1Hyperplane_sq]
  simp
  ring

/-- Chow ring of the projective plane, represented as `P² × P⁰`. -/
abbrev P2Chow := ChowProd 2 0

/-- Hyperplane class on `P²`. -/
noncomputable def p2Hyperplane : P2Chow := chowH₁ 2 0

theorem p2Hyperplane_cube : p2Hyperplane ^ 3 = 0 :=
  chowH₁_pow_eq_zero (by omega)

theorem p2Hyperplane_fourth : p2Hyperplane ^ 4 = 0 :=
  chowH₁_pow_eq_zero (by omega)

/-- Twice the Chern character of `O(d)` on `P²`, clearing its denominator. -/
noncomputable def p2TwiceLineChernCharacter (d : ℤ) : P2Chow :=
  2 + ((2 * d : ℤ) : P2Chow) * p2Hyperplane +
    ((d ^ 2 : ℤ) : P2Chow) * p2Hyperplane ^ 2

/-- Twice the Todd class of `P²`, clearing its denominator. -/
noncomputable def p2TwiceToddClass : P2Chow :=
  2 + (3 : P2Chow) * p2Hyperplane + 2 * p2Hyperplane ^ 2

/-- Denominator-cleared GRR for `O(d)` on `P²`.
The top component is `4χ(O(d)) = 2(d+1)(d+2)`. -/
theorem p2_grr_fourfold_lineBundle (d : ℤ) :
    p2TwiceLineChernCharacter d * p2TwiceToddClass =
      4 + ((4 * d + 6 : ℤ) : P2Chow) * p2Hyperplane +
        ((2 * (d + 1) * (d + 2) : ℤ) : P2Chow) * p2Hyperplane ^ 2 := by
  simp only [p2TwiceLineChernCharacter, p2TwiceToddClass]
  ring_nf
  rw [p2Hyperplane_cube, p2Hyperplane_fourth]
  simp
  ring

/-! ## K-theory Chern character and GRR on `P¹ × P¹` -/

/-- Integral truncated Chern character of line-bundle class `O(a,b)`. -/
noncomputable def p1xp1LineChernCharacter (a b : ℤ) : ChowProd 1 1 :=
  1 + p1xp1DivisorClass a b + ((a * b : ℤ) : ChowProd 1 1) * chowTop 1 1

/-- Todd class of `P¹ × P¹`. -/
noncomputable def p1xp1ToddClass : ChowProd 1 1 :=
  1 + chowH₁ 1 1 + chowH₂ 1 1 + chowTop 1 1

/-- Chern character is multiplicative under tensor product of line bundles. -/
theorem p1xp1_lineChernCharacter_tensor (a b c d : ℤ) :
    p1xp1LineChernCharacter (a + c) (b + d) =
      p1xp1LineChernCharacter a b * p1xp1LineChernCharacter c d := by
  simp only [p1xp1LineChernCharacter, p1xp1DivisorClass, chowTop]
  ring_nf
  rw [p1xp1_chowH₁_sq, p1xp1_chowH₂_sq]
  simp
  ring

/-- GRR for `O(a,b)` pushed to point: top component is `(a+1)(b+1)`. -/
theorem p1xp1_grr_lineBundle (a b : ℤ) :
    p1xp1LineChernCharacter a b * p1xp1ToddClass =
      1 + p1xp1DivisorClass (a + 1) (b + 1) +
        (((a + 1) * (b + 1) : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  simp only [p1xp1LineChernCharacter, p1xp1ToddClass, p1xp1DivisorClass, chowTop]
  ring_nf
  rw [p1xp1_chowH₁_sq, p1xp1_chowH₂_sq]
  simp
  ring

/-- Chern character of virtual line-bundle difference in `K₀`. -/
noncomputable def p1xp1VirtualChernCharacter (a b c d : ℤ) : ChowProd 1 1 :=
  p1xp1LineChernCharacter a b - p1xp1LineChernCharacter c d

/-- Euler characteristic of virtual class `[O(a,b)] - [O(c,d)]`. -/
def p1xp1VirtualEulerCharacteristic (a b c d : ℤ) : ℤ :=
  (a + 1) * (b + 1) - (c + 1) * (d + 1)

/-- GRR is additive on virtual `K₀` differences. -/
theorem p1xp1_grr_virtualLineBundle (a b c d : ℤ) :
    p1xp1VirtualChernCharacter a b c d * p1xp1ToddClass =
      p1xp1DivisorClass (a - c) (b - d) +
        (p1xp1VirtualEulerCharacteristic a b c d : ChowProd 1 1) * chowTop 1 1 := by
  rw [p1xp1VirtualChernCharacter, sub_mul,
    p1xp1_grr_lineBundle, p1xp1_grr_lineBundle]
  simp [p1xp1DivisorClass, p1xp1VirtualEulerCharacteristic]
  ring

/-! ## Grothendieck completion of effective finitely supported cycles -/

/-- Effective finitely supported cycles included into integral cycles. -/
noncomputable def effectiveFinsuppToIntegral (α : Type*) : (α →₀ ℕ) →+ (α →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom Int.ofNatHom.toAddMonoidHom

/-- Extension of an effective-cycle invariant to virtual integral cycles. -/
noncomputable def integralFinsuppLift {α G : Type*} [AddCommGroup G]
    (φ : (α →₀ ℕ) →+ G) : (α →₀ ℤ) →+ G :=
  Finsupp.liftAddHom fun i => zmultiplesHom G (φ (Finsupp.single i 1))

theorem integralFinsuppLift_comp_effective {α G : Type*} [AddCommGroup G]
    (φ : (α →₀ ℕ) →+ G) :
    (integralFinsuppLift φ).comp (effectiveFinsuppToIntegral α) = φ := by
  apply (Finsupp.liftAddHom (α := α) (M := ℕ) (N := G)).symm.injective
  funext i
  apply AddMonoidHom.ext_nat
  simp [integralFinsuppLift, effectiveFinsuppToIntegral]

/-- Homomorphisms out of integral cycles are determined by effective cycles. -/
theorem integralFinsuppHom_ext {α G : Type*} [AddCommGroup G]
    {f g : (α →₀ ℤ) →+ G}
    (h : f.comp (effectiveFinsuppToIntegral α) =
      g.comp (effectiveFinsuppToIntegral α)) : f = g := by
  apply (Finsupp.liftAddHom (α := α) (M := ℤ) (N := G)).symm.injective
  funext i
  apply AddMonoidHom.ext_int
  have hi := DFunLike.congr_fun h (Finsupp.single i 1)
  simpa [effectiveFinsuppToIntegral] using hi

/-- Integral finitely supported cycles satisfy universal property of group completion. -/
theorem finsupp_integral_groupCompletion {α G : Type*} [AddCommGroup G]
    (φ : (α →₀ ℕ) →+ G) :
    ∃! ψ : (α →₀ ℤ) →+ G,
      ψ.comp (effectiveFinsuppToIntegral α) = φ := by
  refine ⟨integralFinsuppLift φ, integralFinsuppLift_comp_effective φ, ?_⟩
  intro ψ hψ
  apply integralFinsuppHom_ext
  rw [hψ, integralFinsuppLift_comp_effective]

/-- Abstract Grothendieck group of effective finitely supported cycles. -/
abbrev EffectiveFinsuppK0 (α : Type*) := GrothendieckAddGroup (α →₀ ℕ)

/-- Canonical virtual-cycle map out of abstract Grothendieck group. -/
noncomputable def effectiveFinsuppK0Class (α : Type*) :
    EffectiveFinsuppK0 α →+ (α →₀ ℤ) :=
  GrothendieckAddGroup.lift (effectiveFinsuppToIntegral α)

theorem effectiveFinsuppK0Class_of {α : Type*} (q : α →₀ ℕ) :
    effectiveFinsuppK0Class α (GrothendieckAddGroup.of q) =
      effectiveFinsuppToIntegral α q := by
  change ((GrothendieckAddGroup.lift
    (M := α →₀ ℕ) (G := α →₀ ℤ)).symm
      (GrothendieckAddGroup.lift (effectiveFinsuppToIntegral α))) q = _
  rw [Equiv.symm_apply_apply]

/-- Integral cycles represented as formal differences in abstract completion. -/
noncomputable def integralFinsuppToK0 (α : Type*) : (α →₀ ℤ) →+ EffectiveFinsuppK0 α :=
  integralFinsuppLift GrothendieckAddGroup.of

theorem integralFinsuppToK0_effective {α : Type*} (q : α →₀ ℕ) :
    integralFinsuppToK0 α (effectiveFinsuppToIntegral α q) =
      GrothendieckAddGroup.of q := by
  exact DFunLike.congr_fun
    (integralFinsuppLift_comp_effective (GrothendieckAddGroup.of :
      (α →₀ ℕ) →+ EffectiveFinsuppK0 α)) q

theorem effectiveFinsuppK0Class_rightInverse {α : Type*} (z : α →₀ ℤ) :
    effectiveFinsuppK0Class α (integralFinsuppToK0 α z) = z := by
  have hhom : (effectiveFinsuppK0Class α).comp (integralFinsuppToK0 α) =
      AddMonoidHom.id (α →₀ ℤ) := by
    apply integralFinsuppHom_ext
    apply AddMonoidHom.ext
    intro q
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      integralFinsuppToK0_effective, effectiveFinsuppK0Class_of]
    rfl
  exact DFunLike.congr_fun hhom z

theorem effectiveFinsuppK0Class_leftInverse {α : Type*}
    (x : EffectiveFinsuppK0 α) :
    integralFinsuppToK0 α (effectiveFinsuppK0Class α x) = x := by
  have hhom : (integralFinsuppToK0 α).comp (effectiveFinsuppK0Class α) =
      AddMonoidHom.id (EffectiveFinsuppK0 α) := by
    apply (GrothendieckAddGroup.lift
      (M := α →₀ ℕ) (G := EffectiveFinsuppK0 α)).symm.injective
    apply AddMonoidHom.ext
    intro q
    change integralFinsuppToK0 α
      (effectiveFinsuppK0Class α (GrothendieckAddGroup.of q)) =
        GrothendieckAddGroup.of q
    rw [effectiveFinsuppK0Class_of, integralFinsuppToK0_effective]
  exact DFunLike.congr_fun hhom x

/-- Grothendieck completion of effective cycles is integral cycle group. -/
noncomputable def effectiveFinsuppK0Equiv (α : Type*) :
    EffectiveFinsuppK0 α ≃+ (α →₀ ℤ) where
  toFun := effectiveFinsuppK0Class α
  invFun := integralFinsuppToK0 α
  left_inv := effectiveFinsuppK0Class_leftInverse
  right_inv := effectiveFinsuppK0Class_rightInverse
  map_add' := map_add (effectiveFinsuppK0Class α)

/-- Effective prime divisors. -/
abbrev EffectivePrimeDivisors := Nat.Primes →₀ ℕ

/-- Integral prime divisors. -/
abbrev PrimeDivisors := Nat.Primes →₀ ℤ

/-- K-zero of effective prime-divisor monoid. -/
abbrev PrimeDivisorK0 := EffectiveFinsuppK0 Nat.Primes

/-- Prime-divisor completion: virtual effective divisors are integer prime divisors. -/
noncomputable def primeDivisorK0Equiv : PrimeDivisorK0 ≃+ PrimeDivisors :=
  effectiveFinsuppK0Equiv Nat.Primes

/-- Degree of a finitely supported integral cycle. -/
noncomputable def integralFinsuppDegree (α : Type*) : (α →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

/-- Multiplicity of integral cycle at one index. -/
def integralFinsuppEvaluation {α : Type*} (i : α) : (α →₀ ℤ) →+ ℤ where
  toFun z := z i
  map_zero' := rfl
  map_add' _ _ := rfl

/-! ## Root and pole multisets as effective divisors -/

/-- Map on Grothendieck groups induced by an additive monoid homomorphism. -/
noncomputable def grothendieckAddGroupMap {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) :
    GrothendieckAddGroup M →+ GrothendieckAddGroup N :=
  GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp f)

theorem grothendieckAddGroupMap_of {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) (x : M) :
    grothendieckAddGroupMap f (GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of (f x) := by
  change ((GrothendieckAddGroup.lift
    (M := M) (G := GrothendieckAddGroup N)).symm
      (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp f))) x = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Additively equivalent monoids have equivalent Grothendieck groups. -/
noncomputable def grothendieckAddGroupCongr {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (e : M ≃+ N) :
    GrothendieckAddGroup M ≃+ GrothendieckAddGroup N where
  toFun := grothendieckAddGroupMap e.toAddMonoidHom
  invFun := grothendieckAddGroupMap e.symm.toAddMonoidHom
  left_inv x := by
    have hhom : (grothendieckAddGroupMap e.symm.toAddMonoidHom).comp
        (grothendieckAddGroupMap e.toAddMonoidHom) =
        AddMonoidHom.id (GrothendieckAddGroup M) := by
      apply (GrothendieckAddGroup.lift
        (M := M) (G := GrothendieckAddGroup M)).symm.injective
      apply AddMonoidHom.ext
      intro m
      change grothendieckAddGroupMap e.symm.toAddMonoidHom
          (grothendieckAddGroupMap e.toAddMonoidHom (GrothendieckAddGroup.of m)) =
        GrothendieckAddGroup.of m
      rw [grothendieckAddGroupMap_of, grothendieckAddGroupMap_of]
      congr 1
      exact e.symm_apply_apply m
    exact DFunLike.congr_fun hhom x
  right_inv y := by
    have hhom : (grothendieckAddGroupMap e.toAddMonoidHom).comp
        (grothendieckAddGroupMap e.symm.toAddMonoidHom) =
        AddMonoidHom.id (GrothendieckAddGroup N) := by
      apply (GrothendieckAddGroup.lift
        (M := N) (G := GrothendieckAddGroup N)).symm.injective
      apply AddMonoidHom.ext
      intro n
      change grothendieckAddGroupMap e.toAddMonoidHom
          (grothendieckAddGroupMap e.symm.toAddMonoidHom (GrothendieckAddGroup.of n)) =
        GrothendieckAddGroup.of n
      rw [grothendieckAddGroupMap_of, grothendieckAddGroupMap_of]
      congr 1
      exact e.apply_symm_apply n
    exact DFunLike.congr_fun hhom y
  map_add' := map_add (grothendieckAddGroupMap e.toAddMonoidHom)

/-- Grothendieck group of finite root or pole multisets. -/
abbrev RootDivisorK0 (α : Type*) := GrothendieckAddGroup (Multiset α)

/-- Multiplicity function of a root or pole multiset. -/
noncomputable def multisetMultiplicity {α : Type*} (s : Multiset α) : α →₀ ℕ := by
  classical
  exact Multiset.toFinsupp s

/-- Completion of root multisets is free integral divisor group on roots. -/
noncomputable def rootDivisorK0Equiv (α : Type*) : RootDivisorK0 α ≃+ (α →₀ ℤ) := by
  classical
  exact (grothendieckAddGroupCongr Multiset.toFinsupp).trans
    (effectiveFinsuppK0Equiv α)

/-- Effective root multiset maps to its integer multiplicity divisor. -/
theorem rootDivisorK0Equiv_of {α : Type*} (s : Multiset α) :
    rootDivisorK0Equiv α (GrothendieckAddGroup.of s) =
      effectiveFinsuppToIntegral α (multisetMultiplicity s) := by
  classical
  change effectiveFinsuppK0Class α
    (grothendieckAddGroupMap Multiset.toFinsupp.toAddMonoidHom
      (GrothendieckAddGroup.of s)) = _
  rw [grothendieckAddGroupMap_of, effectiveFinsuppK0Class_of]
  rfl

/-- Virtual root divisor is difference of multiplicity functions. -/
theorem rootDivisorK0Equiv_difference {α : Type*} (s t : Multiset α) :
    rootDivisorK0Equiv α (GrothendieckAddGroup.of s - GrothendieckAddGroup.of t) =
      effectiveFinsuppToIntegral α (multisetMultiplicity s) -
        effectiveFinsuppToIntegral α (multisetMultiplicity t) := by
  rw [map_sub, rootDivisorK0Equiv_of, rootDivisorK0Equiv_of]

/-- One root becomes corresponding unit divisor. -/
theorem rootDivisorK0Equiv_of_singleton {α : Type*} (z : α) :
    rootDivisorK0Equiv α (GrothendieckAddGroup.of ({z} : Multiset α)) =
      Finsupp.single z 1 := by
  classical
  rw [rootDivisorK0Equiv_of]
  change effectiveFinsuppToIntegral α (Multiset.toFinsupp ({z} : Multiset α)) = _
  rw [Multiset.toFinsupp_singleton]
  ext w
  simp [effectiveFinsuppToIntegral]

/-! ## Ordinary codimension-one cycles -/

/-- Effective codimension-one cycles on `Spec S`. -/
abbrev EffectiveCycles (S : Type*) [CommRing S] := ClosedPoint S →₀ ℕ

/-- K-zero of effective codimension-one cycles. -/
abbrev EffectiveCyclesK0 (S : Type*) [CommRing S] :=
  EffectiveFinsuppK0 (ClosedPoint S)

/-- Completion of effective codimension-one cycles is ordinary integral cycle group. -/
noncomputable def effectiveCyclesK0Equiv (S : Type*) [CommRing S] :
    EffectiveCyclesK0 S ≃+ Cycles S := by
  classical
  exact (effectiveFinsuppK0Equiv (ClosedPoint S)).trans finsuppAddEquivDFinsupp

/-- Effective point with multiplicity `n` becomes ordinary cycle `n[p]`. -/
theorem effectiveCyclesK0Equiv_of_single {S : Type*} [CommRing S]
    (p : ClosedPoint S) (n : ℕ) :
    effectiveCyclesK0Equiv S
        (GrothendieckAddGroup.of (Finsupp.single p n)) = cycleSingle p n := by
  classical
  change Finsupp.toDFinsupp
    (effectiveFinsuppK0Class (ClosedPoint S)
      (GrothendieckAddGroup.of (Finsupp.single p n))) = cycleSingle p n
  rw [effectiveFinsuppK0Class_of]
  simp [effectiveFinsuppToIntegral, cycleSingle, Finsupp.toDFinsupp_single]

/-- A signed point cycle is integer multiple of one completed effective generator. -/
theorem effectiveCyclesK0Equiv_symm_cycleSingle {S : Type*} [CommRing S]
    (p : ClosedPoint S) (n : ℤ) :
    (effectiveCyclesK0Equiv S).symm (cycleSingle p n) =
      n • GrothendieckAddGroup.of (Finsupp.single p 1) := by
  classical
  apply (effectiveCyclesK0Equiv S).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, effectiveCyclesK0Equiv_of_single]
  change cycleSingle p n = n • cycleSingle p 1
  rw [cycleSingle, cycleSingle, ← DFinsupp.single_smul]
  simp

/-- Milnor--Witt Gysin class forgets to signed multiple of universal point generator. -/
theorem effectiveCyclesK0Equiv_symm_mwCyclesRank_mwGysin
    {S : Type*} [CommRing S] (p : ClosedPoint S) (x : MWPointGroup p) :
    (effectiveCyclesK0Equiv S).symm (mwCyclesRank S (mwGysin p x)) =
      mwTwistRank x • GrothendieckAddGroup.of (Finsupp.single p 1) := by
  rw [mwCyclesRank_mwGysin, effectiveCyclesK0Equiv_symm_cycleSingle]

end GaloisForLFunctions.HTGeometry
