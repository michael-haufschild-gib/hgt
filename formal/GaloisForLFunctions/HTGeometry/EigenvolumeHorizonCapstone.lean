import GaloisForLFunctions.HTGeometry.PrimeDivisorPullbackOrder
import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# The eigenvolume horizon theorem for prime divisors

The abstract ramification system is instantiated here at the prime divisors of a normal Noetherian
domain carrying a self-map.  The order of a rational form is the difference of the orders of a
numerator and a denominator, its divisorial support is finite, and if the local order law holds at
every prime divisor with ramification somewhere on each recurrent cycle, then the order is exactly
`-1` on the whole support.

This is the conclusion of the eigenvolume horizon theorem in the local model: the horizon is a
reduced divisor, it is totally invariant, and the map is unramified off it.
-/

namespace GaloisForLFunctions.HTGeometry

variable {B : Type*}
variable [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

/-- The prime divisor below a prime divisor along a self-map. -/
def divisorBelow (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
    (P : PrimeDivisor B) : PrimeDivisor B :=
  ⟨Ideal.comap φ P.1, Ideal.IsPrime.comap _, hwd P⟩

omit [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] in
@[simp] theorem divisorBelow_val (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1) (P : PrimeDivisor B) :
    (divisorBelow φ hwd P).1 = Ideal.comap φ P.1 :=
  rfl

/-- Integer order of the rational form `a / b` along a prime divisor. -/
noncomputable def formOrder (a b : B) (P : PrimeDivisor B) : ℤ :=
  ((orderAt P a).toNat : ℤ) - ((orderAt P b).toNat : ℤ)

theorem formOrder_ne_zero_imp (a b : B) {P : PrimeDivisor B} (hP : formOrder a b P ≠ 0) :
    orderAt P a ≠ 0 ∨ orderAt P b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hP (by simp [formOrder, h1, h2])

/-- **The divisorial support of a rational form is finite.** -/
theorem finite_formOrder_support {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    {P : PrimeDivisor B | formOrder a b P ≠ 0}.Finite := by
  refine Set.Finite.subset ((finite_orderAt_support ha).union (finite_orderAt_support hb)) ?_
  intro P hP
  rcases formOrder_ne_zero_imp a b hP with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **The eigenvolume horizon theorem at prime divisors.**  Under the local order law, with
ramification somewhere on each recurrent cycle, the order of the form is exactly `-1` on its whole
divisorial support: the horizon is a reduced divisor. -/
theorem formOrder_eq_neg_one (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) (e : PrimeDivisor B → ℕ)
    (hone : ∀ P, 1 ≤ e P)
    (hlaw : ∀ P, formOrder a b P + 1 =
      (e P : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    {P : PrimeDivisor B} (hP : formOrder a b P ≠ 0) :
    formOrder a b P = -1 :=
  eigenvolumeOrder_eq_neg_one_of_someRamified hsurj hone hlaw
    (finite_formOrder_support ha hb) hram hP

/-- **Total invariance of the horizon.**  A prime divisor lies on the horizon exactly when the
prime divisor below it does. -/
theorem formOrder_ne_zero_iff (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) (e : PrimeDivisor B → ℕ)
    (hone : ∀ P, 1 ≤ e P)
    (hlaw : ∀ P, formOrder a b P + 1 =
      (e P : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    (P : PrimeDivisor B) :
    formOrder a b P ≠ 0 ↔ formOrder a b (divisorBelow φ hwd P) ≠ 0 := by
  refine ⟨fun hP => ?_, fun hP => order_ne_zero_of_image_ne_zero hlaw hP⟩
  have hval : formOrder a b P = -1 :=
    formOrder_eq_neg_one φ hwd hsurj ha hb e hone hlaw hram hP
  have h := hlaw P
  rw [hval] at h
  have hzero : (e P : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1) = 0 := by linarith
  have hepos : (e P : ℤ) ≠ 0 := by
    have := hone P
    omega
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd h' hepos
  · omega

/-- **The map is unramified off the horizon.** -/
theorem ramificationIndex_eq_one_off_horizon (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
    {a b : B} (e : PrimeDivisor B → ℕ)
    (hlaw : ∀ P, formOrder a b P + 1 =
      (e P : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1))
    {P : PrimeDivisor B} (hP : formOrder a b P = 0) :
    e P = 1 :=
  ramificationIndex_eq_one_of_order_eq_zero hlaw hP

end GaloisForLFunctions.HTGeometry
