import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.SetTheory.Cardinal.Finite

open Equiv Set
namespace GaloisForLFunctions.HTGeometry

/-- A multiplicative coordinate transports every nonnegative permutation iterate. -/
theorem coordinate_perm_pow {A K : Type*} [Field K] (T : Equiv.Perm A)
    (u : A → K) (ζ : K) (hstep : ∀ a, u (T a) = ζ * u a) (k : ℕ) (a : A) :
    u ((T ^ k) a) = ζ ^ k * u a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Perm.mul_apply, hstep, ih, pow_succ', mul_assoc]

/-- A primitive-root coordinate forces one orbit of exactly d sheets, without finiteness input. -/
theorem bijective_orbit_of_primitive_coordinate {A K : Type*} [Field K]
    (T : Equiv.Perm A) (u : A → K) (hu : Function.Injective u)
    (hzero : ∀ a, u a ≠ 0) {d : ℕ} (hd : 0 < d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ d) (hpow : ∀ a b, u a ^ d = u b ^ d)
    (hstep : ∀ a, u (T a) = ζ * u a) (a₀ : A) :
    Function.Bijective (fun i : Fin d => (T ^ (i : ℕ)) a₀) := by
  letI : NeZero d := ⟨hd.ne'⟩
  constructor
  · intro i j hij
    have he := congrArg u hij
    rw [coordinate_perm_pow T u ζ hstep, coordinate_perm_pow T u ζ hstep] at he
    apply Fin.ext
    exact hζ.pow_inj i.isLt j.isLt (mul_right_cancel₀ (hzero a₀) he)
  · intro a
    have hratio : (u a / u a₀) ^ d = 1 := by
      rw [div_pow, hpow a a₀, div_self (pow_ne_zero d (hzero a₀))]
    obtain ⟨k, hk, he⟩ := hζ.eq_pow_of_pow_eq_one hratio
    refine ⟨⟨k, hk⟩, hu ?_⟩
    rw [coordinate_perm_pow T u ζ hstep, he, div_mul_cancel₀ _ (hzero a₀)]

/-- No additional orbit can survive an injective primitive-root coordinate. -/
theorem isCycleOn_of_primitive_coordinate {A K : Type*} [Field K]
    (T : Equiv.Perm A) (u : A → K) (hu : Function.Injective u)
    (hzero : ∀ a, u a ≠ 0) {d : ℕ} (hd : 0 < d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ d) (hpow : ∀ a b, u a ^ d = u b ^ d)
    (hstep : ∀ a, u (T a) = ζ * u a) : T.IsCycleOn univ := by
  refine ⟨⟨fun _ _ => mem_univ _, T.injective.injOn, ?_⟩, ?_⟩
  · intro a _
    exact ⟨T.symm a, mem_univ _, T.apply_symm_apply a⟩
  · intro a _ b _
    obtain ⟨i, hi⟩ := (bijective_orbit_of_primitive_coordinate T u hu hzero hd hζ hpow hstep a).2 b
    exact ⟨((i : ℕ) : ℤ), by simpa only [zpow_natCast] using hi⟩

/-- The sheet cardinality is a consequence of the coordinate dynamics, even for an arbitrary type. -/
theorem natCard_eq_of_primitive_coordinate {A K : Type*} [Field K]
    (T : Equiv.Perm A) (u : A → K) (hu : Function.Injective u)
    (hzero : ∀ a, u a ≠ 0) {d : ℕ} (hd : 0 < d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ d) (hpow : ∀ a b, u a ^ d = u b ^ d)
    (hstep : ∀ a, u (T a) = ζ * u a) (a₀ : A) : Nat.card A = d := by
  let e : Fin d ≃ A := Equiv.ofBijective _
    (bijective_orbit_of_primitive_coordinate T u hu hzero hd hζ hpow hstep a₀)
  exact (Nat.card_congr e).symm.trans (Nat.card_fin d)

end GaloisForLFunctions.HTGeometry
