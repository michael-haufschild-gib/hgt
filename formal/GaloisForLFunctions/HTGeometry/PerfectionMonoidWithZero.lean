import Mathlib.RingTheory.Perfection

/-!
# The perfection of a monoid with zero

The inverse limit `lim_{()^p} M` of a commutative monoid with zero along the `p`-th power map is
again a commutative monoid with zero: the zero is the constant sequence.  If `M` has no zero
divisors then neither does the limit, because an entry of a sequence is a `p`-power of every later
entry, so one vanishing entry makes the sequence vanish identically; and if `M` is a commutative
group with zero then so is the limit, with inverse taken coordinatewise.
-/

namespace HTGeometry

open Perfection

universe u

variable {M : Type u} [CommMonoidWithZero M] {p : ℕ} [NeZero p]

instance perfectionZero : Zero (Perfection M p) :=
  ⟨⟨fun _ => 0, fun _ => zero_pow (NeZero.ne p)⟩⟩

@[simp] theorem perfection_coeff_zero (n : ℕ) :
    coeffMonoidHom M p n (0 : Perfection M p) = 0 := rfl

instance perfectionCommMonoidWithZero : CommMonoidWithZero (Perfection M p) where
  zero_mul _ := Subtype.ext (funext fun _ => zero_mul _)
  mul_zero _ := Subtype.ext (funext fun _ => mul_zero _)

instance perfectionNontrivial [Nontrivial M] : Nontrivial (Perfection M p) :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := M) (congrArg (coeffMonoidHom M p 0) h)⟩⟩

theorem perfection_eq_zero_iff_coeff (x : Perfection M p) :
    x = 0 ↔ ∀ n, coeffMonoidHom M p n x = 0 :=
  ⟨fun h n => by rw [h]; rfl, fun h => Subtype.ext (funext fun n => h n)⟩

omit [NeZero p] in
/-- An entry of a sequence in the perfection is the `p^k`-th power of the entry `k` steps later. -/
theorem perfection_coeff_pow (x : Perfection M p) (i k : ℕ) :
    coeffMonoidHom M p (i + k) x ^ p ^ k = coeffMonoidHom M p i x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hx : coeffMonoidHom M p (i + k + 1) x ^ p = coeffMonoidHom M p (i + k) x := x.2 (i + k)
      have hidx : i + (k + 1) = i + k + 1 := by omega
      calc coeffMonoidHom M p (i + (k + 1)) x ^ p ^ (k + 1)
          = (coeffMonoidHom M p (i + k + 1) x ^ p) ^ p ^ k := by
            rw [hidx, ← pow_mul, ← pow_succ']
        _ = coeffMonoidHom M p (i + k) x ^ p ^ k := by rw [hx]
        _ = coeffMonoidHom M p i x := ih

/-- The map of perfections induced by a pointed multiplicative map. -/
def perfectionMapWithZero {N : Type u} [CommMonoidWithZero N] (φ : M →*₀ N) :
    Perfection M p →*₀ Perfection N p where
  toFun := Perfection.mapMonoidHom p φ.toMonoidHom
  map_zero' := Subtype.ext (funext fun _ => φ.map_zero)
  map_one' := map_one (Perfection.mapMonoidHom p φ.toMonoidHom)
  map_mul' := map_mul (Perfection.mapMonoidHom p φ.toMonoidHom)

@[simp] theorem perfection_coeff_map {N : Type u} [CommMonoidWithZero N] (φ : M →*₀ N)
    (x : Perfection M p) (n : ℕ) :
    coeffMonoidHom N p n (perfectionMapWithZero (p := p) φ x) = φ (coeffMonoidHom M p n x) := rfl

theorem perfectionMapWithZero_injective {N : Type u} [CommMonoidWithZero N] {φ : M →*₀ N}
    (hφ : Function.Injective φ) :
    Function.Injective (perfectionMapWithZero (p := p) φ) := by
  intro x y hxy
  refine Subtype.ext (funext fun n => hφ ?_)
  exact congrArg (fun z => coeffMonoidHom N p n z) hxy

variable [NoZeroDivisors M]

/-- A sequence in the perfection with one vanishing entry vanishes identically. -/
theorem perfection_eq_zero_of_coeff_eq_zero {x : Perfection M p} {n : ℕ}
    (h : coeffMonoidHom M p n x = 0) : x = 0 := by
  have hppos : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k (NeZero.ne p)
  refine (perfection_eq_zero_iff_coeff x).2 fun m => ?_
  rcases le_or_gt m n with hmn | hmn
  · have hpow : coeffMonoidHom M p (m + (n - m)) x ^ p ^ (n - m)
        = coeffMonoidHom M p m x := perfection_coeff_pow x m (n - m)
    have hidx : m + (n - m) = n := by omega
    rw [hidx, h, zero_pow (hppos _)] at hpow
    exact hpow.symm
  · have hpow : coeffMonoidHom M p (n + (m - n)) x ^ p ^ (m - n)
        = coeffMonoidHom M p n x := perfection_coeff_pow x n (m - n)
    have hidx : n + (m - n) = m := by omega
    rw [hidx, h] at hpow
    exact (pow_eq_zero_iff (hppos _)).1 hpow

theorem perfection_coeff_ne_zero {x : Perfection M p} (hx : x ≠ 0) (n : ℕ) :
    coeffMonoidHom M p n x ≠ 0 := fun h => hx (perfection_eq_zero_of_coeff_eq_zero h)

instance perfectionNoZeroDivisors : NoZeroDivisors (Perfection M p) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    by_contra hc
    push Not at hc
    have h0 : coeffMonoidHom M p 0 x * coeffMonoidHom M p 0 y = 0 := by
      rw [← map_mul, hxy]
      rfl
    rcases mul_eq_zero.1 h0 with h | h
    · exact hc.1 (perfection_eq_zero_of_coeff_eq_zero h)
    · exact hc.2 (perfection_eq_zero_of_coeff_eq_zero h)

section GroupWithZero

variable {G : Type u} [CommGroupWithZero G] {p : ℕ} [NeZero p]

instance perfectionInv : Inv (Perfection G p) :=
  ⟨fun x => ⟨fun n => (x.1 n)⁻¹, fun n => by
    show ((x.1 (n + 1))⁻¹) ^ p = (x.1 n)⁻¹
    rw [inv_pow, x.2 n]⟩⟩

omit [NeZero p] in
@[simp] theorem perfection_coeff_inv (x : Perfection G p) (n : ℕ) :
    coeffMonoidHom G p n x⁻¹ = (coeffMonoidHom G p n x)⁻¹ := rfl

/-- The perfection of a commutative group with zero is again one, with inverse taken
coordinatewise. -/
instance perfectionCommGroupWithZero : CommGroupWithZero (Perfection G p) :=
  { perfectionCommMonoidWithZero, perfectionInv with
    exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := G)
      (congrArg (coeffMonoidHom G p 0) h)⟩
    inv_zero := Subtype.ext (funext fun _ => inv_zero)
    mul_inv_cancel := fun x hx => Subtype.ext (funext fun n =>
      mul_inv_cancel₀ (perfection_coeff_ne_zero hx n)) }

end GroupWithZero

end HTGeometry
