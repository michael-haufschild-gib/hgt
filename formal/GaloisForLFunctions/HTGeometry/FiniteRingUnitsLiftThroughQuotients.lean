import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Ring.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-!
# Units lift through quotients of finite commutative rings

A repeated power in a finite monoid yields a positive idempotent power.
For an element with unit image, this idempotent has image one; adjoining
its complementary idempotent turns the original element into a unit
with the same image. Consequently every surjective ring map with finite
source is surjective on unit groups.
-/

namespace GaloisForLFunctions.FiniteRing

/-- Repetition of powers in a finite monoid yields a positive idempotent power. -/
theorem exists_pos_pow_idempotent {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (a ^ n) := by
  obtain ⟨i, j, hij, hp⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => a ^ n) (t := Set.univ)
      (fun _ => Set.mem_univ _) (Set.toFinite _)
  let d := j - i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hp' : a ^ (i + d) = a ^ i := by
    rw [show i + d = j by dsimp [d]; omega]
    exact hp.symm
  have hperiod (k : ℕ) (hk : i ≤ k) : a ^ (k + d) = a ^ k := by
    calc
      a ^ (k + d) = a ^ (i + d + (k - i)) := by congr 1; omega
      _ = a ^ (i + d) * a ^ (k - i) := pow_add _ _ _
      _ = a ^ i * a ^ (k - i) := by rw [hp']
      _ = a ^ k := by rw [← pow_add, Nat.add_sub_of_le hk]
  have hrepeat (k : ℕ) (hk : i ≤ k) (t : ℕ) : a ^ (k + t * d) = a ^ k := by
    induction t with
    | zero => simp only [zero_mul, add_zero]
    | succ t ih =>
      calc
        a ^ (k + (t + 1) * d) = a ^ (k + t * d + d) := by congr 1; ring
        _ = a ^ (k + t * d) := hperiod _ (by omega)
        _ = a ^ k := ih
  let n := (i + 1) * d
  have hn : 0 < n := Nat.mul_pos (Nat.succ_pos _) hd
  have hin : i ≤ n := by
    have h := Nat.mul_le_mul_left (i + 1) (show 1 ≤ d from hd)
    dsimp [n]
    omega
  refine ⟨n, hn, ?_⟩
  change a ^ n * a ^ n = a ^ n
  rw [← pow_add]
  exact hrepeat n hin (i + 1)

/-- A unit image of an element of a finite commutative ring has a unit lift. -/
theorem exists_unit_map_eq {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (r : R) (hr : IsUnit (f r)) :
    ∃ u : Rˣ, f (u : R) = f r := by
  obtain ⟨n, hn, he⟩ := exists_pos_pow_idempotent r
  let e := r ^ n
  have he' : e * e = e := he.eq
  have he2 : e ^ 2 = e := by simpa only [pow_two] using he'
  have hfe : f e = 1 := by
    apply (IsIdempotentElem.iff_eq_one_of_isUnit ?_).mp (he.map f)
    simpa only [e, map_pow] using hr.pow n
  have hre : r * r ^ (n - 1) = e := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ n from hn)]
  let x := r * e + (1 - e)
  let y := r ^ (n - 1) * e + (1 - e)
  have hxy : x * y = 1 := by
    calc
      x * y = (r * r ^ (n - 1)) * e ^ 2 +
          (r + r ^ (n - 1)) * (e - e ^ 2) + (1 - 2 * e + e ^ 2) := by
        dsimp [x, y]
        ring
      _ = 1 := by rw [hre, he2, sub_self, mul_zero, add_zero, he']; ring
  refine ⟨⟨x, y, hxy, by simpa only [mul_comm] using hxy⟩, ?_⟩
  change f (r * e + (1 - e)) = f r
  rw [map_add, map_mul, map_sub, map_one, hfe, mul_one, sub_self, add_zero]

/-- Surjective ring maps from finite commutative rings are surjective on units. -/
theorem units_map_surjective {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨r, hr⟩ := hf (u : S)
  obtain ⟨v, hv⟩ := exists_unit_map_eq f r (hr.symm ▸ u.isUnit)
  refine ⟨v, ?_⟩
  apply Units.ext
  exact hv.trans hr

end GaloisForLFunctions.FiniteRing
