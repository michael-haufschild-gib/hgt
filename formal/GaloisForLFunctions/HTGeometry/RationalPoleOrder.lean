import GaloisForLFunctions.HTGeometry.TelescopingJumpObstruction
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Pole orders of a rational function along an integer orbit

The pole order of a rational function at a point is the multiplicity of that point as a root of its
reduced denominator; it is positive exactly at the poles.  Restricting to one integer orbit gives a
finitely supported order function on `ℤ`, because a nonzero polynomial has finitely many roots and
the orbit map is injective.

That order function is the input of the discrete-residue obstruction: a telescoped difference has at
least two order jumps along any orbit carrying a pole, so it cannot have exactly one pole there.
-/

open scoped BigOperators

namespace GaloisForLFunctions

variable {K : Type*} [Field K]

/-- The pole order of a rational function at a point: the multiplicity of the point as a root of
the reduced denominator. -/
noncomputable def poleOrder (g : RatFunc K) (c : K) : ℕ :=
  Polynomial.rootMultiplicity c g.denom

theorem poleOrder_pos_iff (g : RatFunc K) (c : K) :
    0 < poleOrder g c ↔ g.denom.IsRoot c :=
  Polynomial.rootMultiplicity_pos (RatFunc.denom_ne_zero g)

theorem poleOrder_ne_zero_iff (g : RatFunc K) (c : K) :
    poleOrder g c ≠ 0 ↔ g.denom.IsRoot c := by
  rw [← Nat.pos_iff_ne_zero, poleOrder_pos_iff]

/-- **Finitely many poles on an orbit.**  The pole order of a rational function along an integer
orbit is finitely supported. -/
theorem finite_support_poleOrder_orbit [CharZero K] (g : RatFunc K) (c : K) :
    (Function.support fun n : ℤ => poleOrder g (c + n)).Finite := by
  classical
  have hroot : {w : K | g.denom.IsRoot w}.Finite :=
    Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero g)
  have hinj : Function.Injective fun n : ℤ => c + (n : K) := by
    intro m n hmn
    have : (m : K) = (n : K) := by
      have := hmn
      simpa using this
    exact_mod_cast this
  have hsub : (Function.support fun n : ℤ => poleOrder g (c + n)) ⊆
      (fun n : ℤ => c + (n : K)) ⁻¹' {w : K | g.denom.IsRoot w} := by
    intro n hn
    rw [Function.mem_support] at hn
    exact (poleOrder_ne_zero_iff g _).mp hn
  exact Set.Finite.subset (Set.Finite.preimage (hinj.injOn) hroot) hsub

/-- The orbit order function of a rational function. -/
noncomputable def orbitPoleOrder (g : RatFunc K) (c : K) : ℤ → ℕ :=
  fun n => poleOrder g (c + n)

theorem finite_support_orbitPoleOrder [CharZero K] (g : RatFunc K) (c : K) :
    (Function.support (orbitPoleOrder g c)).Finite :=
  finite_support_poleOrder_orbit g c

/-! ## The obstruction for a rational function -/

/-- **No single-pole orbit.**  If every order jump of `g` along an orbit forces a pole of the
telescoped difference, and the difference has at most one pole on that orbit, then `g` has no poles
on the orbit at all.  This is the discrete-residue obstruction in the form the atomic
scaled-digamma argument uses. -/
theorem poleOrder_orbit_eq_zero_of_subsingleton [CharZero K] (g : RatFunc K) (c : K) (D : Set ℤ)
    (hD : ∀ n : ℤ, orbitPoleOrder g c n ≠ orbitPoleOrder g c (n + 1) → n ∈ D)
    (hsub : D.Subsingleton) : ∀ n : ℤ, poleOrder g (c + n) = 0 :=
  eq_zero_of_jump_poles_subsingleton (orbitPoleOrder g c)
    (finite_support_orbitPoleOrder g c) D hD hsub

/-- The same conclusion phrased at the poles: the orbit meets no pole of `g`. -/
theorem not_isRoot_denom_orbit_of_subsingleton [CharZero K] (g : RatFunc K) (c : K) (D : Set ℤ)
    (hD : ∀ n : ℤ, orbitPoleOrder g c n ≠ orbitPoleOrder g c (n + 1) → n ∈ D)
    (hsub : D.Subsingleton) (n : ℤ) : ¬ g.denom.IsRoot (c + n) := by
  intro hroot
  have hzero := poleOrder_orbit_eq_zero_of_subsingleton g c D hD hsub n
  exact ((poleOrder_ne_zero_iff g (c + n)).mpr hroot) hzero

/-! ## Regularity is a local subring -/

/-- A rational function is regular at a point when it can be written with a denominator that does
not vanish there. -/
def RegularAt (g : RatFunc K) (c : K) : Prop :=
  ∃ p q : Polynomial K, q.eval c ≠ 0 ∧
    g = algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q

theorem isRoot_of_dvd_of_isRoot {d P : Polynomial K} {c : K} (hdvd : d ∣ P)
    (h : d.IsRoot c) : P.IsRoot c := by
  obtain ⟨e, rfl⟩ := hdvd
  rw [Polynomial.IsRoot, Polynomial.eval_mul, h, zero_mul]

theorem regularAt_iff_poleOrder_eq_zero (g : RatFunc K) (c : K) :
    RegularAt g c ↔ poleOrder g c = 0 := by
  constructor
  · rintro ⟨p, q, hq, hg⟩
    have hq0 : q ≠ 0 := fun h => hq (by rw [h, Polynomial.eval_zero])
    have hdvd : g.denom ∣ q := (RatFunc.denom_dvd hq0).mpr ⟨p, hg⟩
    by_contra hcon
    exact hq (isRoot_of_dvd_of_isRoot hdvd ((poleOrder_ne_zero_iff g c).mp hcon))
  · intro h
    refine ⟨g.num, g.denom, ?_, (RatFunc.num_div_denom g).symm⟩
    intro hroot
    exact ((poleOrder_ne_zero_iff g c).mpr hroot) h

theorem RegularAt.add {a b : RatFunc K} {c : K} (ha : RegularAt a c) (hb : RegularAt b c) :
    RegularAt (a + b) c := by
  obtain ⟨p, q, hq, rfl⟩ := ha
  obtain ⟨r, s, hs, rfl⟩ := hb
  refine ⟨p * s + r * q, q * s, by rw [Polynomial.eval_mul]; exact mul_ne_zero hq hs, ?_⟩
  have hq0 : (algebraMap (Polynomial K) (RatFunc K)) q ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact fun h => hq (by rw [h, Polynomial.eval_zero])
  have hs0 : (algebraMap (Polynomial K) (RatFunc K)) s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact fun h => hs (by rw [h, Polynomial.eval_zero])
  rw [map_add, map_mul, map_mul, map_mul]
  field_simp

theorem RegularAt.neg {a : RatFunc K} {c : K} (ha : RegularAt a c) : RegularAt (-a) c := by
  obtain ⟨p, q, hq, rfl⟩ := ha
  exact ⟨-p, q, hq, by rw [map_neg, neg_div']⟩

theorem RegularAt.sub {a b : RatFunc K} {c : K} (ha : RegularAt a c) (hb : RegularAt b c) :
    RegularAt (a - b) c := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-! ## The pole survives the telescoping -/

theorem poleOrder_sub_eq_zero {a b : RatFunc K} {c : K} (ha : poleOrder a c = 0)
    (hb : poleOrder b c = 0) : poleOrder (a - b) c = 0 :=
  (regularAt_iff_poleOrder_eq_zero _ _).mp
    (((regularAt_iff_poleOrder_eq_zero a c).mpr ha).sub
      ((regularAt_iff_poleOrder_eq_zero b c).mpr hb))

/-- **An extreme pole survives.**  If `a` has a pole at `c` and `b` does not, the difference
`b - a` has a pole at `c`: a regular difference would make `a` regular. -/
theorem poleOrder_sub_ne_zero {a b : RatFunc K} {c : K} (ha : poleOrder a c ≠ 0)
    (hb : poleOrder b c = 0) : poleOrder (b - a) c ≠ 0 := by
  intro hcon
  refine ha ?_
  have hrw : a = b - (b - a) := by ring
  rw [hrw]
  exact poleOrder_sub_eq_zero hb hcon

/-! ## The pole order of a reduced power-denominator fraction -/

/-- **A pure power denominator gives its exponent as the pole order.**  If the numerator does not
vanish at the point, the fraction with denominator `(X - c)^m` has pole order exactly `m` there.
This is the step where a constant-coefficient operator of order `d` applied to a simple pole
produces a pole of order `d + 1` with nonzero coefficient. -/
theorem poleOrder_powerDenominator {P : Polynomial K} {c : K} (hP : ¬ P.IsRoot c)
    (hP0 : P ≠ 0) (m : ℕ) :
    poleOrder ((algebraMap (Polynomial K) (RatFunc K)) P /
      (algebraMap (Polynomial K) (RatFunc K)) ((Polynomial.X - Polynomial.C c) ^ m)) c = m := by
  classical
  set Q : Polynomial K := (Polynomial.X - Polynomial.C c) ^ m with hQ
  have hQ0 : Q ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)
  set x : RatFunc K := (algebraMap (Polynomial K) (RatFunc K)) P /
    (algebraMap (Polynomial K) (RatFunc K)) Q with hx
  have hxne : x ≠ 0 := by
    rw [hx]
    refine div_ne_zero ?_ ?_ <;>
      rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    · exact hP0
    · exact hQ0
  have hnd : (algebraMap (Polynomial K) (RatFunc K)) x.num /
      (algebraMap (Polynomial K) (RatFunc K)) x.denom = x := RatFunc.num_div_denom x
  have hcoprime := RatFunc.isCoprime_num_denom x
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hxne
  have hden0 : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  set N : Polynomial K := x.num with hN
  set D : Polynomial K := x.denom with hD
  have hmapQ : (algebraMap (Polynomial K) (RatFunc K)) Q ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact hQ0
  have hmapD : (algebraMap (Polynomial K) (RatFunc K)) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact hden0
  have hcross : P * D = N * Q := by
    have heq : (algebraMap (Polynomial K) (RatFunc K)) N /
        (algebraMap (Polynomial K) (RatFunc K)) D =
        (algebraMap (Polynomial K) (RatFunc K)) P /
          (algebraMap (Polynomial K) (RatFunc K)) Q := by
      rw [hnd, hx]
    rw [div_eq_div_iff hmapD hmapQ] at heq
    refine RatFunc.algebraMap_injective K ?_
    rw [map_mul, map_mul]
    exact heq.symm
  have hmulne : P * D ≠ 0 := mul_ne_zero hP0 hden0
  have hmulne' : N * Q ≠ 0 := mul_ne_zero hnum0 hQ0
  have hrm := congrArg (Polynomial.rootMultiplicity c) hcross
  rw [Polynomial.rootMultiplicity_mul hmulne, Polynomial.rootMultiplicity_mul hmulne',
    hQ, Polynomial.rootMultiplicity_X_sub_C_pow] at hrm
  have hPzero : Polynomial.rootMultiplicity c P = 0 := by
    by_contra hcon
    exact hP ((Polynomial.rootMultiplicity_pos hP0).mp (Nat.pos_of_ne_zero hcon))
  rw [hPzero, zero_add] at hrm
  have hnumzero : Polynomial.rootMultiplicity c N = 0 := by
    by_contra hcon
    have hnumroot : N.IsRoot c :=
      (Polynomial.rootMultiplicity_pos hnum0).mp (Nat.pos_of_ne_zero hcon)
    have hdenroot : D.IsRoot c := by
      refine (Polynomial.rootMultiplicity_pos hden0).mp ?_
      omega
    obtain ⟨u, v, huv⟩ := hcoprime
    have hzero : (1 : Polynomial K).eval c = 0 := by
      rw [← huv, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        hnumroot, hdenroot]
      ring
    simp at hzero
  rw [hnumzero, zero_add] at hrm
  exact hrm

end GaloisForLFunctions
