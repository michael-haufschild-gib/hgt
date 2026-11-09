import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersWithAClosedDegreeGeodesic
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization

/-!
# A prime-unit quotient loses the degree ladder

On the product of the degree geodesic and a tree apartment, the diagonal p-unit
acts by `(z_t,k) ↦ (z_{p²t},k+2)`. The degrees `p^k` and `p^{k+2}` are therefore
identified. Their Frobenius intersections with degree one differ: the prime term
is constant, while the archimedean jet term strictly decreases. Consequently the
actual Frobenius intersection cannot descend as a scalar kernel under this action.
The torsion self-intersection changes by `2 log p` under the same identification.
-/

set_option autoImplicit false
noncomputable section
open Real Set
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ ArithmeticEffectivityTheory ArithmeticIntersectionTheory
namespace PrimeUnit

/-- The product of the archimedean space with one oriented tree apartment. -/
abbrev Apartment := H3 × ℤ

/-- The diagonal p-unit acts by dilation at infinity and translation by two at p. -/
def action (p : ℕ) (hp : p.Prime) (x : Apartment) : Apartment :=
  (h3Act (diagSL2 (p : ℂ) (by exact_mod_cast hp.ne_zero)) x.1, x.2 + 2)

/-- The degree `p^k` on the two local factors. -/
def point (p : ℕ) (hp : p.Prime) (k : ℕ) : Apartment :=
  (degPoint ((p : ℝ) ^ k) (pow_pos (by exact_mod_cast hp.pos) k), (k : ℤ))

theorem action_point (p : ℕ) (hp : p.Prime) (k : ℕ) :
    action p hp (point p hp k) = point p hp (k + 2) := by
  apply Prod.ext
  · change h3Act (diagSL2 (p : ℂ) _) (degPoint ((p : ℝ) ^ k) _) =
      degPoint ((p : ℝ) ^ (k + 2)) _
    rw [h3Act_diag]
    apply degPoint_eq
    rw [Complex.norm_natCast, pow_add]
    ring
  · simp only [action, point, Nat.cast_add, Nat.cast_ofNat]

/-- The exact intersection with degree one along a prime ladder. -/
theorem frobeniusIntersection_one_prime_pow (p : ℕ) (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    frobeniusIntersection 1 (p ^ k) =
      1 / (1 - (1 / ((p : ℝ) ^ k)) ^ 2) + Real.log p := by
  have hpow : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hpowR : (1 : ℝ) < (p : ℝ) ^ k := by exact_mod_cast hpow
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have hposR : (0 : ℝ) < (p : ℝ) ^ k := lt_trans zero_lt_one hpowR
  have hpterm : weilPrimeKernel 1 (p ^ k) = Real.log p / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [weilPrimeKernel, if_pos ⟨one_dvd _, ne_of_lt hpow⟩, Nat.div_one,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have ht := sqrt_mul_weilPrimeKernel (m := 1) one_pos hpos (ne_of_lt hpow)
  rw [hpterm, Nat.cast_one, one_mul, mul_div_cancel₀ _
    (Real.sqrt_pos.mpr (by exact_mod_cast hpos)).ne'] at ht
  rw [frobeniusIntersection_eq one_pos hpos (ne_of_lt hpow), ← ht,
    Nat.cast_one, Nat.cast_pow, min_eq_left hpowR.le, max_eq_right hpowR.le]

/-- Identified odd ladder levels have different actual Frobenius intersections. -/
theorem frobeniusIntersection_one_cube_lt (p : ℕ) (hp : p.Prime) :
    frobeniusIntersection 1 (p ^ 3) < frobeniusIntersection 1 p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hcube : (p : ℝ) < (p : ℝ) ^ 3 := by
    have hh : (1 : ℝ) < (p : ℝ) ^ 2 := one_lt_pow₀ hp1 (by decide : (2 : ℕ) ≠ 0)
    nlinarith only [mul_lt_mul_of_pos_left hh hp0]
  have hsmall : 1 / (p : ℝ) ^ 3 < 1 / (p : ℝ) := one_div_lt_one_div_of_lt hp0 hcube
  have hsmall0 : 0 < 1 / (p : ℝ) ^ 3 := by positivity
  have hratio : 1 / (p : ℝ) < 1 := (div_lt_one hp0).mpr hp1
  have hden : 0 < 1 - (1 / (p : ℝ)) ^ 2 := by nlinarith only [hratio, one_div_pos.mpr hp0]
  have hdenlt : 1 - (1 / (p : ℝ)) ^ 2 < 1 - (1 / (p : ℝ) ^ 3) ^ 2 := by
    nlinarith only [hsmall, hsmall0]
  have h := one_div_lt_one_div_of_lt hden hdenlt
  have h1 := frobeniusIntersection_one_prime_pow p hp (k := 1) le_rfl
  rw [pow_one] at h1
  rw [frobeniusIntersection_one_prime_pow p hp (by decide : 1 ≤ 3), h1]
  exact add_lt_add_right h _

/-- No scalar kernel invariant under the arithmetic prime unit carries the off-diagonal
Frobenius intersections, already on the single prime ladder. -/
theorem not_exists_invariant_frobenius_kernel (p : ℕ) (hp : p.Prime) :
    ¬ ∃ K : Apartment → Apartment → ℝ,
      (∀ x y, K x (action p hp y) = K x y) ∧
      (∀ m n : ℕ, m ≠ n → K (point p hp m) (point p hp n) =
        frobeniusIntersection (p ^ m) (p ^ n)) := by
  rintro ⟨K, hK, hvalues⟩
  have h := hK (point p hp 0) (point p hp 1)
  rw [action_point, hvalues 0 3 (by decide), hvalues 0 1 (by decide), pow_zero, pow_one] at h
  exact (frobeniusIntersection_one_cube_lt p hp).ne h

/-- The torsion diagonal has nonzero additive holonomy along the prime-unit orbit. -/
theorem selfIntersection_cube_sub_prime (p : ℕ) (hp : p.Prime) :
    selfIntersection (p ^ 3) - selfIntersection p = 2 * Real.log p := by
  rw [selfIntersection_eq (pow_pos hp.pos 3), selfIntersection_eq hp.pos,
    tameDifferent_prime_pow hp (by decide : (3 : ℕ) ≠ 0)]
  have ht := tameDifferent_prime_pow hp (by decide : (1 : ℕ) ≠ 0)
  rw [pow_one] at ht
  rw [ht, Nat.cast_pow, Real.log_pow]
  ring

theorem not_exists_invariant_torsion_robin (p : ℕ) (hp : p.Prime) :
    ¬ ∃ R : Apartment → ℝ,
      (∀ x, R (action p hp x) = R x) ∧
      (∀ k : ℕ, 0 < k → R (point p hp k) = selfIntersection (p ^ k)) := by
  rintro ⟨R, hR, hvalues⟩
  have h := hR (point p hp 1)
  rw [action_point, hvalues 3 (by decide), hvalues 1 (by decide), pow_one] at h
  have hc := selfIntersection_cube_sub_prime p hp
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [h, sub_self] at hc
  linarith only [hc, hl]

#print axioms action_point
#print axioms frobeniusIntersection_one_cube_lt
#print axioms not_exists_invariant_frobenius_kernel
#print axioms selfIntersection_cube_sub_prime
#print axioms not_exists_invariant_torsion_robin

end PrimeUnit
end GaloisForLFunctions.HyperbolicArakelovTheory
