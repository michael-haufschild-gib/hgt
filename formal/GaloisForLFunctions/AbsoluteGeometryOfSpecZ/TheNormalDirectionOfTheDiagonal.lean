import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRestrictionToTheFrobeniusGraph

/-!
# The normal direction of the diagonal

On `C × C` the conormal module `I_Δ/I_Δ²` of the diagonal is the line bundle of differentials, and
Stepanov's and Weil's arguments both use it. This file computes it in two squares of `Spec ℤ`.

**In the arithmetic square the conormal classes are torsion.** The ideal `I` of the diagonal is
spanned by the orbits `e_d`, `d ≥ 2`, and `e_d² = d e_d`, so `d e_d ∈ I²`
(`natCast_smul_orbit_mem_ker_sq`); for coprime `a, b ≥ 2`, `e_{ab} = e_a e_b ∈ I²`
(`orbit_mul_mem_ker_sq_of_coprime`); and `e_p ∉ I²` for a prime `p` (`orbit_notMem_ker_sq`). The
diagonal is a branch of a curve: it has one cotangent line at each prime, of characteristic `p`,
and no normal direction in characteristic zero.

**On the toric surface of a base there is one.** Fix `q`. The surface `Spec ℤ[Y]` carries the
sections `Y = qⁿ`; restricting a function to them is the ring homomorphism `Y ↦ [q]` into the
arithmetic square (`surfaceMap`, `ghostComponent_surfaceMap`).

* The diagonal `Y = q` has a conormal module of rank one: `Q ∈ I²` iff `Q(q) = 0` and `Q'(q) = 0`
  (`X_sub_C_sq_dvd_iff`). The normal direction is `∂/∂Y`.
* **The normal derivative restricts to the `p`-derivation through the Fermat quotient**
  (`prime_dvd_coord_surfaceMap_sub`): for `Q(q) = 0`,
  `b_p(Q([q])) ≡ Q'(q) · (q^p − q)/p (mod p)`. It vanishes at the primes where `q^p ≡ q (mod p²)`.
* **Sections with a rank count** (`card_image_digitLatticeMap`): the polynomials of degree `< b`
  in `[q]` with coefficients of absolute value `≤ A` are `(2A + 1)^b` distinct elements of the
  square: the logarithm of the count is bilinear in the two degrees `log A` and `b`. Restriction to
  `Γ_n` multiplies the second degree by `n` (`abs_ghostComponent_digitLatticeMap_le`).
* **The forced zeros are the contacts** (`pow_dvd_eval_of_pow_dvd`): a function vanishing to order
  `ℓ` on the diagonal is divisible by `(qⁿ − q)^ℓ` on `Y = qⁿ`, with equality for `(Y − q)^ℓ`; and
  `qⁿ − q` lies in the graph ideal of the square (`pow_sub_self_mem_graphIdeal`). The count on
  each section is the product formula for `qⁿ − q`.
-/

open Finset Polynomial

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The arithmetic square: torsion conormal classes -/

theorem orbit_mem_ker {d : ℕ+} (hd : 1 < d) : orbit d ∈ RingHom.ker (ghostComponent 1) := by
  have h1 : ¬ (d : ℕ) ∣ ((1 : ℕ+) : ℕ) := by
    rw [PNat.one_coe, Nat.dvd_one]
    exact fun h => hd.ne' (PNat.eq (by simpa using h))
  rw [RingHom.mem_ker, ghostComponent_apply, orbit_apply, if_neg h1]

/-- `e_d² = d e_d`. -/
theorem orbit_mul_self (d : ℕ+) : orbit d * orbit d = ((d : ℕ) : ℤ) • orbit d := by
  refine Subtype.ext (funext fun n => ?_)
  change (orbit d).1 n * (orbit d).1 n = ((d : ℕ) : ℤ) • (orbit d).1 n
  rw [orbit_apply]
  split_ifs <;> simp

/-- **The conormal class of an orbit is torsion**: `d e_d ∈ I²`. -/
theorem natCast_smul_orbit_mem_ker_sq {d : ℕ+} (hd : 1 < d) :
    ((d : ℕ) : ℤ) • orbit d ∈ RingHom.ker (ghostComponent 1) ^ 2 := by
  rw [← orbit_mul_self, pow_two]
  exact Ideal.mul_mem_mul (orbit_mem_ker hd) (orbit_mem_ker hd)

/-- For coprime `a, b ≥ 2` the orbit `e_{ab} = e_a e_b` lies in `I²`: off the prime powers the
conormal class vanishes. -/
theorem orbit_mul_mem_ker_sq_of_coprime {a b : ℕ+} (h : Nat.Coprime a b) (ha : 1 < a)
    (hb : 1 < b) : orbit (a * b) ∈ RingHom.ker (ghostComponent 1) ^ 2 := by
  have hprod : orbit (a * b) = orbit a * orbit b := by
    refine Subtype.ext (funext fun n => ?_)
    change (orbit (a * b)).1 n = (orbit a).1 n * (orbit b).1 n
    rw [orbit_apply, orbit_apply, orbit_apply, PNat.mul_coe]
    by_cases h1 : (a : ℕ) ∣ n
    · by_cases h2 : (b : ℕ) ∣ n
      · rw [if_pos h1, if_pos h2, if_pos (h.mul_dvd_of_dvd_of_dvd h1 h2)]
        push_cast; rfl
      · rw [if_neg h2, if_neg fun hd => h2 ((dvd_mul_left _ _).trans hd), mul_zero]
    · rw [if_neg h1, if_neg fun hd => h1 ((dvd_mul_right _ _).trans hd), zero_mul]
  rw [hprod, pow_two]
  exact Ideal.mul_mem_mul (orbit_mem_ker ha) (orbit_mem_ker hb)

/-- **At a prime the conormal class is not zero**: `e_p ∉ I²`. -/
theorem orbit_notMem_ker_sq {p : ℕ+} (hp : p.Prime) :
    orbit p ∉ RingHom.ker (ghostComponent 1) ^ 2 := by
  intro h
  have hp' : (p : ℕ).Prime := hp
  have hd := pow_dvd_ghostComponent_of_mem_ker_pow hp one_ne_zero h
  rw [pow_one, ghostComponent_apply, orbit_apply, if_pos dvd_rfl] at hd
  have h2 : (p : ℕ) ^ 2 ∣ (p : ℕ) ^ 1 := by
    rw [pow_one]; exact_mod_cast hd
  have := (Nat.pow_dvd_pow_iff_le_right hp'.one_lt).mp h2
  omega

/-! ### The toric surface of a base -/

/-- Restriction of the functions on the surface `Spec ℤ[Y]` to its sections `Y = qⁿ`:
the ring homomorphism `Y ↦ [q]` into the arithmetic square. -/
noncomputable def surfaceMap (q : ℤ) : ℤ[X] →+* ghostRing :=
  eval₂RingHom (Int.castRingHom ghostRing) (teichmuller q)

/-- The `n`-th component of a function on the surface is its value on the section `Y = qⁿ`. -/
theorem ghostComponent_surfaceMap (q : ℤ) (n : ℕ+) (Q : ℤ[X]) :
    ghostComponent n (surfaceMap q Q) = Q.eval (q ^ (n : ℕ)) := by
  have h : (ghostComponent n).comp (surfaceMap q) = evalRingHom (q ^ (n : ℕ)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [surfaceMap]
    · simp [surfaceMap]
  exact congrArg (fun φ : ℤ[X] →+* ℤ => φ Q) h

/-- **The diagonal of the surface has a normal direction.** A function lies in the square of the
ideal of `Y = q` iff it and its derivative vanish at `q`: the conormal module is free of rank one,
spanned by `d(Y − q)`. -/
theorem X_sub_C_sq_dvd_iff (q : ℤ) (Q : ℤ[X]) :
    (X - C q) ^ 2 ∣ Q ↔ Q.eval q = 0 ∧ Q.derivative.eval q = 0 := by
  constructor
  · rintro ⟨R, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [derivative_mul, eval_add, eval_mul, eval_mul, pow_two, derivative_mul]
    simp
  · rintro ⟨h0, h1⟩
    obtain ⟨Q₁, rfl⟩ := dvd_iff_isRoot.mpr h0
    have hQ₁ : Q₁.eval q = 0 := by simpa [derivative_mul] using h1
    obtain ⟨Q₂, rfl⟩ := dvd_iff_isRoot.mpr hQ₁
    exact ⟨Q₂, by ring⟩

/-- Taylor to second order along the section `Y = q^p`: for `Q(q) = 0`,
`Q(q^p) ≡ Q'(q)(q^p − q) (mod p²)`. -/
theorem sq_dvd_eval_pow_sub {p : ℕ} (hp : p.Prime) (q : ℤ) {Q : ℤ[X]} (hQ : Q.eval q = 0) :
    (p : ℤ) ^ 2 ∣ Q.eval (q ^ p) - Q.derivative.eval q * (q ^ p - q) := by
  obtain ⟨k, hk⟩ := Q.binomExpansion q (q ^ p - q)
  rw [add_sub_cancel] at hk
  rw [hk, hQ, zero_add, add_sub_cancel_left]
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (prime_dvd_pow_sub_self hp q) 2) k

/-- **The normal derivative restricts to the `p`-derivation through the Fermat quotient.** For a
function `Q` on the surface vanishing on the diagonal, the necklace coordinate at `p` of its
restriction to the graphs is `Q'(q) · (q^p − q)/p` modulo `p`. -/
theorem prime_dvd_coord_surfaceMap_sub {p : ℕ+} (hp : p.Prime) (q : ℤ) {Q : ℤ[X]}
    (hQ : Q.eval q = 0) :
    ((p : ℕ) : ℤ) ∣ coord (surfaceMap q Q) p -
      Q.derivative.eval q * ((q ^ (p : ℕ) - q) / ((p : ℕ) : ℤ)) := by
  have hp' : (p : ℕ).Prime := hp
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have hx1 : ghostComponent 1 (surfaceMap q Q) = 0 := by
    rw [ghostComponent_surfaceMap, PNat.one_coe, pow_one, hQ]
  have hxp := ghostComponent_prime_eq (surfaceMap q Q) hp
  rw [hx1, zero_add, ghostComponent_surfaceMap] at hxp
  have hφ : ((p : ℕ) : ℤ) * ((q ^ (p : ℕ) - q) / ((p : ℕ) : ℤ)) = q ^ (p : ℕ) - q :=
    Int.mul_ediv_cancel' (prime_dvd_pow_sub_self hp' q)
  have h2 := sq_dvd_eval_pow_sub hp' q hQ
  have hrw : Q.eval (q ^ (p : ℕ)) - Q.derivative.eval q * (q ^ (p : ℕ) - q) =
      ((p : ℕ) : ℤ) * (coord (surfaceMap q Q) p -
        Q.derivative.eval q * ((q ^ (p : ℕ) - q) / ((p : ℕ) : ℤ))) := by
    linear_combination hxp + Q.derivative.eval q * hφ
  rw [hrw, sq] at h2
  exact (mul_dvd_mul_iff_left hp0).mp h2

/-- The contact of the diagonal with the section `Y = qⁿ` on the surface, `qⁿ − q`, lies in the
graph ideal of the arithmetic square. -/
theorem pow_sub_self_mem_graphIdeal (q : ℤ) (n : ℕ+) : q ^ (n : ℕ) - q ∈ graphIdeal 1 n := by
  have h : ghostComponent 1 (teichmuller q) - ghostComponent n (teichmuller q) ∈ graphIdeal 1 n :=
    Ideal.subset_span ⟨teichmuller q, rfl⟩
  rw [ghostComponent_teichmuller, ghostComponent_teichmuller, PNat.one_coe, pow_one] at h
  have := (Ideal.neg_mem_iff _).mpr h
  rwa [neg_sub] at this

/-- **The forced zeros on a section are the contacts.** A function vanishing to order `ℓ` on the
diagonal `Y = q` is divisible by `(qⁿ − q)^ℓ` on the section `Y = qⁿ`. -/
theorem pow_dvd_eval_of_pow_dvd (q : ℤ) (n l : ℕ) {Q : ℤ[X]} (h : (X - C q) ^ l ∣ Q) :
    (q ^ n - q) ^ l ∣ Q.eval (q ^ n) := by
  have := eval_dvd (x := q ^ n) h
  simpa using this

/-- The bound is attained by `(Y − q)^ℓ`. -/
theorem eval_X_sub_C_pow (q : ℤ) (n l : ℕ) : ((X - C q) ^ l : ℤ[X]).eval (q ^ n) = (q ^ n - q) ^ l := by
  simp

/-! ### Sections with a rank count -/

theorem teichmuller_pow (a : ℤ) (j : ℕ) : teichmuller (a ^ j) = teichmuller a ^ j := by
  refine Subtype.ext (funext fun n => ?_)
  rw [Subring.coe_pow, Pi.pow_apply, teichmuller_apply, teichmuller_apply, pow_right_comm]

/-- The section `Σ_{j < b} c_j [q]^j` of the surface with coefficient vector `c`. -/
def digitLatticeMap (q : ℕ+) (b : ℕ) : (Fin b → ℤ) →+ ghostRing where
  toFun c := ∑ j : Fin b, c j • teichmuller (((q : ℕ) : ℤ)) ^ (j : ℕ)
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]

/-- For a base `q ≥ 2` the powers of `[q]` are independent: a section determines its
coefficients. -/
theorem digitLatticeMap_injective {q : ℕ+} (hq : 1 < q) (b : ℕ) :
    Function.Injective (digitLatticeMap q b) := by
  have hq2 : 2 ≤ (q : ℕ) := hq
  have hinj : Function.Injective fun j : Fin b => q ^ (j : ℕ) := fun i j hij => Fin.ext (by
    have h : ((q ^ (i : ℕ) : ℕ+) : ℕ) = ((q ^ (j : ℕ) : ℕ+) : ℕ) := congrArg _ hij
    rw [PNat.pow_coe, PNat.pow_coe] at h
    exact Nat.pow_right_injective hq2 h)
  have hLI := linearIndependent_teichmuller.comp _ hinj
  refine (injective_iff_map_eq_zero _).mpr fun c hc => funext fun j => ?_
  refine Fintype.linearIndependent_iff.mp hLI c ?_ j
  rw [← hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, PNat.pow_coe, Nat.cast_pow, teichmuller_pow]

open scoped Classical in
/-- **The rank count.** For a base `q ≥ 2` there are exactly `(2A + 1)^b` sections of degree `< b`
with coefficients of absolute value `≤ A`: the logarithm of the count is bilinear in the two
degrees. -/
theorem card_image_digitLatticeMap {q : ℕ+} (hq : 1 < q) (A b : ℕ) :
    ((Fintype.piFinset fun _ : Fin b => Finset.Icc (-(A : ℤ)) A).image
      (digitLatticeMap q b)).card = (2 * A + 1) ^ b := by
  have hcard : (Finset.Icc (-(A : ℤ)) A).card = 2 * A + 1 := by
    rw [Int.card_Icc]; omega
  rw [Finset.card_image_of_injective _ (digitLatticeMap_injective hq b), Fintype.card_piFinset]
  simp [hcard]

/-- **Restriction to `Γ_n` multiplies the second degree by `n`**: `|x_n| ≤ b · A · (q^b)ⁿ`. -/
theorem abs_ghostComponent_digitLatticeMap_le (q : ℕ+) {A b : ℕ} {c : Fin b → ℤ}
    (hc : ∀ j, |c j| ≤ A) (n : ℕ+) :
    |ghostComponent n (digitLatticeMap q b c)| ≤
      (b : ℤ) * (A * ((((q : ℕ) : ℤ)) ^ b) ^ (n : ℕ)) := by
  have hq1 : (1 : ℤ) ≤ ((q : ℕ) : ℤ) := by exact_mod_cast q.pos
  have hcomp : ghostComponent n (digitLatticeMap q b c) =
      ∑ j : Fin b, c j * ((((q : ℕ) : ℤ)) ^ (n : ℕ)) ^ (j : ℕ) := by
    change ghostComponent n (∑ j : Fin b, c j • teichmuller (((q : ℕ) : ℤ)) ^ (j : ℕ)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_pow, ghostComponent_teichmuller, smul_eq_mul]
  rw [hcomp]
  calc |∑ j : Fin b, c j * ((((q : ℕ) : ℤ)) ^ (n : ℕ)) ^ (j : ℕ)|
      ≤ ∑ j : Fin b, |c j * ((((q : ℕ) : ℤ)) ^ (n : ℕ)) ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin b, (A : ℤ) * ((((q : ℕ) : ℤ)) ^ b) ^ (n : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hpos : (0 : ℤ) ≤ ((((q : ℕ) : ℤ)) ^ (n : ℕ)) ^ (j : ℕ) := by positivity
        have hle : ((((q : ℕ) : ℤ)) ^ (n : ℕ)) ^ (j : ℕ) ≤ ((((q : ℕ) : ℤ)) ^ b) ^ (n : ℕ) := by
          rw [← pow_mul, ← pow_mul]
          exact pow_le_pow_right₀ hq1 (by
            have := j.isLt
            nlinarith [n.pos])
        rw [abs_mul, abs_of_nonneg hpos]
        exact mul_le_mul (hc j) hle hpos (by positivity)
    _ = (b : ℤ) * (A * ((((q : ℕ) : ℤ)) ^ b) ^ (n : ℕ)) := by simp

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
