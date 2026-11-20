import Mathlib

/-!
# Representation numbers of the norm form of a principal quadratic order

Let `a, b ∈ ℤ` with `Δ = b² + 4a < 0` and `R = ℤ[ω]`, `ω² = a + bω` (`QuadraticAlgebra ℤ a b`),
with norm `N(x + yω) = x² + bxy − ay²`. Assume `R` is a principal ideal ring and let
`r(n) = #{z ∈ R : N(z) = n}` (`repCount`).

* `splitSym a b p ∈ {−1, 0, 1}` records how the rational prime `p` factors in `R`: `−1` if no
  element has norm `p` (then `p` is prime in `R`), `0` if some `π` of norm `p` is associated to its
  conjugate, `1` otherwise.
* `repCount_prime_mul`: `r(pm) = (1 + ε_p) r(m) − ε_p [p ∣ m] r(m/p)`, by sorting the elements of
  norm `pm` according to which prime above `p` divides them.
* `repCount_eq`: `r(n) = r(1) ∑_{d ∣ n} χ(d)`, with `χ` completely multiplicative and
  `χ(p) = ε_p`; the divisor sum obeys the same recursion.
* `splitSym_eq_legendreSym`: `ε_p = (Δ/p)` for odd `p`.
-/

namespace GaloisForLFunctions.RHTower.Deuring

variable {a b : ℤ}

/-! ### The norm form -/

/-- `4 N(x + yω) = (2x + by)² − Δ y²`, `Δ = b² + 4a`. -/
theorem four_mul_qnorm (z : QuadraticAlgebra ℤ a b) :
    4 * z.norm = (2 * z.re + b * z.im) ^ 2 - (b ^ 2 + 4 * a) * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem qnorm_nonneg (hΔ : b ^ 2 + 4 * a < 0) (z : QuadraticAlgebra ℤ a b) : 0 ≤ z.norm := by
  have h := four_mul_qnorm z
  have h1 : 0 ≤ -(b ^ 2 + 4 * a) * z.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [sq_nonneg (2 * z.re + b * z.im)]

theorem qnorm_eq_zero_iff (hΔ : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b} :
    z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h4 := four_mul_qnorm z
    rw [h, mul_zero] at h4
    have him : z.im = 0 := by
      by_contra hne
      have hpos : 0 < z.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      have h1 : 0 < -(b ^ 2 + 4 * a) * z.im ^ 2 := mul_pos (by linarith) hpos
      nlinarith [sq_nonneg (2 * z.re + b * z.im)]
    have hre : z.re = 0 := by
      rw [him] at h4
      have h5 : (2 * z.re) ^ 2 = 0 := by linear_combination (-1 : ℤ) * h4
      have h6 : 2 * z.re = 0 := (pow_eq_zero_iff two_ne_zero).mp h5
      omega
    exact QuadraticAlgebra.ext hre him
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

/-- A quadratic order of negative discriminant is a domain. -/
theorem isDomain_of_disc_neg (hΔ : b ^ 2 + 4 * a < 0) : IsDomain (QuadraticAlgebra ℤ a b) := by
  haveI : NoZeroDivisors (QuadraticAlgebra ℤ a b) := ⟨fun {x y} h => by
    have h' : (x * y).norm = 0 := by rw [h, QuadraticAlgebra.norm_zero]
    rw [map_mul, mul_eq_zero, qnorm_eq_zero_iff hΔ, qnorm_eq_zero_iff hΔ] at h'
    exact h'⟩
  exact NoZeroDivisors.to_isDomain _

theorem isUnit_iff_qnorm_eq_one (hΔ : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b} :
    IsUnit z ↔ z.norm = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  constructor
  · rintro (h | h)
    · exact h
    · have := qnorm_nonneg hΔ z
      omega
  · exact Or.inl

theorem qnorm_intCast (n : ℤ) : (n : QuadraticAlgebra ℤ a b).norm = n ^ 2 := by
  rw [QuadraticAlgebra.norm_intCast, Int.cast_id]

/-- `N(z) = z z̄` in `R`. -/
theorem intCast_qnorm_eq_mul_star (z : QuadraticAlgebra ℤ a b) :
    ((z.norm : ℤ) : QuadraticAlgebra ℤ a b) = z * star z := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  exact (eq_intCast _ _).symm

/-- An integer divides `x + yω` iff it divides `x` and `y`. -/
theorem intCast_dvd_iff {n : ℤ} {z : QuadraticAlgebra ℤ a b} :
    (n : QuadraticAlgebra ℤ a b) ∣ z ↔ n ∣ z.re ∧ n ∣ z.im := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨⟨c.re, ?_⟩, ⟨c.im, ?_⟩⟩
    · show n * c.re + a * 0 * c.im = n * c.re
      ring
    · show n * c.im + 0 * c.re + b * 0 * c.im = n * c.im
      ring
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, y⟩, QuadraticAlgebra.ext ?_ ?_⟩
    · show z.re = n * x + a * 0 * y
      rw [hx]
      ring
    · show z.im = n * y + 0 * x + b * 0 * y
      rw [hy]
      ring

theorem star_dvd_of_dvd_star {x t : QuadraticAlgebra ℤ a b} (h : x ∣ star t) : star x ∣ t := by
  obtain ⟨c, hc⟩ := h
  exact ⟨star c, by rw [← star_mul', ← hc, star_star]⟩

/-! ### Counting elements of given norm -/

/-- The elements of norm `n`. -/
def normSet (a b : ℤ) (n : ℤ) : Set (QuadraticAlgebra ℤ a b) := {z | z.norm = n}

/-- The elements of norm `N` divisible by `w`. -/
def normDvdSet (a b : ℤ) (N : ℤ) (w : QuadraticAlgebra ℤ a b) : Set (QuadraticAlgebra ℤ a b) :=
  {t | t.norm = N ∧ w ∣ t}

theorem finite_normSet (hΔ : b ^ 2 + 4 * a < 0) (n : ℤ) : (normSet a b n).Finite := by
  have hinj : Function.Injective
      (fun z : QuadraticAlgebra ℤ a b => (z.im, 2 * z.re + b * z.im)) := by
    intro z w h
    have h1 : z.im = w.im := congrArg Prod.fst h
    have h2 : 2 * z.re + b * z.im = 2 * w.re + b * w.im := congrArg Prod.snd h
    rw [h1] at h2
    exact QuadraticAlgebra.ext (by linarith) h1
  have key : ∀ t : ℤ, t ^ 2 ≤ 4 * |n| → t ∈ Set.Icc (-(4 * |n|)) (4 * |n|) := by
    intro t ht
    have h1 := Int.le_self_sq t
    have h2 := Int.le_self_sq (-t)
    rw [neg_sq] at h2
    exact ⟨by linarith, by linarith⟩
  refine (((Set.finite_Icc (-(4 * |n|)) (4 * |n|)).prod
    (Set.finite_Icc (-(4 * |n|)) (4 * |n|))).preimage hinj.injOn).subset ?_
  intro z hz
  have h4 := four_mul_qnorm z
  rw [show z.norm = n from hz] at h4
  have hn : n ≤ |n| := le_abs_self n
  have h1 : 0 ≤ (-(b ^ 2 + 4 * a) - 1) * z.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hX := sq_nonneg (2 * z.re + b * z.im)
  have hY := sq_nonneg z.im
  have hA : z.im ^ 2 ≤ 4 * |n| := by nlinarith
  have hB : (2 * z.re + b * z.im) ^ 2 ≤ 4 * |n| := by nlinarith
  exact ⟨key _ hA, key _ hB⟩

/-- `r(n)`: the number of elements of norm `n`. -/
noncomputable def repCount (a b : ℤ) (n : ℕ) : ℕ := (normSet a b (n : ℤ)).ncard

/-- Multiplication by `w` of norm `q ≠ 0` maps the elements of norm `n` onto the multiples of `w`
of norm `qn`. -/
theorem ncard_normDvdSet (hΔ : b ^ 2 + 4 * a < 0) {w : QuadraticAlgebra ℤ a b} {q : ℤ}
    (hq : q ≠ 0) (hw : w.norm = q) {N n : ℤ} (hN : N = q * n) :
    (normDvdSet a b N w).ncard = (normSet a b n).ncard := by
  haveI := isDomain_of_disc_neg hΔ
  subst hN
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [QuadraticAlgebra.norm_zero] at hw
    exact hq hw.symm
  have himg : normDvdSet a b (q * n) w = (fun c => w * c) '' normSet a b n := by
    ext t
    constructor
    · rintro ⟨ht, c, rfl⟩
      refine ⟨c, ?_, rfl⟩
      rw [map_mul, hw] at ht
      exact mul_left_cancel₀ hq ht
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      show (w * c).norm = q * n
      rw [map_mul, hw, show c.norm = n from hc]
  rw [himg, Set.ncard_image_of_injective _ (mul_right_injective₀ hw0)]

/-- The multiples of `p` of norm `pm`: `r(m/p)` of them if `p ∣ m`, none otherwise. -/
theorem ncard_normDvdSet_intCast (hΔ : b ^ 2 + 4 * a < 0) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((normDvdSet a b ((p * m : ℕ) : ℤ) ((p : ℤ) : QuadraticAlgebra ℤ a b)).ncard : ℤ) =
      if p ∣ m then (repCount a b (m / p) : ℤ) else 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs with hpm
  · obtain ⟨m', rfl⟩ := hpm
    rw [Nat.mul_div_cancel_left m' hp.pos]
    exact congrArg (Nat.cast : ℕ → ℤ)
      (ncard_normDvdSet hΔ (w := ((p : ℤ) : QuadraticAlgebra ℤ a b)) (n := (m' : ℤ))
        (pow_ne_zero 2 hp0) (qnorm_intCast _) (by push_cast; ring))
  · have hempty : normDvdSet a b ((p * m : ℕ) : ℤ) ((p : ℤ) : QuadraticAlgebra ℤ a b) = ∅ := by
      ext t
      refine ⟨?_, fun h => False.elim h⟩
      rintro ⟨ht, c, rfl⟩
      exfalso
      rw [map_mul, qnorm_intCast, Nat.cast_mul] at ht
      have h1 : (p : ℤ) * ((p : ℤ) * c.norm) = (p : ℤ) * (m : ℤ) := by linear_combination ht
      exact hpm (Int.natCast_dvd_natCast.mp ⟨c.norm, (mul_left_cancel₀ hp0 h1).symm⟩)
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-! ### Primes of `R` above a rational prime -/

/-- An element of prime norm is prime. -/
theorem prime_of_qnorm_eq_prime (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} (hp : p.Prime)
    {π : QuadraticAlgebra ℤ a b} (hπ : π.norm = p) : Prime π := by
  haveI := isDomain_of_disc_neg hΔ
  have hpi : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).irreducible
  refine Irreducible.prime ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · have h := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    rw [hπ] at h
    exact hpi.not_isUnit h
  · have h : π.norm = (x * y).norm := by rw [hxy]
    rw [hπ, map_mul] at h
    exact (hpi.isUnit_or_isUnit h).imp QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr

/-- If no element has norm `p`, then `p` stays prime in `R`: a proper factorization `p = xy` has
`N(x) N(y) = p²` with `N(x) ∉ {1, p²}`. -/
theorem prime_intCast_of_forall_qnorm_ne (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} (hp : p.Prime)
    (hno : ∀ π : QuadraticAlgebra ℤ a b, π.norm ≠ p) :
    Prime ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
  haveI := isDomain_of_disc_neg hΔ
  have hpi := Nat.prime_iff_prime_int.mp hp
  refine Irreducible.prime ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · have h := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    rw [qnorm_intCast] at h
    exact hpi.not_unit ((isUnit_pow_iff two_ne_zero).mp h)
  · have h : ((p : ℤ) : QuadraticAlgebra ℤ a b).norm = (x * y).norm := by rw [hxy]
    rw [qnorm_intCast, map_mul] at h
    have hx := qnorm_nonneg hΔ x
    have hy := qnorm_nonneg hΔ y
    have hnat : x.norm.natAbs * y.norm.natAbs = p ^ 2 := by
      have h' := congrArg Int.natAbs h
      rw [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] at h'
      exact h'.symm
    obtain ⟨i, hi, hxi⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hnat)
    interval_cases i
    · left
      rw [isUnit_iff_qnorm_eq_one hΔ]
      rw [pow_zero] at hxi
      omega
    · rw [pow_one] at hxi
      exact absurd (by omega : x.norm = (p : ℤ)) (hno x)
    · right
      rw [isUnit_iff_qnorm_eq_one hΔ]
      rw [hxi] at hnat
      have hy1 : y.norm.natAbs = 1 :=
        Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [hnat, mul_one])
      omega

open Classical in
/-- The splitting symbol of a rational prime in `R`: `−1` if no element has norm `p`, `0` if some
element of norm `p` is associated to its conjugate, `1` otherwise. -/
noncomputable def splitSym (a b : ℤ) (p : ℕ) : ℤ :=
  if ∃ π : QuadraticAlgebra ℤ a b, π.norm = p then
    if ∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π) then 0 else 1
  else -1

theorem splitSym_of_not_exists {p : ℕ} (h : ¬∃ π : QuadraticAlgebra ℤ a b, π.norm = p) :
    splitSym a b p = -1 := by
  unfold splitSym
  exact if_neg h

theorem splitSym_of_assoc {p : ℕ}
    (h : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π)) :
    splitSym a b p = 0 := by
  unfold splitSym
  rw [if_pos (h.imp fun _ hπ => hπ.1), if_pos h]

theorem splitSym_of_not_assoc {p : ℕ} (h : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p)
    (h' : ¬∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π)) :
    splitSym a b p = 1 := by
  unfold splitSym
  rw [if_pos h, if_neg h']

theorem splitSym_cases (a b : ℤ) (p : ℕ) :
    splitSym a b p = -1 ∨ splitSym a b p = 0 ∨ splitSym a b p = 1 := by
  by_cases hex : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p
  · by_cases hass : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π)
    · exact Or.inr (Or.inl (splitSym_of_assoc hass))
    · exact Or.inr (Or.inr (splitSym_of_not_assoc hex hass))
  · exact Or.inl (splitSym_of_not_exists hex)

/-- **Recursion for the representation numbers**:
`r(pm) = (1 + ε_p) r(m) − ε_p [p ∣ m] r(m/p)`. An element `t` of norm `pm` has `p ∣ t t̄`, so it is
divisible by a prime above `p`; each prime `π` of norm `p` divides `r(m)` such elements, and two
non-associated ones divide `t` together iff `p ∣ t`. -/
theorem repCount_prime_mul (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (repCount a b (p * m) : ℤ) = (1 + splitSym a b p) * repCount a b m -
      splitSym a b p * (if p ∣ m then (repCount a b (m / p) : ℤ) else 0) := by
  haveI := isDomain_of_disc_neg hΔ
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcast : ((p * m : ℕ) : ℤ) = (p : ℤ) * (m : ℤ) := Nat.cast_mul p m
  have hdiv : ∀ t : QuadraticAlgebra ℤ a b, t ∈ normSet a b ((p * m : ℕ) : ℤ) →
      ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ t * star t := by
    intro t ht
    rw [← intCast_qnorm_eq_mul_star, show t.norm = ((p * m : ℕ) : ℤ) from ht, hcast,
      Int.cast_mul]
    exact dvd_mul_right _ _
  have hT2 := ncard_normDvdSet_intCast (a := a) (b := b) hΔ hp m
  have hr : repCount a b (p * m) = (normSet a b ((p * m : ℕ) : ℤ)).ncard := rfl
  have hrm : (repCount a b m : ℤ) = ((normSet a b (m : ℤ)).ncard : ℤ) := rfl
  by_cases hex : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p
  · by_cases hass : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π)
    · -- one prime above the rational prime, associated to its conjugate
      rw [splitSym_of_assoc hass]
      obtain ⟨π, hπ, hassoc⟩ := hass
      have hπp := prime_of_qnorm_eq_prime hΔ hp hπ
      have hππ : π * star π = ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
        rw [← intCast_qnorm_eq_mul_star, hπ]
      have hall : normSet a b ((p * m : ℕ) : ℤ) = normDvdSet a b ((p * m : ℕ) : ℤ) π := by
        ext t
        refine ⟨fun ht => ⟨ht, ?_⟩, fun ht => ht.1⟩
        rcases hπp.dvd_or_dvd ((Dvd.intro _ hππ).trans (hdiv t ht)) with h | h
        · exact h
        · exact hassoc.dvd_iff_dvd_left.mpr (star_dvd_of_dvd_star h)
      rw [hr, hall, ncard_normDvdSet hΔ hp0 hπ hcast, hrm]
      ring
    · -- two non-associated conjugate primes: inclusion–exclusion
      rw [splitSym_of_not_assoc hex hass]
      obtain ⟨π, hπ⟩ := hex
      have hπp := prime_of_qnorm_eq_prime hΔ hp hπ
      have hσ : (star π).norm = p := by rw [QuadraticAlgebra.norm_star, hπ]
      have hσp := prime_of_qnorm_eq_prime hΔ hp hσ
      have hna : ¬Associated π (star π) := fun h => hass ⟨π, hπ, h⟩
      have hππ : π * star π = ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
        rw [← intCast_qnorm_eq_mul_star, hπ]
      have hU : normSet a b ((p * m : ℕ) : ℤ) =
          normDvdSet a b ((p * m : ℕ) : ℤ) π ∪ normDvdSet a b ((p * m : ℕ) : ℤ) (star π) := by
        ext t
        constructor
        · intro ht
          rcases hπp.dvd_or_dvd ((Dvd.intro _ hππ).trans (hdiv t ht)) with h | h
          · exact Or.inl ⟨ht, h⟩
          · exact Or.inr ⟨ht, star_dvd_of_dvd_star h⟩
        · rintro (h | h)
          · exact h.1
          · exact h.1
      have hI : normDvdSet a b ((p * m : ℕ) : ℤ) π ∩ normDvdSet a b ((p * m : ℕ) : ℤ) (star π) =
          normDvdSet a b ((p * m : ℕ) : ℤ) ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
        ext t
        constructor
        · rintro ⟨⟨ht, c, rfl⟩, -, h2⟩
          refine ⟨ht, ?_⟩
          have h3 : star π ∣ c := (hσp.dvd_or_dvd h2).resolve_left fun h =>
            hna (hσp.irreducible.associated_of_dvd hπp.irreducible h).symm
          obtain ⟨d, rfl⟩ := h3
          exact ⟨d, by rw [← mul_assoc, hππ]⟩
        · rintro ⟨ht, h⟩
          exact ⟨⟨ht, (Dvd.intro _ hππ).trans h⟩, ht, (Dvd.intro_left _ hππ).trans h⟩
      have hfin := finite_normSet (a := a) (b := b) hΔ ((p * m : ℕ) : ℤ)
      have hie := Set.ncard_union_add_ncard_inter
        (normDvdSet a b ((p * m : ℕ) : ℤ) π) (normDvdSet a b ((p * m : ℕ) : ℤ) (star π))
        (hfin.subset fun t ht => ht.1) (hfin.subset fun t ht => ht.1)
      rw [← hU, hI, ncard_normDvdSet hΔ hp0 hπ hcast, ncard_normDvdSet hΔ hp0 hσ hcast,
        ← hr] at hie
      have hie' := congrArg (Nat.cast : ℕ → ℤ) hie
      rw [Nat.cast_add, Nat.cast_add, hT2] at hie'
      rw [hrm]
      linarith
  · -- the rational prime stays prime
    rw [splitSym_of_not_exists hex]
    have hpp := prime_intCast_of_forall_qnorm_ne hΔ hp fun π h => hex ⟨π, h⟩
    have hall : normSet a b ((p * m : ℕ) : ℤ) =
        normDvdSet a b ((p * m : ℕ) : ℤ) ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
      ext t
      refine ⟨fun ht => ⟨ht, ?_⟩, fun ht => ht.1⟩
      rcases hpp.dvd_or_dvd (hdiv t ht) with h | h
      · exact h
      · have h' := star_dvd_of_dvd_star h
        rwa [star_intCast] at h'
    rw [hr, hall, hT2]
    ring

/-! ### The divisor sum -/

/-- The completely multiplicative function with `χ(p) = ε_p`; `χ(0) = 0`. -/
noncomputable def chi (a b : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p k => splitSym a b p ^ k

theorem chi_zero : chi a b 0 = 0 := by rw [chi, if_pos rfl]

theorem chi_one : chi a b 1 = 1 := by
  rw [chi, if_neg one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]

theorem chi_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    chi a b (m * n) = chi a b m * chi a b n := by
  rw [chi, chi, chi, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem chi_prime {p : ℕ} (hp : p.Prime) : chi a b p = splitSym a b p := by
  rw [chi, if_neg hp.ne_zero, hp.factorization]
  simp only [Finsupp.prod_single_index, pow_zero, pow_one]

theorem abs_chi_le_one (a b : ℤ) (n : ℕ) : |chi a b n| ≤ 1 := by
  unfold chi
  split_ifs
  · simp
  · rw [Finsupp.prod, Finset.abs_prod]
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => ?_)
    rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rcases splitSym_cases a b p with h | h | h <;> rw [h] <;> norm_num

/-- `g(n) = ∑_{d ∣ n} χ(d)`. -/
noncomputable def divSum (a b : ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi a b d

theorem divSum_one : divSum a b 1 = 1 := by
  rw [divSum, Nat.divisors_one, Finset.sum_singleton, chi_one]

/-- The divisor sum obeys the recursion of the representation numbers: the divisors of `pm` are
those of `m` and their `p`-multiples, overlapping in the `p`-multiples of the divisors of `m/p`. -/
theorem divSum_prime_mul {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) :
    divSum a b (p * m) = (1 + splitSym a b p) * divSum a b m -
      splitSym a b p * (if p ∣ m then divSum a b (m / p) else 0) := by
  have hp0 := hp.pos
  have hU : (p * m).divisors = m.divisors ∪ m.divisors.image (p * ·) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      by_cases hpd : p ∣ d
      · obtain ⟨e, rfl⟩ := hpd
        exact Or.inr ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hd, hm.ne'⟩, rfl⟩
      · exact Or.inl ⟨((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm.dvd_of_dvd_mul_left hd,
          hm.ne'⟩
    · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact ⟨Dvd.dvd.mul_left hd p, (Nat.mul_pos hp0 hm).ne'⟩
      · exact ⟨Nat.mul_dvd_mul_left p he, (Nat.mul_pos hp0 hm).ne'⟩
  have hI : m.divisors ∩ m.divisors.image (p * ·) =
      if p ∣ m then (m / p).divisors.image (p * ·) else ∅ := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, e, -, rfl⟩
      have hpm : p ∣ m := (Dvd.intro e rfl).trans hd
      rw [if_pos hpm]
      obtain ⟨k, rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left k hp0]
      simp only [Finset.mem_image, Nat.mem_divisors]
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hd, by
        rintro rfl
        simp at hm⟩, rfl⟩
    · intro h
      split_ifs at h with hpm
      · simp only [Finset.mem_image, Nat.mem_divisors] at h
        obtain ⟨e, ⟨he, -⟩, rfl⟩ := h
        obtain ⟨k, rfl⟩ := hpm
        rw [Nat.mul_div_cancel_left k hp0] at he
        exact ⟨⟨Nat.mul_dvd_mul_left p he, hm.ne'⟩, e,
          ⟨he.trans (Dvd.intro_left p rfl), hm.ne'⟩, rfl⟩
      · simp at h
  have hne : ∀ n : ℕ, ∀ d ∈ n.divisors, d ≠ 0 := fun n d hd => (Nat.pos_of_mem_divisors hd).ne'
  have hsum : ∀ D : Finset ℕ, (∀ d ∈ D, d ≠ 0) →
      ∑ d ∈ D.image (p * ·), chi a b d = splitSym a b p * ∑ d ∈ D, chi a b d := fun D hD => by
    rw [Finset.sum_image (mul_right_injective₀ hp.ne_zero).injOn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d hd => by rw [chi_mul hp.ne_zero (hD d hd), chi_prime hp]
  have h := Finset.sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (p * ·))
    (f := chi a b)
  rw [← hU, hI, hsum _ (hne m)] at h
  unfold divSum
  split_ifs at h ⊢ with hpm
  · rw [hsum _ (hne (m / p))] at h
    linarith
  · rw [Finset.sum_empty, add_zero] at h
    linarith

/-- **The representation numbers of a principal quadratic order**:
`r(n) = r(1) ∑_{d ∣ n} χ(d)` for `n ≥ 1`. -/
theorem repCount_eq (hΔ : b ^ 2 + 4 * a < 0) [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)]
    {n : ℕ} (hn : 0 < n) : (repCount a b n : ℤ) = repCount a b 1 * divSum a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [divSum_one, mul_one]
    -- split off the least prime factor
    obtain ⟨p, hp, m, rfl⟩ : ∃ p : ℕ, p.Prime ∧ ∃ m, n = p * m :=
      ⟨n.minFac, Nat.minFac_prime hn1, Nat.minFac_dvd n⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by
      rintro rfl
      simp at hn)
    have hmn : m < p * m := lt_mul_left hm0 hp.one_lt
    rw [repCount_prime_mul hΔ hp, divSum_prime_mul hp hm0, ih m hmn hm0]
    split_ifs with hpm
    · have hq0 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
      have hqn : m / p < p * m := (Nat.div_le_self m p).trans_lt hmn
      rw [ih (m / p) hqn hq0]
      ring
    · ring

/-! ### The splitting symbol at odd primes is the Legendre symbol of `Δ` -/

/-- An element of prime norm `p` has `p ∤ y`: otherwise `p ∣ x` and `p² ∣ N`. -/
theorem not_dvd_im_of_qnorm_eq_prime {p : ℕ} (hp : p.Prime) {π : QuadraticAlgebra ℤ a b}
    (hπ : π.norm = p) : ¬(p : ℤ) ∣ π.im := by
  rintro ⟨c, hc⟩
  have hpi := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := hπ
  rw [QuadraticAlgebra.norm_def] at h
  have hn : (p : ℤ) = π.re * π.re + b * π.re * π.im - a * π.im * π.im := by
    linear_combination (-1 : ℤ) * h
  have hre2 : (p : ℤ) ∣ π.re * π.re :=
    ⟨1 - b * π.re * c + a * c * π.im, by
      linear_combination (-1 : ℤ) * hn + (-b * π.re + a * π.im) * hc⟩
  obtain ⟨e, he⟩ := (hpi.dvd_or_dvd hre2).elim id id
  have h1 : (p : ℤ) * ((p : ℤ) * (e * e + b * e * c - a * c * c)) = (p : ℤ) * 1 := by
    rw [he, hc] at hn
    linear_combination (-1 : ℤ) * hn
  exact hpi.not_unit (isUnit_of_dvd_one ⟨_, (mul_left_cancel₀ hp0 h1).symm⟩)

/-- If some element has norm `p`, then `Δ` is a square modulo `p`:
`(2x + by)² ≡ Δ y²` with `p ∤ y`. -/
theorem isSquare_disc_of_qnorm_eq_prime {p : ℕ} [Fact p.Prime] {π : QuadraticAlgebra ℤ a b}
    (hπ : π.norm = p) : IsSquare ((b ^ 2 + 4 * a : ℤ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hy : ((π.im : ℤ) : ZMod p) ≠ 0 := fun h0 =>
    not_dvd_im_of_qnorm_eq_prime hp hπ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  have hinv : ((π.im : ℤ) : ZMod p) * ((π.im : ℤ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hy
  have h4 : ((4 * (p : ℤ) : ℤ) : ZMod p) =
      (((2 * π.re + b * π.im) ^ 2 - (b ^ 2 + 4 * a) * π.im ^ 2 : ℤ) : ZMod p) := by
    rw [← hπ, four_mul_qnorm]
  have hp0 : ((4 * (p : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero]
  rw [hp0] at h4
  push_cast at h4
  refine ⟨(2 * ((π.re : ℤ) : ZMod p) + (b : ZMod p) * ((π.im : ℤ) : ZMod p)) *
    ((π.im : ℤ) : ZMod p)⁻¹, ?_⟩
  push_cast
  linear_combination ((π.im : ℤ) : ZMod p)⁻¹ ^ 2 * h4 -
    ((b : ZMod p) ^ 2 + 4 * (a : ZMod p)) *
      (1 + ((π.im : ℤ) : ZMod p) * ((π.im : ℤ) : ZMod p)⁻¹) * hinv

/-- If `Δ` is a square modulo an odd prime `p`, some element has norm `p`: with `2r ≡ b + √Δ`,
`p` divides `N(ω − r)` but neither `ω − r` nor its conjugate, so `p` is not prime in `R`. -/
theorem exists_qnorm_eq_prime_of_isSquare (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hsq : IsSquare ((b ^ 2 + 4 * a : ℤ) : ZMod p)) :
    ∃ π : QuadraticAlgebra ℤ a b, π.norm = p := by
  have hp : p.Prime := Fact.out
  have hpi := Nat.prime_iff_prime_int.mp hp
  by_contra hno
  have hpp := prime_intCast_of_forall_qnorm_ne hΔ hp fun π h => hno ⟨π, h⟩
  obtain ⟨c, hc⟩ := hsq
  push_cast at hc
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h22 : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  obtain ⟨r, hr⟩ := ZMod.intCast_surjective (((b : ZMod p) + c) * (2 : ZMod p)⁻¹)
  have h2r : 2 * (r : ZMod p) = (b : ZMod p) + c := by
    rw [hr, mul_comm (2 : ZMod p) _, mul_assoc, inv_mul_cancel₀ h2, mul_one]
  have h4G : 4 * ((r : ZMod p) ^ 2 - (b : ZMod p) * (r : ZMod p) - (a : ZMod p)) = 0 := by
    linear_combination (2 * (r : ZMod p) - (b : ZMod p) + c) * h2r - hc
  have hG : ((r ^ 2 - b * r - a : ℤ) : ZMod p) = 0 := by
    push_cast
    exact (mul_eq_zero.mp h4G).resolve_left h4
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hG
  have hnorm : (⟨-r, 1⟩ : QuadraticAlgebra ℤ a b).norm = (p : ℤ) * e := by
    rw [← he]
    show -r * -r + b * -r * 1 - a * 1 * 1 = r ^ 2 - b * r - a
    ring
  have hdvd : ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣
      (⟨-r, 1⟩ : QuadraticAlgebra ℤ a b) * star (⟨-r, 1⟩ : QuadraticAlgebra ℤ a b) := by
    rw [← intCast_qnorm_eq_mul_star, hnorm, Int.cast_mul]
    exact dvd_mul_right _ _
  have hone : ¬(p : ℤ) ∣ 1 := fun h => hpi.not_unit (isUnit_of_dvd_one h)
  rcases hpp.dvd_or_dvd hdvd with h | h
  · exact hone (intCast_dvd_iff.mp h).2
  · have h' := (intCast_dvd_iff.mp h).2
    rw [QuadraticAlgebra.im_star] at h'
    exact hone (dvd_neg.mp h')

/-- A prime element `π` of norm `p` is associated to its conjugate iff `p ∣ Δ`:
`π + π̄ = 2x + by` and `4p = (2x + by)² − Δ y²` with `p ∤ y`. -/
theorem associated_star_iff_dvd_disc (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} (hp : p.Prime)
    {π : QuadraticAlgebra ℤ a b} (hπ : π.norm = p) :
    Associated π (star π) ↔ (p : ℤ) ∣ b ^ 2 + 4 * a := by
  haveI := isDomain_of_disc_neg hΔ
  have hpi := Nat.prime_iff_prime_int.mp hp
  have hπp := prime_of_qnorm_eq_prime hΔ hp hπ
  have hσ : (star π).norm = p := by rw [QuadraticAlgebra.norm_star, hπ]
  have hσp := prime_of_qnorm_eq_prime hΔ hp hσ
  have h4 := four_mul_qnorm π
  rw [hπ] at h4
  have hny := not_dvd_im_of_qnorm_eq_prime hp hπ
  have htr : π + star π = ((2 * π.re + b * π.im : ℤ) : QuadraticAlgebra ℤ a b) := by
    refine QuadraticAlgebra.ext ?_ ?_
    · show π.re + (π.re + b * π.im) = 2 * π.re + b * π.im
      ring
    · show π.im + -π.im = 0
      ring
  have hππ : π * star π = ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
    rw [← intCast_qnorm_eq_mul_star, hπ]
  have key : π ∣ star π ↔ (p : ℤ) ∣ 2 * π.re + b * π.im := by
    constructor
    · intro h
      have h1 : π ∣ ((2 * π.re + b * π.im : ℤ) : QuadraticAlgebra ℤ a b) := by
        rw [← htr]
        exact dvd_add dvd_rfl h
      obtain ⟨c, hc⟩ := h1
      have h2 : ((2 * π.re + b * π.im : ℤ) : QuadraticAlgebra ℤ a b).norm = (π * c).norm := by
        rw [hc]
      rw [qnorm_intCast, map_mul, hπ] at h2
      exact hpi.dvd_of_dvd_pow ⟨c.norm, h2⟩
    · rintro ⟨e, he⟩
      have h1 : π ∣ ((2 * π.re + b * π.im : ℤ) : QuadraticAlgebra ℤ a b) :=
        (Dvd.intro _ hππ).trans ⟨(e : QuadraticAlgebra ℤ a b), by rw [he, Int.cast_mul]⟩
      rw [← htr] at h1
      exact (dvd_add_right dvd_rfl).mp h1
  have hassoc : Associated π (star π) ↔ π ∣ star π :=
    ⟨fun h => h.dvd, fun h => hπp.irreducible.associated_of_dvd hσp.irreducible h⟩
  rw [hassoc, key]
  constructor
  · rintro ⟨e, he⟩
    have h1 : (p : ℤ) ∣ (b ^ 2 + 4 * a) * π.im ^ 2 :=
      ⟨(p : ℤ) * e ^ 2 - 4, by
        linear_combination h4 + (2 * π.re + b * π.im + (p : ℤ) * e) * he⟩
    rcases hpi.dvd_or_dvd h1 with h | h
    · exact h
    · exact absurd (hpi.dvd_of_dvd_pow h) hny
  · rintro ⟨e, he⟩
    exact hpi.dvd_of_dvd_pow (n := 2) ⟨4 + e * π.im ^ 2, by
      linear_combination (-1 : ℤ) * h4 + π.im ^ 2 * he⟩

/-- **The splitting symbol at an odd prime is the Legendre symbol of the discriminant.** -/
theorem splitSym_eq_legendreSym (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    splitSym a b p = legendreSym p (b ^ 2 + 4 * a) := by
  have hp : p.Prime := Fact.out
  by_cases hex : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p
  · by_cases hass : ∃ π : QuadraticAlgebra ℤ a b, π.norm = p ∧ Associated π (star π)
    · rw [splitSym_of_assoc hass]
      obtain ⟨π, hπ, h⟩ := hass
      have hd := (associated_star_iff_dvd_disc hΔ hp hπ).mp h
      exact ((legendreSym.eq_zero_iff p _).mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd)).symm
    · rw [splitSym_of_not_assoc hex hass]
      obtain ⟨π, hπ⟩ := hex
      have hne : ((b ^ 2 + 4 * a : ℤ) : ZMod p) ≠ 0 := fun h0 =>
        hass ⟨π, hπ, (associated_star_iff_dvd_disc hΔ hp hπ).mpr
          ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)⟩
      exact ((legendreSym.eq_one_iff p hne).mpr (isSquare_disc_of_qnorm_eq_prime hπ)).symm
  · rw [splitSym_of_not_exists hex]
    exact ((legendreSym.eq_neg_one_iff p).mpr fun hsq =>
      hex (exists_qnorm_eq_prime_of_isSquare hΔ hodd hsq)).symm

end GaloisForLFunctions.RHTower.Deuring
