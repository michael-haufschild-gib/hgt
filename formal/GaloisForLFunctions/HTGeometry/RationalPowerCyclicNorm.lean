import GaloisForLFunctions.HTGeometry.GeneralPrimaryFactor
import GaloisForLFunctions.HTGeometry.RootOfUnityPacketFilter

/-!
# Root-of-unity filtering of primary factors and the rational-power cyclic norm

For a positive real exponent `a`, the *power canonical product*

`W_a(z) = ∏_{n ≥ 1} E_{⌊1/a⌋}(-z / n^a)`

is the Weierstrass canonical product of minimal genus with simple zeros exactly at `-n^a`.  The
genus choice `g(a) = ⌊1/a⌋` is admissible because `a · (g(a) + 1) > 1`.

This file proves the exact cyclic-norm law for rational exponents.  Let `p, q` be positive
integers and let `ω` be a primitive `q`-th root of unity.  Then

`∏_{j < q} W_{p/q}(ω^j z) = W_p((-1)^{q+1} z^q)`.

The identity is exact: no asymptotic equivalence, regularisation, or exponential-polynomial
counterterm appears.  It rests on two finite facts about the Weierstrass primary factor
`E_g(w) = (1 - w) exp(∑_{r=1}^{g} w^r / r)`:

* the *linear filter* `∏_{j<q} (1 + ω^j u) = 1 - (-u)^q`, obtained by evaluating the
  factorisation of `X^q - (-u)^q` at `X = 1`;
* the *exponential filter* `∑_{j<q} exponent_g(-ω^j u) = exponent_{⌊g/q⌋}((-u)^q)`, obtained from
  the orthogonality relation `∑_{j<q} ω^{jr} = q · [q ∣ r]`, which kills every degree not divisible
  by `q` and divides the surviving degrees by `q`.

Together they give the packet identity `∏_{j<q} E_g(-ω^j u) = E_{⌊g/q⌋}((-u)^q)`.  Combined with
the genus bookkeeping `⌊⌊q/p⌋/q⌋ = ⌊1/p⌋`, the exponent `q`-th power `(n^{p/q})^q = n^p`, and the
interchange of a finite product with the locally uniformly convergent canonical product, this
yields the cyclic-norm law.
-/

namespace HTGeometry

open Finset Polynomial

section RootOfUnityFilter

variable {q : ℕ} {ω : ℂ}

/-- **Exponential filter.**  The genus-`g` primary exponent, summed over the root-of-unity packet,
is the genus-`⌊g/q⌋` primary exponent of the `q`-th power.

Degrees not divisible by `q` are annihilated by orthogonality; a surviving degree `q·m ≤ g`
contributes `q · (-u)^{qm} / (qm) = ((-u)^q)^m / m`, and the surviving `m` are exactly
`1 ≤ m ≤ ⌊g/q⌋`. -/
theorem sum_primaryExponent_primitiveRoot (g : ℕ) (hq : 0 < q) (hω : IsPrimitiveRoot ω q) (u : ℂ) :
    ∑ j ∈ Finset.range q, primaryExponent g (-(ω ^ j) * u)
      = primaryExponent (g / q) ((-u) ^ q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  induction g with
  | zero => simp [Nat.zero_div]
  | succ g ih =>
    have hsplit : ∀ j : ℕ,
        primaryExponent (g + 1) (-(ω ^ j) * u)
          = primaryExponent g (-(ω ^ j) * u)
            + (-u) ^ (g + 1) * ω ^ (j * (g + 1)) / ((g : ℂ) + 1) := by
      intro j
      have h1 : (-(ω ^ j) * u) ^ (g + 1) = (-u) ^ (g + 1) * ω ^ (j * (g + 1)) := by
        rw [mul_pow, neg_pow, neg_pow, ← pow_mul]
        ring
      rw [primaryExponent_succ, h1]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ih]
    have hfactor : ∑ j ∈ Finset.range q, (-u) ^ (g + 1) * ω ^ (j * (g + 1)) / ((g : ℂ) + 1)
        = (-u) ^ (g + 1) / ((g : ℂ) + 1) *
            (if q ∣ (g + 1) then (q : ℂ) else 0) := by
      rw [← sum_primitiveRoot_pow_mul hω (g + 1), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfactor]
    by_cases hdvd : q ∣ (g + 1)
    · obtain ⟨m, hm⟩ := hdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · simp [h] at hm
        · exact h
      have hdivm : (g + 1) / q = m := by
        rw [hm, Nat.mul_div_cancel_left _ hq]
      have hstep : (g + 1) / q = g / q + 1 := by
        rw [Nat.succ_div, if_pos ⟨m, hm⟩]
      have hgq : g / q + 1 = m := by rw [← hstep, hdivm]
      rw [if_pos ⟨m, hm⟩, hstep, primaryExponent_succ]
      congr 1
      have hgm : ((g : ℂ) + 1) = (q : ℂ) * (m : ℂ) := by
        have hcast : ((g + 1 : ℕ) : ℂ) = ((q * m : ℕ) : ℂ) := by rw [hm]
        push_cast at hcast
        exact hcast
      have hpowm : ((-u) ^ q) ^ (g / q + 1) = (-u) ^ (g + 1) := by
        rw [hgq, ← pow_mul, ← hm]
      have hmC : ((g / q : ℕ) : ℂ) + 1 = (m : ℂ) := by
        have hcast : ((g / q + 1 : ℕ) : ℂ) = ((m : ℕ) : ℂ) := by rw [hgq]
        push_cast at hcast
        exact hcast
      have hmC0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
      rw [hpowm, hmC, hgm]
      field_simp
    · rw [if_neg hdvd, Nat.succ_div, if_neg hdvd]
      simp

/-- **Root-of-unity filter for primary factors.**  For a primitive `q`-th root of unity `ω`,

`∏_{j<q} E_g(-ω^j u) = E_{⌊g/q⌋}((-u)^q)`. -/
theorem prod_primaryFactor_primitiveRoot (g : ℕ) (hq : 0 < q) (hω : IsPrimitiveRoot ω q) (u : ℂ) :
    ∏ j ∈ Finset.range q, primaryFactor g (-(ω ^ j) * u)
      = primaryFactor (g / q) ((-u) ^ q) := by
  simp only [primaryFactor]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum,
    sum_primaryExponent_primitiveRoot g hq hω u]
  congr 1
  rw [← prod_one_add_primitiveRoot_pow_mul hq hω u]
  exact Finset.prod_congr rfl fun j _ => by ring

end RootOfUnityFilter

section PowerCanonicalProduct

/-- The minimal admissible genus `g(a) = ⌊1/a⌋` for the canonical product with zeros `-n^a`.
It is admissible because `a·(g(a)+1) > 1`. -/
noncomputable def powerGenus (a : ℝ) : ℕ := ⌊1 / a⌋₊

/-- The zero sequence `-(n+1)^a` of the power canonical product, indexed by `n : ℕ`. -/
noncomputable def powerZero (a : ℝ) (n : ℕ) : ℂ := -((((n : ℝ) + 1) ^ a : ℝ) : ℂ)

/-- The power canonical product `W_a(z) = ∏_{n ≥ 1} E_{⌊1/a⌋}(-z / n^a)`: the Weierstrass
canonical product of minimal genus with simple zeros exactly at `-n^a`. -/
noncomputable def powerCanonicalProduct (a : ℝ) : ℂ → ℂ :=
  canonicalProduct (powerGenus a) (powerZero a)

@[simp] theorem norm_powerZero (a : ℝ) (n : ℕ) : ‖powerZero a n‖ = ((n : ℝ) + 1) ^ a := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos (by positivity) a
  simp [powerZero, abs_of_pos hpos]

theorem powerZero_ne_zero (a : ℝ) (n : ℕ) : powerZero a n ≠ 0 := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos (by positivity) a
  simp only [powerZero, ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
  exact hpos.ne'

/-- The genus `⌊1/a⌋` is admissible: the `(g+1)`-st inverse powers of the zeros are summable,
because `a·(⌊1/a⌋+1) > 1`. -/
theorem powerZero_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / ‖powerZero a n‖ ^ (powerGenus a + 1)) := by
  have hgt : 1 < a * ((powerGenus a : ℝ) + 1) := by
    have h := Nat.lt_floor_add_one (1 / a)
    have h' : 1 / a < (powerGenus a : ℝ) + 1 := by simpa [powerGenus] using h
    have hmul : a * (1 / a) < a * ((powerGenus a : ℝ) + 1) := by
      exact mul_lt_mul_of_pos_left h' ha
    rwa [mul_one_div, div_self ha.ne'] at hmul
  have hrw : (fun n : ℕ => 1 / ‖powerZero a n‖ ^ (powerGenus a + 1))
      = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (a * ((powerGenus a : ℝ) + 1)) := by
    funext n
    have hb : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [norm_powerZero, ← Real.rpow_natCast (((n : ℝ) + 1) ^ a) (powerGenus a + 1),
      ← Real.rpow_mul hb]
    push_cast
    ring_nf
  rw [hrw]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (a * ((powerGenus a : ℝ) + 1))) :=
    Real.summable_one_div_nat_rpow.mpr hgt
  have hshift := (summable_nat_add_iff (f := fun n : ℕ =>
    1 / (n : ℝ) ^ (a * ((powerGenus a : ℝ) + 1))) 1).mpr hsum
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

/-- The power canonical product is entire. -/
theorem analyticOnNhd_powerCanonicalProduct {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ (powerCanonicalProduct a) Set.univ :=
  canonicalProduct_analytic (powerGenus a) (powerZero a) (powerZero_ne_zero a)
    (powerZero_summable ha)

/-- Pointwise convergence datum for the power canonical product. -/
theorem hasProd_powerCanonicalProduct {a : ℝ} (ha : 0 < a) (z : ℂ) :
    HasProd (fun n : ℕ => primaryFactor (powerGenus a) (z / powerZero a n))
      (powerCanonicalProduct a z) :=
  (canonicalProduct_hasProdLocallyUniformlyOn (powerGenus a) (powerZero a)
    (powerZero_ne_zero a) (powerZero_summable ha)).hasProd (Set.mem_univ z)

/-- Genus bookkeeping: `⌊⌊q/p⌋/q⌋ = ⌊1/p⌋` for natural numbers, with `q > 0`.

Both sides are `1` when `p = 1` and `0` when `p ≥ 2`. -/
theorem nat_div_div_self (p : ℕ) {q : ℕ} (hq : 0 < q) : q / p / q = 1 / p := by
  rw [Nat.div_div_eq_div_mul]
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · simp
    · simp [Nat.div_self hq]
  · have hlt : q < p * q := by
      calc q = 1 * q := (one_mul q).symm
        _ < p * q := (Nat.mul_lt_mul_right hq).mpr (by omega)
    rw [Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega)]

@[simp] theorem powerGenus_natCast (p : ℕ) : powerGenus (p : ℝ) = 1 / p := by
  rw [powerGenus, Nat.floor_div_natCast, Nat.floor_one]

@[simp] theorem powerGenus_ratio (p q : ℕ) :
    powerGenus ((p : ℝ) / (q : ℝ)) = q / p := by
  rw [powerGenus, one_div_div, Nat.floor_div_natCast, Nat.floor_natCast]

/-- **Exact cyclic-norm law.**  For coprimality-free positive integers `p, q` and any primitive
`q`-th root of unity `ω`,

`∏_{j<q} W_{p/q}(ω^j z) = W_p((-1)^{q+1} z^q)`.

Grouping the finite root-of-unity packet at each zero index `n` turns the genus-`⌊q/p⌋` primary
factor of `-ω^j z / n^{p/q}` into the genus-`⌊1/p⌋` primary factor of `(-1)^q z^q / n^p`, which is
exactly the `n`-th factor of the right-hand product.  No regularisation or exponential-polynomial
counterterm occurs. -/
theorem prod_powerCanonicalProduct_primitiveRoot {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {ω : ℂ} (hω : IsPrimitiveRoot ω q) (z : ℂ) :
    ∏ j ∈ Finset.range q, powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)
      = powerCanonicalProduct (p : ℝ) ((-1) ^ (q + 1) * z ^ q) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha : 0 < (p : ℝ) / (q : ℝ) := div_pos hpR hqR
  have h1 : HasProd
      (fun n : ℕ => ∏ j ∈ Finset.range q,
        primaryFactor (powerGenus ((p : ℝ) / (q : ℝ)))
          ((ω ^ j * z) / powerZero ((p : ℝ) / (q : ℝ)) n))
      (∏ j ∈ Finset.range q, powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) :=
    hasProd_prod fun j _ => hasProd_powerCanonicalProduct ha (ω ^ j * z)
  have h2 : HasProd
      (fun n : ℕ => primaryFactor (powerGenus (p : ℝ))
        (((-1) ^ (q + 1) * z ^ q) / powerZero (p : ℝ) n))
      (powerCanonicalProduct (p : ℝ) ((-1) ^ (q + 1) * z ^ q)) :=
    hasProd_powerCanonicalProduct hpR _
  have hkey : ∀ n : ℕ,
      (∏ j ∈ Finset.range q,
          primaryFactor (powerGenus ((p : ℝ) / (q : ℝ)))
            ((ω ^ j * z) / powerZero ((p : ℝ) / (q : ℝ)) n))
        = primaryFactor (powerGenus (p : ℝ))
            (((-1) ^ (q + 1) * z ^ q) / powerZero (p : ℝ) n) := by
    intro n
    set R : ℝ := ((n : ℝ) + 1) ^ ((p : ℝ) / (q : ℝ)) with hRdef
    set S : ℝ := ((n : ℝ) + 1) ^ (p : ℝ) with hSdef
    have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hRpos : (0 : ℝ) < R := Real.rpow_pos_of_pos hbase _
    have hSpos : (0 : ℝ) < S := Real.rpow_pos_of_pos hbase _
    have hRC : ((R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRpos.ne'
    have hSC : ((S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hSpos.ne'
    have hRq : R ^ q = S := by
      rw [hRdef, hSdef, ← Real.rpow_natCast (((n : ℝ) + 1) ^ ((p : ℝ) / (q : ℝ))) q,
        ← Real.rpow_mul hbase.le, div_mul_cancel₀ _ hqR.ne']
    have hzR : powerZero ((p : ℝ) / (q : ℝ)) n = -((R : ℝ) : ℂ) := rfl
    have hzS : powerZero (p : ℝ) n = -((S : ℝ) : ℂ) := rfl
    have hstep : ∀ j : ℕ,
        (ω ^ j * z) / powerZero ((p : ℝ) / (q : ℝ)) n = -(ω ^ j) * (z / ((R : ℝ) : ℂ)) := by
      intro j
      rw [hzR, div_neg]
      ring
    rw [Finset.prod_congr rfl fun j _ => congrArg _ (hstep j),
      prod_primaryFactor_primitiveRoot _ hq hω (z / ((R : ℝ) : ℂ))]
    have hgenus : powerGenus ((p : ℝ) / (q : ℝ)) / q = powerGenus (p : ℝ) := by
      rw [powerGenus_ratio, powerGenus_natCast, nat_div_div_self p hq]
    rw [hgenus]
    congr 1
    have hpow : (((R : ℝ) : ℂ)) ^ q = ((S : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hRq]
    have hnum : (-(z / ((R : ℝ) : ℂ))) ^ q = (-1 : ℂ) ^ q * z ^ q / ((S : ℝ) : ℂ) := by
      rw [neg_pow, div_pow, hpow]
      ring
    rw [hnum, hzS, div_neg, pow_succ]
    ring
  have h1' : HasProd
      (fun n : ℕ => primaryFactor (powerGenus (p : ℝ))
        (((-1) ^ (q + 1) * z ^ q) / powerZero (p : ℝ) n))
      (∏ j ∈ Finset.range q, powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) := by
    simpa only [hkey] using h1
  exact h1'.unique h2

end PowerCanonicalProduct

end HTGeometry
