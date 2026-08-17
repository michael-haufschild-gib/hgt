import GaloisForLFunctions.HTGeometry.MilnorKTameSymbol
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The residue of a rational number modulo a prime

For a prime `p` the reduction

`ratRes p q = q.num / q.den  ∈  ZMod p`

is defined for every rational, and is a unit exactly when neither numerator nor denominator meets
`p`.  The only tool needed for every property of it is the *presentation lemma*: if `q = m / n`
with `p ∤ n`, then `ratRes p q = m̄ / n̄`.  Multiplicativity, the inverse, the value at an integer,
and the congruence criterion all follow from it by one cross-multiplication each.

This is the residue map of the tame symbol on `K_2^M(ℚ)`, with the residue field taken to be
`ZMod p` itself rather than an abstract quotient — so every statement about the tame symbol at `p`
becomes an explicit congruence.
-/

namespace GaloisForLFunctions.HTGeometry

section RationalPadic

theorem intCast_zmod_ne_zero_iff {p : ℕ} {n : ℤ} : ((n : ZMod p) ≠ 0) ↔ ¬ ((p : ℤ) ∣ n) :=
  not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd n p)

theorem natCast_zmod_eq_zero_iff {p : ℕ} {n : ℕ} : ((n : ZMod p) = 0) ↔ p ∣ n := by
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p)

theorem den_cast_ne_zero (q : ℚ) : ((q.den : ℚ)) ≠ 0 := by
  exact_mod_cast q.den_nz

theorem num_eq_mul_den (q : ℚ) : (q.num : ℚ) = q * (q.den : ℚ) :=
  (div_eq_iff (den_cast_ne_zero q)).mp (Rat.num_div_den q)

variable {p : ℕ} [Fact p.Prime]

/-! ## The residue -/

/-- The reduction of a rational modulo `p`. -/
def ratRes (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p := (q.num : ZMod p) / (q.den : ZMod p)

/-- A rational presented as `m / n` with `p ∤ n` has denominator prime to `p`. -/
theorem den_ne_zero_of_eq_div {q : ℚ} {m n : ℤ} (hn : ((n : ZMod p) ≠ 0))
    (h : q = (m : ℚ) / (n : ℚ)) : ((q.den : ZMod p) ≠ 0) := by
  have hdvd : ((q.den : ℤ)) ∣ n := by
    have hq : q = Rat.divInt m n := by rw [h, Rat.divInt_eq_div]
    rw [hq]
    exact Rat.den_dvd m n
  intro hcon
  obtain ⟨c, hc⟩ := hdvd
  refine hn ?_
  have hcast : ((n : ZMod p)) = ((q.den : ℤ) : ZMod p) * (c : ZMod p) := by
    rw [← Int.cast_mul, ← hc]
  have hnat : (((q.den : ℤ)) : ZMod p) = ((q.den : ℕ) : ZMod p) := by push_cast; ring
  rw [hcast, hnat, hcon, zero_mul]

/-- **The presentation lemma.**  A rational presented as `m / n` with `p ∤ n` reduces to `m̄ / n̄`,
whatever presentation is used. -/
theorem ratRes_of_eq_div {q : ℚ} {m n : ℤ} (hn : ((n : ZMod p) ≠ 0)) (h : q = (m : ℚ) / (n : ℚ)) :
    ratRes p q = (m : ZMod p) / (n : ZMod p) := by
  have hn0 : n ≠ 0 := by
    intro hcon
    exact hn (by rw [hcon]; simp)
  have hnQ : ((n : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hn0
  have hdenne : ((q.den : ZMod p) ≠ 0) := den_ne_zero_of_eq_div hn h
  have hcross : q.num * n = m * (q.den : ℤ) := by
    have h1 : (q.num : ℚ) * (n : ℚ) = (m : ℚ) * ((q.den : ℕ) : ℚ) := by
      rw [num_eq_mul_den q, h]
      field_simp
    exact_mod_cast h1
  have hcrossZ : (q.num : ZMod p) * (n : ZMod p) = (m : ZMod p) * ((q.den : ℕ) : ZMod p) := by
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hcross
    push_cast at hc
    exact hc
  simp only [ratRes]
  rw [div_eq_div_iff hdenne hn]
  linear_combination hcrossZ

theorem ratRes_intCast (n : ℤ) : ratRes p (n : ℚ) = (n : ZMod p) := by
  have hone : ((1 : ℤ) : ZMod p) ≠ 0 := by
    simp
  have h := ratRes_of_eq_div (p := p) (q := (n : ℚ)) (m := n) (n := 1) hone (by norm_num)
  rw [h]
  simp

theorem ratRes_natCast (n : ℕ) : ratRes p (n : ℚ) = (n : ZMod p) := by
  have h := ratRes_intCast (p := p) (n : ℤ)
  push_cast at h
  exact h

theorem ratRes_one : ratRes p (1 : ℚ) = 1 := by
  have h := ratRes_natCast (p := p) 1
  push_cast at h
  exact h

/-! ## The `p`-unit rationals -/

/-- A rational is a `p`-unit when neither numerator nor denominator meets `p`. -/
def IsPadicUnit (p : ℕ) [Fact p.Prime] (q : ℚ) : Prop :=
  ((q.num : ZMod p) ≠ 0) ∧ ((q.den : ZMod p) ≠ 0)

theorem IsPadicUnit.ne_zero {q : ℚ} (h : IsPadicUnit p q) : q ≠ 0 := by
  intro hcon
  refine h.1 ?_
  rw [hcon]
  simp

theorem IsPadicUnit.ratRes_ne_zero {q : ℚ} (h : IsPadicUnit p q) : ratRes p q ≠ 0 := by
  simp only [ratRes]
  exact div_ne_zero h.1 h.2

/-- A rational whose residue is nonzero is a `p`-unit. -/
theorem isPadicUnit_of_ratRes_ne_zero {q : ℚ} (h : ratRes p q ≠ 0) : IsPadicUnit p q := by
  constructor
  · intro hcon
    exact h (by simp only [ratRes, hcon, zero_div])
  · intro hcon
    exact h (by simp only [ratRes, hcon, div_zero])

theorem isPadicUnit_one : IsPadicUnit p (1 : ℚ) :=
  isPadicUnit_of_ratRes_ne_zero (by rw [ratRes_one]; exact one_ne_zero)

theorem isPadicUnit_intCast {n : ℤ} (h : ((n : ZMod p) ≠ 0)) : IsPadicUnit p (n : ℚ) :=
  isPadicUnit_of_ratRes_ne_zero (by rw [ratRes_intCast]; exact h)

theorem isPadicUnit_natCast {n : ℕ} (h : ((n : ZMod p) ≠ 0)) : IsPadicUnit p (n : ℚ) :=
  isPadicUnit_of_ratRes_ne_zero (by rw [ratRes_natCast]; exact h)

/-! ## Multiplicativity -/

private theorem ratRes_mul_aux {q r : ℚ} (hq : IsPadicUnit p q) (hr : IsPadicUnit p r) :
    ratRes p (q * r) = ratRes p q * ratRes p r := by
  have hden : (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hq.2 hr.2
  have hqd : ((q.den : ℚ)) ≠ 0 := den_cast_ne_zero q
  have hrd : ((r.den : ℚ)) ≠ 0 := den_cast_ne_zero r
  have hpres : q * r = (((q.num * r.num : ℤ)) : ℚ) / (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [num_eq_mul_den q, num_eq_mul_den r]
    field_simp
  rw [ratRes_of_eq_div (p := p) hden hpres]
  simp only [ratRes]
  push_cast
  rw [div_mul_div_comm]

theorem ratRes_mul {q r : ℚ} (hq : IsPadicUnit p q) (hr : IsPadicUnit p r) :
    ratRes p (q * r) = ratRes p q * ratRes p r := ratRes_mul_aux hq hr

theorem IsPadicUnit.mul {q r : ℚ} (hq : IsPadicUnit p q) (hr : IsPadicUnit p r) :
    IsPadicUnit p (q * r) := by
  refine isPadicUnit_of_ratRes_ne_zero ?_
  rw [ratRes_mul hq hr]
  exact mul_ne_zero hq.ratRes_ne_zero hr.ratRes_ne_zero

theorem ratRes_inv {q : ℚ} (hq : IsPadicUnit p q) : ratRes p q⁻¹ = (ratRes p q)⁻¹ := by
  have hnum : ((q.num : ℚ)) ≠ 0 := Int.cast_ne_zero.2 (Rat.num_ne_zero.2 hq.ne_zero)
  have hden : ((q.den : ℚ)) ≠ 0 := den_cast_ne_zero q
  have hq0 : q ≠ 0 := hq.ne_zero
  have hnum' : (((q.num : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.2 hq0
  have hpres : q⁻¹ = (((q.den : ℤ)) : ℚ) / ((q.num : ℤ) : ℚ) := by
    rw [eq_div_iff hnum']
    push_cast
    rw [num_eq_mul_den q]
    field_simp
  rw [ratRes_of_eq_div (p := p) hq.1 hpres]
  simp only [ratRes]
  push_cast
  rw [inv_div]

theorem IsPadicUnit.inv {q : ℚ} (hq : IsPadicUnit p q) : IsPadicUnit p q⁻¹ := by
  refine isPadicUnit_of_ratRes_ne_zero ?_
  rw [ratRes_inv hq]
  exact inv_ne_zero hq.ratRes_ne_zero

end RationalPadic

end GaloisForLFunctions.HTGeometry
