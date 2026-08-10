import GaloisForLFunctions.HTGeometry.PowerSeriesFactorization
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The Newton slope substitution

A Newton polygon edge of slope `p / q` is realised on polynomials by the substitution
`t = s ^ q`, `X = s ^ p · Y`, followed by division by `s ^ (p · d)`.  The first half is
`PowerSeries.expand q`, the second is division by a power of the variable, and the whole
operation sends a monic polynomial over `K⟦t⟧` to a monic polynomial of the same degree over
`K⟦s⟧` whose special fibre is the edge polynomial of the chosen slope.

Two facts are proved.  A root of the transform produces a root of the expanded polynomial —
this is what turns a Puiseux root of the smaller problem into a Puiseux root of the original —
and the special fibre of the transform is read off coefficientwise as
`coeff (p · (d − i)) (expand q aᵢ)`, which is nonzero exactly when the point `(i, ord aᵢ)` lies
on the edge.

The divisibility hypothesis `X ^ (p (d − i)) ∣ expand q aᵢ` is exactly the statement that the
Newton polygon lies on or above the line of slope `p / q` through the leading vertex, so it is
available for the minimal slope and for no smaller one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

/-! ## Division by a power of the variable -/

variable {R : Type*} [CommRing R]

/-- Division of a power series by `X ^ k`, read off coefficientwise. -/
noncomputable def shiftPow (k : ℕ) (φ : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + k) φ

@[simp]
theorem coeff_shiftPow (k n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (shiftPow k φ) = PowerSeries.coeff (n + k) φ :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem shiftPow_zero (φ : PowerSeries R) : shiftPow 0 φ = φ := by
  ext n
  rw [coeff_shiftPow, Nat.add_zero]

/-- **Dividing by a power of the variable inverts multiplying by it.** -/
theorem X_pow_mul_shiftPow {k : ℕ} {φ : PowerSeries R}
    (h : (PowerSeries.X : PowerSeries R) ^ k ∣ φ) :
    (PowerSeries.X : PowerSeries R) ^ k * shiftPow k φ = φ := by
  ext n
  rcases Nat.lt_or_ge n k with hn | hn
  · have hzero : (PowerSeries.X : PowerSeries R) ^ k ∣
        (PowerSeries.X : PowerSeries R) ^ k * shiftPow k φ := ⟨_, rfl⟩
    rw [PowerSeries.X_pow_dvd_iff] at hzero h
    rw [hzero n hn, h n hn]
  · obtain ⟨d, hd⟩ : ∃ d, n = d + k := ⟨n - k, by omega⟩
    subst hd
    rw [PowerSeries.coeff_X_pow_mul, coeff_shiftPow]

/-- The constant term of the quotient is the coefficient at the divided-out order. -/
theorem constantCoeff_shiftPow (k : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (shiftPow k φ) = PowerSeries.coeff k φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_shiftPow, Nat.zero_add]

variable {K : Type} [Field K]

/-! ## The transform -/

/-- **The Newton transform of slope `p / q`.**  Substitute `t = s ^ q` and `X = s ^ p · Y`, then
divide by `s ^ (p · deg f)`. -/
noncomputable def newtonTransform (f : (PowerSeries K)[X]) (p q : ℕ) (hq : q ≠ 0) :
    (PowerSeries K)[X] :=
  ∑ i ∈ Finset.range (f.natDegree + 1),
    Polynomial.C (shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)))
      * Polynomial.X ^ i

theorem coeff_newtonTransform (f : (PowerSeries K)[X]) (p q : ℕ) (hq : q ≠ 0) (i : ℕ) :
    (newtonTransform f p q hq).coeff i
      = if i ≤ f.natDegree then
          shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)) else 0 := by
  classical
  rw [newtonTransform, Polynomial.finsetSum_coeff]
  by_cases hi : i ≤ f.natDegree
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbd : b < f.natDegree + 1 := Finset.mem_range.1 hb
    have hne : i ≠ b := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]

theorem natDegree_newtonTransform_le (f : (PowerSeries K)[X]) (p q : ℕ) (hq : q ≠ 0) :
    (newtonTransform f p q hq).natDegree ≤ f.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
  rw [coeff_newtonTransform, if_neg (by exact_mod_cast Nat.not_le.2 (by exact_mod_cast hm))]

/-- **The transform of a monic polynomial is monic of the same degree.** -/
theorem monic_newtonTransform {f : (PowerSeries K)[X]} (hf : f.Monic) (p q : ℕ) (hq : q ≠ 0) :
    (newtonTransform f p q hq).Monic ∧ (newtonTransform f p q hq).natDegree = f.natDegree := by
  have hlead : (newtonTransform f p q hq).coeff f.natDegree = 1 := by
    rw [coeff_newtonTransform, if_pos le_rfl, Nat.sub_self, Nat.mul_zero, shiftPow_zero,
      hf.coeff_natDegree, map_one]
  have hle := natDegree_newtonTransform_le f p q hq
  have hge : f.natDegree ≤ (newtonTransform f p q hq).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hlead]; exact one_ne_zero)
  have hdeg : (newtonTransform f p q hq).natDegree = f.natDegree := le_antisymm hle hge
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hlead]

/-! ## What the transform does -/

/-- **The special fibre of the transform is the edge polynomial.**  Its `i`-th coefficient is the
coefficient of `expand q aᵢ` at the height of the line of slope `p / q`, so it is nonzero exactly
when `(i, ord aᵢ)` lies on that line. -/
theorem coeff_map_constantCoeff_newtonTransform (f : (PowerSeries K)[X]) (p q : ℕ) (hq : q ≠ 0)
    {i : ℕ} (hi : i ≤ f.natDegree) :
    ((newtonTransform f p q hq).map (PowerSeries.constantCoeff (R := K))).coeff i
      = PowerSeries.coeff (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)) := by
  rw [Polynomial.coeff_map, coeff_newtonTransform, if_pos hi, constantCoeff_shiftPow]

/-- **A root of the transform is a root of the expanded polynomial, scaled by `s ^ p`.**  This is
the step that converts a Puiseux root of the reduced problem into one of the original. -/
theorem isRoot_map_expand_of_isRoot_newtonTransform {f : (PowerSeries K)[X]}
    (p q : ℕ) (hq : q ≠ 0)
    (hdvd : ∀ i ≤ f.natDegree, (PowerSeries.X : PowerSeries K) ^ (p * (f.natDegree - i)) ∣
      PowerSeries.expand q hq (f.coeff i))
    {y : PowerSeries K} (hy : (newtonTransform f p q hq).IsRoot y) :
    (f.map (PowerSeries.expand (R := K) q hq).toRingHom).IsRoot
      ((PowerSeries.X : PowerSeries K) ^ p * y) := by
  classical
  have hexpand : ∀ i ≤ f.natDegree, PowerSeries.expand q hq (f.coeff i)
      = (PowerSeries.X : PowerSeries K) ^ (p * (f.natDegree - i)) *
        shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)) :=
    fun i hi => (X_pow_mul_shiftPow (hdvd i hi)).symm
  have heval : (newtonTransform f p q hq).eval y
      = ∑ i ∈ Finset.range (f.natDegree + 1),
          shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)) * y ^ i := by
    rw [newtonTransform, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hrewrite : ∀ i ∈ Finset.range (f.natDegree + 1),
      (PowerSeries.expand (R := K) q hq).toRingHom (f.coeff i) *
          ((PowerSeries.X : PowerSeries K) ^ p * y) ^ i
        = (PowerSeries.X : PowerSeries K) ^ (p * f.natDegree) *
          (shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)) * y ^ i) := by
    intro i hi
    have hid : i ≤ f.natDegree := by
      have hmem := Finset.mem_range.1 hi
      omega
    have hcoe : (PowerSeries.expand (R := K) q hq).toRingHom (f.coeff i)
        = PowerSeries.expand q hq (f.coeff i) := rfl
    have hsum : p * (f.natDegree - i) + p * i = p * f.natDegree := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [hcoe]
    nth_rewrite 1 [hexpand i hid]
    rw [mul_pow, ← pow_mul, ← hsum, pow_add]
    ring
  rw [Polynomial.IsRoot, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum_range' _ (n := f.natDegree + 1) (by omega),
    Finset.sum_congr rfl hrewrite, ← Finset.mul_sum, ← heval, hy, mul_zero]

/-! ## Composing the substitution with a further expansion -/

/-- Expanding commutes with division by a power of the variable, at the expanded exponent. -/
theorem expand_shiftPow (N : ℕ) (hN : N ≠ 0) (k : ℕ) (φ : PowerSeries K) :
    PowerSeries.expand N hN (shiftPow k φ) = shiftPow (N * k) (PowerSeries.expand N hN φ) := by
  ext n
  rw [PowerSeries.coeff_expand, coeff_shiftPow, coeff_shiftPow, PowerSeries.coeff_expand]
  by_cases hdvd : N ∣ n
  · obtain ⟨m, rfl⟩ := hdvd
    have h1 : N ∣ N * m + N * k := ⟨m + k, by ring⟩
    rw [if_pos ⟨m, rfl⟩, if_pos h1, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
    congr 1
    rw [← Nat.mul_add, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
  · have hdvd' : ¬ N ∣ (n + N * k) := by
      intro hcon
      have hk : N ∣ N * k := ⟨k, rfl⟩
      exact hdvd ((Nat.dvd_add_iff_left hk).mpr hcon)
    rw [if_neg hdvd, if_neg hdvd']

/-- **A further expansion of the transform is again a transform.**  Substituting `s = u ^ N` in the
slope-`p / q` transform gives the slope-`Np / Nq` transform of the same polynomial, so a Puiseux
root of the transform found after another ramification still feeds the substitution identity. -/
theorem map_expand_newtonTransform (f : (PowerSeries K)[X]) (p q N : ℕ) (hq : q ≠ 0) (hN : N ≠ 0) :
    (newtonTransform f p q hq).map (PowerSeries.expand (R := K) N hN).toRingHom
      = newtonTransform f (N * p) (N * q) (Nat.mul_ne_zero hN hq) := by
  ext i
  rw [Polynomial.coeff_map, coeff_newtonTransform, coeff_newtonTransform]
  by_cases hi : i ≤ f.natDegree
  · rw [if_pos hi, if_pos hi]
    have hcoe : (PowerSeries.expand (R := K) N hN).toRingHom
        (shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i)))
        = PowerSeries.expand N hN
            (shiftPow (p * (f.natDegree - i)) (PowerSeries.expand q hq (f.coeff i))) := rfl
    rw [hcoe, expand_shiftPow, ← PowerSeries.expand_mul N hN q hq]
    congr 2
    ring
  · rw [if_neg hi, if_neg hi, map_zero]

end GaloisForLFunctions.HTGeometry
