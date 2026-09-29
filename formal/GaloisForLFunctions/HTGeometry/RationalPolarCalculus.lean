import GaloisForLFunctions.HTGeometry.RittCoefficientRegularity
import GaloisForLFunctions.HTGeometry.RatFuncChainRule

/-!
# Values and residues of rational functions, and their pullbacks

For a rational function `f` over a field of characteristic zero and a point `z`:

* `f` is *regular* at `z` when `ratOrder f z ≥ 0`; its value `ratValue f z` is then additive and
  multiplicative, and vanishes exactly when the order is positive.
* The *residue* `ratResidue f z` is the value of `(X − z)·f` at `z`, meaningful when `f` has at most
a
  simple pole.  The residue of a logarithmic derivative `g'/g` is the order of `g`.
* **Pullback of residues.**  For a rational map `P` regular at `z` with value `w` and local degree
  `e = ord_z(P − w)`, the function `f(P)·P'` has at most a simple pole at `z` when `f` has at most a
  simple pole at `w`, and `res_z(f(P)·P') = e·res_w f`.  Consequently the affine-connection pullback
  `P^*a = a(P)·P' + P''/P'` has residue `e·res_w a + (e − 1)`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### Values -/

omit [CharZero K] in
theorem denom_eval_ne_zero_of_regular {f : RatFunc K} {z : K} (h : 0 ≤ ratOrder f z) :
    f.denom.eval z ≠ 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · exact denom_eval_ne_zero_of_ratOrder_nonneg hf h

omit [CharZero K] in
theorem ratValue_eq_eval (f : RatFunc K) (z : K) :
    ratValue f z = RatFunc.eval (RingHom.id K) z f := by
  simp [ratValue, RatFunc.eval, Polynomial.eval₂_id]

omit [CharZero K] in
theorem ratValue_add {f g : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) (hg : 0 ≤ ratOrder g z) :
    ratValue (f + g) z = ratValue f z + ratValue g z := by
  rw [ratValue_eq_eval, ratValue_eq_eval, ratValue_eq_eval]
  exact RatFunc.eval_add (RingHom.id K) z
    (by simpa [Polynomial.eval₂_id] using denom_eval_ne_zero_of_regular hf)
    (by simpa [Polynomial.eval₂_id] using denom_eval_ne_zero_of_regular hg)

omit [CharZero K] in
theorem ratValue_mul {f g : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) (hg : 0 ≤ ratOrder g z) :
    ratValue (f * g) z = ratValue f z * ratValue g z := by
  rw [ratValue_eq_eval, ratValue_eq_eval, ratValue_eq_eval]
  exact RatFunc.eval_mul (RingHom.id K) z
    (by simpa [Polynomial.eval₂_id] using denom_eval_ne_zero_of_regular hf)
    (by simpa [Polynomial.eval₂_id] using denom_eval_ne_zero_of_regular hg)

omit [CharZero K] in
theorem ratValue_C (a z : K) : ratValue (RatFunc.C a) z = a := by
  rw [ratValue_eq_eval, RatFunc.eval_C]
  rfl

omit [CharZero K] in
theorem ratValue_X (z : K) : ratValue (RatFunc.X : RatFunc K) z = z := by
  rw [ratValue_eq_eval, RatFunc.eval_X]

omit [CharZero K] in
theorem ratValue_zero (z : K) : ratValue (0 : RatFunc K) z = 0 := by
  rw [ratValue_eq_eval, RatFunc.eval_zero]

omit [CharZero K] in
theorem ratValue_one (z : K) : ratValue (1 : RatFunc K) z = 1 := by
  rw [ratValue_eq_eval, RatFunc.eval_one]

omit [CharZero K] in
theorem ratOrder_C_nonneg (a z : K) : 0 ≤ ratOrder (RatFunc.C a : RatFunc K) z := by
  rw [ratOrder_C]

omit [CharZero K] in
theorem ratOrder_X_nonneg (w : K) : 0 ≤ ratOrder (RatFunc.X : RatFunc K) w := by
  have : (RatFunc.X : RatFunc K) = algebraMap K[X] (RatFunc K) Polynomial.X := by simp
  rw [this]
  exact ratOrder_algebraMap_nonneg _ _

omit [CharZero K] in
theorem ratOrder_mul_nonneg {f g : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z)
    (hg : 0 ≤ ratOrder g z) : 0 ≤ ratOrder (f * g) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, ratOrder_zero]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, ratOrder_zero]
  rw [ratOrder_mul hf0 hg0]
  omega

theorem ratOrder_neg_nonneg {f : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) :
    0 ≤ ratOrder (-f) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [neg_zero, ratOrder_zero]
  · rw [ratOrder_neg hf0]; exact hf

theorem ratOrder_sub_nonneg {f g : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z)
    (hg : 0 ≤ ratOrder g z) : 0 ≤ ratOrder (f - g) z := by
  rw [sub_eq_add_neg]
  exact ratOrder_add_nonneg hf (ratOrder_neg_nonneg hg)

theorem ratValue_neg {f : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) :
    ratValue (-f) z = -ratValue f z := by
  have h := ratValue_mul (ratOrder_C_nonneg (-1) z) hf
  rw [ratValue_C] at h
  rw [show -f = RatFunc.C (-1) * f by simp, h]
  ring

theorem ratValue_sub {f g : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) (hg : 0 ≤ ratOrder g z) :
    ratValue (f - g) z = ratValue f z - ratValue g z := by
  rw [sub_eq_add_neg, ratValue_add hf (ratOrder_neg_nonneg hg), ratValue_neg hg, sub_eq_add_neg]

omit [CharZero K] in
/-- A regular function vanishes at a point exactly when its order there is positive. -/
theorem ratValue_eq_zero_iff {f : RatFunc K} {z : K} (hf0 : f ≠ 0) (hf : 0 ≤ ratOrder f z) :
    ratValue f z = 0 ↔ 0 < ratOrder f z := by
  have hden := denom_eval_ne_zero_of_regular hf
  rw [ratValue, div_eq_zero_iff, or_iff_left hden]
  constructor
  · intro hnum
    rcases lt_or_eq_of_le hf with h | h
    · exact h
    · exact absurd ((ratOrder_eq_zero_iff hf0 z).mp h.symm).1
        (by simpa [Polynomial.IsRoot] using hnum)
  · intro hpos
    by_contra hnum
    have := (ratOrder_eq_zero_iff hf0 z).mpr ⟨by simpa [Polynomial.IsRoot] using hnum,
      by simpa [Polynomial.IsRoot] using hden⟩
    omega

omit [CharZero K] in
/-- The value of the inverse of a unit. -/
theorem ratValue_inv {f : RatFunc K} {z : K} (hf0 : f ≠ 0) (hf : ratOrder f z = 0) :
    ratValue f⁻¹ z = (ratValue f z)⁻¹ := by
  have hinv : 0 ≤ ratOrder f⁻¹ z := by rw [ratOrder_inv hf0, hf]; rfl
  have h := ratValue_mul hf.symm.le hinv
  rw [mul_inv_cancel₀ hf0, ratValue_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit [CharZero K] in
theorem ratValue_ne_zero_of_unit {f : RatFunc K} {z : K} (hf0 : f ≠ 0) (hf : ratOrder f z = 0) :
    ratValue f z ≠ 0 := by
  intro h
  have := (ratValue_eq_zero_iff hf0 hf.symm.le).mp h
  omega

/-! ### Values under substitution -/

omit [CharZero K] in
theorem regular_aeval_and_value {P : RatFunc K} {z : K} (hP : 0 ≤ ratOrder P z) (N : K[X]) :
    0 ≤ ratOrder (Polynomial.aeval P N) z ∧
      ratValue (Polynomial.aeval P N) z = N.eval (ratValue P z) := by
  induction N using Polynomial.induction_on with
  | C a => rw [Polynomial.aeval_C, Polynomial.eval_C]; exact ⟨ratOrder_C_nonneg a z, ratValue_C a z⟩
  | add p q hp hq =>
      rw [map_add, Polynomial.eval_add]
      exact ⟨ratOrder_add_nonneg hp.1 hq.1, by rw [ratValue_add hp.1 hq.1, hp.2, hq.2]⟩
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul,
        Polynomial.eval_X]
      exact ⟨ratOrder_mul_nonneg ih.1 hP, by rw [ratValue_mul ih.1 hP, ih.2]⟩

omit [CharZero K] in
/-- **Value of a substitution.** -/
theorem ratValue_ratFuncSubstitution {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {f : RatFunc K} (hf : 0 ≤ ratOrder f (ratValue P z)) :
    0 ≤ ratOrder (ratFuncSubstitutionAlgHom P hPc f) z ∧
      ratValue (ratFuncSubstitutionAlgHom P hPc f) z = ratValue f (ratValue P z) := by
  set w := ratValue P z with hw
  have hdenw := denom_eval_ne_zero_of_regular hf
  have hQeq : f = algebraMap K[X] (RatFunc K) f.num
      * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := eq_num_div_denom f
  have hsub : ratFuncSubstitutionAlgHom P hPc f
      = Polynomial.aeval P f.num * (Polynomial.aeval P f.denom)⁻¹ := by
    conv_lhs => rw [hQeq]
    rw [map_mul, map_inv₀, ratFuncSubstitutionAlgHom_aeval, ratFuncSubstitutionAlgHom_aeval]
  obtain ⟨hn1, hn2⟩ := regular_aeval_and_value hP f.num
  obtain ⟨hd1, hd2⟩ := regular_aeval_and_value hP f.denom
  have hd0 : Polynomial.aeval P f.denom ≠ 0 := by
    intro h
    rw [h, ratValue_zero] at hd2
    exact hdenw hd2.symm
  have hdunit : ratOrder (Polynomial.aeval P f.denom) z = 0 := by
    rcases lt_or_eq_of_le hd1 with h | h
    · exfalso
      have := (ratValue_eq_zero_iff hd0 hd1).mpr h
      rw [hd2] at this
      exact hdenw this
    · exact h.symm
  have hinv : 0 ≤ ratOrder (Polynomial.aeval P f.denom)⁻¹ z := by
    rw [ratOrder_inv hd0, hdunit]; rfl
  rw [hsub]
  refine ⟨ratOrder_mul_nonneg hn1 hinv, ?_⟩
  rw [ratValue_mul hn1 hinv, ratValue_inv hd0 hdunit, hn2, hd2]
  show _ = f.num.eval w / f.denom.eval w
  rw [div_eq_mul_inv]

/-! ### Orders of sums with distinct orders -/

omit [CharZero K] in
theorem ratOrder_add_of_lt {f g : RatFunc K} {z : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : ratOrder f z < ratOrder g z) : ratOrder (f + g) z = ratOrder f z := by
  have hq : 0 < ratOrder (g / f) z := by
    rw [div_eq_mul_inv, ratOrder_mul hg (inv_ne_zero hf), ratOrder_inv hf]
    omega
  have h1 : 0 ≤ ratOrder (1 + g / f) z :=
    ratOrder_add_nonneg (by rw [ratOrder_one]) hq.le
  have hval : ratValue (1 + g / f) z = 1 := by
    rw [ratValue_add (by rw [ratOrder_one]) hq.le, ratValue_one,
      (ratValue_eq_zero_iff (div_ne_zero hg hf) hq.le).mpr hq, add_zero]
  have hne : 1 + g / f ≠ 0 := by
    intro h
    rw [h, ratValue_zero] at hval
    exact zero_ne_one hval
  have hunit : ratOrder (1 + g / f) z = 0 := by
    rcases lt_or_eq_of_le h1 with h | h
    · have := (ratValue_eq_zero_iff hne h1).mpr h
      rw [hval] at this
      exact absurd this one_ne_zero
    · exact h.symm
  have hsum : f + g = f * (1 + g / f) := by field_simp
  rw [hsum, ratOrder_mul hf hne, hunit, add_zero]

/-! ### Residues -/

/-- The linear factor `X − z`. -/
def ratLinFac (z : K) : RatFunc K := RatFunc.X - RatFunc.C z

omit [CharZero K] in
theorem ratLinFac_eq (z : K) :
    ratLinFac z = algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C z) := by
  simp [ratLinFac]

omit [CharZero K] in
theorem ratLinFac_ne_zero (z : K) : ratLinFac z ≠ 0 := by
  rw [ratLinFac_eq]
  exact algebraMap_ne_zero_of_ne_zero (Polynomial.X_sub_C_ne_zero z)

omit [CharZero K] in
theorem ratOrder_linFac_self (z : K) : ratOrder (ratLinFac z) z = 1 := by
  rw [ratLinFac_eq, ratOrder_algebraMap, Polynomial.rootMultiplicity_X_sub_C_self]
  rfl

omit [CharZero K] in
theorem ratOrder_linFac_nonneg (z w : K) : 0 ≤ ratOrder (ratLinFac z) w := by
  rw [ratLinFac_eq]
  exact ratOrder_algebraMap_nonneg _ _

omit [CharZero K] in
theorem ratValue_linFac (z w : K) : ratValue (ratLinFac z) w = w - z := by
  rw [ratLinFac_eq, ratValue_eq_eval, RatFunc.eval_algebraMap]
  simp

theorem ratFuncDeriv_linFac (z : K) : ratFuncDeriv (ratLinFac z) = 1 := by
  rw [ratLinFac, ← ratFuncDerivation_apply, map_sub, ratFuncDerivation_apply,
    ratFuncDerivation_apply,
    ratFuncDeriv_X, ratFuncDeriv_C, sub_zero]

/-- **The residue** of `f` at `z`: the value of `(X − z)·f`. -/
def ratResidue (f : RatFunc K) (z : K) : K := ratValue (ratLinFac z * f) z

omit [CharZero K] in
theorem ratOrder_linFac_mul_nonneg {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    0 ≤ ratOrder (ratLinFac z * f) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, ratOrder_zero]
  · rw [ratOrder_mul (ratLinFac_ne_zero z) hf0, ratOrder_linFac_self]
    omega

omit [CharZero K] in
theorem ratResidue_add {f g : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) (hg : -1 ≤ ratOrder g z) :
    ratResidue (f + g) z = ratResidue f z + ratResidue g z := by
  rw [ratResidue, mul_add,
    ratValue_add (ratOrder_linFac_mul_nonneg hf) (ratOrder_linFac_mul_nonneg hg)]
  rfl

omit [CharZero K] in
theorem ratResidue_eq_zero_of_regular {f : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) :
    ratResidue f z = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [ratResidue, mul_zero, ratValue_zero]
  · have hpos : 0 < ratOrder (ratLinFac z * f) z := by
      rw [ratOrder_mul (ratLinFac_ne_zero z) hf0, ratOrder_linFac_self]
      omega
    exact (ratValue_eq_zero_iff (mul_ne_zero (ratLinFac_ne_zero z) hf0) hpos.le).mpr hpos

omit [CharZero K] in
theorem ratResidue_mul_regular {h f : RatFunc K} {z : K} (hh : 0 ≤ ratOrder h z)
    (hf : -1 ≤ ratOrder f z) : ratResidue (h * f) z = ratValue h z * ratResidue f z := by
  rw [ratResidue, ratResidue, mul_left_comm, ratValue_mul hh (ratOrder_linFac_mul_nonneg hf)]

omit [CharZero K] in
theorem ratOrder_mul_ge {h f : RatFunc K} {z : K} (hh : 0 ≤ ratOrder h z)
    (hf : -1 ≤ ratOrder f z) : -1 ≤ ratOrder (h * f) z := by
  rcases eq_or_ne h 0 with rfl | hh0
  · rw [zero_mul, ratOrder_zero]; omega
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, ratOrder_zero]; omega
  rw [ratOrder_mul hh0 hf0]
  omega

omit [CharZero K] in
theorem ratResidue_inv_linFac (z : K) : ratResidue (ratLinFac z)⁻¹ z = 1 := by
  rw [ratResidue, mul_inv_cancel₀ (ratLinFac_ne_zero z), ratValue_one]

omit [CharZero K] in
theorem ratOrder_inv_linFac (z : K) : ratOrder (ratLinFac z)⁻¹ z = -1 := by
  rw [ratOrder_inv (ratLinFac_ne_zero z), ratOrder_linFac_self]

/-! ### Logarithmic derivatives -/

/-- The logarithmic derivative. -/
def logDerivRat (g : RatFunc K) : RatFunc K := ratFuncDeriv g / g

theorem logDerivRat_mul {a b : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0) :
    logDerivRat (a * b) = logDerivRat a + logDerivRat b := by
  rw [logDerivRat, logDerivRat, logDerivRat, ratFuncDeriv_mul]
  field_simp
  ring

theorem logDerivRat_inv {a : RatFunc K} (ha : a ≠ 0) :
    logDerivRat a⁻¹ = -logDerivRat a := by
  have h := logDerivRat_mul ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha] at h
  have h1 : logDerivRat (1 : RatFunc K) = 0 := by
    rw [logDerivRat, ← ratFuncDerivation_apply, Derivation.map_one_eq_zero, zero_div]
  rw [h1] at h
  linear_combination -h

theorem logDerivRat_zpow_linFac (z : K) (k : ℤ) :
    logDerivRat (ratLinFac z ^ k) = (k : RatFunc K) * (ratLinFac z)⁻¹ := by
  have hnat : ∀ m : ℕ, logDerivRat (ratLinFac z ^ m) = (m : RatFunc K) * (ratLinFac z)⁻¹ := by
    intro m
    induction m with
    | zero =>
        rw [pow_zero, logDerivRat, ← ratFuncDerivation_apply, Derivation.map_one_eq_zero]
        simp
    | succ m ih =>
        rw [pow_succ,
          logDerivRat_mul (pow_ne_zero _ (ratLinFac_ne_zero z)) (ratLinFac_ne_zero z), ih,
          logDerivRat, ratFuncDeriv_linFac]
        push_cast
        field_simp
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, hnat]
    push_cast
    rfl
  · rw [zpow_neg, zpow_natCast, logDerivRat_inv (pow_ne_zero _ (ratLinFac_ne_zero z)), hnat]
    push_cast
    ring

/-- **The residue of a logarithmic derivative is the order.** -/
theorem logDerivRat_residue {g : RatFunc K} (hg : g ≠ 0) (z : K) :
    -1 ≤ ratOrder (logDerivRat g) z ∧ ratResidue (logDerivRat g) z = ratOrder g z := by
  set k := ratOrder g z with hk
  set h := g * ratLinFac z ^ (-k) with hh
  have hlz : ratLinFac z ^ (-k) ≠ 0 := zpow_ne_zero _ (ratLinFac_ne_zero z)
  have hh0 : h ≠ 0 := mul_ne_zero hg hlz
  have hordh : ratOrder h z = 0 := by
    rw [hh, ratOrder_mul hg hlz, ratOrder_zpow (ratLinFac_ne_zero z), ratOrder_linFac_self]
    ring
  have hg_eq : g = ratLinFac z ^ k * h := by
    rw [hh, ← mul_assoc, mul_comm (ratLinFac z ^ k), mul_assoc, ← zpow_add₀ (ratLinFac_ne_zero z),
      add_neg_cancel, zpow_zero, mul_one]
  have hsplit : logDerivRat g = (k : RatFunc K) * (ratLinFac z)⁻¹ + logDerivRat h := by
    rw [hg_eq, logDerivRat_mul (zpow_ne_zero _ (ratLinFac_ne_zero z)) hh0,
      logDerivRat_zpow_linFac]
  have hreg : 0 ≤ ratOrder (logDerivRat h) z := by
    rw [logDerivRat]
    exact ratOrder_div_nonneg hh0 (ratOrder_deriv_nonneg hordh.symm.le) hordh
  have hkC : (k : RatFunc K) = RatFunc.C (k : K) := by simp
  have hfirst : -1 ≤ ratOrder ((k : RatFunc K) * (ratLinFac z)⁻¹) z := by
    rw [hkC]
    exact ratOrder_mul_ge (ratOrder_C_nonneg _ z) (by rw [ratOrder_inv_linFac])
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    rcases eq_or_ne ((k : RatFunc K) * (ratLinFac z)⁻¹) 0 with h0 | h0
    · rw [h0, zero_add]; omega
    rcases eq_or_ne (logDerivRat h) 0 with h1 | h1
    · rw [h1, add_zero]; exact hfirst
    rcases eq_or_ne ((k : RatFunc K) * (ratLinFac z)⁻¹ + logDerivRat h) 0 with h2 | h2
    · rw [h2, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h1 h2 z
    omega
  · rw [hsplit, ratResidue_add hfirst (by omega), ratResidue_eq_zero_of_regular hreg, add_zero, hkC,
      ratResidue_mul_regular (ratOrder_C_nonneg _ z) (by rw [ratOrder_inv_linFac]), ratValue_C,
      ratResidue_inv_linFac, mul_one]

/-- **The order of a derivative.**  At a point of nonzero order `k`, the derivative has order
`k − 1`. -/
theorem ratOrder_ratFuncDeriv_of_ne_zero {g : RatFunc K} (hg : g ≠ 0) {z : K}
    (hk : ratOrder g z ≠ 0) : ratOrder (ratFuncDeriv g) z = ratOrder g z - 1 := by
  obtain ⟨hge, hres⟩ := logDerivRat_residue hg z
  have hL0 : logDerivRat g ≠ 0 := by
    intro h0
    rw [h0, ratResidue, mul_zero, ratValue_zero] at hres
    exact hk (by exact_mod_cast hres.symm)
  have hLord : ratOrder (logDerivRat g) z = -1 := by
    rcases lt_or_eq_of_le hge with h | h
    · exfalso
      have := ratResidue_eq_zero_of_regular (f := logDerivRat g) (z := z) (by omega)
      rw [hres] at this
      exact hk (by exact_mod_cast this)
    · exact h.symm
  have hd : ratFuncDeriv g = g * logDerivRat g := by
    rw [logDerivRat]; field_simp
  rw [hd, ratOrder_mul hg hL0, hLord]
  ring

/-! ### Pullback of residues -/

omit [CharZero K] in
theorem ratFuncSubstitution_linFac {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) (w : K) :
    ratFuncSubstitutionAlgHom P hPc (ratLinFac w) = P - RatFunc.C w := by
  rw [ratLinFac, map_sub, ratFuncSubstitutionAlgHom_X, ratFuncSubstitutionAlgHom_C]

theorem ratFuncDeriv_sub_C (P : RatFunc K) (w : K) :
    ratFuncDeriv (P - RatFunc.C w) = ratFuncDeriv P := by
  rw [← ratFuncDerivation_apply, map_sub, ratFuncDerivation_apply, ratFuncDerivation_apply,
    ratFuncDeriv_C, sub_zero]

omit [CharZero K] in
theorem sub_C_ne_zero_of_nonconst {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) (w : K) :
    P - RatFunc.C w ≠ 0 := fun h => hPc ⟨w, sub_eq_zero.mp h⟩

/-- A function with at most a simple pole, minus its polar part, is regular. -/
theorem regular_sub_polar {f : RatFunc K} {w : K} (hf : -1 ≤ ratOrder f w) :
    0 ≤ ratOrder (f - RatFunc.C (ratResidue f w) * (ratLinFac w)⁻¹) w := by
  set g := f - RatFunc.C (ratResidue f w) * (ratLinFac w)⁻¹ with hg
  have hlg : ratLinFac w * g = ratLinFac w * f - RatFunc.C (ratResidue f w) := by
    rw [hg, mul_sub, mul_left_comm, mul_inv_cancel₀ (ratLinFac_ne_zero w), mul_one]
  have hreg : 0 ≤ ratOrder (ratLinFac w * g) w := by
    rw [hlg]
    exact ratOrder_sub_nonneg (ratOrder_linFac_mul_nonneg hf) (ratOrder_C_nonneg _ w)
  have hval : ratValue (ratLinFac w * g) w = 0 := by
    rw [hlg, ratValue_sub (ratOrder_linFac_mul_nonneg hf) (ratOrder_C_nonneg _ w), ratValue_C]
    rw [ratResidue, sub_self]
  rcases eq_or_ne g 0 with h0 | h0
  · rw [h0, ratOrder_zero]
  · have hpos := (ratValue_eq_zero_iff (mul_ne_zero (ratLinFac_ne_zero w) h0) hreg).mp hval
    rw [ratOrder_mul (ratLinFac_ne_zero w) h0, ratOrder_linFac_self] at hpos
    omega

/-- **Residues pull back with the local degree.** -/
theorem ratResidue_subst_mul_deriv {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {f : RatFunc K} (hf : -1 ≤ ratOrder f (ratValue P z)) :
    -1 ≤ ratOrder (ratFuncSubstitutionAlgHom P hPc f * ratFuncDeriv P) z ∧
      ratResidue (ratFuncSubstitutionAlgHom P hPc f * ratFuncDeriv P) z
        = (ratOrder (P - RatFunc.C (ratValue P z)) z : K) * ratResidue f (ratValue P z) := by
  set w := ratValue P z with hw
  set r := ratResidue f w with hr
  set g := f - RatFunc.C r * (ratLinFac w)⁻¹ with hg
  have hgreg : 0 ≤ ratOrder g w := regular_sub_polar hf
  have hfeq : f = RatFunc.C r * (ratLinFac w)⁻¹ + g := by rw [hg]; ring
  have hPw := sub_C_ne_zero_of_nonconst hPc w
  have hsubst : ratFuncSubstitutionAlgHom P hPc f * ratFuncDeriv P
      = RatFunc.C r * logDerivRat (P - RatFunc.C w)
        + ratFuncSubstitutionAlgHom P hPc g * ratFuncDeriv P := by
    conv_lhs => rw [hfeq]
    rw [map_add, map_mul, map_inv₀, ratFuncSubstitution_linFac,
      ratFuncSubstitutionAlgHom_C,
      logDerivRat, ratFuncDeriv_sub_C]
    field_simp
  obtain ⟨hL, hLres⟩ := logDerivRat_residue hPw z
  have hsg : 0 ≤ ratOrder (ratFuncSubstitutionAlgHom P hPc g * ratFuncDeriv P) z :=
    ratOrder_mul_nonneg (ratValue_ratFuncSubstitution hPc hP hgreg).1 (ratOrder_deriv_nonneg hP)
  have h1 : -1 ≤ ratOrder (RatFunc.C r * logDerivRat (P - RatFunc.C w)) z :=
    ratOrder_mul_ge (ratOrder_C_nonneg r z) hL
  rw [hsubst]
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne (RatFunc.C r * logDerivRat (P - RatFunc.C w)) 0 with h0 | h0
    · rw [h0, zero_add]; omega
    rcases eq_or_ne (ratFuncSubstitutionAlgHom P hPc g * ratFuncDeriv P) 0 with h2 | h2
    · rw [h2, add_zero]; exact h1
    rcases eq_or_ne (RatFunc.C r * logDerivRat (P - RatFunc.C w)
      + ratFuncSubstitutionAlgHom P hPc g * ratFuncDeriv P) 0 with h3 | h3
    · rw [h3, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h2 h3 z
    omega
  · rw [ratResidue_add h1 (by omega), ratResidue_eq_zero_of_regular hsg, add_zero,
      ratResidue_mul_regular (ratOrder_C_nonneg r z) hL, ratValue_C, hLres]
    ring

theorem ratFuncDeriv_ne_zero_of_nonconst {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c)
    {z : K} (hP : 0 ≤ ratOrder P z) : ratFuncDeriv P ≠ 0 := by
  have hPw := sub_C_ne_zero_of_nonconst hPc (ratValue P z)
  obtain ⟨-, hres⟩ := logDerivRat_residue hPw z
  have hpos := ratOrder_sub_ratValue_pos hPc (denom_eval_ne_zero_of_regular hP)
  intro h0
  rw [logDerivRat, ratFuncDeriv_sub_C, h0, zero_div, ratResidue, mul_zero, ratValue_zero] at hres
  have : (ratOrder (P - RatFunc.C (ratValue P z)) z : K) = 0 := hres.symm
  exact (show ratOrder (P - RatFunc.C (ratValue P z)) z ≠ 0 by omega) (by exact_mod_cast this)

/-- The order of the derivative of a map at a point of local degree `e` is `e − 1`. -/
theorem ratOrder_ratFuncDeriv_map {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) :
    ratOrder (ratFuncDeriv P) z = ratOrder (P - RatFunc.C (ratValue P z)) z - 1 := by
  have hpos := ratOrder_sub_ratValue_pos hPc (denom_eval_ne_zero_of_regular hP)
  rw [← ratFuncDeriv_sub_C P (ratValue P z)]
  exact ratOrder_ratFuncDeriv_of_ne_zero (sub_C_ne_zero_of_nonconst hPc _) (by omega)

/-- **The affine-connection pullback** `P^*a = a(P)·P' + P''/P'`. -/
def connPull (P : RatFunc K) (hPc : ¬ ∃ c : K, P = RatFunc.C c) (a : RatFunc K) : RatFunc K :=
  ratFuncSubstitutionAlgHom P hPc a * ratFuncDeriv P + logDerivRat (ratFuncDeriv P)

/-- **Residues of an affine connection pull back as `s ↦ e·s`** for `s = 1 + residue`. -/
theorem ratResidue_connPull {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {a : RatFunc K} (ha : -1 ≤ ratOrder a (ratValue P z)) :
    -1 ≤ ratOrder (connPull P hPc a) z ∧
      ratResidue (connPull P hPc a) z + 1
        = (ratOrder (P - RatFunc.C (ratValue P z)) z : K) * (ratResidue a (ratValue P z) + 1) := by
  obtain ⟨h1, hres1⟩ := ratResidue_subst_mul_deriv hPc hP ha
  have hP' := ratFuncDeriv_ne_zero_of_nonconst hPc hP
  obtain ⟨h2, hres2⟩ := logDerivRat_residue hP' z
  rw [ratOrder_ratFuncDeriv_map hPc hP] at hres2
  refine ⟨?_, ?_⟩
  · rw [connPull]
    rcases eq_or_ne (ratFuncSubstitutionAlgHom P hPc a * ratFuncDeriv P) 0 with h0 | h0
    · rw [h0, zero_add]; exact h2
    rcases eq_or_ne (logDerivRat (ratFuncDeriv P)) 0 with h3 | h3
    · rw [h3, add_zero]; exact h1
    rcases eq_or_ne (ratFuncSubstitutionAlgHom P hPc a * ratFuncDeriv P
      + logDerivRat (ratFuncDeriv P)) 0 with h4 | h4
    · rw [h4, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h3 h4 z
    omega
  · rw [connPull, ratResidue_add h1 h2, hres1, hres2]
    push_cast
    ring

/-- **Higher-order poles of a connection propagate.** -/
theorem ratOrder_connPull_of_le {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {a : RatFunc K} (ha0 : a ≠ 0)
    (ha : ratOrder a (ratValue P z) ≤ -2) :
    ratOrder (connPull P hPc a) z
      = ratOrder a (ratValue P z) * ratOrder (P - RatFunc.C (ratValue P z)) z
        + (ratOrder (P - RatFunc.C (ratValue P z)) z - 1) := by
  have hP' := ratFuncDeriv_ne_zero_of_nonconst hPc hP
  have hpos := ratOrder_sub_ratValue_pos hPc (denom_eval_ne_zero_of_regular hP)
  have hsa : ratFuncSubstitutionAlgHom P hPc a ≠ 0 := by
    intro h
    exact ha0 ((ratFuncSubstitutionAlgHom P hPc).toRingHom.injective (by simpa using h))
  have hord1 : ratOrder (ratFuncSubstitutionAlgHom P hPc a * ratFuncDeriv P) z
      = ratOrder a (ratValue P z) * ratOrder (P - RatFunc.C (ratValue P z)) z
        + (ratOrder (P - RatFunc.C (ratValue P z)) z - 1) := by
    rw [ratOrder_mul hsa hP', ratOrder_ratFuncSubstitution_ratFunc hPc
      (denom_eval_ne_zero_of_regular hP) ha0, ratOrder_ratFuncDeriv_map hPc hP]
  obtain ⟨h2, -⟩ := logDerivRat_residue hP' z
  have hlt : ratOrder (ratFuncSubstitutionAlgHom P hPc a * ratFuncDeriv P) z
      < ratOrder (logDerivRat (ratFuncDeriv P)) z := by
    rw [hord1]
    nlinarith
  rw [connPull]
  rcases eq_or_ne (logDerivRat (ratFuncDeriv P)) 0 with h3 | h3
  · rw [h3, add_zero, hord1]
  · rw [ratOrder_add_of_lt (mul_ne_zero hsa hP') h3 hlt, hord1]

/-! ### Double-pole coefficients and projective connections -/

/-- The coefficient of `(X − z)⁻²`: the value of `(X − z)²·f`. -/
def ratDpc (f : RatFunc K) (z : K) : K := ratValue (ratLinFac z ^ 2 * f) z

omit [CharZero K] in
theorem ratOrder_linFac_sq_mul_nonneg {f : RatFunc K} {z : K} (hf : -2 ≤ ratOrder f z) :
    0 ≤ ratOrder (ratLinFac z ^ 2 * f) z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, ratOrder_zero]
  · rw [ratOrder_mul (pow_ne_zero _ (ratLinFac_ne_zero z)) hf0, ratOrder_pow (ratLinFac_ne_zero z),
      ratOrder_linFac_self]
    omega

omit [CharZero K] in
theorem ratDpc_add {f g : RatFunc K} {z : K} (hf : -2 ≤ ratOrder f z) (hg : -2 ≤ ratOrder g z) :
    ratDpc (f + g) z = ratDpc f z + ratDpc g z := by
  rw [ratDpc, mul_add, ratValue_add (ratOrder_linFac_sq_mul_nonneg hf)
    (ratOrder_linFac_sq_mul_nonneg hg)]
  rfl

omit [CharZero K] in
theorem ratDpc_eq_zero_of_simple {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    ratDpc f z = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [ratDpc, mul_zero, ratValue_zero]
  · have hne : ratLinFac z ^ 2 * f ≠ 0 := mul_ne_zero (pow_ne_zero _ (ratLinFac_ne_zero z)) hf0
    have hpos : 0 < ratOrder (ratLinFac z ^ 2 * f) z := by
      rw [ratOrder_mul (pow_ne_zero _ (ratLinFac_ne_zero z)) hf0,
        ratOrder_pow (ratLinFac_ne_zero z),
        ratOrder_linFac_self]
      omega
    exact (ratValue_eq_zero_iff hne hpos.le).mpr hpos

omit [CharZero K] in
theorem ratDpc_mul_regular {h f : RatFunc K} {z : K} (hh : 0 ≤ ratOrder h z)
    (hf : -2 ≤ ratOrder f z) : ratDpc (h * f) z = ratValue h z * ratDpc f z := by
  rw [ratDpc, ratDpc, mul_left_comm, ratValue_mul hh (ratOrder_linFac_sq_mul_nonneg hf)]

omit [CharZero K] in
theorem ratOrder_mul_ge_two {h f : RatFunc K} {z : K} (hh : 0 ≤ ratOrder h z)
    (hf : -2 ≤ ratOrder f z) : -2 ≤ ratOrder (h * f) z := by
  rcases eq_or_ne h 0 with rfl | hh0
  · rw [zero_mul, ratOrder_zero]; omega
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, ratOrder_zero]; omega
  rw [ratOrder_mul hh0 hf0]
  omega

omit [CharZero K] in
/-- The square of a function with a simple pole has double-pole coefficient the squared residue. -/
theorem ratDpc_sq {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    -2 ≤ ratOrder (f ^ 2) z ∧ ratDpc (f ^ 2) z = ratResidue f z ^ 2 := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne f 0 with rfl | hf0
    · simp [ratOrder_zero]
    · rw [ratOrder_pow hf0]; omega
  · rw [ratDpc, show ratLinFac z ^ 2 * f ^ 2 = (ratLinFac z * f) ^ 2 by ring, pow_two, pow_two,
      ratValue_mul (ratOrder_linFac_mul_nonneg hf) (ratOrder_linFac_mul_nonneg hf)]
    rfl

theorem ratFuncDeriv_inv_linFac (z : K) :
    ratFuncDeriv (ratLinFac z)⁻¹ = -(ratLinFac z ^ 2)⁻¹ := by
  rw [inv_eq_one_div, ratFuncDeriv_div_general (ratLinFac_ne_zero z), ratFuncDeriv_linFac,
    ← ratFuncDerivation_apply, Derivation.map_one_eq_zero]
  field_simp
  ring

/-- The derivative of a function with a simple pole has double-pole coefficient minus the
residue. -/
theorem ratDpc_deriv {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    -2 ≤ ratOrder (ratFuncDeriv f) z ∧ ratDpc (ratFuncDeriv f) z = -ratResidue f z := by
  set r := ratResidue f z with hr
  set g := f - RatFunc.C r * (ratLinFac z)⁻¹ with hg
  have hgreg : 0 ≤ ratOrder g z := regular_sub_polar hf
  have hfeq : ratFuncDeriv f = -(RatFunc.C r * (ratLinFac z ^ 2)⁻¹) + ratFuncDeriv g := by
    have : f = RatFunc.C r * (ratLinFac z)⁻¹ + g := by rw [hg]; ring
    rw [this, ratFuncDeriv_add, ratFuncDeriv_mul, ratFuncDeriv_C, ratFuncDeriv_inv_linFac]
    ring
  have hg' : 0 ≤ ratOrder (ratFuncDeriv g) z := ratOrder_deriv_nonneg hgreg
  have hpolar : -2 ≤ ratOrder (-(RatFunc.C r * (ratLinFac z ^ 2)⁻¹)) z := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, map_zero, zero_mul, neg_zero, ratOrder_zero]; omega
    · rw [ratOrder_neg (mul_ne_zero ((_root_.map_ne_zero _).mpr h0)
        (inv_ne_zero (pow_ne_zero _ (ratLinFac_ne_zero z)))),
        ratOrder_mul ((_root_.map_ne_zero _).mpr h0)
        (inv_ne_zero (pow_ne_zero _ (ratLinFac_ne_zero z))), ratOrder_C, ratOrder_inv
        (pow_ne_zero _ (ratLinFac_ne_zero z)), ratOrder_pow (ratLinFac_ne_zero z),
        ratOrder_linFac_self]
      omega
  refine ⟨?_, ?_⟩
  · rw [hfeq]
    rcases eq_or_ne (-(RatFunc.C r * (ratLinFac z ^ 2)⁻¹)) 0 with h0 | h0
    · rw [h0, zero_add]; omega
    rcases eq_or_ne (ratFuncDeriv g) 0 with h1 | h1
    · rw [h1, add_zero]; exact hpolar
    rcases eq_or_ne (-(RatFunc.C r * (ratLinFac z ^ 2)⁻¹) + ratFuncDeriv g) 0 with h2 | h2
    · rw [h2, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h1 h2 z
    omega
  · rw [hfeq, ratDpc_add hpolar (by omega),
      ratDpc_eq_zero_of_simple (f := ratFuncDeriv g) (by omega), add_zero]
    have hval : ratLinFac z ^ 2 * -(RatFunc.C r * (ratLinFac z ^ 2)⁻¹) = RatFunc.C (-r) := by
      rw [map_neg, mul_neg, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ (ratLinFac_ne_zero z)),
        mul_one]
    rw [ratDpc, hval, ratValue_C]

/-- The Schwarzian derivative of a rational map. -/
def schwarzRat (P : RatFunc K) : RatFunc K :=
  ratFuncDeriv (logDerivRat (ratFuncDeriv P)) - logDerivRat (ratFuncDeriv P) ^ 2 / 2

/-- **The projective-connection pullback** `P^*γ = γ(P)·P'² + S(P)`. -/
def projPull (P : RatFunc K) (hPc : ¬ ∃ c : K, P = RatFunc.C c) (γ : RatFunc K) : RatFunc K :=
  ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2 + schwarzRat P

/-- **The Schwarzian of a map of local degree `e` has double-pole coefficient `(1 − e²)/2`.** -/
theorem ratDpc_schwarzRat {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) :
    -2 ≤ ratOrder (schwarzRat P) z ∧
      ratDpc (schwarzRat P) z
        = (1 - (ratOrder (P - RatFunc.C (ratValue P z)) z : K) ^ 2) / 2 := by
  have hP' := ratFuncDeriv_ne_zero_of_nonconst hPc hP
  obtain ⟨hL, hLres⟩ := logDerivRat_residue hP' z
  rw [ratOrder_ratFuncDeriv_map hPc hP] at hLres
  obtain ⟨hD, hDdpc⟩ := ratDpc_deriv hL
  obtain ⟨hS, hSdpc⟩ := ratDpc_sq hL
  have hS2 : -2 ≤ ratOrder (logDerivRat (ratFuncDeriv P) ^ 2 / 2) z := by
    rw [div_eq_mul_inv, mul_comm]
    have h2 : (2 : RatFunc K)⁻¹ = RatFunc.C (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat, one_div]
    rw [h2]
    exact ratOrder_mul_ge_two (ratOrder_C_nonneg _ z) hS
  have hneg : -2 ≤ ratOrder (-(logDerivRat (ratFuncDeriv P) ^ 2 / 2)) z := by
    rcases eq_or_ne (logDerivRat (ratFuncDeriv P) ^ 2 / 2) 0 with h0 | h0
    · rw [h0, neg_zero, ratOrder_zero]; omega
    · rw [ratOrder_neg h0]; exact hS2
  have hsplit : schwarzRat P
      = ratFuncDeriv (logDerivRat (ratFuncDeriv P))
        + -(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2) := by
    rw [schwarzRat]
    have h2 : RatFunc.C (1 / 2 : K) = (2 : RatFunc K)⁻¹ := by
      rw [map_div₀, map_one, map_ofNat, one_div]
    rw [h2]
    ring
  have hneg' : -2 ≤ ratOrder (-(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2)) z := by
    have hC : -2 ≤ ratOrder (RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2) z :=
      ratOrder_mul_ge_two (ratOrder_C_nonneg _ z) hS
    rcases eq_or_ne (RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2) 0 with h0 | h0
    · rw [h0, neg_zero, ratOrder_zero]; omega
    · rw [ratOrder_neg h0]; exact hC
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    rcases eq_or_ne (ratFuncDeriv (logDerivRat (ratFuncDeriv P))) 0 with h0 | h0
    · rw [h0, zero_add]; exact hneg'
    rcases eq_or_ne (-(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2)) 0 with h1 | h1
    · rw [h1, add_zero]; exact hD
    rcases eq_or_ne (ratFuncDeriv (logDerivRat (ratFuncDeriv P))
      + -(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2)) 0 with h2 | h2
    · rw [h2, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h1 h2 z
    omega
  · rw [hsplit, ratDpc_add hD hneg']
    have hnegdpc : ratDpc (-(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2)) z
        = -(1 / 2 * ratResidue (logDerivRat (ratFuncDeriv P)) z ^ 2) := by
      rw [show -(RatFunc.C (1 / 2) * logDerivRat (ratFuncDeriv P) ^ 2)
          = RatFunc.C (-(1 / 2)) * logDerivRat (ratFuncDeriv P) ^ 2 by simp,
        ratDpc_mul_regular (ratOrder_C_nonneg _ z) hS, ratValue_C, hSdpc]
      ring
    rw [hDdpc, hnegdpc, hLres]
    push_cast
    ring

/-- **Double-pole coefficients pull back with the square of the local degree.** -/
theorem ratDpc_projPull {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {γ : RatFunc K} (hγ : -2 ≤ ratOrder γ (ratValue P z)) :
    -2 ≤ ratOrder (projPull P hPc γ) z ∧
      ratDpc (projPull P hPc γ) z
        = (ratOrder (P - RatFunc.C (ratValue P z)) z : K) ^ 2 * ratDpc γ (ratValue P z)
          + (1 - (ratOrder (P - RatFunc.C (ratValue P z)) z : K) ^ 2) / 2 := by
  set w := ratValue P z with hw
  set c := ratDpc γ w with hc
  set f₁ := γ - RatFunc.C c * (ratLinFac w ^ 2)⁻¹ with hf₁
  have hf₁ord : -1 ≤ ratOrder f₁ w := by
    have hlf : ratLinFac w ^ 2 * f₁ = ratLinFac w ^ 2 * γ - RatFunc.C c := by
      rw [hf₁, mul_sub, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ (ratLinFac_ne_zero w)),
        mul_one]
    have hreg : 0 ≤ ratOrder (ratLinFac w ^ 2 * f₁) w := by
      rw [hlf]
      exact ratOrder_sub_nonneg (ratOrder_linFac_sq_mul_nonneg hγ) (ratOrder_C_nonneg _ w)
    have hval : ratValue (ratLinFac w ^ 2 * f₁) w = 0 := by
      rw [hlf, ratValue_sub (ratOrder_linFac_sq_mul_nonneg hγ) (ratOrder_C_nonneg _ w),
        ratValue_C, hc, ratDpc, sub_self]
    rcases eq_or_ne f₁ 0 with h0 | h0
    · rw [h0, ratOrder_zero]; omega
    · have hne := mul_ne_zero (pow_ne_zero 2 (ratLinFac_ne_zero w)) h0
      have hpos := (ratValue_eq_zero_iff hne hreg).mp hval
      rw [ratOrder_mul (pow_ne_zero _ (ratLinFac_ne_zero w)) h0, ratOrder_pow (ratLinFac_ne_zero w),
        ratOrder_linFac_self] at hpos
      omega
  have hPw := sub_C_ne_zero_of_nonconst hPc w
  have hP' := ratFuncDeriv_ne_zero_of_nonconst hPc hP
  obtain ⟨hL0, hL0res⟩ := logDerivRat_residue hPw z
  obtain ⟨hsq, hsqdpc⟩ := ratDpc_sq hL0
  obtain ⟨h1, -⟩ := ratResidue_subst_mul_deriv hPc hP hf₁ord
  have hP'reg : 0 ≤ ratOrder (ratFuncDeriv P) z := ratOrder_deriv_nonneg hP
  have hsplit : ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2
      = RatFunc.C c * logDerivRat (P - RatFunc.C w) ^ 2
        + ratFuncDeriv P * (ratFuncSubstitutionAlgHom P hPc f₁ * ratFuncDeriv P) := by
    have hγeq : γ = RatFunc.C c * (ratLinFac w ^ 2)⁻¹ + f₁ := by rw [hf₁]; ring
    conv_lhs => rw [hγeq]
    rw [map_add, map_mul, map_inv₀, map_pow, ratFuncSubstitution_linFac,
      ratFuncSubstitutionAlgHom_C, logDerivRat, ratFuncDeriv_sub_C]
    field_simp
  have hA : -2 ≤ ratOrder (RatFunc.C c * logDerivRat (P - RatFunc.C w) ^ 2) z :=
    ratOrder_mul_ge_two (ratOrder_C_nonneg _ z) hsq
  have hB :
      -1 ≤ ratOrder (ratFuncDeriv P * (ratFuncSubstitutionAlgHom P hPc f₁ * ratFuncDeriv P)) z :=
    ratOrder_mul_ge hP'reg h1
  obtain ⟨hS, hSdpc⟩ := ratDpc_schwarzRat hPc hP
  have hfirst : -2 ≤ ratOrder (ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2) z := by
    rw [hsplit]
    rcases eq_or_ne (RatFunc.C c * logDerivRat (P - RatFunc.C w) ^ 2) 0 with h0 | h0
    · rw [h0, zero_add]; omega
    rcases eq_or_ne (ratFuncDeriv P * (ratFuncSubstitutionAlgHom P hPc f₁ * ratFuncDeriv P)) 0
      with h2 | h2
    · rw [h2, add_zero]; exact hA
    rcases eq_or_ne (RatFunc.C c * logDerivRat (P - RatFunc.C w) ^ 2
      + ratFuncDeriv P * (ratFuncSubstitutionAlgHom P hPc f₁ * ratFuncDeriv P)) 0 with h3 | h3
    · rw [h3, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h2 h3 z
    omega
  refine ⟨?_, ?_⟩
  · rw [projPull]
    rcases eq_or_ne (ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2) 0 with h0 | h0
    · rw [h0, zero_add]; exact hS
    rcases eq_or_ne (schwarzRat P) 0 with h2 | h2
    · rw [h2, add_zero]; exact hfirst
    rcases eq_or_ne (ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2 + schwarzRat P) 0
      with h3 | h3
    · rw [h3, ratOrder_zero]; omega
    have := min_le_ratOrder_add h0 h2 h3 z
    omega
  · rw [projPull, ratDpc_add hfirst hS, hSdpc, hsplit, ratDpc_add hA (by omega),
      ratDpc_eq_zero_of_simple hB, add_zero, ratDpc_mul_regular (ratOrder_C_nonneg _ z) hsq,
      ratValue_C, hsqdpc, hL0res]
    ring

/-- **Poles of order at least three of a projective connection propagate.** -/
theorem ratOrder_projPull_of_le {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) {z : K}
    (hP : 0 ≤ ratOrder P z) {γ : RatFunc K} (hγ0 : γ ≠ 0)
    (hγ : ratOrder γ (ratValue P z) ≤ -3) :
    ratOrder (projPull P hPc γ) z
      = ratOrder γ (ratValue P z) * ratOrder (P - RatFunc.C (ratValue P z)) z
        + 2 * (ratOrder (P - RatFunc.C (ratValue P z)) z - 1) := by
  have hP' := ratFuncDeriv_ne_zero_of_nonconst hPc hP
  have hpos := ratOrder_sub_ratValue_pos hPc (denom_eval_ne_zero_of_regular hP)
  have hsa : ratFuncSubstitutionAlgHom P hPc γ ≠ 0 := by
    intro h
    exact hγ0 ((ratFuncSubstitutionAlgHom P hPc).toRingHom.injective (by simpa using h))
  have hord1 : ratOrder (ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2) z
      = ratOrder γ (ratValue P z) * ratOrder (P - RatFunc.C (ratValue P z)) z
        + 2 * (ratOrder (P - RatFunc.C (ratValue P z)) z - 1) := by
    rw [ratOrder_mul hsa (pow_ne_zero _ hP'), ratOrder_pow hP',
      ratOrder_ratFuncSubstitution_ratFunc hPc (denom_eval_ne_zero_of_regular hP) hγ0,
      ratOrder_ratFuncDeriv_map hPc hP]
    push_cast
    ring
  obtain ⟨hS, -⟩ := ratDpc_schwarzRat hPc hP
  have hlt : ratOrder (ratFuncSubstitutionAlgHom P hPc γ * ratFuncDeriv P ^ 2) z
      < ratOrder (schwarzRat P) z := by
    rw [hord1]
    nlinarith
  rw [projPull]
  rcases eq_or_ne (schwarzRat P) 0 with h3 | h3
  · rw [h3, add_zero, hord1]
  · rw [ratOrder_add_of_lt (mul_ne_zero hsa (pow_ne_zero _ hP')) h3 hlt, hord1]

end

end GaloisForLFunctions.HTGeometry
