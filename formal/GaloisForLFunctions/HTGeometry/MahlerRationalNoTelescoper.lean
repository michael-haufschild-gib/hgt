import GaloisForLFunctions.HTGeometry.RamifiedLaurentTransfer

/-!
# Inhomogeneous Mahler equations have no rational solutions

For `λ ≠ 0` the equation `λ·z(w^p) − z(w) = ρ(w)` with polynomial right side forces `z` to be a
polynomial: the reduced denominator would have to divide its own `p`-fold expansion, which is
impossible by degree.  For the two-term right side `a·w^N + b·w^(pN)` supported on the powers of
`p`, the coefficients of the polynomial solution are then forced to be `λ^i·(λa+b)` along the
lacunary set, so a solution exists only when `λa + b = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem polyPow_eq_expand (q : ℕ) (P : Polynomial k) :
    polyPow q P = Polynomial.expand k q P := rfl

theorem coeff_polyPow (q : ℕ) (hq : 0 < q) (P : Polynomial k) (d : ℕ) :
    (polyPow q P).coeff d = if q ∣ d then P.coeff (d / q) else 0 := by
  rw [polyPow_eq_expand]
  exact Polynomial.coeff_expand hq P d

theorem natDegree_polyPow (q : ℕ) (P : Polynomial k) :
    (polyPow q P).natDegree = P.natDegree * q := by
  rw [polyPow_eq_expand]
  exact Polynomial.natDegree_expand q P

theorem polyPow_ne_zero {q : ℕ} (hq : 0 < q) {P : Polynomial k} (hP : P ≠ 0) :
    polyPow q P ≠ 0 := by
  intro h
  exact hP (polyPow_injective hq (by rw [h, map_zero]))

/-- **A rational solution of an inhomogeneous Mahler equation is a polynomial.** -/
theorem exists_poly_of_ratFunc_mahler_eq (p : ℕ) (hp : 1 < p) (lam : k) (hlam : lam ≠ 0)
    (z : RatFunc k) (ρ : Polynomial k)
    (heq : algebraMap (Polynomial k) (RatFunc k) (Polynomial.C lam)
        * ratFuncPow p (by omega) z - z = algebraMap (Polynomial k) (RatFunc k) ρ) :
    ∃ P : Polynomial k, z = algebraMap (Polynomial k) (RatFunc k) P := by
  classical
  set N : Polynomial k := z.num with hNdef
  set Q : Polynomial k := z.denom with hQdef
  set Np : Polynomial k := polyPow p N with hNpdef
  set Qp : Polynomial k := polyPow p Q with hQpdef
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero z
  have hQp0 : Qp ≠ 0 := polyPow_ne_zero (by omega) hQ0
  have hQrf : algebraMap (Polynomial k) (RatFunc k) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ0
  have hQprf : algebraMap (Polynomial k) (RatFunc k) Qp ≠ 0 := RatFunc.algebraMap_ne_zero hQp0
  have hz : z = algebraMap (Polynomial k) (RatFunc k) N
      / algebraMap (Polynomial k) (RatFunc k) Q := (RatFunc.num_div_denom z).symm
  have hpow : ratFuncPow p (by omega) z = algebraMap (Polynomial k) (RatFunc k) Np
      / algebraMap (Polynomial k) (RatFunc k) Qp := by
    conv_lhs => rw [hz]
    rw [ratFuncPow_div]
  have hNQ : algebraMap (Polynomial k) (RatFunc k) N
      = z * algebraMap (Polynomial k) (RatFunc k) Q := by
    rw [hz, div_mul_cancel₀ _ hQrf]
  have hNQp : algebraMap (Polynomial k) (RatFunc k) Np
      = ratFuncPow p (by omega) z * algebraMap (Polynomial k) (RatFunc k) Qp := by
    rw [hpow, div_mul_cancel₀ _ hQprf]
  have hlin : algebraMap (Polynomial k) (RatFunc k) (Polynomial.C lam)
      * ratFuncPow p (by omega) z = z + algebraMap (Polynomial k) (RatFunc k) ρ := by
    rw [← heq]; ring
  have key : Polynomial.C lam * Np * Q = (N + ρ * Q) * Qp := by
    refine IsFractionRing.injective (Polynomial k) (RatFunc k) ?_
    rw [map_mul, map_mul, map_mul, map_add, map_mul, hNQ, hNQp]
    linear_combination (algebraMap (Polynomial k) (RatFunc k) Qp
      * algebraMap (Polynomial k) (RatFunc k) Q) * hlin
  have hdvd : Qp ∣ Np * Q := by
    have h1 : Qp ∣ Polynomial.C lam * Np * Q := ⟨N + ρ * Q, by rw [key]; ring⟩
    have h2 : Np * Q = Polynomial.C lam⁻¹ * (Polynomial.C lam * Np * Q) := by
      rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlam, Polynomial.C_1,
        one_mul]
    rw [h2]
    exact Dvd.dvd.mul_left h1 _
  have hcop : IsCoprime Qp Np :=
    ((RatFunc.isCoprime_num_denom z).symm.map (polyPow p))
  have hdvdQ : Qp ∣ Q := hcop.dvd_of_dvd_mul_left hdvd
  have hdeg : Qp.natDegree ≤ Q.natDegree := Polynomial.natDegree_le_of_dvd hdvdQ hQ0
  rw [hQpdef, natDegree_polyPow] at hdeg
  have hQdeg : Q.natDegree = 0 := by nlinarith [Nat.zero_le Q.natDegree]
  have hQ1 : Q = 1 := (RatFunc.monic_denom z).natDegree_eq_zero.mp hQdeg
  refine ⟨N, ?_⟩
  rw [hz, hQ1, map_one, div_one]

theorem ratFuncPow_algebraMap (q : ℕ) (hq : 0 < q) (P : Polynomial k) :
    ratFuncPow q hq (algebraMap (Polynomial k) (RatFunc k) P)
      = algebraMap (Polynomial k) (RatFunc k) (polyPow q P) := by
  simpa using ratFuncPow_div q hq P 1

/-! ## The coefficient descent -/

theorem coeff_mahlerOp (q : ℕ) (hq : 0 < q) (lam : k) (P : Polynomial k) (d : ℕ) :
    (Polynomial.C lam * polyPow q P - P).coeff d
      = lam * (if q ∣ d then P.coeff (d / q) else 0) - P.coeff d := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_polyPow q hq]

theorem coeff_twoTerm (a b : k) (m₁ m₂ d : ℕ) :
    (Polynomial.C a * X ^ m₁ + Polynomial.C b * X ^ m₂).coeff d
      = (if d = m₁ then a else 0) + (if d = m₂ then b else 0) := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  split_ifs <;> ring

variable {p : ℕ}

theorem pow_ne_pow_of_ne (hp : 1 < p) {i j : ℕ} (hij : i ≠ j) : p ^ i ≠ p ^ j := by
  intro h
  exact hij (Nat.pow_right_injective (by omega) h)

theorem not_dvd_pow_zero (hp : 1 < p) : ¬ (p ∣ p ^ (0 : ℕ)) := by
  rw [pow_zero]
  intro hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

theorem pow_succ_div (hp : 1 < p) (i : ℕ) : p ^ (i + 1) / p = p ^ i := by
  rw [pow_succ, Nat.mul_div_cancel _ (by omega)]

theorem poly_mahler_coeff_low (hp : 1 < p) {lam a b : k} {n : ℕ} {P : Polynomial k}
    (heq : Polynomial.C lam * polyPow p P - P
      = Polynomial.C a * X ^ (p ^ n) + Polynomial.C b * X ^ (p ^ (n + 1))) :
    ∀ i : ℕ, i < n → P.coeff (p ^ i) = 0 := by
  intro i
  induction i with
  | zero =>
      intro hn
      have h : (Polynomial.C lam * polyPow p P - P).coeff (p ^ 0)
          = (Polynomial.C a * X ^ (p ^ n)
            + Polynomial.C b * X ^ (p ^ (n + 1))).coeff (p ^ 0) := by rw [heq]
      rw [coeff_mahlerOp p (by omega), coeff_twoTerm, if_neg (not_dvd_pow_zero hp),
        if_neg (pow_ne_pow_of_ne hp (show (0 : ℕ) ≠ n by omega)),
        if_neg (pow_ne_pow_of_ne hp (show (0 : ℕ) ≠ n + 1 by omega))] at h
      linear_combination -h
  | succ i ih =>
      intro hn
      have hlow := ih (by omega)
      have h : (Polynomial.C lam * polyPow p P - P).coeff (p ^ (i + 1))
          = (Polynomial.C a * X ^ (p ^ n)
            + Polynomial.C b * X ^ (p ^ (n + 1))).coeff (p ^ (i + 1)) := by rw [heq]
      rw [coeff_mahlerOp p (by omega), coeff_twoTerm,
        if_pos (dvd_pow_self p (show i + 1 ≠ 0 by omega) : p ∣ p ^ (i + 1)),
        pow_succ_div hp, if_neg (pow_ne_pow_of_ne hp (show i + 1 ≠ n by omega)),
        if_neg (pow_ne_pow_of_ne hp (show i + 1 ≠ n + 1 by omega))] at h
      linear_combination -h + lam * hlow

theorem poly_mahler_coeff_top (hp : 1 < p) {lam a b : k} {n : ℕ} {P : Polynomial k}
    (heq : Polynomial.C lam * polyPow p P - P
      = Polynomial.C a * X ^ (p ^ n) + Polynomial.C b * X ^ (p ^ (n + 1))) :
    P.coeff (p ^ n) = -a := by
  have h : (Polynomial.C lam * polyPow p P - P).coeff (p ^ n)
      = (Polynomial.C a * X ^ (p ^ n)
        + Polynomial.C b * X ^ (p ^ (n + 1))).coeff (p ^ n) := by rw [heq]
  rw [coeff_mahlerOp p (by omega), coeff_twoTerm, if_pos rfl,
    if_neg (pow_ne_pow_of_ne hp (show n ≠ n + 1 by omega))] at h
  cases n with
  | zero =>
      rw [if_neg (not_dvd_pow_zero hp)] at h
      linear_combination -h
  | succ m =>
      have hlow := poly_mahler_coeff_low hp heq m (by omega)
      rw [if_pos (dvd_pow_self p (show m + 1 ≠ 0 by omega) : p ∣ p ^ (m + 1)),
        pow_succ_div hp] at h
      linear_combination -h + lam * hlow

theorem poly_mahler_coeff_high (hp : 1 < p) {lam a b : k} {n : ℕ} {P : Polynomial k}
    (heq : Polynomial.C lam * polyPow p P - P
      = Polynomial.C a * X ^ (p ^ n) + Polynomial.C b * X ^ (p ^ (n + 1))) :
    ∀ i : ℕ, P.coeff (p ^ (n + 1 + i)) = lam ^ i * (-(lam * a + b)) := by
  intro i
  induction i with
  | zero =>
      have htop := poly_mahler_coeff_top hp heq
      have h : (Polynomial.C lam * polyPow p P - P).coeff (p ^ (n + 1))
          = (Polynomial.C a * X ^ (p ^ n)
            + Polynomial.C b * X ^ (p ^ (n + 1))).coeff (p ^ (n + 1)) := by rw [heq]
      rw [coeff_mahlerOp p (by omega), coeff_twoTerm,
        if_neg (pow_ne_pow_of_ne hp (show n + 1 ≠ n by omega)), if_pos rfl,
        if_pos (dvd_pow_self p (show n + 1 ≠ 0 by omega) : p ∣ p ^ (n + 1)),
        pow_succ_div hp] at h
      rw [show n + 1 + 0 = n + 1 from rfl, pow_zero, one_mul]
      linear_combination -h + lam * htop
  | succ i ih =>
      have h : (Polynomial.C lam * polyPow p P - P).coeff (p ^ (n + 1 + i + 1))
          = (Polynomial.C a * X ^ (p ^ n)
            + Polynomial.C b * X ^ (p ^ (n + 1))).coeff (p ^ (n + 1 + i + 1)) := by rw [heq]
      rw [coeff_mahlerOp p (by omega), coeff_twoTerm,
        if_neg (pow_ne_pow_of_ne hp (show n + 1 + i + 1 ≠ n by omega)),
        if_neg (pow_ne_pow_of_ne hp (show n + 1 + i + 1 ≠ n + 1 by omega)),
        if_pos (dvd_pow_self p (show n + 1 + i + 1 ≠ 0 by omega) : p ∣ p ^ (n + 1 + i + 1)),
        pow_succ_div hp] at h
      rw [show n + 1 + (i + 1) = n + 1 + i + 1 from by omega]
      linear_combination -h + lam * ih

/-- **The two-term inhomogeneous Mahler equation has no polynomial solution** unless the
resonance `λa + b` vanishes. -/
theorem no_poly_mahler_solution (hp : 1 < p) {lam a b : k} {n : ℕ} (hlam : lam ≠ 0)
    (hab : lam * a + b ≠ 0) (P : Polynomial k) :
    Polynomial.C lam * polyPow p P - P
      ≠ Polynomial.C a * X ^ (p ^ n) + Polynomial.C b * X ^ (p ^ (n + 1)) := by
  intro heq
  obtain ⟨i, hi⟩ : ∃ i : ℕ, P.natDegree < p ^ (n + 1 + i) := by
    refine ⟨P.natDegree, ?_⟩
    calc P.natDegree < 2 ^ P.natDegree := Nat.lt_two_pow_self
      _ ≤ p ^ P.natDegree := Nat.pow_le_pow_left (by omega) _
      _ ≤ p ^ (n + 1 + P.natDegree) := Nat.pow_le_pow_right (by omega) (by omega)
  have hzero : P.coeff (p ^ (n + 1 + i)) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hi
  rw [poly_mahler_coeff_high hp heq i] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact pow_ne_zero i hlam h
  · exact hab (neg_eq_zero.mp h)

/-- **The two-term inhomogeneous Mahler equation has no rational solution.** -/
theorem no_ratFunc_mahler_solution (hp : 1 < p) {lam a b : k} {n : ℕ} (hlam : lam ≠ 0)
    (hab : lam * a + b ≠ 0) (z : RatFunc k) :
    algebraMap (Polynomial k) (RatFunc k) (Polynomial.C lam) * ratFuncPow p (by omega) z - z
      ≠ algebraMap (Polynomial k) (RatFunc k)
        (Polynomial.C a * X ^ (p ^ n) + Polynomial.C b * X ^ (p ^ (n + 1))) := by
  intro heq
  obtain ⟨P, rfl⟩ := exists_poly_of_ratFunc_mahler_eq p hp lam hlam z _ heq
  refine no_poly_mahler_solution (n := n) hp hlam hab P ?_
  refine IsFractionRing.injective (Polynomial k) (RatFunc k) ?_
  rw [map_sub, map_mul, ← ratFuncPow_algebraMap]
  exact heq

end

end GaloisForLFunctions.HTGeometry
