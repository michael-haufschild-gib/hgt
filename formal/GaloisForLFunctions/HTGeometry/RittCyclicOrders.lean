import GaloisForLFunctions.HTGeometry.RittCyclicNormalForm
import GaloisForLFunctions.HTGeometry.RittUnicriticalNoCocycle

/-!
# Local orders for the cyclic normal form

Every local quantity of `h(w) = (A − Bλw^p)/(1 − λw^p)` is read off from the three identities.  At a
point `z` where the denominator does not vanish the map is regular with value
`(A − Bλz^p)/(1 − λz^p)`, and:

* the derivative is a unit unless `z = 0`, where it vanishes to order `p − 1`;
* the map minus its value vanishes simply unless `z = 0`, where it vanishes to order `p` — the
  origin is the only critical point in the finite chart, and it is totally ramified over `A`.

Feeding these into the substitution law for the order turns the homogeneous transport equation
`F(h)·(h′)^k = b·F` into two statements: the order of `F` is constant along the map away from the
origin, and at the origin `p · ord_A F + k(p−1) = ord_0 F`.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-! ## Orders of a presented quotient -/

omit [CharZero K] in
theorem ratOrder_algebraMap_div {N D : K[X]} (hN : N ≠ 0) (hD : D ≠ 0) (z : K) :
    ratOrder (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D) z
      = (rootMultiplicity z N : ℤ) - rootMultiplicity z D := by
  have hNR : algebraMap K[X] (RatFunc K) N ≠ 0 := algebraMap_ne_zero_of_ne_zero hN
  have hDR : algebraMap K[X] (RatFunc K) D ≠ 0 := algebraMap_ne_zero_of_ne_zero hD
  rw [div_eq_mul_inv, ratOrder_mul hNR (inv_ne_zero hDR), ratOrder_inv hDR,
    ratOrder_algebraMap, ratOrder_algebraMap]
  ring

omit [CharZero K] in
theorem denom_div_eval_ne_zero {N D : K[X]} {z : K} (hz : D.eval z ≠ 0) :
    (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D).denom.eval z ≠ 0 := by
  obtain ⟨E, hE⟩ := RatFunc.denom_div_dvd N D
  intro h
  apply hz
  rw [hE, eval_mul, h, zero_mul]

omit [CharZero K] in
theorem ratValue_algebraMap_div {N D : K[X]} (hD : D ≠ 0) {z : K} (hz : D.eval z ≠ 0) :
    ratValue (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D) z
      = N.eval z / D.eval z := by
  set P : RatFunc K := algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D with hP
  have hDR : algebraMap K[X] (RatFunc K) D ≠ 0 := algebraMap_ne_zero_of_ne_zero hD
  have hPd : algebraMap K[X] (RatFunc K) P.denom ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (RatFunc.denom_ne_zero P)
  have hcross : P.num * D = N * P.denom := by
    refine RatFunc.algebraMap_injective K ?_
    rw [map_mul, map_mul]
    have h1 : algebraMap K[X] (RatFunc K) P.num / algebraMap K[X] (RatFunc K) P.denom
        = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D := by
      rw [RatFunc.num_div_denom]
    exact (div_eq_div_iff hPd hDR).mp h1
  have hPdz : P.denom.eval z ≠ 0 := denom_div_eval_ne_zero hz
  have heval : P.num.eval z * D.eval z = N.eval z * P.denom.eval z := by
    have := congrArg (Polynomial.eval z) hcross
    rwa [eval_mul, eval_mul] at this
  rw [ratValue, div_eq_div_iff hPdz hz]
  linear_combination heval

/-! ## The map is not constant -/

theorem cnf_not_isConst {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B) :
    ¬ ∃ c : K, cnf p A B lam = RatFunc.C c := by
  classical
  rintro ⟨c, hc⟩
  have hc0 : lam * (A - B) ≠ 0 := mul_ne_zero hlam (sub_ne_zero.mpr hAB)
  have hN : (C (lam * (A - B)) * X ^ p : K[X]) ≠ 0 :=
    mul_ne_zero (by rwa [ne_eq, Polynomial.C_eq_zero]) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hmult : rootMultiplicity (0 : K) (C (lam * (A - B)) * X ^ p) = p := by
    rw [rootMultiplicity_mul hN,
      Polynomial.rootMultiplicity_eq_zero
        (by rw [Polynomial.IsRoot, Polynomial.eval_C]; exact hc0),
      rootMultiplicity_pow Polynomial.X_ne_zero, rootMultiplicity_X_eq, if_pos rfl]
    omega
  have hdenm : rootMultiplicity (0 : K) (cnfDen p lam) = 0 := by
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp [Polynomial.IsRoot, zero_pow (by omega : p ≠ 0)]
  have hord := ratOrder_algebraMap_div hN (cnfDen_ne_zero hp lam) (0 : K)
  rw [← cnf_sub_C_A hp, hc, ← map_sub, ratOrder_C, hmult, hdenm] at hord
  omega

/-! ## Local structure at a point of regularity -/

omit [CharZero K] in
theorem cnf_sub_C {p : ℕ} (hp : 0 < p) (A B lam y : K) :
    cnf p A B lam - RatFunc.C y
      = algebraMap K[X] (RatFunc K) (cnfNum p A B lam - C y * cnfDen p lam)
        / algebraMap K[X] (RatFunc K) (cnfDen p lam) := by
  have hD : algebraMap K[X] (RatFunc K) (cnfDen p lam) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (cnfDen_ne_zero hp lam)
  rw [cnf, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, ← RatFunc.algebraMap_C, ← map_mul,
    ← map_sub]

omit [CharZero K] in
theorem cnfFiberPoly_eq (p : ℕ) (A B lam y : K) :
    cnfNum p A B lam - C y * cnfDen p lam = C (A - y) - C ((B - y) * lam) * X ^ p := by
  rw [cnfNum, cnfDen]
  simp only [map_mul, map_sub]
  ring

omit [CharZero K] in
omit [CharZero K] in
theorem cnfFiberPoly_ne_zero {p : ℕ} (hp : 0 < p) {A B lam y : K} (hc : (B - y) * lam ≠ 0) :
    cnfNum p A B lam - C y * cnfDen p lam ≠ 0 := by
  intro h
  have hdeg : (C (A - y) - C ((B - y) * lam) * X ^ p : K[X]).natDegree = p := by
    have he : (C (A - y) - C ((B - y) * lam) * X ^ p : K[X])
        = C (-((B - y) * lam)) * X ^ p + C (A - y) := by rw [map_neg]; ring
    rw [he, Polynomial.natDegree_add_C,
      Polynomial.natDegree_C_mul_X_pow p _ (neg_ne_zero.mpr hc)]
  rw [cnfFiberPoly_eq] at h
  rw [h, natDegree_zero] at hdeg
  omega

omit [CharZero K] in
theorem ratValue_cnf {p : ℕ} (hp : 0 < p) (A B lam : K) {z : K} (hz : 1 - lam * z ^ p ≠ 0) :
    ratValue (cnf p A B lam) z = (A - B * lam * z ^ p) / (1 - lam * z ^ p) := by
  rw [cnf, ratValue_algebraMap_div (cnfDen_ne_zero hp lam) (by rwa [cnfDen_eval]),
    cnfNum_eval, cnfDen_eval]

omit [CharZero K] in
theorem denom_cnf_eval_ne_zero {p : ℕ} (A B lam : K) {z : K} (hz : 1 - lam * z ^ p ≠ 0) :
    (cnf p A B lam).denom.eval z ≠ 0 := by
  rw [cnf]
  exact denom_div_eval_ne_zero (by rwa [cnfDen_eval])

omit [CharZero K] in
/-- The value at a point of regularity is never the critical value at infinity. -/
theorem ratValue_cnf_ne {p : ℕ} (hp : 0 < p) {A B lam : K} (hAB : A ≠ B) {z : K}
    (hz : 1 - lam * z ^ p ≠ 0) : ratValue (cnf p A B lam) z ≠ B := by
  rw [ratValue_cnf hp A B lam hz]
  intro h
  rw [div_eq_iff hz] at h
  exact hAB (by linear_combination h)

/-- Away from the origin the map is unramified. -/
theorem ratOrder_cnf_sub_ratValue_regular {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) {z : K} (hz0 : z ≠ 0) (hz : 1 - lam * z ^ p ≠ 0) :
    ratOrder (cnf p A B lam - RatFunc.C (ratValue (cnf p A B lam) z)) z = 1 := by
  set y : K := ratValue (cnf p A B lam) z with hy
  have hyB : y ≠ B := ratValue_cnf_ne hp hAB hz
  have hcoeff : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
  set f : K[X] := cnfNum p A B lam - C y * cnfDen p lam with hf
  have hfeq : f = C (A - y) - C ((B - y) * lam) * X ^ p := cnfFiberPoly_eq p A B lam y
  have hf0 : f ≠ 0 := cnfFiberPoly_ne_zero hp hcoeff
  have hroot : f.eval z = 0 := by
    rw [hfeq]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    have hyval : y * (1 - lam * z ^ p) = A - B * lam * z ^ p := by
      rw [hy, ratValue_cnf hp A B lam hz, div_mul_cancel₀ _ hz]
    linear_combination -hyval
  have hpK : ((p : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hderiv : (derivative f).eval z ≠ 0 := by
    have hval : (derivative f).eval z = -((B - y) * lam * (p : K) * z ^ (p - 1)) := by
      rw [hfeq, derivative_sub, derivative_C, derivative_C_mul, derivative_X_pow, zero_sub]
      simp only [eval_neg, eval_mul, eval_C, eval_pow, eval_X]
      ring
    rw [hval]
    exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero hcoeff hpK) (pow_ne_zero _ hz0))
  have hmult : rootMultiplicity z f = 1 := rootMultiplicity_eq_one hf0 hroot hderiv
  have hdenm : rootMultiplicity z (cnfDen p lam) = 0 := by
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simpa [Polynomial.IsRoot] using hz
  rw [cnf_sub_C hp, ← hf, ratOrder_algebraMap_div hf0 (cnfDen_ne_zero hp lam), hmult, hdenm]
  omega

omit [CharZero K] in
/-- The origin is totally ramified. -/
theorem ratOrder_cnf_sub_C_A_zero {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) : ratOrder (cnf p A B lam - RatFunc.C A) 0 = (p : ℤ) := by
  classical
  have hc0 : lam * (A - B) ≠ 0 := mul_ne_zero hlam (sub_ne_zero.mpr hAB)
  have hN : (C (lam * (A - B)) * X ^ p : K[X]) ≠ 0 :=
    mul_ne_zero (by rwa [ne_eq, Polynomial.C_eq_zero]) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hmult : rootMultiplicity (0 : K) (C (lam * (A - B)) * X ^ p) = p := by
    rw [rootMultiplicity_mul hN,
      Polynomial.rootMultiplicity_eq_zero
        (by rw [Polynomial.IsRoot, Polynomial.eval_C]; exact hc0),
      rootMultiplicity_pow Polynomial.X_ne_zero, rootMultiplicity_X_eq, if_pos rfl]
    omega
  have hdenm : rootMultiplicity (0 : K) (cnfDen p lam) = 0 := by
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp [Polynomial.IsRoot, zero_pow (by omega : p ≠ 0)]
  rw [cnf_sub_C_A hp, ratOrder_algebraMap_div hN (cnfDen_ne_zero hp lam), hmult, hdenm]
  omega

omit [CharZero K] in
theorem ratValue_cnf_zero {p : ℕ} (hp : 0 < p) (A B lam : K) :
    ratValue (cnf p A B lam) 0 = A := by
  have hz : (1 : K) - lam * (0 : K) ^ p ≠ 0 := by
    rw [zero_pow (by omega : p ≠ 0), mul_zero, sub_zero]
    exact one_ne_zero
  rw [ratValue_cnf hp A B lam hz, zero_pow (by omega : p ≠ 0)]
  simp

/-! ## The order of the derivative -/

theorem ratFuncDeriv_cnf_ne_zero {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) : ratFuncDeriv (cnf p A B lam) ≠ 0 := by
  have hcoeff : (p : K) * lam * (A - B) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlam) (sub_ne_zero.mpr hAB)
  have hN : (C ((p : K) * lam * (A - B)) * X ^ (p - 1) : K[X]) ≠ 0 :=
    mul_ne_zero (by rwa [ne_eq, Polynomial.C_eq_zero]) (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [ratFuncDeriv_cnf hp]
  exact div_ne_zero (algebraMap_ne_zero_of_ne_zero hN)
    (algebraMap_ne_zero_of_ne_zero (pow_ne_zero _ (cnfDen_ne_zero hp lam)))

theorem ratOrder_ratFuncDeriv_cnf_ne_zero {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) {z : K} (hz0 : z ≠ 0) (hz : 1 - lam * z ^ p ≠ 0) :
    ratOrder (ratFuncDeriv (cnf p A B lam)) z = 0 := by
  classical
  have hcoeff : (p : K) * lam * (A - B) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlam) (sub_ne_zero.mpr hAB)
  have hN : (C ((p : K) * lam * (A - B)) * X ^ (p - 1) : K[X]) ≠ 0 :=
    mul_ne_zero (by rwa [ne_eq, Polynomial.C_eq_zero]) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hmult : rootMultiplicity z (C ((p : K) * lam * (A - B)) * X ^ (p - 1)) = 0 := by
    rw [rootMultiplicity_mul hN,
      Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, Polynomial.eval_C]; exact hcoeff),
      rootMultiplicity_pow Polynomial.X_ne_zero, rootMultiplicity_X_eq, if_neg hz0]
    omega
  have hdenm : rootMultiplicity z ((cnfDen p lam) ^ 2) = 0 := by
    rw [rootMultiplicity_pow (cnfDen_ne_zero hp lam),
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hz)]
  rw [ratFuncDeriv_cnf hp,
    ratOrder_algebraMap_div hN (pow_ne_zero _ (cnfDen_ne_zero hp lam)), hmult, hdenm]
  omega

theorem ratOrder_ratFuncDeriv_cnf_zero {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) : ratOrder (ratFuncDeriv (cnf p A B lam)) 0 = (p : ℤ) - 1 := by
  classical
  have hcoeff : (p : K) * lam * (A - B) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlam) (sub_ne_zero.mpr hAB)
  have hN : (C ((p : K) * lam * (A - B)) * X ^ (p - 1) : K[X]) ≠ 0 :=
    mul_ne_zero (by rwa [ne_eq, Polynomial.C_eq_zero]) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hmult : rootMultiplicity (0 : K) (C ((p : K) * lam * (A - B)) * X ^ (p - 1)) = p - 1 := by
    rw [rootMultiplicity_mul hN,
      Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, Polynomial.eval_C]; exact hcoeff),
      rootMultiplicity_pow Polynomial.X_ne_zero, rootMultiplicity_X_eq, if_pos rfl]
    omega
  have hdenm : rootMultiplicity (0 : K) ((cnfDen p lam) ^ 2) = 0 := by
    rw [rootMultiplicity_pow (cnfDen_ne_zero hp lam),
      Polynomial.rootMultiplicity_eq_zero
        (by simp [Polynomial.IsRoot, zero_pow (by omega : p ≠ 0)])]
  rw [ratFuncDeriv_cnf hp,
    ratOrder_algebraMap_div hN (pow_ne_zero _ (cnfDen_ne_zero hp lam)), hmult, hdenm]
  omega

/-! ## The transport equation -/

omit [CharZero K] in
theorem ratFuncSubstitution_ne_zero {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) : ratFuncSubstitutionAlgHom P hP Q ≠ 0 := by
  intro h
  exact hQ ((ratFuncSubstitutionAlgHom P hP).toRingHom.injective (by simpa using h))

/-- **The master local relation.**  The order of a solution at a point, the order at its image, the
local multiplicity of the map and the order of the derivative are tied by the transport equation. -/
theorem cnf_transport_master {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F)
    {z : K} (hz : 1 - lam * z ^ p ≠ 0) :
    ratOrder F (ratValue (cnf p A B lam) z)
        * ratOrder (cnf p A B lam - RatFunc.C (ratValue (cnf p A B lam) z)) z
      + k * ratOrder (ratFuncDeriv (cnf p A B lam)) z = ratOrder F z := by
  have hd0 : ratFuncDeriv (cnf p A B lam) ≠ 0 := ratFuncDeriv_cnf_ne_zero hp hlam hAB
  have hbC : (RatFunc.C b : RatFunc K) ≠ 0 := by simpa using hb
  have hsub := ratOrder_ratFuncSubstitution_ratFunc hP (denom_cnf_eval_ne_zero A B lam hz) hF
  have hlhs : ratOrder (ratFuncSubstitutionAlgHom (cnf p A B lam) hP F
        * (ratFuncDeriv (cnf p A B lam)) ^ k) z
      = ratOrder F (ratValue (cnf p A B lam) z)
          * ratOrder (cnf p A B lam - RatFunc.C (ratValue (cnf p A B lam) z)) z
        + k * ratOrder (ratFuncDeriv (cnf p A B lam)) z := by
    rw [ratOrder_mul (ratFuncSubstitution_ne_zero hP hF) (zpow_ne_zero k hd0),
      ratOrder_zpow hd0, hsub]
  rw [heq, add_zero, ratOrder_mul hbC hF, ratOrder_C, zero_add] at hlhs
  exact hlhs.symm

/-- Away from the critical point the order of a solution is constant along the map. -/
theorem cnf_transport_regular {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F)
    {z : K} (hz0 : z ≠ 0) (hz : 1 - lam * z ^ p ≠ 0) :
    ratOrder F ((A - B * lam * z ^ p) / (1 - lam * z ^ p)) = ratOrder F z := by
  have hm := cnf_transport_master hp hlam hAB hb hF heq hz
  rw [ratOrder_cnf_sub_ratValue_regular hp hlam hAB hz0 hz,
    ratOrder_ratFuncDeriv_cnf_ne_zero hp hlam hAB hz0 hz, ratValue_cnf hp A B lam hz] at hm
  omega

/-- At the critical point the transport equation acquires the ramification term. -/
theorem cnf_transport_critical {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F) :
    ratOrder F A * (p : ℤ) + k * ((p : ℤ) - 1) = ratOrder F 0 := by
  have hz : (1 : K) - lam * (0 : K) ^ p ≠ 0 := by
    rw [zero_pow (by omega : p ≠ 0), mul_zero, sub_zero]
    exact one_ne_zero
  have hm := cnf_transport_master hp hlam hAB hb hF heq hz
  rw [ratValue_cnf_zero hp, ratOrder_cnf_sub_C_A_zero hp hlam hAB,
    ratOrder_ratFuncDeriv_cnf_zero hp hlam hAB] at hm
  exact hm

end

end GaloisForLFunctions.HTGeometry
