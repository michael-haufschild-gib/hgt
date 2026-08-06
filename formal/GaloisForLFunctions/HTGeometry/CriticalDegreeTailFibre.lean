import GaloisForLFunctions.HTGeometry.MonomialTailFibreEquiv
import GaloisForLFunctions.HTGeometry.OneDeepFibreBound

/-!
# The fibre over an observation whose tails have exactly the critical degrees

The monomial-tail analysis uses of its tails only that they have exactly the critical degrees: the
low product then cannot reach the horizon, so the truncated compatibility equation closes to the
exact factorization `(A + U)(B + V) = 1 + U V`, and the completed jet is a polynomial of degree the
first depth whose leading coefficient is the observed one.

Both facts hold for arbitrary tails of those degrees, with no monomial assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

omit [Field K] in
/-- **The exact factorization satisfied by a fibre point of a critical-degree observation.**  The
truncation is vacuous at these degrees, so the compatibility equation closes on the nose. -/
theorem criticalFibre_mul_eq_of_degree_le {K : Type*} [CommRing K] [IsDomain K] (hm : 0 < m)
    {U V : K[X]} (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ))
    (p : criticalFibre K m n U V) :
    (p.1.1 + U) * (p.1.2 + V) = 1 + U * V := by
  obtain ⟨⟨A, B⟩, hA, hB, hdvd⟩ := p
  have hdeg := degree_criticalLowProduct_lt hA hB hU hV
  have hsub : (criticalLowProduct U V A B - 1).degree < ((m + n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg ?_)
    refine lt_of_le_of_lt Polynomial.degree_one_le ?_
    exact_mod_cast (by omega : (0 : ℕ) < m + n)
  exact (criticalLowProduct_factorization_iff U V A B).1 ((dvd_sub_one_iff_eq_one hsub).1 hdvd)

/-- **The completed jet of a critical-degree observation has degree the first depth, with the
observed leading coefficient.** -/
theorem degree_leadingCoeff_add_tail {U : K[X]} (hU : U.degree ≤ (m : ℕ))
    (hUm : U.coeff m ≠ 0) {A : K[X]} (hA : A.degree < (m : ℕ)) :
    (A + U).degree = ((m : ℕ) : WithBot ℕ) ∧ (A + U).leadingCoeff = U.coeff m := by
  have hUdeg : U.degree = ((m : ℕ) : WithBot ℕ) := by
    refine le_antisymm hU ?_
    exact Polynomial.le_degree_of_ne_zero hUm
  have hdeg : (A + U).degree = ((m : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_right_of_degree_lt (by rw [hUdeg]; exact hA), hUdeg]
  refine ⟨hdeg, ?_⟩
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg,
    Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt hA, zero_add]


/-! ## The fibre as a set of divisors -/

section Divisors

variable {K : Type*} [Field K] {m n : ℕ}

/-- **A fibre point of a critical-degree observation is a monic divisor of the target.**  Scaling
the completed jet by the inverse of its leading coefficient makes it monic, and the exact
factorization exhibits it as a divisor of `1 + U V`. -/
noncomputable def criticalTailToDivisor (hm : 0 < m) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (p : criticalFibre K m n U V) :
    {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m} := by
  refine ⟨C (U.coeff m)⁻¹ * (p.1.1 + U), ?_, ?_, ?_⟩
  · obtain ⟨-, hlc⟩ := degree_leadingCoeff_add_tail hU hUm p.2.1
    show (C (U.coeff m)⁻¹ * (p.1.1 + U)).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlc, inv_mul_cancel₀ hUm]
  · refine dvd_trans ⟨C (U.coeff m), ?_⟩
      ⟨p.1.2 + V, (criticalFibre_mul_eq_of_degree_le hm hU hV p).symm⟩
    rw [mul_comm (C (U.coeff m)⁻¹ * (p.1.1 + U)) (C (U.coeff m)), ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hUm, map_one, one_mul]
  · obtain ⟨hdeg, -⟩ := degree_leadingCoeff_add_tail hU hUm p.2.1
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hUm)]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- **The divisor determines the fibre point.** -/
theorem criticalTailToDivisor_injective (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    Function.Injective (criticalTailToDivisor (K := K) (n := n) hm hU hV hUm) := by
  intro p q hpq
  refine criticalFibre_fst_injective hm hn hU0 hV0 ?_
  have h : C (U.coeff m)⁻¹ * (p.1.1 + U) = C (U.coeff m)⁻¹ * (q.1.1 + U) :=
    congrArg Subtype.val hpq
  have hC : (C (U.coeff m)⁻¹ : K[X]) ≠ 0 := by
    simpa using inv_ne_zero hUm
  have hadd : p.1.1 + U = q.1.1 + U := mul_left_cancel₀ hC h
  exact add_right_cancel hadd

end Divisors


/-! ## The target of the factorization -/

section Target

variable {K : Type*} [Field K] {m n : ℕ}

/-- **The target of a critical-degree observation has degree the horizon and the product of the two
observed leading coefficients as its own.** -/
theorem degree_leadingCoeff_target_tail (hm : 0 < m) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) :
    (1 + U * V).degree = ((m + n : ℕ) : WithBot ℕ) ∧
      (1 + U * V).leadingCoeff = U.coeff m * V.coeff n := by
  have hUdeg : U.degree = ((m : ℕ) : WithBot ℕ) :=
    le_antisymm hU (Polynomial.le_degree_of_ne_zero hUm)
  have hVdeg : V.degree = ((n : ℕ) : WithBot ℕ) :=
    le_antisymm hV (Polynomial.le_degree_of_ne_zero hVn)
  have hU0 : U ≠ 0 := fun h => hUm (by rw [h]; simp)
  have hV0 : V ≠ 0 := fun h => hVn (by rw [h]; simp)
  have hUlc : U.leadingCoeff = U.coeff m := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hUdeg]
  have hVlc : V.leadingCoeff = V.coeff n := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hVdeg]
  have hmul : (U * V).degree = ((m + n : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, hUdeg, hVdeg]
    exact_mod_cast rfl
  have hone : (1 : K[X]).degree < (U * V).degree := by
    rw [hmul]
    refine lt_of_le_of_lt Polynomial.degree_one_le ?_
    exact_mod_cast (by omega : (0 : ℕ) < m + n)
  refine ⟨?_, ?_⟩
  · rw [Polynomial.degree_add_eq_right_of_degree_lt hone, hmul]
  · rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some
      (by rw [Polynomial.degree_add_eq_right_of_degree_lt hone, hmul] :
        (1 + U * V).degree = ((m + n : ℕ) : WithBot ℕ)),
      Polynomial.coeff_add, Polynomial.coeff_one,
      if_neg (by omega : ¬ (m + n = 0)), zero_add]
    have := Polynomial.coeff_mul_degree_add_degree U V
    rw [Polynomial.natDegree_eq_of_degree_eq_some hUdeg,
      Polynomial.natDegree_eq_of_degree_eq_some hVdeg, hUlc, hVlc] at this
    exact this

end Target


/-! ## Every divisor arises -/

section Surjectivity

variable {K : Type*} [Field K] {m n : ℕ}

/-- **The fibre of a critical-degree observation is the set of monic divisors of its target of the
first depth.**  Given such a divisor, scaling it by the observed leading coefficient and its
cofactor by the inverse produces a fibre point mapping to it. -/
theorem criticalTailToDivisor_surjective (hm : 0 < m) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) :
    Function.Surjective (criticalTailToDivisor (K := K) (n := n) hm hU hV hUm) := by
  rintro ⟨M, hMonic, hdvd, hMdeg⟩
  obtain ⟨N, hN⟩ := hdvd
  set c : K := U.coeff m with hc
  obtain ⟨htdeg, htlc⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hUdeg : U.degree = ((m : ℕ) : WithBot ℕ) :=
    le_antisymm hU (Polynomial.le_degree_of_ne_zero hUm)
  have hVdeg : V.degree = ((n : ℕ) : WithBot ℕ) :=
    le_antisymm hV (Polynomial.le_degree_of_ne_zero hVn)
  have hUlc : U.leadingCoeff = c := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hUdeg]
  have hVlc : V.leadingCoeff = V.coeff n := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hVdeg]
  have hMd : M.degree = ((m : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hMonic.ne_zero, hMdeg]
  -- the cofactor has the complementary degree and the observed leading coefficient
  have hMN : M * N = 1 + U * V := hN.symm
  have hNne : N ≠ 0 := by
    intro h
    have hzero : (1 + U * V) = 0 := by rw [← hMN, h, mul_zero]
    rw [hzero, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  have hNdeg : N.degree = ((n : ℕ) : WithBot ℕ) := by
    have := Polynomial.degree_mul (p := M) (q := N)
    rw [hMN, htdeg, hMd] at this
    have hcast : ((m + n : ℕ) : WithBot ℕ) = ((m : ℕ) : WithBot ℕ) + ((n : ℕ) : WithBot ℕ) := by
      exact_mod_cast rfl
    rw [hcast] at this
    exact (WithBot.add_left_cancel (by simp) this).symm
  have hNlc : N.leadingCoeff = c * V.coeff n := by
    have := Polynomial.leadingCoeff_mul M N
    rw [hMN, htlc, hMonic.leadingCoeff, one_mul] at this
    exact this.symm
  -- the two components
  refine ⟨⟨(C c * M - U, C c⁻¹ * N - V), ?_, ?_, ?_⟩, ?_⟩
  · refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ ?_ ?_) (le_of_eq ?_)
    · rw [Polynomial.degree_C_mul hUm, hMd, hUdeg]
    · exact mul_ne_zero (by simpa using hUm) hMonic.ne_zero
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hMonic.leadingCoeff, mul_one,
        hUlc]
    · rw [Polynomial.degree_C_mul hUm, hMd]
  · refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ ?_ ?_) (le_of_eq ?_)
    · rw [Polynomial.degree_C_mul (inv_ne_zero hUm), hNdeg, hVdeg]
    · exact mul_ne_zero (by simpa using inv_ne_zero hUm) hNne
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hNlc, ← mul_assoc,
        inv_mul_cancel₀ hUm, one_mul, hVlc]
    · rw [Polynomial.degree_C_mul (inv_ne_zero hUm), hNdeg]
  · have hprod : (C c * M - U + U) * (C c⁻¹ * N - V + V) = 1 + U * V := by
      rw [sub_add_cancel, sub_add_cancel, show C c * M * (C c⁻¹ * N) = (C c * C c⁻¹) * (M * N) from
        by ring, ← map_mul, mul_inv_cancel₀ hUm, map_one, one_mul, hMN]
    rw [show criticalLowProduct U V (C c * M - U) (C c⁻¹ * N - V) - 1 = 0 from by
      have := (criticalLowProduct_factorization_iff U V (C c * M - U) (C c⁻¹ * N - V)).2 hprod
      rw [this, sub_self]]
    exact dvd_zero _
  · refine Subtype.ext ?_
    show C c⁻¹ * (C c * M - U + U) = M
    rw [sub_add_cancel, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hUm, map_one, one_mul]

end Surjectivity


/-! ## The count at the critical degrees -/

section Count

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- **The monic divisors of a separable polynomial of a prescribed degree are counted by a binomial
coefficient**, with no monicity assumed of the polynomial itself: normalising by the leading
coefficient changes neither the divisors nor separability. -/
theorem nat_card_monic_divisors_of_separable {P : K[X]} (hP : P ≠ 0) (hsep : P.Separable)
    (m : ℕ) :
    Nat.card {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} = P.natDegree.choose m := by
  classical
  set c : K := P.leadingCoeff with hc
  have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  set M : K[X] := P * C c⁻¹ with hM
  have hMmonic : M.Monic := Polynomial.monic_mul_leadingCoeff_inv hP
  have hMdeg : M.natDegree = P.natDegree := by
    rw [hM, Polynomial.natDegree_mul_C (inv_ne_zero hc0)]
  have hCC : (C c : K[X]) * C c⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hc0, map_one]
  have hMsep : M.Separable := by
    obtain ⟨a, b, hab⟩ := hsep
    refine ⟨a * C c, b * C c, ?_⟩
    have hder : derivative M = derivative P * C c⁻¹ := by
      rw [hM, derivative_mul, derivative_C, mul_zero, add_zero]
    rw [hM, hder]
    calc a * C c * (P * C c⁻¹) + b * C c * (derivative P * C c⁻¹)
        = (a * P + b * derivative P) * (C c * C c⁻¹) := by ring
      _ = 1 := by rw [hCC, mul_one]; exact hab
  have hdvd : ∀ A : K[X], A ∣ P ↔ A ∣ M := by
    intro A
    rw [hM]
    exact ((isUnit_C.2 (inv_ne_zero hc0).isUnit).dvd_mul_right).symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun A => by rw [hdvd A]),
    nat_card_monic_divisors hMmonic hMsep (IsAlgClosed.splits _) m, hMdeg]

/-- **The fibre over an observation with arbitrary tails of the critical degrees has exactly the
critical binomial multiplicity of points**, whenever its target is separable. -/
theorem nat_card_criticalFibre_criticalTails (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hsep : (1 + U * V).Separable) :
    Nat.card (criticalFibre K m n U V) = criticalHorizonMultiplicity m n := by
  classical
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  have hnat : (1 + U * V).natDegree = m + n :=
    Polynomial.natDegree_eq_of_degree_eq_some htdeg
  rw [Nat.card_congr (Equiv.ofBijective _
      ⟨criticalTailToDivisor_injective hm hn hU hV hUm hU0 hV0,
        criticalTailToDivisor_surjective hm hU hV hUm hVn⟩),
    nat_card_monic_divisors_of_separable hne hsep m, hnat]
  rfl

end Count


/-! ## Only the first coefficients of a tail matter -/

section Truncation

variable {R : Type*} [CommRing R] {m n : ℕ}

theorem criticalLowProduct_sub_tails (U U' V V' A B : R[X]) :
    criticalLowProduct U V A B - criticalLowProduct U' V' A B
      = A * (V - V') + (U - U') * B := by
  simp only [criticalLowProduct]
  ring

/-- **Tails agreeing to the horizon impose the same compatibility.** -/
theorem dvd_criticalLowProduct_of_dvd_sub_tails {U U' V V' A B : R[X]}
    (hU : (X : R[X]) ^ (m + n) ∣ (U - U')) (hV : (X : R[X]) ^ (m + n) ∣ (V - V'))
    (h : (X : R[X]) ^ (m + n) ∣ (criticalLowProduct U V A B - 1)) :
    (X : R[X]) ^ (m + n) ∣ (criticalLowProduct U' V' A B - 1) := by
  have hdiff : (X : R[X]) ^ (m + n) ∣
      (criticalLowProduct U V A B - criticalLowProduct U' V' A B) := by
    rw [criticalLowProduct_sub_tails]
    exact dvd_add (Dvd.dvd.mul_left hV _) (Dvd.dvd.mul_right hU _)
  have hid : (criticalLowProduct U V A B - 1)
      - (criticalLowProduct U V A B - criticalLowProduct U' V' A B)
      = criticalLowProduct U' V' A B - 1 := by ring
  rw [← hid]
  exact dvd_sub h hdiff

/-- **The fibre of an observation is the fibre of its truncation.**  An observed tail is seen only
through its coefficients below the horizon, so a tail of any length imposes the same condition as
its truncation and the count is a question about finitely many coefficients. -/
def criticalFibreCongr {U U' V V' : R[X]}
    (hU : (X : R[X]) ^ (m + n) ∣ (U - U')) (hV : (X : R[X]) ^ (m + n) ∣ (V - V')) :
    criticalFibre R m n U V ≃ criticalFibre R m n U' V' where
  toFun p := ⟨p.1, p.2.1, p.2.2.1,
    dvd_criticalLowProduct_of_dvd_sub_tails hU hV p.2.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1,
    dvd_criticalLowProduct_of_dvd_sub_tails
      (by simpa using (dvd_neg.2 hU)) (by simpa using (dvd_neg.2 hV)) p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Truncation


/-! ## The count for tails of any length -/

section LongTails

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- **The count for an observation of any tail length whose truncation has the critical degrees.**
Only the coefficients below the horizon are seen, so an observation is counted by the critical
binomial multiplicity as soon as its truncation has the critical degrees and a separable target —
with no bound whatever on the degrees of the observed tails themselves. -/
theorem nat_card_criticalFibre_of_truncation (hm : 0 < m) (hn : 0 < n) {U V U' V' : K[X]}
    (hUU : (X : K[X]) ^ (m + n) ∣ (U - U')) (hVV : (X : K[X]) ^ (m + n) ∣ (V - V'))
    (hU : U'.degree ≤ (m : ℕ)) (hV : V'.degree ≤ (n : ℕ)) (hUm : U'.coeff m ≠ 0)
    (hVn : V'.coeff n ≠ 0) (hU0 : U'.coeff 0 = 0) (hV0 : V'.coeff 0 = 0)
    (hsep : (1 + U' * V').Separable) :
    Nat.card (criticalFibre K m n U V) = criticalHorizonMultiplicity m n := by
  rw [Nat.card_congr (criticalFibreCongr hUU hVV)]
  exact nat_card_criticalFibre_criticalTails hm hn hU hV hUm hVn hU0 hV0 hsep

end LongTails


/-! ## The hypothesis is satisfiable -/

section Satisfiable

variable {K : Type*} [Field K]

/-- **Separability survives a nonzero scalar multiple.**  Mathlib has no such lemma; the witnesses
of coprimality are rescaled by the inverse. -/
theorem separable_C_mul {P : K[X]} (hsep : P.Separable) {c : K} (hc : c ≠ 0) :
    (C c * P).Separable := by
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨a * C c⁻¹, b * C c⁻¹, ?_⟩
  have hCC : (C c⁻¹ : K[X]) * C c = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, map_one]
  have hder : derivative (C c * P) = C c * derivative P := by
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [hder]
  calc a * C c⁻¹ * (C c * P) + b * C c⁻¹ * (C c * derivative P)
      = (a * P + b * derivative P) * (C c⁻¹ * C c) := by ring
    _ = 1 := by rw [hCC, mul_one]; exact hab

/-- **A monomial target is separable.**  It is a scalar multiple of `X ^ L - C a` with `a` nonzero,
which is separable in characteristic zero. -/
theorem separable_one_add_C_mul_X_pow [CharZero K] {L : ℕ} (hL : 0 < L) {e : K} (he : e ≠ 0) :
    (1 + C e * X ^ L : K[X]).Separable := by
  have hcast : (L : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hassoc : (1 + C e * X ^ L : K[X]) = C e * (X ^ L - C (-e⁻¹)) := by
    rw [mul_sub, ← C_mul, show e * -e⁻¹ = -1 from by field_simp, map_neg, map_one]
    ring
  rw [hassoc]
  exact separable_C_mul (Polynomial.separable_X_pow_sub_C _ hcast (neg_ne_zero.2 (inv_ne_zero he)))
    he

end Satisfiable


/-! ## Depth one sees the reciprocal tail only through one coefficient -/

section DepthOneGeneral

variable {K : Type*} [Field K] {n : ℕ}

/-- **At depth one the system involves a single coefficient of the observed reciprocal tail.**  So
two observations agreeing in that coefficient have the same solution set. -/
def criticalSystemSolutionsCongrOne {U V V' : K[X]} (h : V.coeff n = V'.coeff n) :
    criticalSystemSolutions K 1 n U V ≃ criticalSystemSolutions K 1 n U V' where
  toFun p := ⟨p.1, p.2.1, p.2.2.1, fun k hk1 hk2 => by
    have hkn : k = n := by omega
    subst hkn
    rw [← h]
    exact p.2.2.2 k hk1 hk2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, fun k hk1 hk2 => by
    have hkn : k = n := by omega
    subst hkn
    rw [h]
    exact p.2.2.2 k hk1 hk2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The count at depth one, for an arbitrary observed reciprocal tail.**  The corpus's depth-one
theorem is stated for a monomial tail; at depth one the system reads only the tail's coefficient at
the reciprocal depth, so the count holds for every tail with that coefficient. -/
theorem nat_card_criticalFibre_one_eq_multiplicity_of_tail [IsAlgClosed K] (hn : 0 < n)
    {U V : K[X]} (hU0 : U.coeff 0 = 0) (hU : (X : K[X]) ^ 1 ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hVdeg : V.degree < ((1 + n : ℕ) : WithBot ℕ)) (hVn : V.coeff n ≠ 0)
    (hsep : (oneDeepEquation U (V.coeff n) n).Separable)
    (hzero : ¬ (oneDeepEquation U (V.coeff n) n).IsRoot 0) :
    Nat.card (criticalFibre K 1 n U V) = criticalHorizonMultiplicity 1 n := by
  have hmono : ((C (V.coeff n) * X ^ n : K[X])).coeff n = V.coeff n := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hdvdmono : (X : K[X]) ^ n ∣ (C (V.coeff n) * X ^ n) := Dvd.intro_left _ rfl
  have hdegmono : ((C (V.coeff n) * X ^ n : K[X])).degree < ((1 + n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (by omega : n < 1 + n)
  rw [nat_card_criticalFibre_eq_solutions (by omega) hn hU hV hVdeg,
    Nat.card_congr (criticalSystemSolutionsCongrOne (V' := C (V.coeff n) * X ^ n) hmono.symm),
    ← nat_card_criticalFibre_eq_solutions (by omega) hn hU hdvdmono hdegmono]
  exact nat_card_criticalFibre_one_eq_multiplicity hn hU0 hVn hsep hzero

end DepthOneGeneral

end GaloisForLFunctions.HTGeometry
