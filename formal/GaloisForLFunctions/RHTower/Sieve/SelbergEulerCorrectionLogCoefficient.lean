import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogLocal
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogCoefficient
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionPrimePowers

/-!
# The differentiated Euler correction

`corr^{log}` is the `s`-derivative at `s = 1` of the Barban--Vehov Euler correction of the
two-parameter family `c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)`.  Being such a derivative it is a Leibniz
derivation of `corr`, hence determined by the local coefficients `selbergCorrectionLogLocal`
through the standard formula

`D m n = ∑_{p ∣ mn} L_p(v_p m, v_p n) · corr(m / p^{v_p m}, n / p^{v_p n})`.

This file takes that formula as the definition and proves it has the two properties the rigidity
lemma consumes: the prescribed prime-power values, and the Leibniz rule.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- The differentiated Euler correction. -/
def selbergEulerCorrectionLogCoeff (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ p ∈ (m * n).primeFactors,
      selbergCorrectionLogLocal p (m.factorization p) (n.factorization p) *
        selbergEulerCorrectionCoeff (m / p ^ (m.factorization p))
          (n / p ^ (n.factorization p))

@[simp] theorem selbergEulerCorrectionLogCoeff_one :
    selbergEulerCorrectionLogCoeff 1 1 = 0 := by
  rw [selbergEulerCorrectionLogCoeff, if_neg (by simp)]
  simp

theorem selbergEulerCorrectionLogCoeff_zero_left (n : ℕ) :
    selbergEulerCorrectionLogCoeff 0 n = 0 := by
  rw [selbergEulerCorrectionLogCoeff, if_pos (Or.inl rfl)]

theorem selbergEulerCorrectionLogCoeff_zero_right (m : ℕ) :
    selbergEulerCorrectionLogCoeff m 0 = 0 := by
  rw [selbergEulerCorrectionLogCoeff, if_pos (Or.inr rfl)]

/-- **Prime-power values of the differentiated correction.** -/
theorem selbergEulerCorrectionLogCoeff_prime_pow
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergEulerCorrectionLogCoeff (p ^ i) (p ^ j) =
      selbergCorrectionLogLocal p i j := by
  rcases Nat.eq_zero_or_pos (i + j) with hij | hij
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hj
    rw [pow_zero, selbergEulerCorrectionLogCoeff_one, selbergCorrectionLogLocal]
    simp
  · have hpow : (p ^ i) * (p ^ j) = p ^ (i + j) := (pow_add p i j).symm
    rw [selbergEulerCorrectionLogCoeff, if_neg (by
      simp [hp.ne_zero]), hpow]
    have hpf : (p ^ (i + j)).primeFactors = {p} := by
      rw [Nat.primeFactors_prime_pow (by omega) hp]
    rw [hpf, Finset.sum_singleton]
    have hfi : (p ^ i).factorization p = i := by
      rw [Nat.Prime.factorization_pow hp]
      simp
    have hfj : (p ^ j).factorization p = j := by
      rw [Nat.Prime.factorization_pow hp]
      simp
    rw [hfi, hfj, Nat.div_self (pow_pos hp.pos i), Nat.div_self (pow_pos hp.pos j)]
    simp

private theorem localTerm_split
    {a b c d p : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : Nat.Coprime (a * b) (c * d)) (hpc : ¬ p ∣ c) (hpd : ¬ p ∣ d) :
    selbergCorrectionLogLocal p ((a * c).factorization p) ((b * d).factorization p) *
        selbergEulerCorrectionCoeff ((a * c) / p ^ ((a * c).factorization p))
          ((b * d) / p ^ ((b * d).factorization p)) =
      selbergCorrectionLogLocal p (a.factorization p) (b.factorization p) *
        selbergEulerCorrectionCoeff (a / p ^ (a.factorization p))
          (b / p ^ (b.factorization p)) *
        selbergEulerCorrectionCoeff c d := by
  have hfac1 : (a * c).factorization p = a.factorization p := by
    rw [Nat.factorization_mul ha.ne' hc.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpc]
  have hfac2 : (b * d).factorization p = b.factorization p := by
    rw [Nat.factorization_mul hb.ne' hd.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpd]
  have hdiv1 : (a * c) / p ^ (a.factorization p) =
      (a / p ^ (a.factorization p)) * c :=
    Nat.mul_div_right_comm (Nat.ordProj_dvd a p) c
  have hdiv2 : (b * d) / p ^ (b.factorization p) =
      (b / p ^ (b.factorization p)) * d :=
    Nat.mul_div_right_comm (Nat.ordProj_dvd b p) d
  have hcop : Nat.Coprime
      ((a / p ^ (a.factorization p)) * (b / p ^ (b.factorization p))) (c * d) :=
    h.of_dvd_left (mul_dvd_mul (Nat.div_dvd_of_dvd (Nat.ordProj_dvd a p))
      (Nat.div_dvd_of_dvd (Nat.ordProj_dvd b p)))
  rw [hfac1, hfac2, hdiv1, hdiv2,
    bivariateMultiplicative_selbergEulerCorrectionCoeff.map_mul_of_pair_coprime hcop]
  ring

/-- **The differentiated Euler correction is a Leibniz derivation of the correction.** -/
theorem bivariateDerivation_selbergEulerCorrectionLogCoeff :
    BivariateDerivation selbergEulerCorrectionCoeff selbergEulerCorrectionLogCoeff := by
  constructor
  · exact selbergEulerCorrectionLogCoeff_one
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · have hcd1 : c * d = 1 := by
        have hcop : Nat.Coprime 0 (c * d) := by rw [← hab0]; exact h
        simpa using hcop
      have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
      have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by rw [Nat.mul_comm]; exact hcd1.symm⟩
      subst hc1
      subst hd1
      simp [selbergEulerCorrectionLogCoeff_one, selbergEulerCorrectionCoeff_one]
    by_cases hcd0 : c * d = 0
    · have hab1 : a * b = 1 := by
        have hcop : Nat.Coprime (a * b) 0 := by rw [← hcd0]; exact h
        simpa using hcop
      have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
      have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by rw [Nat.mul_comm]; exact hab1.symm⟩
      subst ha1
      subst hb1
      simp [selbergEulerCorrectionLogCoeff_one, selbergEulerCorrectionCoeff_one]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hac : 0 < a * c := Nat.mul_pos ha hc
    have hbd : 0 < b * d := Nat.mul_pos hb hd
    rw [selbergEulerCorrectionLogCoeff, if_neg (not_or_intro hac.ne' hbd.ne'),
      selbergEulerCorrectionLogCoeff, if_neg (not_or_intro ha.ne' hb.ne'),
      selbergEulerCorrectionLogCoeff, if_neg (not_or_intro hc.ne' hd.ne')]
    have hreassoc : (a * c) * (b * d) = (a * b) * (c * d) := by ring
    rw [hreassoc, Nat.primeFactors_mul hab0 hcd0,
      Finset.sum_union h.disjoint_primeFactors, Finset.sum_mul, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl ?_
      intro p hp
      have hpmem : p ∉ (c * d).primeFactors := by
        intro hcon
        exact (Finset.disjoint_left.mp h.disjoint_primeFactors hp) hcon
      have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpnd : ¬ p ∣ c * d := by
        intro hcon
        exact hpmem (Nat.mem_primeFactors.mpr ⟨hprime, hcon, hcd0⟩)
      have hpc : ¬ p ∣ c := fun hcon => hpnd (hcon.mul_right d)
      have hpd : ¬ p ∣ d := fun hcon => hpnd (hcon.mul_left c)
      exact localTerm_split ha hb hc hd h hpc hpd
    · refine Finset.sum_congr rfl ?_
      intro p hp
      have hpmem : p ∉ (a * b).primeFactors := by
        intro hcon
        exact (Finset.disjoint_right.mp h.disjoint_primeFactors hp) hcon
      have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpnd : ¬ p ∣ a * b := by
        intro hcon
        exact hpmem (Nat.mem_primeFactors.mpr ⟨hprime, hcon, hab0⟩)
      have hpa : ¬ p ∣ a := fun hcon => hpnd (hcon.mul_right b)
      have hpb : ¬ p ∣ b := fun hcon => hpnd (hcon.mul_left a)
      have hswap : Nat.Coprime (c * d) (a * b) := h.symm
      have hterm := localTerm_split hc hd ha hb hswap hpa hpb
      have hcomm1 : (c * a).factorization p = (a * c).factorization p := by
        rw [Nat.mul_comm]
      have hcomm2 : (d * b).factorization p = (b * d).factorization p := by
        rw [Nat.mul_comm]
      have hnum1 : c * a = a * c := Nat.mul_comm c a
      have hnum2 : d * b = b * d := Nat.mul_comm d b
      rw [hcomm1, hcomm2, hnum1, hnum2] at hterm
      rw [hterm]
      ring

end

end RHTower.Sieve
