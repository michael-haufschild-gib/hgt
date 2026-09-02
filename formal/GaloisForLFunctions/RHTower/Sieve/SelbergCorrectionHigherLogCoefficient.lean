import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionHigherLogLocal
import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogSummable
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCoefficientIdentity

/-!
# All logarithmic jets of the Selberg Euler correction

The local correction factor is encoded as an exponential power series: coefficient `k` is its
`k`-th logarithmic derivative divided by `k!`.  Taking the finite Euler product over primes dividing
the pair gives the global jet without any analytic infinite product.  Pair-coprime
multiplicativity then follows directly from disjoint prime support.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Exponential jet of one local correction factor. -/
def selbergCorrectionJetLocal (p i j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun k =>
    if k = 0 then selbergLocalCorrection p i j
    else selbergCorrectionLogPowerLocal k p i j / (k.factorial : ℝ)

@[simp] theorem coeff_selbergCorrectionJetLocal_zero (p i j : ℕ) :
    PowerSeries.coeff 0 (selbergCorrectionJetLocal p i j) =
      selbergLocalCorrection p i j := by
  simp [selbergCorrectionJetLocal]

theorem coeff_selbergCorrectionJetLocal_succ (k p i j : ℕ) :
    PowerSeries.coeff (k + 1) (selbergCorrectionJetLocal p i j) =
      selbergCorrectionLogPowerLocal (k + 1) p i j / ((k + 1).factorial : ℝ) := by
  simp [selbergCorrectionJetLocal]

@[simp] theorem selbergCorrectionJetLocal_zero_zero (p : ℕ) :
    selbergCorrectionJetLocal p 0 0 = 1 := by
  ext k
  rcases k with _ | k
  · simp [selbergCorrectionJetLocal, selbergLocalCorrection,
      selbergEulerCorrectionCoeff_one]
  · simp [selbergCorrectionJetLocal, selbergCorrectionLogPowerLocal]

/-- Finite Euler product of the local correction jets. -/
def selbergEulerCorrectionJet (m n : ℕ) : PowerSeries ℝ :=
  if m = 0 ∨ n = 0 then 0 else
    ∏ p ∈ (m * n).primeFactors,
      selbergCorrectionJetLocal p (m.factorization p) (n.factorization p)

@[simp] theorem selbergEulerCorrectionJet_one :
    selbergEulerCorrectionJet 1 1 = 1 := by
  simp [selbergEulerCorrectionJet]

@[simp] theorem selbergEulerCorrectionJet_zero_left (n : ℕ) :
    selbergEulerCorrectionJet 0 n = 0 := by
  simp [selbergEulerCorrectionJet]

@[simp] theorem selbergEulerCorrectionJet_zero_right (m : ℕ) :
    selbergEulerCorrectionJet m 0 = 0 := by
  simp [selbergEulerCorrectionJet]

private theorem correctionJetLocal_factorization_mul_left
    {a b c d p : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : Nat.Coprime (a * b) (c * d)) (hp : p ∈ (a * b).primeFactors) :
    selbergCorrectionJetLocal p ((a * c).factorization p) ((b * d).factorization p) =
      selbergCorrectionJetLocal p (a.factorization p) (b.factorization p) := by
  have hpmem : p ∉ (c * d).primeFactors := by
    exact Finset.disjoint_left.mp h.disjoint_primeFactors hp
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpnd : ¬ p ∣ c * d := by
    intro hdiv
    exact hpmem (Nat.mem_primeFactors.mpr ⟨hprime, hdiv, (Nat.mul_ne_zero hc.ne' hd.ne')⟩)
  have hpc : ¬ p ∣ c := fun hdiv => hpnd (hdiv.mul_right d)
  have hpd : ¬ p ∣ d := fun hdiv => hpnd (hdiv.mul_left c)
  rw [Nat.factorization_mul ha.ne' hc.ne', Nat.factorization_mul hb.ne' hd.ne']
  simp [Nat.factorization_eq_zero_of_not_dvd hpc,
    Nat.factorization_eq_zero_of_not_dvd hpd]

private theorem correctionJetLocal_factorization_mul_right
    {a b c d p : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : Nat.Coprime (a * b) (c * d)) (hp : p ∈ (c * d).primeFactors) :
    selbergCorrectionJetLocal p ((a * c).factorization p) ((b * d).factorization p) =
      selbergCorrectionJetLocal p (c.factorization p) (d.factorization p) := by
  have hpmem : p ∉ (a * b).primeFactors := by
    exact Finset.disjoint_right.mp h.disjoint_primeFactors hp
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpnd : ¬ p ∣ a * b := by
    intro hdiv
    exact hpmem (Nat.mem_primeFactors.mpr ⟨hprime, hdiv, (Nat.mul_ne_zero ha.ne' hb.ne')⟩)
  have hpa : ¬ p ∣ a := fun hdiv => hpnd (hdiv.mul_right b)
  have hpb : ¬ p ∣ b := fun hdiv => hpnd (hdiv.mul_left a)
  rw [Nat.factorization_mul ha.ne' hc.ne', Nat.factorization_mul hb.ne' hd.ne']
  simp [Nat.factorization_eq_zero_of_not_dvd hpa,
    Nat.factorization_eq_zero_of_not_dvd hpb]

/-- The global correction jet is multiplicative over pair-coprime arguments. -/
theorem bivariateMultiplicative_selbergEulerCorrectionJet :
    BivariateMultiplicative selbergEulerCorrectionJet := by
  constructor
  · exact selbergEulerCorrectionJet_one
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · have hcd1 : c * d = 1 := by
        have hc : Nat.Coprime 0 (c * d) := by rw [← hab0]; exact h
        simpa using hc
      have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
      have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by simpa [Nat.mul_comm] using hcd1.symm⟩
      subst c
      subst d
      rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;> simp
    by_cases hcd0 : c * d = 0
    · have hab1 : a * b = 1 := by
        have hc : Nat.Coprime (a * b) 0 := by rw [← hcd0]; exact h
        simpa using hc
      have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
      have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by simpa [Nat.mul_comm] using hab1.symm⟩
      subst a
      subst b
      rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;> simp
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    rw [selbergEulerCorrectionJet, if_neg (not_or_intro
        (Nat.mul_ne_zero ha.ne' hc.ne') (Nat.mul_ne_zero hb.ne' hd.ne')),
      selbergEulerCorrectionJet, if_neg (not_or_intro ha.ne' hb.ne'),
      selbergEulerCorrectionJet, if_neg (not_or_intro hc.ne' hd.ne')]
    have hreassoc : (a * c) * (b * d) = (a * b) * (c * d) := by ring
    rw [hreassoc, Nat.primeFactors_mul hab0 hcd0,
      Finset.prod_union h.disjoint_primeFactors]
    refine congrArg₂ (· * ·) ?_ ?_
    · apply Finset.prod_congr rfl
      intro p hp
      exact correctionJetLocal_factorization_mul_left ha hb hc hd h hp
    · apply Finset.prod_congr rfl
      intro p hp
      exact correctionJetLocal_factorization_mul_right ha hb hc hd h hp

/-- Prime-power values of the global correction jet. -/
theorem selbergEulerCorrectionJet_prime_pow
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergEulerCorrectionJet (p ^ i) (p ^ j) = selbergCorrectionJetLocal p i j := by
  rcases Nat.eq_zero_or_pos (i + j) with hij | hij
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    simp
  · have hpow : (p ^ i) * (p ^ j) = p ^ (i + j) := (pow_add p i j).symm
    rw [selbergEulerCorrectionJet, if_neg (by simp [hp.ne_zero]), hpow,
      Nat.primeFactors_prime_pow hij.ne' hp, Finset.prod_singleton,
      Nat.Prime.factorization_pow hp, Nat.Prime.factorization_pow hp]
    simp

/-- The zeroth coefficient recovers the existing Euler correction. -/
theorem coeff_zero_selbergEulerCorrectionJet (m n : ℕ) :
    PowerSeries.coeff 0 (selbergEulerCorrectionJet m n) =
      selbergEulerCorrectionCoeff m n := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [selbergEulerCorrectionCoeff]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [selbergEulerCorrectionCoeff]
  have hcoeff : BivariateMultiplicative
      (fun a b => PowerSeries.coeff 0 (selbergEulerCorrectionJet a b)) := by
    constructor
    · simp
    · intro a b c d h
      change PowerSeries.coeff 0 (selbergEulerCorrectionJet (a * c) (b * d)) = _
      rw [bivariateMultiplicative_selbergEulerCorrectionJet.map_mul_of_pair_coprime h,
        PowerSeries.coeff_zero_eq_constantCoeff]
      exact map_mul _ _ _
  refine BivariateMultiplicative.eq_of_prime_pow_eq hcoeff
    bivariateMultiplicative_selbergEulerCorrectionCoeff ?_ hm hn
  intro p hp i j
  rw [selbergEulerCorrectionJet_prime_pow hp, coeff_selbergCorrectionJetLocal_zero]
  rfl

end

end RHTower.Sieve
