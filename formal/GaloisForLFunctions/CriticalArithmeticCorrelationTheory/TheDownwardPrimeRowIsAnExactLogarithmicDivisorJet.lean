import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPrimeRowsHaveAdjunctionEnergy

/-!
# The finite logarithmic divisor jet of a Ramanujan row

Expanding the actual Ramanujan coefficient before the Mangoldt divisor sum
isolates its leading logarithm. The remaining finite divisor jet supplies
the exact conductor excitation when evaluated at a conductor multiple.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticFunction BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

/-- The finite logarithmic divisor correction, with its exact row support. -/
def ramanujanLogDivisorJet (m n : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, if d ∣ n then
    (ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d else 0

private theorem quotient_dvd_swap {n a d : ℕ} (ha : a ∣ n) (hd0 : 0 < d)
    (h : d ∣ n / a) : a ∣ n / d := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  have he : n = (a * r) * d := by
    calc
      n = (n / a) * a := (Nat.div_mul_cancel ha).symm
      _ = (d * r) * a := by rw [hr]
      _ = (a * r) * d := by ring
  rw [he, Nat.mul_div_cancel _ hd0]

private theorem sum_vonMangoldt_quotient_filter {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (∑ a ∈ n.divisors, if d ∣ n / a then (ArithmeticFunction.vonMangoldt a : ℝ) else 0) =
      if d ∣ n then Real.log (n / d : ℕ) else 0 := by
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, ← sum_filter]
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have hset : n.divisors.filter (fun a => d ∣ n / a) = (n / d).divisors := by
      ext a
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨han, _⟩, hquot⟩
        exact ⟨quotient_dvd_swap han hd hquot, hnd.ne'⟩
      · rintro ⟨ha, _⟩
        have hdiv : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hdn).symm⟩
        have han := ha.trans hdiv
        have ha0 : 0 < a := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨han, hn.ne'⟩)
        exact ⟨⟨han, hn.ne'⟩, quotient_dvd_swap hdn ha0 ha⟩
    rw [hset, vonMangoldt_sum]
  · rw [if_neg hdn]
    refine sum_eq_zero fun a ha => if_neg ?_
    intro h
    have han := Nat.dvd_of_mem_divisors ha
    exact hdn (h.trans ⟨a, (Nat.div_mul_cancel han).symm⟩)

private theorem ramanujan_coefficient_eq_divisor_indicator (m n : ℕ) :
    ramanujanLagCoefficient m n = ∑ d ∈ m.divisors,
      if d ∣ n then (ArithmeticFunction.moebius (m / d) : ℝ) * d else 0 := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d _ => ?_
  change (ArithmeticFunction.moebius (m / d) : ℝ) * (if d ∣ n then (d : ℝ) else 0) = _
  split_ifs <;> simp only [mul_zero]

/-- The literal downward prime convolution has an exact logarithmic leading
term and a finite arithmetic correction. -/
theorem sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ a ∈ n.divisors, (ArithmeticFunction.vonMangoldt a : ℝ) *
      ramanujanLagCoefficient m (n / a)) =
        Real.log n * ramanujanLagCoefficient m n - ramanujanLogDivisorJet m n := by
  simp_rw [ramanujan_coefficient_eq_divisor_indicator, mul_sum]
  rw [sum_comm, ramanujanLogDivisorJet, ← sum_sub_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hd0 := Nat.pos_of_mem_divisors hd
  have he : (∑ a ∈ n.divisors, (ArithmeticFunction.vonMangoldt a : ℝ) *
      (if d ∣ n / a then (ArithmeticFunction.moebius (m / d) : ℝ) * d else 0)) =
      ((ArithmeticFunction.moebius (m / d) : ℝ) * d) *
        ∑ a ∈ n.divisors, if d ∣ n / a then (ArithmeticFunction.vonMangoldt a : ℝ) else 0 := by
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring
  rw [he, sum_vonMangoldt_quotient_filter hn hd0]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hlog : Real.log (n / d : ℕ) + Real.log d = Real.log n := by
      rw [← Real.log_mul (by exact_mod_cast hnd.ne') (by exact_mod_cast hd0.ne'),
        ← Nat.cast_mul, Nat.div_mul_cancel hdn]
    linear_combination ((ArithmeticFunction.moebius (m / d) : ℝ) * d) * hlog
  · simp only [if_neg hdn, mul_zero, sub_zero]

/-- The existing finite downward correction is precisely minus the divisor
jet; the leading logarithm is already cancelled. -/
theorem ramanujanDownCorrection_eq_neg_logDivisorJet (m : ℕ) {n : ℕ} (hn : 0 < n) :
    ramanujanDownCorrection m n = -ramanujanLogDivisorJet m n := by
  have h := sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hn
  unfold ramanujanDownCorrection
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, vonMangoldt_sum]
  have he : (∑ a ∈ n.divisors, ramanujanLagCoefficient m (n / a) *
      (ArithmeticFunction.vonMangoldt a : ℝ)) =
      ∑ a ∈ n.divisors, (ArithmeticFunction.vonMangoldt a : ℝ) *
        ramanujanLagCoefficient m (n / a) := sum_congr rfl fun _ _ => mul_comm _ _
  rw [he, h]
  ring

/-- The logarithmic totient identity is the actual completed prime-row energy
at a conductor multiple, where every upward correction vanishes. -/
theorem sum_moebius_mul_divisor_log_eq_totient_excitation {m : ℕ} (hm : 0 < m) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d) =
      (m.totient : ℝ) * (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) := by
  have hz : ramanujanUpCorrectionTerm m m = fun _ => 0 := by
    funext t
    rw [ramanujanUpCorrectionTerm, ramanujanLagCoefficient_of_dvd (dvd_mul_right m t),
      ramanujanLagCoefficient_of_dvd dvd_rfl, sub_self, zero_mul, zero_div]
  have hs := hasSum_ramanujan_correction m hm m hm
  rw [hz] at hs
  have he := hs.unique hasSum_zero
  rw [ramanujanLagCoefficient_of_dvd dvd_rfl,
    ramanujanDownCorrection_eq_neg_logDivisorJet m hm, sub_neg_eq_add] at he
  have hj : ramanujanLogDivisorJet m m =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d := by
    unfold ramanujanLogDivisorJet
    exact sum_congr rfl fun d hd => if_pos (Nat.dvd_of_mem_divisors hd)
  rw [hj] at he
  linarith only [he]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ramanujanDownCorrection_eq_neg_logDivisorJet
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_moebius_mul_divisor_log_eq_totient_excitation
