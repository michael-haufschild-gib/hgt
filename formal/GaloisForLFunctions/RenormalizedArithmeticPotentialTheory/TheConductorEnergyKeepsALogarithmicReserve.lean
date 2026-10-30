import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations
import Mathlib.Data.Nat.Factorization.Induction

/-!
# A logarithmic reserve for completed conductor energies

The divisor formula bounds a Ramanujan coefficient at a positive integer lag independently of
its conductor. Combined with the elementary inequality `m ≤ 2 φ(m)²`, this makes the shell
correction at most one beyond a polynomial conductor cutoff. Below that cutoff, the adjunction
energy is logarithmic in the overlap and the completed Fourier energy is nonnegative.
-/

noncomputable section
open MeasureTheory Finset
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open CompletedShell BezoutValuationIncidence ArithmeticIntersectionTheory
open _root_.RHTower.Sieve

private theorem prime_power_bounds (p k : ℕ) (hp : p.Prime) :
    p ^ (k + 1) ≤ 2 * (p ^ (k + 1)).totient ^ 2 ∧
      (¬2 ∣ p ^ (k + 1) → p ^ (k + 1) ≤ (p ^ (k + 1)).totient ^ 2) := by
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have hp2 := hp.two_le
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have ha : 1 ≤ p ^ k := one_le_pow₀ (by omega)
  have ha2 : p ^ k ≤ (p ^ k) ^ 2 := by
    have h := Nat.mul_le_mul_left (p ^ k) ha
    nlinarith only [h]
  have hg : p ≤ 2 * (p - 1) ^ 2 := by nlinarith only [hp2, hsub]
  constructor
  · calc
      p ^ k * p ≤ p ^ k * (2 * (p - 1) ^ 2) := Nat.mul_le_mul_left _ hg
      _ ≤ (p ^ k) ^ 2 * (2 * (p - 1) ^ 2) := Nat.mul_le_mul_right _ ha2
      _ = _ := by ring
  · intro hodd
    have hp3 : 3 ≤ p := by
      by_contra h
      have : p = 2 := by omega
      subst p
      exact hodd (dvd_mul_left 2 (2 ^ k))
    have hg' : p ≤ (p - 1) ^ 2 := by nlinarith only [hp3, hsub]
    calc
      p ^ k * p ≤ p ^ k * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hg'
      _ ≤ (p ^ k) ^ 2 * (p - 1) ^ 2 := Nat.mul_le_mul_right _ ha2
      _ = _ := by ring

/-- The prime two is the only loss in the square lower bound for Euler's totient. -/
theorem nat_le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  suffices h : ∀ n : ℕ, n ≤ 2 * n.totient ^ 2 ∧
      (¬2 ∣ n → n ≤ n.totient ^ 2) from (h n).1
  apply Nat.recOnPosPrimePosCoprime
  · intro p k hp hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact prime_power_bounds p j hp
  · simp
  · norm_num
  · intro a b _ _ hab ha hb
    rw [Nat.totient_mul hab]
    have hnot : ¬2 ∣ a ∨ ¬2 ∣ b := by
      by_contra h
      push Not at h
      have hd := Nat.dvd_gcd h.1 h.2
      rw [hab] at hd
      norm_num at hd
    constructor
    · rcases hnot with hna | hnb
      · calc
          a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) :=
            Nat.mul_le_mul (ha.2 hna) hb.1
          _ = _ := by ring
      · calc
          a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 :=
            Nat.mul_le_mul ha.1 (hb.2 hnb)
          _ = _ := by ring
    · intro hn
      have hna : ¬2 ∣ a := fun h => hn (dvd_mul_of_dvd_left h b)
      have hnb : ¬2 ∣ b := fun h => hn (dvd_mul_of_dvd_right h a)
      calc
        a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (ha.2 hna) (hb.2 hnb)
        _ = _ := by ring


/-- The common-divisor formula gives a conductor-independent bound at each positive lag. -/
theorem abs_ramanujanLagCoefficient_le_lag_sq (m : ℕ) {h : ℕ} (hh : 0 < h) :
    |ramanujanLagCoefficient m h| ≤ (h : ℝ) ^ 2 := by
  have hsub : (Nat.gcd m h).divisors ⊆ Icc 1 h := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd hh ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right m h))⟩
  rw [ramanujanLagCoefficient_eq_gcd_divisor_sum]
  calc
    _ ≤ ∑ d ∈ (Nat.gcd m h).divisors, |(d : ℝ) * moebiusReal (m / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Nat.gcd m h).divisors, (d : ℝ) := by
      apply sum_le_sum
      intro d _
      have hmu : |moebiusReal (m / d)| ≤ 1 := by
        unfold moebiusReal
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m / d))
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmu (Nat.cast_nonneg d)
    _ ≤ ∑ d ∈ Icc 1 h, (d : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.cast_nonneg d)
    _ ≤ ∑ _d ∈ Icc 1 h, (h : ℝ) :=
      sum_le_sum fun d hd => by exact_mod_cast (mem_Icc.mp hd).2
    _ = _ := by simp [Nat.card_Icc, pow_two]

private theorem abs_shell_integral_le_mass_mul_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {h : ℕ} (hh : 0 < h) (hhc : (h : ℝ) < c) :
    |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ (∫ u, φ u ^ 2) * c := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hr : (h : ℝ) / c < 1 := (div_lt_one hc).mpr hhc
  have hr0 := div_pos hh0 hc
  have hM : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hb : ∀ u ∈ Set.uIoc ((h : ℝ) / c) 1,
      ‖shellAutocorr φ u / u‖ ≤ (∫ u, φ u ^ 2) * c := by
    intro u hu
    rw [Set.uIoc_of_le hr.le] at hu
    have hu0 : 0 < u := hr0.trans hu.1
    have hcu : 1 ≤ c * u := by
      have h := (div_lt_iff₀ hc).mp hu.1
      linarith only [hh1, h]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc
      _ ≤ ∫ v, φ v ^ 2 := abs_shellAutocorr_le hφ hsupp u
      _ ≤ (∫ v, φ v ^ 2) * (c * u) := le_mul_of_one_le_right hM hcu
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr.le)] at hi
  exact hi.trans (mul_le_of_le_one_right (mul_nonneg hM hc.le) (by linarith only [hr0]))

/-- Integer lags and the autocorrelation mass bound make the shell correction small at large
conductors. The fourth power is a coarse bound sufficient for a logarithmic energy cutoff. -/
theorem abs_shellCorrection_le_polynomial_div_totient {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc1 : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    |shellCorrection φ c m| ≤ 2 * c ^ 4 / m.totient := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ c := by
    rw [Nat.card_Ico]
    have hceil1 : 1 ≤ ⌈c⌉₊ := Nat.one_le_ceil_iff.mpr hc
    rw [Nat.cast_sub hceil1, Nat.cast_one]
    have hh := Nat.ceil_lt_add_one hc.le
    linarith only [hh]
  have hsum : |∑ h ∈ Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
      ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ (∫ u, φ u ^ 2) * c ^ 4 := by
    calc
      _ ≤ ∑ h ∈ Ico 1 ⌈c⌉₊, |ramanujanLagCoefficient m h *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ Ico 1 ⌈c⌉₊, c ^ 2 * ((∫ u, φ u ^ 2) * c) := by
        apply sum_le_sum
        intro h hh
        have hh0 : 0 < h := (mem_Ico.mp hh).1
        have hhc : (h : ℝ) < c := Nat.lt_ceil.mp (mem_Ico.mp hh).2
        have hsq : (h : ℝ) ^ 2 ≤ c ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hhc.le 2
        rw [abs_mul]
        exact mul_le_mul ((abs_ramanujanLagCoefficient_le_lag_sq m hh0).trans hsq)
          (abs_shell_integral_le_mass_mul_overlap hφ hsupp hc hh0 hhc)
          (abs_nonneg _) (sq_nonneg _)
      _ = ((Ico 1 ⌈c⌉₊).card : ℝ) * (c ^ 2 * ((∫ u, φ u ^ 2) * c)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ c * (c ^ 2 * ((∫ u, φ u ^ 2) * c)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  rw [shellCorrection, abs_mul, abs_div, abs_mul, abs_of_pos hM, abs_of_pos ht, abs_two]
  calc
    _ ≤ 2 / ((∫ u, φ u ^ 2) * m.totient) * ((∫ u, φ u ^ 2) * c ^ 4) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp


/-- The conductor cutoff is polynomial in the overlap, uniformly in the profile. -/
theorem abs_shellCorrection_le_one_of_large_conductor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc1 : 1 ≤ c) {m : ℕ} (hm : 0 < m)
    (hmc : 8 * c ^ 8 ≤ (m : ℝ)) : |shellCorrection φ c m| ≤ 1 := by
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hnat : (m : ℝ) ≤ 2 * (m.totient : ℝ) ^ 2 := by
    exact_mod_cast nat_le_two_mul_totient_sq m
  have hs : (2 * c ^ 4) ^ 2 ≤ (m.totient : ℝ) ^ 2 := by
    nlinarith only [hnat, hmc]
  have hroot : 2 * c ^ 4 ≤ (m.totient : ℝ) := by
    by_contra h
    have hl := mul_self_lt_mul_self ht.le (lt_of_not_ge h)
    nlinarith only [hl, hs]
  exact (abs_shellCorrection_le_polynomial_div_totient hφ hsupp hM hc1 hm).trans
    ((div_le_one ht).mpr hroot)

private theorem completeWeilSelfFinitePart_eq_sub_log {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) :
    completeWeilSelfFinitePart φ c = completeWeilSelfFinitePart φ 1 - Real.log c := by
  unfold completeWeilSelfFinitePart
  rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc.ne',
    Real.log_div one_ne_zero (by positivity), Real.log_one]
  ring

/-- An explicit logarithmic loss for the complete conductor energy, independent of conductor. -/
def conductorLogarithmicLoss (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  |Real.eulerMascheroniConstant| +
    |completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant| +
      2 * Real.log 8 + 16 * Real.log (2 * c) + 1

/-- The complete Fourier energy retains any subunit fraction of adjunction energy after a
logarithmic overlap loss. The small-conductor case uses positivity; the large-conductor case
uses the integer-lag shell bound. -/
theorem completedConductorEnergy_ge_logarithmic_reserve {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc1 : 1 ≤ c) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ * (ramanujanAdjunctionEnergy m - conductorLogarithmicLoss φ c) ≤
      completedConductorEnergy φ c m := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hE := completedConductorEnergy_nonneg hφ hsupp hM hc hm
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hlogc : Real.log c ≤ Real.log (2 * c) :=
    Real.log_le_log hc (by linarith only [hc])
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  by_cases hlarge : 8 * c ^ 8 ≤ (m : ℝ)
  · have hs := (abs_le.mp
        (abs_shellCorrection_le_one_of_large_conductor hφ hsupp hM hc1 hm hlarge)).2
    have hp : 0 ≤ if m = 1 then completeWeilPoleShift φ c else 0 := by
      split_ifs
      · exact completeWeilPoleShift_nonneg φ hc.le
      · exact le_rfl
    have hraw : ramanujanAdjunctionEnergy m - conductorLogarithmicLoss φ c ≤
        completedConductorEnergy φ c m := by
      rw [completedConductorEnergy_eq_sub_shellCorrection hc hm,
        completeWeilAdjunctionEnergy, completeWeilSelfFinitePart_eq_sub_log hc]
      unfold conductorLogarithmicLoss
      linarith only [hs, hp, hlog0, hlogc, hlog8,
        abs_nonneg Real.eulerMascheroniConstant,
        neg_le_abs (completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant)]
    by_cases hpos : 0 ≤ ramanujanAdjunctionEnergy m - conductorLogarithmicLoss φ c
    · exact (mul_le_of_le_one_left hpos hδ1).trans hraw
    · exact (mul_nonpos_of_nonneg_of_nonpos hδ (le_of_not_ge hpos)).trans hE
  · have hlm : Real.log (m : ℝ) ≤ Real.log 8 + 8 * Real.log c := by
      have h := Real.log_le_log hmR (le_of_lt (lt_of_not_ge hlarge))
      rw [Real.log_mul (by norm_num) (pow_pos hc 8).ne', Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      exact h
    have hsmall : ramanujanAdjunctionEnergy m ≤ conductorLogarithmicLoss φ c := by
      unfold ramanujanAdjunctionEnergy conductorLogarithmicLoss
      linarith only [tameDifferent_le_log hm, hlm, hlogc,
        le_abs_self Real.eulerMascheroniConstant,
        abs_nonneg (completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant)]
    exact (mul_nonpos_of_nonneg_of_nonpos hδ (sub_nonpos.mpr hsmall)).trans hE

#print axioms nat_le_two_mul_totient_sq
#print axioms completedConductorEnergy_ge_logarithmic_reserve

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

