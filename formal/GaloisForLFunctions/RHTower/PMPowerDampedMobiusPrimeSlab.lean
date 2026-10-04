import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeGrowth
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusGramDiagonal

/-!
# The first band beyond a finite prime aperture

Below twice the aperture threshold, every omitted coefficient is a prime
coefficient. The finite-prime Fermi source is therefore the literal full source
plus a positive weighted prime sum on this band. The identity retains the
physical cutoff and the original Möbius coefficients.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- In the first band, failure of prime coverage means that the integer itself
is a prime beyond the aperture. -/
theorem pm_primeFactors_aperture_first_band {P d : ℕ} (hP : 1 ≤ P)
    (hd : d < 2 * P) :
    ¬d.primeFactors ⊆ mobiusFinitePrimeAperture (P - 1) ↔ d.Prime ∧ P ≤ d := by
  constructor
  · intro h
    obtain ⟨q, hq, hqS⟩ := Finset.not_subset.mp h
    obtain ⟨hqprime, hqd, hd0⟩ := Nat.mem_primeFactors.mp hq
    have hPq : P ≤ q := by
      simp only [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range] at hqS
      by_contra h
      exact hqS ⟨by omega, hqprime⟩
    obtain ⟨k, hdk⟩ := hqd
    have hk : k = 1 := by
      have hk0 : k ≠ 0 := by intro h; simp [h] at hdk; exact hd0 hdk
      have hlt : q * k < 2 * q := by omega
      have hklt : k < 2 := by nlinarith [hqprime.pos]
      omega
    have hdq : d = q := by simpa [hk] using hdk
    simpa [hdq] using And.intro hqprime hPq
  · rintro ⟨hdprime, hPd⟩ hcover
    have hmem := hcover hdprime.mem_primeFactors_self
    simp only [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range] at hmem
    omega

/-- Exact coefficient correction on the first band of the canonical aperture. -/
theorem pm_finitePrime_coefficient_first_band {P d : ℕ} (hP : 1 ≤ P)
    (hd : d < 2 * P) :
    finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture (P - 1)) d =
      mobiusComplexCoefficient d + if d.Prime ∧ P ≤ d then 1 else 0 := by
  by_cases h : d.Prime ∧ P ≤ d
  · have hc := (pm_primeFactors_aperture_first_band hP hd).mpr h
    rw [finitePrimeApertureMobiusCoefficient, if_neg hc, if_pos h,
      mobiusComplexCoefficient, moebius_apply_prime h.1]
    norm_num
  · have hc : d.primeFactors ⊆ mobiusFinitePrimeAperture (P - 1) := by
      by_contra hn
      exact h ((pm_primeFactors_aperture_first_band hP hd).mp hn)
    simp [finitePrimeApertureMobiusCoefficient, hc, h]

/-- A finite prime source can be summed up to any horizon covering its physical
support, independently of the product of its primes. -/
theorem pmFinitePrimePowerDampedFermiSource_eq_sum {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmFinitePrimePowerDampedFermiSource S ε t =
      -(∑ d ∈ Finset.Icc 1 N, finitePrimeApertureMobiusCoefficient S d *
        (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t) := by
  let M := ∏ p ∈ S, p
  let f : ℕ → ℂ := fun d => finitePrimeApertureMobiusCoefficient S d *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t
  have hleft : (∑ d ∈ Finset.Icc 1 M, f d) = ∑ d ∈ Finset.Icc 1 (max M N), f d := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _))
    intro d hd hn
    have hdM : M < d := by
      have := (Finset.mem_Icc.mp hd).1
      simp only [Finset.mem_Icc, not_and] at hn
      exact lt_of_not_ge (hn this)
    simp only [f, pm_finitePrime_coefficient_eq_zero_above_product hS hdM,
      zero_mul]
  have hright : (∑ d ∈ Finset.Icc 1 N, f d) = ∑ d ∈ Finset.Icc 1 (max M N), f d := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_right _ _))
    intro d hd hn
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdN : N < d := by
      simp only [Finset.mem_Icc, not_and] at hn
      exact lt_of_not_ge (hn hd1)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdt : 1 / t < (d : ℝ) :=
      (Nat.lt_floor_add_one (1 / t)).trans_le (by exact_mod_cast (by omega : ⌊1/t⌋₊+1 ≤ d))
    have hinv : 1 / (d : ℝ) < t := by
      apply (div_lt_iff₀ hd0).mpr
      have h := (div_lt_iff₀ ht).mp hdt
      nlinarith
    simp only [f, fermiNymanGen_eq_zero_of_inv_lt hd0 hinv, mul_zero]
  exact congrArg Neg.neg (hleft.trans hright.symm)

/-- The weighted missing-prime mass at reciprocal physical position `x`. -/
def pmPrimeSlabMass (ε : ℝ) (P : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc P ⌊x⌋₊).filter Nat.Prime, (q : ℝ) ^ (-ε)

theorem pmPrimeSlabMass_nonneg (ε : ℝ) (P : ℕ) (x : ℝ) :
    0 ≤ pmPrimeSlabMass ε P x := by
  exact Finset.sum_nonneg fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _

/-- The canonical prime core equals the full source plus the positive missing
prime mass throughout its first physical band. -/
theorem pmFinitePrimePowerDampedFermiSource_first_band (ε : ℝ) {P : ℕ}
    (hP : 1 ≤ P) {t : ℝ} (ht : 0 < t) (hband : 1 / t < 2 * (P : ℝ)) :
    pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P - 1)) ε t =
      pmPowerDampedFermiSource ε t + (pmPrimeSlabMass ε P (1 / t) : ℂ) := by
  classical
  let N := ⌊1 / t⌋₊
  have hN : N < 2 * P := by
    have hle := Nat.floor_le (show 0 ≤ 1 / t by positivity)
    dsimp only [N]
    exact_mod_cast hle.trans_lt hband
  have hS : ∀ q ∈ mobiusFinitePrimeAperture (P - 1), q.Prime :=
    fun _ hq => (Finset.mem_filter.mp hq).2
  rw [pmFinitePrimePowerDampedFermiSource_eq_sum hS ε ht (le_refl N),
    pmPowerDampedFermiSource]
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture (P - 1)) d *
        (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t =
      ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t -
        if d.Prime ∧ P ≤ d then (((d : ℝ) ^ (-ε) : ℝ) : ℂ) else 0 := by
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    rw [pm_finitePrime_coefficient_first_band hP (hdN.trans_lt hN)]
    by_cases hp : d.Prime ∧ P ≤ d
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hPd : (P : ℝ) ≤ d := by exact_mod_cast hp.2
      have hNd : (d : ℝ) ≤ 1 / t :=
        (show (d : ℝ) ≤ N by exact_mod_cast hdN).trans (Nat.floor_le (by positivity))
      have hh : 1 / 2 < (d : ℝ) * t := by
        have hb := (div_lt_iff₀ ht).mp hband
        have := mul_le_mul_of_nonneg_right hPd ht.le
        nlinarith
      have hl : (d : ℝ) * t ≤ 1 := (le_div_iff₀ ht).mp hNd
      rw [pm_fermiNymanGen_first_band hd0 ht hh hl]
      rw [if_pos hp, if_pos hp]
      simp only [mobiusComplexCoefficient, Complex.ofReal_mul,
        Complex.ofReal_intCast]
      ring
    · simp [hp, mobiusComplexCoefficient]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hfilter : (Finset.Icc 1 N).filter (fun d => d.Prime ∧ P ≤ d) =
      (Finset.Icc P N).filter Nat.Prime := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hdN⟩, hp, hPd⟩
      exact ⟨⟨hPd, hdN⟩, hp⟩
    · rintro ⟨⟨hPd, hdN⟩, hp⟩
      exact ⟨⟨hP.trans hPd, hdN⟩, hp, hPd⟩
  rw [← Finset.sum_filter, hfilter]
  simp only [pmPrimeSlabMass, Complex.ofReal_sum, N]
  ring

end RHTower
