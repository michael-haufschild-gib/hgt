import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeConductorMomentsBoundTheGreatestGap
import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeTailExhaustionHasVanishingGreatestGaps
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.MertensThird

/-!
# Explicit decay of the greatest prime-tail gaps

Elementary Mertens bounds control both the counted harmonic density and
the exact conductor energy moment. Their combination gives an inverse
logarithmic cube bound for the actual attained greatest hyperplane gaps.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open RHTower.Sieve

open private primeTailCutoff_prime from
  GaloisForLFunctions.ArithmeticCountingPositivity.PrimeTailExhaustionHasVanishingGreatestGaps

/-- The explicit constant in the prime-tail harmonic-density bound. -/
def primeTailDensityConstant (B : ℕ) : ℝ :=
  Real.exp (2 * (mertensSecondLowerConst + 1 + mertensS B))

private theorem primeTailCutoff_eq (B Q : ℕ) :
    primeTailCutoff B Q = (Nat.primesLE Q).filter (fun p => B < p) := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    obtain ⟨hpQ, hBp⟩ := mem_filter.mp hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hprime⟩, hBp⟩
  · intro hp
    obtain ⟨hpQ, hBp⟩ := mem_filter.mp hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hpQ
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, hBp⟩

private theorem primeTailCutoff_subset (B Q : ℕ) :
    primeTailCutoff B Q ⊆ Nat.primesLE Q := by
  rw [primeTailCutoff_eq]
  exact filter_subset _ _

private theorem prime_shift_correction {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) - 1 / ((p : ℝ) + 1) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hpp : 0 < (p : ℝ) + 1 := by positivity
  calc
    _ = 1 / ((p : ℝ) * ((p : ℝ) + 1)) := by
      field_simp [hp0.ne', hpp.ne']
      ring
    _ ≤ _ := one_div_le_one_div_of_le (mul_pos hp0 hp1)
      (mul_le_mul_of_nonneg_left (by linarith) hp0.le)

private theorem prime_shifted_sum_lower {Q : ℕ} (hQ : 2 ≤ Q) :
    mertensS Q - 1 ≤ ∑ p ∈ Nat.primesLE Q, 1 / ((p : ℝ) + 1) := by
  have hsub : Nat.primesLE Q ⊆ Icc 2 Q := by
    intro p hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hp
    exact mem_Icc.mpr ⟨hprime.two_le, hpQ⟩
  have hbound : (∑ p ∈ Nat.primesLE Q,
      (1 / (p : ℝ) - 1 / ((p : ℝ) + 1))) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE Q, 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
        sum_le_sum fun p hp => prime_shift_correction (Nat.prime_of_mem_primesLE hp)
      _ ≤ ∑ k ∈ Icc 2 Q, 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro k hk _
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith only [hkR]
        positivity
      _ ≤ 1 := sum_inv_mul_pred_le_one (by omega)
  rw [sum_sub_distrib, ← mertensS] at hbound
  linarith only [hbound]

private theorem primeTail_shifted_sum_lower (B : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    Real.log (Real.log (Q : ℝ)) - (mertensSecondLowerConst + 1 + mertensS B) ≤
      ∑ p ∈ primeTailCutoff B Q, 1 / ((p : ℝ) + 1) := by
  let S := (Nat.primesLE Q).filter (fun p => p ≤ B)
  have hsmall : (∑ p ∈ S, 1 / ((p : ℝ) + 1)) ≤ mertensS B := by
    calc
      _ ≤ ∑ p ∈ S, 1 / (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hprime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
        exact one_div_le_one_div_of_le hp0 (by linarith)
      _ ≤ mertensS B := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2,
            Nat.prime_of_mem_primesLE (mem_filter.mp hp).1⟩
        · intro p _ _
          positivity
  have hsplit : (∑ p ∈ Nat.primesLE Q, 1 / ((p : ℝ) + 1)) =
      (∑ p ∈ primeTailCutoff B Q, 1 / ((p : ℝ) + 1)) +
        ∑ p ∈ S, 1 / ((p : ℝ) + 1) := by
    rw [primeTailCutoff_eq]
    dsimp only [S]
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : B < p
    · simp only [if_pos hp, if_neg (show ¬ p ≤ B by omega), add_zero]
    · simp only [if_neg hp, if_pos (show p ≤ B by omega), zero_add]
  have hm := le_mertensS hQ
  change Real.log (Real.log (Q : ℝ)) - mertensSecondLowerConst ≤ mertensS Q at hm
  have hs := prime_shifted_sum_lower hQ
  linarith only [hm, hs, hsplit, hsmall]

private theorem log_prime_density_le {p : ℕ} (hp : p.Prime) :
    Real.log (((p : ℝ) - 1) / ((p : ℝ) + 1)) ≤ -2 / ((p : ℝ) + 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : 0 < (p : ℝ) + 1 := by positivity
  have hc : 0 < ((p : ℝ) - 1) / ((p : ℝ) + 1) := div_pos (sub_pos.mpr hpR) hpp
  calc
    _ ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) - 1 := Real.log_le_sub_one_of_pos hc
    _ = _ := by field_simp [hpp.ne']; ring

/-- Above a fixed prime cutoff, the harmonic density is bounded by an
explicit constant times the inverse square of the logarithm. -/
theorem finiteFlipHarmonicDensity_primeTail_le (B : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    finiteFlipHarmonicDensity (primeTailCutoff B Q) ≤
      primeTailDensityConstant B / (Real.log (Q : ℝ)) ^ 2 := by
  have hF := primeTailCutoff_prime B Q
  have hc := finiteFlipHarmonicDensity_pos hF
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlog : Real.log (finiteFlipHarmonicDensity (primeTailCutoff B Q)) ≤
      2 * (mertensSecondLowerConst + 1 + mertensS B) -
        2 * Real.log (Real.log (Q : ℝ)) := by
    have hsum : Real.log (finiteFlipHarmonicDensity (primeTailCutoff B Q)) ≤
        -2 * ∑ p ∈ primeTailCutoff B Q, 1 / ((p : ℝ) + 1) := by
      rw [finiteFlipHarmonicDensity, Real.log_prod]
      · rw [mul_sum]
        apply sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv, one_mul] using log_prime_density_le (hF p hp)
      · intro p hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
        exact (div_pos (sub_pos.mpr hpR) (by positivity)).ne'
    have hsumLower := primeTail_shifted_sum_lower B hQ
    linarith only [hsum, hsumLower]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hc, Real.exp_sub] at hexp
  have he : Real.exp (2 * Real.log (Real.log (Q : ℝ))) = (Real.log (Q : ℝ)) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hlogQ, ← pow_two]
  rw [he] at hexp
  exact hexp

private theorem prime_energy_moment_le {p : ℕ} (hp : p.Prime) :
    4 * (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤
      (16 / 3 : ℝ) * (Real.log p / (p : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hpR]
  have hpSq : 4 ≤ (p : ℝ) ^ 2 := by nlinarith only [hpR]
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by linarith only [hpSq]
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith only [hpR])
  have hcoef : 4 * (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 16 / (3 * (p : ℝ)) := by
    rw [div_le_div_iff₀ hden (mul_pos (by norm_num) hp0)]
    nlinarith only [hpSq]
  calc
    _ = (4 * (p : ℝ) / ((p : ℝ) ^ 2 - 1)) * Real.log p := by ring
    _ ≤ (16 / (3 * (p : ℝ))) * Real.log p := mul_le_mul_of_nonneg_right hcoef hlog
    _ = _ := by ring

private theorem conductorEnergyMoment_nonneg (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) : 0 ≤ finiteFlipConductorEnergyMoment F := by
  apply sum_nonneg
  intro p hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hF p hp).two_le
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith only [hpR])
  have hden : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith only [hpR]
  positivity

/-- The prime-tail conductor moment grows at most logarithmically, with
the explicit constant from the first elementary Mertens bound. -/
theorem finiteFlipConductorEnergyMoment_primeTail_le (B : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    finiteFlipConductorEnergyMoment (primeTailCutoff B Q) ≤
      (16 / 3 : ℝ) * (Real.log (Q : ℝ) + mertensFirstConst) := by
  have hsum : (∑ p ∈ primeTailCutoff B Q, Real.log p / (p : ℝ)) ≤ mertensA Q := by
    apply sum_le_sum_of_subset_of_nonneg (primeTailCutoff_subset B Q)
    intro p hp _
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    exact div_nonneg (Real.log_nonneg hpR) (Nat.cast_nonneg _)
  have hm : mertensA Q ≤ Real.log (Q : ℝ) + mertensFirstConst := by
    have h := (abs_le.mp (abs_mertensA_sub_log_le hQ)).2
    linarith only [h]
  calc
    _ ≤ ∑ p ∈ primeTailCutoff B Q, (16 / 3 : ℝ) * (Real.log p / (p : ℝ)) :=
      sum_le_sum fun p hp => prime_energy_moment_le (primeTailCutoff_prime B Q p hp)
    _ = (16 / 3 : ℝ) * ∑ p ∈ primeTailCutoff B Q, Real.log p / (p : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ (16 / 3 : ℝ) * (Real.log (Q : ℝ) + mertensFirstConst) :=
      mul_le_mul_of_nonneg_left (hsum.trans hm) (by norm_num)

/-- Every fixed prime tail has an eventual explicit inverse-log-cube upper
bound for its attained greatest hyperplane gap. -/
theorem eventually_primeTailGreatestGap_le_inverse_log_cube (B : ℕ) :
    ∀ᶠ Q : ℕ in atTop, finiteFlipGreatestGap (primeTailCutoff B Q) ≤
      (64 / 3 : ℝ) * primeTailDensityConstant B ^ 2 / (Real.log (Q : ℝ)) ^ 3 := by
  have ht : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop
    (max 1 (max mertensFirstConst (2 * primeTailDensityConstant B))),
    eventually_ge_atTop (2 : ℕ)] with Q hL hQ
  have hL1 : 1 ≤ Real.log (Q : ℝ) := (le_max_left _ _).trans hL
  have hLC : mertensFirstConst ≤ Real.log (Q : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLD : 2 * primeTailDensityConstant B ≤ Real.log (Q : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < Real.log (Q : ℝ) := zero_lt_one.trans_le hL1
  have hLsq : Real.log (Q : ℝ) ≤ (Real.log (Q : ℝ)) ^ 2 := by
    nlinarith only [hL1]
  let F := primeTailCutoff B Q
  let c := finiteFlipHarmonicDensity F
  let M := finiteFlipConductorEnergyMoment F
  have hF : ∀ p ∈ F, p.Prime := primeTailCutoff_prime B Q
  have hcpos : 0 < c := finiteFlipHarmonicDensity_pos hF
  have hcbound : c ≤ primeTailDensityConstant B / (Real.log (Q : ℝ)) ^ 2 :=
    finiteFlipHarmonicDensity_primeTail_le B hQ
  have hcHalf : c ≤ 1 / 2 := by
    apply hcbound.trans
    apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr
    linarith only [hLsq, hLD]
  have hne : F.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hc : c = 1 := by simp only [c, he, finiteFlipHarmonicDensity, prod_empty]
    rw [hc] at hcHalf
    norm_num at hcHalf
  have hcSq : c ^ 2 ≤ 1 / 4 := by nlinarith only [hcpos, hcHalf]
  have hden : 0 < 1 - c ^ 2 := by linarith only [hcSq]
  have hratio : c ^ 2 / (1 - c ^ 2) ≤ 2 * c ^ 2 := by
    rw [div_le_iff₀ hden]
    have hx : 0 ≤ 1 - 2 * c ^ 2 := by linarith only [hcSq]
    nlinarith only [mul_nonneg (sq_nonneg c) hx]
  have hM0 : 0 ≤ M := conductorEnergyMoment_nonneg F hF
  have hM : M ≤ (32 / 3 : ℝ) * Real.log (Q : ℝ) := by
    have hm := finiteFlipConductorEnergyMoment_primeTail_le B (show 1 ≤ Q by omega)
    change M ≤ _ at hm
    linarith only [hm, hLC]
  have hDpos : 0 < primeTailDensityConstant B := Real.exp_pos _
  have hcSqBound : c ^ 2 ≤ (primeTailDensityConstant B / (Real.log (Q : ℝ)) ^ 2) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hcbound hcbound hcpos.le
      (div_nonneg hDpos.le (sq_nonneg _))
  calc
    finiteFlipGreatestGap F ≤ c ^ 2 / (1 - c ^ 2) * M :=
      finiteFlipGreatestGap_le_energyMoment F hF hne
    _ ≤ 2 * c ^ 2 * M := mul_le_mul_of_nonneg_right hratio hM0
    _ ≤ 2 * (primeTailDensityConstant B / (Real.log (Q : ℝ)) ^ 2) ^ 2 * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcSqBound (by norm_num)) hM0
    _ ≤ 2 * (primeTailDensityConstant B / (Real.log (Q : ℝ)) ^ 2) ^ 2 *
        ((32 / 3 : ℝ) * Real.log (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by field_simp [hLpos.ne']; ring

end GaloisForLFunctions.ArithmeticCountingPositivity
