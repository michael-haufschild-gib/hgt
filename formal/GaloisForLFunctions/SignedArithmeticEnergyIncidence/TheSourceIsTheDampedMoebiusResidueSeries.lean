import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ResidueModesAndBackwardContinuation

/-!
# The source is the damped Möbius residue series

In residue coordinates the chain orbit of the reciprocal is an absolutely convergent series
(`centeredOperator_reciprocal_eq_tsum`):

`(C_η r)(n) = Σ_{d ≥ 1} μ(d) d^{−η} v_d(n)`,   `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d`.

The receiver is the `ℓ²` energy of this series; the whole question of admission is how the signs
`μ(d)` cancel against the residue-mode Gram.

* **Sign-blind admission** (`orbit_partial_energy_le`, `admits_of_signBlind`): the triangle
  inequality in `ℓ²` bounds every horizon by `(Σ_d d^{−η} ‖v_d‖_{ℓ²})²`, finite exactly for
  `η > 1/2` (`summable_signBlind_iff`).  This reproves the unconditional endpoint of the damped
  Möbius energy through residue coordinates alone.
* **The positive twin** (`not_summable_positiveTwin`): replacing every `μ(d)` by `1` gives the
  series `Σ_d d^{−ε} v_d`, whose terms all have one sign; its receiver energy diverges for every
  `0 < ε ≤ 1/2`, because its tail `Σ_{d > n+1} d^{−1−ε}` is of size `(n+1)^{−ε}`.  Below half
  damping no argument insensitive to the signs of `μ` can admit the source.
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open ArithmeticFunction

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The `d`-th term `μ(d) d^{−η} v_d(n)` of the residue series. -/
def residueTerm (η : ℝ) (d n : ℕ) : ℝ :=
  ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * normalizedResidueProfile d n

theorem normalizedResidueProfile_nonpos (d n : ℕ) : normalizedResidueProfile d n ≤ 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have he : (((n + 1) % d : ℕ) : ℝ) + (d : ℝ) * ((n + 1) / d : ℕ) = (n + 1 : ℕ) := by
    exact_mod_cast Nat.mod_add_div (n + 1) d
  have hform : normalizedResidueProfile d n =
      -(((n + 1) % d : ℕ) : ℝ) / ((d : ℝ) * (n + 1 : ℕ)) := by
    unfold normalizedResidueProfile
    field_simp
    nlinarith
  rw [hform]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

/-- `|d^{−η} v_d(n)| ≤ d^{−1−η}`. -/
theorem abs_rpow_mul_normalizedResidueProfile_le {η : ℝ} {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |(d : ℝ) ^ (-η) * normalizedResidueProfile d n| ≤ (d : ℝ) ^ (-1 - η) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) ^ (-η))]
  have h := abs_normalizedResidueProfile_le_inv_d hd n
  calc (d : ℝ) ^ (-η) * |normalizedResidueProfile d n| ≤ (d : ℝ) ^ (-η) * (1 / d) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (d : ℝ) ^ (-1 - η) := by
        rw [show (-1 - η) = -η + (-1) by ring, Real.rpow_add hd', Real.rpow_neg_one]
        ring

theorem summable_rpow_mul_normalizedResidueProfile {η : ℝ} (hη : 0 < η) (n : ℕ) :
    Summable fun d : ℕ => (d : ℝ) ^ (-η) * normalizedResidueProfile d n := by
  have hmaj : Summable fun d : ℕ => (d : ℝ) ^ (-1 - η) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded hmaj fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [Real.norm_eq_abs]
  exact abs_rpow_mul_normalizedResidueProfile_le hd n

theorem summable_residueTerm {η : ℝ} (hη : 0 < η) (n : ℕ) :
    Summable fun d : ℕ => residueTerm η d n := by
  refine Summable.of_norm_bounded ((summable_rpow_mul_normalizedResidueProfile hη n).abs)
    fun d => ?_
  rw [Real.norm_eq_abs, residueTerm, mul_assoc, abs_mul]
  have : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  calc |((moebius d : ℤ) : ℝ)| * |(d : ℝ) ^ (-η) * normalizedResidueProfile d n|
      ≤ 1 * |(d : ℝ) ^ (-η) * normalizedResidueProfile d n| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = _ := one_mul _

/-- **The source is the damped Möbius residue series.** -/
theorem centeredOperator_reciprocal_eq_tsum {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη reciprocalObservable n = ∑' d : ℕ, residueTerm η d n := by
  rw [centeredOperator_reciprocal_apply]
  set x : ℝ := ((n + 1 : ℕ) : ℝ) with hx
  have hxpos : 0 < x := by positivity
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re with hρ
  -- the complex identities: prefix average and density as Dirichlet series
  have h1 := RHTower.pmPowerDampedDivisorSum_div_eq_tsum η hxpos
  have h2 := RHTower.pmPowerDampedDivisorDensity_eq_tsum hη
  have hS1 : Summable fun d : ℕ => RHTower.pmPowerDampedMobiusCoeff η d *
      ((((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := range (n + 2)) fun d hd => ?_
    have hdlt : n + 1 < d := by simp at hd; omega
    have : ⌊x / (d : ℝ)⌋₊ = 0 := by
      rw [hx, Nat.floor_div_eq_div, Nat.div_eq_of_lt hdlt]
    simp [this]
  have hS2 := RHTower.summable_pmPowerDampedDivisorDensity_terms hη
  have hdiff := (hS1.tsum_sub hS2).symm
  rw [← h1, ← h2] at hdiff
  -- each term is real
  have hterm : ∀ d : ℕ, RHTower.pmPowerDampedMobiusCoeff η d *
      ((((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x : ℝ) : ℂ) - RHTower.pmPowerDampedMobiusCoeff η d / (d : ℂ) =
      ((residueTerm η d n : ℝ) : ℂ) := by
    intro d
    have hfl : ⌊x / (d : ℝ)⌋₊ = (n + 1) / d := by rw [hx, Nat.floor_div_eq_div]
    simp only [RHTower.pmPowerDampedMobiusCoeff, residueTerm, normalizedResidueProfile, hfl, hx]
    push_cast
    ring
  simp only [hterm] at hdiff
  rw [← Complex.ofReal_tsum, RHTower.pmPowerDampedDivisorDensity_eq_ofReal_re hη, ← hρ,
    ← Complex.ofReal_div, ← Complex.ofReal_sub] at hdiff
  have hreal := Complex.ofReal_injective hdiff
  rw [← hreal, RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
  have hsum : RHTower.pmPowerDampedDivisorSum η x =
      ∑ j ∈ Icc 1 (n + 1), RHTower.pmPowerDampedDivisorCoeff η j := by
    simp only [RHTower.pmPowerDampedDivisorSum, hx, Nat.floor_natCast]
  rw [hsum, hx]
  push_cast
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-! ### Sign-blind admission -/

/-- **Sign-blind bound at every horizon**: `Σ_{m<T} (C_η r)(m)² ≤ (Σ_d d^{−η} ‖v_d‖_{ℓ²})²`. -/
theorem orbit_partial_energy_le {η : ℝ} (hη : 0 < η)
    (hs : Summable fun d : ℕ => (d : ℝ) ^ (-η) *
      Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) (T : ℕ) :
    ∑ m ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 ≤
      (∑' d : ℕ, (d : ℝ) ^ (-η) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) ^ 2 := by
  set u := fun m => arithmeticDampingCenteredOperator hη reciprocalObservable m with hu
  set S := ∑ m ∈ range T, u m ^ 2 with hS
  set B := ∑' d : ℕ, (d : ℝ) ^ (-η) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)
  have hS0 : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  -- `S = Σ_d Σ_m u_m · term_d(m) ≤ Σ_d √S · d^{−η} ‖v_d‖ = √S · B`
  have hexp : S = ∑' d : ℕ, ∑ m ∈ range T, u m * residueTerm η d m := by
    rw [← Summable.tsum_finsetSum fun m _ => (summable_residueTerm hη m).mul_left (u m)]
    simp only [tsum_mul_left]
    refine sum_congr rfl fun m _ => ?_
    rw [sq, hu, centeredOperator_reciprocal_eq_tsum]
  have hbound : ∀ d : ℕ, ∑ m ∈ range T, u m * residueTerm η d m ≤
      Real.sqrt S * ((d : ℝ) ^ (-η) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) := by
    intro d
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (range T) u (fun m => residueTerm η d m)
    have hterm : ∑ m ∈ range T, residueTerm η d m ^ 2 ≤
        ((d : ℝ) ^ (-η)) ^ 2 * ∑' n, normalizedResidueProfile d n ^ 2 := by
      have hle : ∑ m ∈ range T, normalizedResidueProfile d m ^ 2 ≤
          ∑' n, normalizedResidueProfile d n ^ 2 :=
        (summable_sq_normalizedResidueProfile d).sum_le_tsum _ fun n _ => sq_nonneg _
      have hμ : ∀ m, residueTerm η d m ^ 2 ≤ ((d : ℝ) ^ (-η)) ^ 2 * normalizedResidueProfile d m ^ 2 := by
        intro m
        have : ((moebius d : ℤ) : ℝ) ^ 2 ≤ 1 := by
          have h1 : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
          nlinarith [abs_nonneg ((moebius d : ℤ) : ℝ), sq_abs ((moebius d : ℤ) : ℝ)]
        simp only [residueTerm, mul_pow]
        have h0 : 0 ≤ ((d : ℝ) ^ (-η)) ^ 2 * normalizedResidueProfile d m ^ 2 := by positivity
        nlinarith
      calc _ ≤ ∑ m ∈ range T, ((d : ℝ) ^ (-η)) ^ 2 * normalizedResidueProfile d m ^ 2 :=
            sum_le_sum fun m _ => hμ m
        _ = ((d : ℝ) ^ (-η)) ^ 2 * ∑ m ∈ range T, normalizedResidueProfile d m ^ 2 := by
            rw [mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)
    have hsq : Real.sqrt (∑ m ∈ range T, residueTerm η d m ^ 2) ≤
        (d : ℝ) ^ (-η) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2) := by
      calc _ ≤ Real.sqrt (((d : ℝ) ^ (-η)) ^ 2 * ∑' n, normalizedResidueProfile d n ^ 2) :=
            Real.sqrt_le_sqrt hterm
        _ = _ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc _ ≤ Real.sqrt (∑ m ∈ range T, u m ^ 2) *
          Real.sqrt (∑ m ∈ range T, residueTerm η d m ^ 2) := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
  have hsumm : Summable fun d : ℕ => ∑ m ∈ range T, u m * residueTerm η d m :=
    summable_sum fun m _ => (summable_residueTerm hη m).mul_left (u m)
  have hSB : S ≤ Real.sqrt S * B := by
    rw [hexp]
    calc _ ≤ ∑' d : ℕ, Real.sqrt S * ((d : ℝ) ^ (-η) *
          Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) :=
          hsumm.tsum_le_tsum hbound (hs.mul_left _)
      _ = _ := by rw [tsum_mul_left]
  have hsqS := Real.sq_sqrt hS0
  have hroot : Real.sqrt S ≤ B := by
    rcases (Real.sqrt_nonneg S).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact tsum_nonneg fun d => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · nlinarith
  calc S = Real.sqrt S ^ 2 := hsqS.symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2

/-- **Sign-blind admission above half damping**, through residue coordinates alone. -/
theorem admits_of_signBlind {η : ℝ} (hη : 1 / 2 < η) :
    Admits dampedMobiusEnergy η := by
  have hη0 : 0 < η := by linarith
  have hs := (summable_signBlind_iff η).mpr hη
  exact (admits_iff_summable_orbit hη0).mpr
    (summable_of_sum_range_le (fun m => sq_nonneg _) (orbit_partial_energy_le hη0 hs))

/-! ### The positive twin -/

/-- The positive twin: the residue series with every Möbius sign replaced by `+1`. -/
def positiveTwin (ε : ℝ) (n : ℕ) : ℝ := ∑' d : ℕ, (d : ℝ) ^ (-ε) * normalizedResidueProfile d n

/-- The twin is at most `−2^{−1−ε} (n+1)^{−ε}`: its terms all have one sign and the moduli
`d ∈ (n+1, 2n+2]` contribute `−d^{−1−ε}` each. -/
theorem positiveTwin_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    positiveTwin ε n ≤ -((n : ℝ) + 1) * ((2 : ℝ) * ((n : ℝ) + 1)) ^ (-1 - ε) := by
  set s := Finset.Ioc (n + 1) (2 * n + 2) with hs
  have hsum := summable_rpow_mul_normalizedResidueProfile hε n
  have hle : positiveTwin ε n ≤ ∑ d ∈ s, (d : ℝ) ^ (-ε) * normalizedResidueProfile d n := by
    unfold positiveTwin
    rw [← sum_add_tsum_compl (s := s) hsum]
    have : ∑' d : ↥(sᶜ : Set ℕ), (d : ℝ) ^ (-ε) * normalizedResidueProfile d n ≤ 0 :=
      tsum_nonpos fun d => mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (normalizedResidueProfile_nonpos _ _)
    linarith
  have hterm : ∀ d ∈ s, (d : ℝ) ^ (-ε) * normalizedResidueProfile d n ≤
      -((2 : ℝ) * ((n : ℝ) + 1)) ^ (-1 - ε) := by
    intro d hd
    have hd1 : n + 1 < d := (mem_Ioc.mp hd).1
    have hd2 : d ≤ 2 * n + 2 := (mem_Ioc.mp hd).2
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [normalizedResidueProfile_of_lt hd1]
    have e : (d : ℝ) ^ (-ε) * (-1 / (d : ℝ)) = -(d : ℝ) ^ (-1 - ε) := by
      rw [show (-1 - ε) = -ε + (-1) by ring, Real.rpow_add hdpos, Real.rpow_neg_one]
      ring
    rw [e, neg_le_neg_iff]
    apply Real.rpow_le_rpow_of_nonpos hdpos _ (by linarith)
    have : (d : ℝ) ≤ 2 * n + 2 := by exact_mod_cast hd2
    linarith
  have hcard : (s.card : ℝ) = (n : ℝ) + 1 := by
    rw [hs, Nat.card_Ioc]
    push_cast [show n + 1 ≤ 2 * n + 2 by omega]
    ring
  calc positiveTwin ε n ≤ _ := hle
    _ ≤ ∑ _d ∈ s, -((2 : ℝ) * ((n : ℝ) + 1)) ^ (-1 - ε) := sum_le_sum hterm
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]; ring

/-- **The positive twin is not admitted below half damping.** -/
theorem not_summable_positiveTwin {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ¬ Summable fun n => positiveTwin ε n ^ 2 := by
  intro hsum
  -- `twin(n)² ≥ 4^{−1−ε} (n+1)^{−2ε}`, and `Σ (n+1)^{−2ε}` diverges
  have hlow : ∀ n : ℕ, (2 : ℝ) ^ (-2 - 2 * ε) * ((n + 1 : ℕ) : ℝ) ^ (-(2 * ε)) ≤
      positiveTwin ε n ^ 2 := by
    intro n
    have h := positiveTwin_le hε n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set a := ((n : ℝ) + 1) * ((2 : ℝ) * ((n : ℝ) + 1)) ^ (-1 - ε) with ha
    have ha0 : 0 ≤ a := by positivity
    have hsq : a ^ 2 ≤ positiveTwin ε n ^ 2 := by nlinarith
    refine le_trans (le_of_eq ?_) hsq
    rw [ha, mul_pow, Real.mul_rpow (by norm_num) hn.le]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity)]
    have e1 : ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) = ((n : ℝ) + 1) ^ (2 : ℝ) := by norm_num
    rw [e1, show ((-1 - ε) * ((2 : ℕ) : ℝ)) = -2 - 2 * ε by push_cast; ring,
      mul_comm ((2 : ℝ) ^ (-2 - 2 * ε)), mul_assoc, ← Real.rpow_add hn]
    ring_nf
  have hdiv : ¬ Summable fun n : ℕ => (2 : ℝ) ^ (-2 - 2 * ε) * ((n + 1 : ℕ) : ℝ) ^ (-(2 * ε)) := by
    intro h
    have h1 := h.mul_left ((2 : ℝ) ^ (-2 - 2 * ε))⁻¹
    have h2 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(2 * ε)) := by
      refine h1.congr fun n => ?_
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    have h3 := (summable_nat_add_iff 1).mp h2
    have := Real.summable_nat_rpow.mp h3
    linarith
  exact hdiv (Summable.of_nonneg_of_le (fun n => by positivity) hlow hsum)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
