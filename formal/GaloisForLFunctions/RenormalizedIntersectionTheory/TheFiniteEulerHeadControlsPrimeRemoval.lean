import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughMeanAtAFixedScale
import GaloisForLFunctions.RHTower.Sieve.MertensThird

/-!
# Uniform control of the finite Euler head

Removing primes below `Q` at the real argument `1 + 1/u` costs the untilted
Euler head times a bounded factor when `log Q ≤ u`. The ordinary Mertens
product then supplies the factor `1/log Q`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

private theorem damped_euler_factor_bounds {w x t : ℝ} (hw : |w| ≤ 1)
    (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) (ht : 0 ≤ t) :
    0 < 1 - w * x * Real.exp (-t) ∧
      1 - w * x * Real.exp (-t) ≤ (1 - w * x) * Real.exp (2 * x * t) := by
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
  have hwx := mul_le_mul_of_nonneg_right (abs_le.mp hw).2 hx
  have hD : 1 / 2 ≤ 1 - w * x := by nlinarith only [hwx, hx2]
  have hwxe := mul_le_mul_of_nonneg_right hwx he0
  have hxe := mul_le_mul_of_nonneg_left he1 hx
  constructor
  · nlinarith only [hwxe, hxe, hx2]
  have hd0 : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr he1
  have hdt : 1 - Real.exp (-t) ≤ t := by
    have h := Real.add_one_le_exp (-t)
    linarith only [h]
  have hwdelta := mul_le_mul_of_nonneg_right (abs_le.mp hw).2 (mul_nonneg hx hd0)
  have hxdelta := mul_le_mul_of_nonneg_left hdt hx
  have hfirst : 1 - w * x * Real.exp (-t) ≤ (1 - w * x) + x * t := by
    nlinarith only [hwdelta, hxdelta]
  have hDxt := mul_le_mul_of_nonneg_right hD (mul_nonneg hx ht)
  have hsecond : (1 - w * x) + x * t ≤ (1 - w * x) * (1 + 2 * x * t) := by
    nlinarith only [hDxt]
  have hthird := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * x * t))
    (show 0 ≤ 1 - w * x by linarith only [hD])
  exact hfirst.trans (hsecond.trans (by simpa only [add_comm] using hthird))

/-- The finite factor multiplying a Dirichlet series when all primes below `Q`
are removed at the argument `1 + 1/u`. -/
def tiltedPrimeRemovalFactor (ω : ℕ → ℝ) (Q : ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + 1 / u)))

private theorem tilted_prime_factor_bounds {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u) :
    0 < 1 - ω p * (p : ℝ) ^ (-(1 + 1 / u)) ∧
      1 - ω p * (p : ℝ) ^ (-(1 + 1 / u)) ≤
        (1 - ω p / p) * Real.exp ((2 / u) * (Real.log p / p)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hpow : (p : ℝ) ^ (-(1 + 1 / u)) = (1 / p) * Real.exp (-(Real.log p / u)) := by
    rw [show -(1 + 1 / u) = -1 + -(1 / u) by ring,
      Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0,
      show Real.log p * -(1 / u) = -(Real.log p / u) by ring, one_div]
  have h := damped_euler_factor_bounds (hbd p) (by positivity : (0 : ℝ) ≤ 1 / p)
    (one_div_le_one_div_of_le (by norm_num) hp2)
    (div_nonneg (Real.log_natCast_nonneg p) hu.le)
  rw [show 2 * (1 / (p : ℝ)) * (Real.log p / u) = (2 / u) * (Real.log p / p) by ring] at h
  rw [hpow]
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

/-- Every finite prime-removal factor is positive to the right of one. -/
theorem tiltedPrimeRemovalFactor_pos {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    (Q : ℕ) {u : ℝ} (hu : 0 < u) : 0 < tiltedPrimeRemovalFactor ω Q u := by
  change 0 < ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + 1 / u)))
  exact prod_pos fun p hp => (tilted_prime_factor_bounds hbd (Nat.mem_primesBelow.mp hp).2 hu).1

private theorem primeHead_tilt_le {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    (Q : ℕ) {u : ℝ} (hu : 0 < u) :
    tiltedPrimeRemovalFactor ω Q u ≤
      (∏ p ∈ Nat.primesBelow Q, (1 - ω p / p)) *
        Real.exp ((2 / u) * ∑ p ∈ Nat.primesBelow Q, Real.log p / p) := by
  calc
    _ ≤ ∏ p ∈ Nat.primesBelow Q,
        ((1 - ω p / p) * Real.exp ((2 / u) * (Real.log p / p))) :=
      prod_le_prod (fun p hp => (tilted_prime_factor_bounds hbd (Nat.mem_primesBelow.mp hp).2 hu).1.le)
        (fun p hp => (tilted_prime_factor_bounds hbd (Nat.mem_primesBelow.mp hp).2 hu).2)
    _ = _ := by rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum]

private theorem ordinaryPrimeHead_le {Q : ℕ} (hQ : 3 ≤ Q) :
    (∏ p ∈ Nat.primesBelow Q, (1 - 1 / (p : ℝ))) ≤
      2 * RHTower.Sieve.mertensThirdUpperConst / Real.log Q := by
  let N := Q - 1
  have hN : 2 ≤ N := by dsimp only [N]; omega
  have hNsucc : N + 1 = Q := by dsimp only [N]; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hNcast : (N : ℝ) = (Q : ℝ) - 1 := by
    change ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1
    simpa only [Nat.cast_one] using
      (Nat.cast_sub (R := ℝ) (m := 1) (n := Q) (show 1 ≤ Q by omega))
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith only [hNr])
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQsq : (Q : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith only [hNcast, hNr, sq_nonneg ((N : ℝ) - 2)]
  have hlog : Real.log Q ≤ 2 * Real.log N := by
    have h := Real.log_le_log hQ0 hQsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hsets : Nat.primesBelow Q = Nat.primesLE N := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpQ, hpp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesLE.mpr ⟨by omega, hpp⟩
    · intro hp
      obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  rw [hsets]
  have h := RHTower.Sieve.prod_one_sub_inv_le hN
  simp only [one_div] at ⊢
  refine h.trans ?_
  rw [div_le_div_iff₀ hlogN hlogQ]
  nlinarith only [mul_le_mul_of_nonneg_left hlog RHTower.Sieve.mertensThirdUpperConst_pos.le]

/-- A universal constant bounds every finite removal head by its reciprocal Euler
density and `1/log Q`, throughout `3 ≤ Q ≤ exp u`, `u ≥ 1`. -/
theorem exists_uniform_tiltedPrimeRemovalFactor_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : ℕ → ℝ), (∀ n, |ω n| ≤ 1) → ∀ Q : ℕ,
      3 ≤ Q → ∀ u : ℝ, 1 ≤ u → Real.log Q ≤ u →
        tiltedPrimeRemovalFactor ω Q u ≤ C / (Real.log Q * flipDensityBelow ω Q) := by
  let D := |(Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)|
  let E := Real.exp (2 + 2 * D)
  let C := 2 * RHTower.Sieve.mertensThirdUpperConst * E
  have hD : 0 ≤ D := abs_nonneg _
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := mul_pos (mul_pos two_pos RHTower.Sieve.mertensThirdUpperConst_pos) hE
  refine ⟨C, hC, fun ω hbd Q hQ u hu1 hQu => ?_⟩
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hδ : 0 < flipDensityBelow ω Q := (flipDensityBelow_pos_le_one hbd Q).1
  have hsum : (∑ p ∈ Nat.primesBelow Q, Real.log p / p) ≤ Real.log Q + D := by
    have hsub : Nat.primesBelow Q ⊆ (Icc 1 Q).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpQ, hpp⟩ := Nat.mem_primesBelow.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.one_lt.le, hpQ.le⟩, hpp⟩
    have hmono := sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    have hmertens := (abs_le.mp (RHTower.Mertens.mertens_first_prime Q (by omega))).2
    have hsmall := le_abs_self ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))
    change (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) ≤ D at hsmall
    linarith only [hmono, hmertens, hsmall]
  have htilt : Real.exp ((2 / u) * ∑ p ∈ Nat.primesBelow Q, Real.log p / p) ≤ E := by
    apply Real.exp_le_exp.mpr
    rw [show (2 / u) * (∑ p ∈ Nat.primesBelow Q, Real.log p / p) =
      (2 * ∑ p ∈ Nat.primesBelow Q, Real.log p / p) / u by ring, div_le_iff₀ hu]
    have hDu := mul_nonneg hD (show 0 ≤ u - 1 by linarith only [hu1])
    nlinarith only [hsum, hQu, hDu]
  let H := ∏ p ∈ Nat.primesBelow Q, (1 - ω p / p)
  have hH : 0 ≤ H := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have h := div_le_div_of_nonneg_right (abs_le.mp (hbd p)).2 hp0.le
    have hhalf := one_div_le_one_div_of_le (by norm_num) hp2
    linarith only [h, hhalf]
  have hHδ : H * flipDensityBelow ω Q = ∏ p ∈ Nat.primesBelow Q, (1 - 1 / (p : ℝ)) := by
    simpa only [one_mul] using mul_flipDensityBelow hbd 1 Q
  have hHbound : H ≤ (2 * RHTower.Sieve.mertensThirdUpperConst / Real.log Q) / flipDensityBelow ω Q :=
    (le_div_iff₀ hδ).mpr (hHδ.trans_le (ordinaryPrimeHead_le hQ))
  calc
    _ ≤ H * E := (primeHead_tilt_le hbd Q hu).trans (mul_le_mul_of_nonneg_left htilt hH)
    _ ≤ ((2 * RHTower.Sieve.mertensThirdUpperConst / Real.log Q) / flipDensityBelow ω Q) * E :=
      mul_le_mul_of_nonneg_right hHbound hE.le
    _ = _ := by dsimp only [C]; ring

end GaloisForLFunctions.RenormalizedIntersectionTheory
