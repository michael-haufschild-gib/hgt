import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingEntranceTailBarrier

/-!
# The pronic dual norm of the arithmetic entrance law

The centred damped transition `P_η - e_η` is a compact operator on `c₀`, while the
receiver's critical energy is a pronic `ℓ²` quantity, with weight `1 / (n (n + 1))`.
Centring is subtraction of the entrance functional, so a pronic version of the centred
transition needs that functional to be pronic-bounded.  Its pronic dual norm is computed
here: two-sided Bernoulli bounds make it `∑ k ^ (-2 η)` up to bounded factors, hence
finite exactly for `η > 1/2`.  Below that threshold the functional is unbounded on the
pronic space, with an explicit divergent witness, so no pronic version of the centred
transition exists; the obstruction sits in the centring, not in the transition.  Dividing
out the size bias — passing to the reciprocal observable — restores a finite pronic dual
norm at every damping.
-/

open Finset RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ### Two-sided Bernoulli bounds for the discrete derivative of the zeta power law -/

/-- Bernoulli's inequality at the negative exponent bounds the discrete derivative of
`t ↦ t ^ (-1 - η)` from above by its continuous counterpart. -/
private theorem powerLaw_diff_le {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    t ^ (-1 - η) - (t + 1) ^ (-1 - η) ≤ (1 + η) * t ^ (-1 - η) / (t + 1) := by
  have h1 : (0 : ℝ) < t + 1 := by linarith
  have hs : (-1 : ℝ) ≤ -(1 / (t + 1)) := by
    rw [neg_le_neg_iff, div_le_one h1]; linarith
  have key := one_add_mul_self_le_rpow_one_add hs (p := 1 + η) (by linarith)
  have hrw : (1 : ℝ) + -(1 / (t + 1)) = t / (t + 1) := by field_simp
  rw [hrw, Real.div_rpow ht.le h1.le] at key
  have hmul : t ^ (-1 - η) * t ^ (1 + η) = 1 := by
    rw [← Real.rpow_add ht]; norm_num
  have hpow : t ^ (-1 - η) * (t ^ (1 + η) / (t + 1) ^ (1 + η)) = (t + 1) ^ (-1 - η) := by
    rw [show (-1 - η) = -(1 + η) by ring, Real.rpow_neg h1.le]
    rw [mul_div_assoc'] at *
    rw [show t ^ (-(1 + η)) * t ^ (1 + η) = 1 by rw [← Real.rpow_add ht]; norm_num]
    rw [one_div]
  have hpos : (0 : ℝ) < t ^ (-1 - η) := Real.rpow_pos_of_pos ht _
  have := mul_le_mul_of_nonneg_left key hpos.le
  rw [hpow] at this
  have hexp : t ^ (-1 - η) * (1 + (1 + η) * -(1 / (t + 1))) =
      t ^ (-1 - η) - (1 + η) * t ^ (-1 - η) / (t + 1) := by
    field_simp; ring
  rw [hexp] at this
  linarith

/-- Bernoulli's inequality at the positive exponent bounds the same discrete derivative
from below. -/
private theorem powerLaw_le_diff {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    (1 + η) * t ^ (-1 - η) / (t + 1 + η) ≤ t ^ (-1 - η) - (t + 1) ^ (-1 - η) := by
  have h1 : (0 : ℝ) < t + 1 := by linarith
  have h2 : (0 : ℝ) < t + 1 + η := by linarith
  have hs : (-1 : ℝ) ≤ 1 / t := le_trans (by norm_num) (by positivity)
  have key := one_add_mul_self_le_rpow_one_add hs (p := 1 + η) (by linarith)
  have hrw : (1 : ℝ) + 1 / t = (t + 1) / t := by field_simp
  rw [hrw, Real.div_rpow h1.le ht.le] at key
  have hleft : (1 : ℝ) + (1 + η) * (1 / t) = (t + 1 + η) / t := by field_simp; ring
  rw [hleft] at key
  -- invert the comparison of positive quantities
  have hA : (0 : ℝ) < t ^ (1 + η) := Real.rpow_pos_of_pos ht _
  have hB : (0 : ℝ) < (t + 1) ^ (1 + η) := Real.rpow_pos_of_pos h1 _
  have hinv : t ^ (1 + η) / (t + 1) ^ (1 + η) ≤ t / (t + 1 + η) := by
    rw [div_le_div_iff₀ hB (by positivity)]
    rw [div_le_div_iff₀ (by positivity) hA] at key
    nlinarith [key]
  have hpos : (0 : ℝ) < t ^ (-1 - η) := Real.rpow_pos_of_pos ht _
  have hpow : t ^ (-1 - η) * (t ^ (1 + η) / (t + 1) ^ (1 + η)) = (t + 1) ^ (-1 - η) := by
    rw [show (-1 - η) = -(1 + η) by ring, Real.rpow_neg h1.le, mul_div_assoc']
    rw [show t ^ (-(1 + η)) * t ^ (1 + η) = 1 by rw [← Real.rpow_add ht]; norm_num]
    rw [one_div]
  have := mul_le_mul_of_nonneg_left hinv hpos.le
  rw [hpow] at this
  have hexp : t ^ (-1 - η) * (t / (t + 1 + η)) =
      t ^ (-1 - η) - (1 + η) * t ^ (-1 - η) / (t + 1 + η) := by
    field_simp; ring
  rw [hexp] at this
  linarith

/-! ### Two-sided bounds for the entrance weight -/

/-- The entrance weight is at most `ρ (1 + η) k ^ (-η) / (k + 1)`. -/
theorem arithmeticDampingEntrance_le {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 0 < k) :
    arithmeticDampingEntrance η k ≤
      (pmPowerDampedDivisorDensity η).re * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ := (pmPowerDampedDivisorDensity_re_pos hη).le
  have hd := powerLaw_diff_le hη hk0
  have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  have hkpow : (k : ℝ) * (k : ℝ) ^ (-1 - η) = (k : ℝ) ^ (-η) := by
    rw [show ((k : ℝ)) = (k : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_add hk0]
    norm_num
  unfold arithmeticDampingEntrance
  rw [hcast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  have := mul_le_mul_of_nonneg_left hd hk0.le
  calc (k : ℝ) * ((k : ℝ) ^ (-1 - η) - ((k : ℝ) + 1) ^ (-1 - η))
      ≤ (k : ℝ) * ((1 + η) * (k : ℝ) ^ (-1 - η) / ((k : ℝ) + 1)) := this
    _ = (1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1) := by
        rw [← hkpow]; field_simp; ring

/-- The entrance weight is at least `ρ (1 + η) k ^ (-η) / (k + 1 + η)`. -/
theorem arithmeticDampingEntrance_ge {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 0 < k) :
    (pmPowerDampedDivisorDensity η).re * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η)) ≤
      arithmeticDampingEntrance η k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ := (pmPowerDampedDivisorDensity_re_pos hη).le
  have hd := powerLaw_le_diff hη hk0
  have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  have hkpow : (k : ℝ) * (k : ℝ) ^ (-1 - η) = (k : ℝ) ^ (-η) := by
    rw [show ((k : ℝ)) = (k : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_add hk0]
    norm_num
  unfold arithmeticDampingEntrance
  rw [hcast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  have hstep := mul_le_mul_of_nonneg_left hd hk0.le
  calc (1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η)
      = (k : ℝ) * ((1 + η) * (k : ℝ) ^ (-1 - η) / ((k : ℝ) + 1 + η)) := by
        rw [← hkpow]; field_simp; ring
    _ ≤ _ := hstep

/-! ### The pronic dual norm of the entrance functional -/

/-- The pronic dual norm is finite above half damping: the squared entrance weights
against the reciprocal pronic weight `k (k + 1)` are dominated by `k ^ (-2 η)`. -/
theorem summable_arithmeticDampingEntrance_pronicDual {η : ℝ} (hη : 1 / 2 < η) :
    Summable fun k : ℕ =>
      arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hη0 : (0 : ℝ) < η := by linarith
  set ρ := (pmPowerDampedDivisorDensity η).re with hρdef
  have hρ : 0 < ρ := pmPowerDampedDivisorDensity_re_pos hη0
  have hmaj : Summable fun k : ℕ => (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
  · exact mul_nonneg (sq_nonneg _) (by positivity)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [arithmeticDampingEntrance]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hle := arithmeticDampingEntrance_le hη0 hk
  have hnn := arithmeticDampingEntrance_nonneg hη0 k
  have hsq : arithmeticDampingEntrance η k ^ 2 ≤
      (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 := by
    exact pow_le_pow_left₀ hnn hle 2
  have hpow : ((k : ℝ) ^ (-η)) ^ 2 = (k : ℝ) ^ (-(2 * η)) := by
    rw [sq, ← Real.rpow_add hk0]; ring_nf
  have hexp : (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 *
      ((k : ℝ) * ((k : ℝ) + 1)) =
      (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) * ((k : ℝ) / ((k : ℝ) + 1)) := by
    rw [← hpow]; field_simp; ring
  have hratio : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  calc arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1))
      ≤ (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 * ((k : ℝ) * ((k : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) * ((k : ℝ) / ((k : ℝ) + 1)) := hexp
    _ ≤ (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) * 1 := by
        refine mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- At or below half damping the pronic dual norm diverges: the squared entrance weights
dominate `k ^ (-2 η) / 4` against the reciprocal pronic weight. -/
theorem not_summable_arithmeticDampingEntrance_pronicDual {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 2) :
    ¬ Summable fun k : ℕ =>
      arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1)) := by
  set ρ := (pmPowerDampedDivisorDensity η).re with hρdef
  have hρ : 0 < ρ := pmPowerDampedDivisorDensity_re_pos hη
  intro hs
  have hmin : ¬ Summable fun k : ℕ => ρ ^ 2 / 4 * (k : ℝ) ^ (-(2 * η)) := by
    intro h
    have := (summable_mul_left_iff (by positivity : ρ ^ 2 / 4 ≠ 0)).mp h
    exact absurd (Real.summable_nat_rpow.mp this) (by linarith)
  refine hmin (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [arithmeticDampingEntrance, Real.zero_rpow (by linarith : -(2 * η) ≠ 0)]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hge := arithmeticDampingEntrance_ge hη hk
  have hlow : 0 ≤ ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η)) := by positivity
  have hsq : (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η))) ^ 2 ≤
      arithmeticDampingEntrance η k ^ 2 := pow_le_pow_left₀ hlow hge 2
  have hpow : ((k : ℝ) ^ (-η)) ^ 2 = (k : ℝ) ^ (-(2 * η)) := by
    rw [sq, ← Real.rpow_add hk0]; ring_nf
  have hexp : (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η))) ^ 2 *
      ((k : ℝ) * ((k : ℝ) + 1)) =
      (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) *
        ((k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 1 + η) ^ 2) := by
    rw [← hpow]; field_simp; ring
  have hfrac : (1 : ℝ) / 4 ≤ (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 1 + η) ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hpos : (0 : ℝ) ≤ (k : ℝ) ^ (-(2 * η)) := Real.rpow_nonneg hk0.le _
  have honeη : (1 : ℝ) ≤ (1 + η) ^ 2 := by nlinarith
  calc ρ ^ 2 / 4 * (k : ℝ) ^ (-(2 * η))
      = (ρ * 1) ^ 2 * (k : ℝ) ^ (-(2 * η)) * (1 / 4) := by ring
    _ ≤ (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) *
          ((k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 1 + η) ^ 2) := by
        have h1 : (ρ * 1) ^ 2 * (k : ℝ) ^ (-(2 * η)) ≤
            (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos
          rw [mul_pow, mul_pow, one_pow]
          exact mul_le_mul_of_nonneg_left honeη (sq_nonneg ρ)
        exact mul_le_mul h1 hfrac (by norm_num) (by positivity)
    _ = (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η))) ^ 2 *
          ((k : ℝ) * ((k : ℝ) + 1)) := hexp.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq (by positivity)

/-- The entrance functional is pronic-bounded exactly above half damping.  The threshold
`1/2` is the receiver's damping threshold, read off here from the size bias alone. -/
theorem summable_arithmeticDampingEntrance_pronicDual_iff {η : ℝ} (hη : 0 < η) :
    (Summable fun k : ℕ =>
        arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1))) ↔ 1 / 2 < η := by
  refine ⟨fun hs => ?_, summable_arithmeticDampingEntrance_pronicDual⟩
  by_contra h
  exact not_summable_arithmeticDampingEntrance_pronicDual hη (not_lt.mp h) hs

/-! ### The entrance functional on the pronic space -/

/-- Above half damping the entrance functional is bounded on the pronic inner product,
with the square root of the pronic dual norm as its constant. -/
theorem exists_pronicPairing_bound {η : ℝ} (hη : 1 / 2 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (b : ℕ → ℝ),
      |∑ k ∈ s, arithmeticDampingEntrance η k * b k| ≤
        C * Real.sqrt (∑ k ∈ s, b k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  have hη0 : (0 : ℝ) < η := by linarith
  set D := fun k : ℕ => arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1))
    with hDdef
  have hsum : Summable D := summable_arithmeticDampingEntrance_pronicDual hη
  have hDnn : ∀ k, 0 ≤ D k := fun k => mul_nonneg (sq_nonneg _) (by positivity)
  refine ⟨Real.sqrt (∑' k, D k), Real.sqrt_nonneg _, fun s b => ?_⟩
  set f := fun k : ℕ => arithmeticDampingEntrance η k *
    Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) with hfdef
  set g := fun k : ℕ => b k / Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) with hgdef
  have hfg : ∀ k, f k * g k = arithmeticDampingEntrance η k * b k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hfdef, hgdef, arithmeticDampingEntrance]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hw : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
    have := Real.sqrt_pos.mpr hw
    field_simp [hfdef, hgdef]
  have hf2 : ∀ k, f k ^ 2 = D k := by
    intro k
    have hw : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by positivity
    simp [hfdef, hDdef, mul_pow, Real.sq_sqrt hw]
  have hg2 : ∀ k, g k ^ 2 = b k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hgdef]
    have hw : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by positivity
    simp [hgdef, div_pow, Real.sq_sqrt hw]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hA : ∑ k ∈ s, f k ^ 2 ≤ ∑' k, D k := by
    simpa [hf2] using hsum.sum_le_tsum s (fun k _ => hDnn k)
  have hAnn : (0 : ℝ) ≤ ∑ k ∈ s, f k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hBnn : (0 : ℝ) ≤ ∑ k ∈ s, g k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsq : |∑ k ∈ s, arithmeticDampingEntrance η k * b k| ≤
      Real.sqrt ((∑ k ∈ s, f k ^ 2) * ∑ k ∈ s, g k ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    calc (∑ k ∈ s, arithmeticDampingEntrance η k * b k) ^ 2
        = (∑ k ∈ s, f k * g k) ^ 2 := by simp [hfg]
      _ ≤ _ := hcs
  refine hsq.trans ?_
  rw [Real.sqrt_mul hAnn]
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hA) (Real.sqrt_nonneg _)
  
/-- At or below half damping the entrance functional is unbounded on the pronic space:
its truncated dual vectors give pairing-to-norm ratios beyond every constant.  So the
centred damped transition has no pronic version there. -/
theorem exists_pronicPairing_gt {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (C : ℝ) :
    ∃ (s : Finset ℕ) (b : ℕ → ℝ),
      C * Real.sqrt (∑ k ∈ s, b k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) <
        ∑ k ∈ s, arithmeticDampingEntrance η k * b k := by
  set D := fun k : ℕ => arithmeticDampingEntrance η k ^ 2 * ((k : ℝ) * ((k : ℝ) + 1))
    with hDdef
  have hDnn : ∀ k, 0 ≤ D k := fun k => mul_nonneg (sq_nonneg _) (by positivity)
  have hdiv := not_summable_arithmeticDampingEntrance_pronicDual hη hη'
  have htend : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, D k)
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hDnn).mp hdiv
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp htend (C ^ 2 + 1)).exists
  set b := fun k : ℕ => arithmeticDampingEntrance η k * ((k : ℝ) * ((k : ℝ) + 1)) with hbdef
  refine ⟨Finset.range N, b, ?_⟩
  have hpair : ∑ k ∈ Finset.range N, arithmeticDampingEntrance η k * b k =
      ∑ k ∈ Finset.range N, D k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hbdef, hDdef]; ring
  have hnorm : ∑ k ∈ Finset.range N, b k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) =
      ∑ k ∈ Finset.range N, D k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hbdef, hDdef, arithmeticDampingEntrance]
    have hw : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
    rw [hbdef, hDdef]
    field_simp
    ring
  set S := ∑ k ∈ Finset.range N, D k with hSdef
  have hS1 : C ^ 2 + 1 ≤ S := hN
  have hSpos : 0 < S := by nlinarith [sq_nonneg C]
  have hCs : C < Real.sqrt S := by
    rcases le_or_gt C 0 with hC | hC
    · exact lt_of_le_of_lt hC (Real.sqrt_pos.mpr hSpos)
    · have : C ^ 2 < S := by linarith
      nlinarith [Real.sq_sqrt hSpos.le, Real.sqrt_nonneg S]
  rw [hpair, hnorm]
  have hsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSpos.le
  calc C * Real.sqrt S < Real.sqrt S * Real.sqrt S := by
        exact mul_lt_mul_of_pos_right hCs (Real.sqrt_pos.mpr hSpos)
    _ = S := hsq

/-- Below half damping the divergence is witnessed by a single power sequence: the
pronic-square-summable `k ↦ k ^ ((η + 1/2)/2)` has divergent entrance pairing, so the
centring is not even defined on the pronic space. -/
theorem exists_pronicWitness_not_summable_pairing {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    ∃ b : ℕ → ℝ, (∀ k, 0 ≤ b k) ∧
      (Summable fun k : ℕ => b k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) ∧
      ¬ Summable fun k : ℕ => arithmeticDampingEntrance η k * b k := by
  set ρ := (pmPowerDampedDivisorDensity η).re with hρdef
  have hρ : 0 < ρ := pmPowerDampedDivisorDensity_re_pos hη
  set α := (η + 1 / 2) / 2 with hαdef
  have hαη : η < α := by rw [hαdef]; linarith
  have hα2 : α < 1 / 2 := by rw [hαdef]; linarith
  have hα0 : 0 < α := by linarith
  refine ⟨fun k => (k : ℝ) ^ α, fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _, ?_, ?_⟩
  · have hmaj : Summable fun k : ℕ => (k : ℝ) ^ (2 * α - 2) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Real.zero_rpow hα0.ne']
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hw : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
    rw [div_le_iff₀ hw]
    have hsq : ((k : ℝ) ^ α) ^ 2 = (k : ℝ) ^ (2 * α) := by
      rw [sq, ← Real.rpow_add hk0]; ring_nf
    have hsplit : (k : ℝ) ^ (2 * α - 2) * ((k : ℝ) * ((k : ℝ) + 1)) =
        (k : ℝ) ^ (2 * α) * (((k : ℝ) + 1) / (k : ℝ)) := by
      rw [show (2 * α - 2 : ℝ) = 2 * α + (-2) by ring, Real.rpow_add hk0]
      rw [show ((k : ℝ)) ^ (-2 : ℝ) = 1 / (k : ℝ) ^ (2 : ℕ) by
        rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_neg hk0.le]; norm_num]
      field_simp
      ring
    rw [hsq, hsplit]
    have hone : (1 : ℝ) ≤ ((k : ℝ) + 1) / (k : ℝ) := by
      rw [le_div_iff₀ hk0]; linarith
    exact le_mul_of_one_le_right (by positivity) hone
  · intro hs
    have hmin : ¬ Summable fun k : ℕ => ρ / 3 * (k : ℝ) ^ (α - η - 1) := by
      intro h
      have := (summable_mul_left_iff (by positivity : ρ / 3 ≠ 0)).mp h
      exact absurd (Real.summable_nat_rpow.mp this) (by linarith)
    refine hmin (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [arithmeticDampingEntrance, Real.zero_rpow (by linarith : α - η - 1 ≠ 0)]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hge := arithmeticDampingEntrance_ge hη hk
    have hstep : ρ / 3 * (k : ℝ) ^ (α - η - 1) ≤
        ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η)) * (k : ℝ) ^ α := by
      have hden : (k : ℝ) + 1 + η ≤ 3 * (k : ℝ) := by linarith
      have hsplit : (k : ℝ) ^ (α - η - 1) =
          (k : ℝ) ^ (-η) * (k : ℝ) ^ α / (k : ℝ) := by
        rw [← Real.rpow_add hk0]
        rw [show ((k : ℝ)) = (k : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one]]
        rw [← Real.rpow_sub hk0]
        congr 1
        ring
      rw [hsplit]
      have hA : (0 : ℝ) < (k : ℝ) ^ (-η) * (k : ℝ) ^ α := by positivity
      rw [div_le_iff₀ hk0] at *
      have hmono : ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1 + η)) * (k : ℝ) ^ α =
          ρ * (1 + η) * ((k : ℝ) ^ (-η) * (k : ℝ) ^ α) / ((k : ℝ) + 1 + η) := by
        field_simp; ring
      rw [hmono, ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith [hA.le, mul_le_mul_of_nonneg_left hden (by positivity : (0:ℝ) ≤ ρ * ((k : ℝ) ^ (-η) * (k : ℝ) ^ α))]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right hge (Real.rpow_nonneg hk0.le _)

/-! ### The surviving observable -/

/-- Removing the size bias restores pronic boundedness at every damping: the reciprocal
entrance observable has finite pronic dual norm for every `η > 0`.  This is the pronic
counterpart of the exact telescoping of the reciprocal tail. -/
theorem summable_arithmeticDampingEntrance_reciprocal_pronicDual {η : ℝ} (hη : 0 < η) :
    Summable fun k : ℕ =>
      (arithmeticDampingEntrance η k / (k : ℝ)) ^ 2 * ((k : ℝ) * ((k : ℝ) + 1)) := by
  set ρ := (pmPowerDampedDivisorDensity η).re with hρdef
  have hρ : 0 < ρ := pmPowerDampedDivisorDensity_re_pos hη
  have hmaj : Summable fun k : ℕ => 2 * (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-2 - 2 * η) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
  · exact mul_nonneg (sq_nonneg _) (by positivity)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [arithmeticDampingEntrance]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hle := arithmeticDampingEntrance_le hη hk
  have hnn := arithmeticDampingEntrance_nonneg hη k
  have hsq : arithmeticDampingEntrance η k ^ 2 ≤
      (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 := pow_le_pow_left₀ hnn hle 2
  have hpow : ((k : ℝ) ^ (-η)) ^ 2 = (k : ℝ) ^ (-(2 * η)) := by
    rw [sq, ← Real.rpow_add hk0]; ring_nf
  have hid : (arithmeticDampingEntrance η k / (k : ℝ)) ^ 2 * ((k : ℝ) * ((k : ℝ) + 1)) =
      arithmeticDampingEntrance η k ^ 2 * (((k : ℝ) + 1) / (k : ℝ)) := by
    field_simp; ring
  have hstep : arithmeticDampingEntrance η k ^ 2 * (((k : ℝ) + 1) / (k : ℝ)) ≤
      (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 * 2 := by
    have hr : ((k : ℝ) + 1) / (k : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hk0]; linarith
    exact mul_le_mul hsq hr (by positivity) (by positivity)
  have hfinal : (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 * 2 ≤
      2 * (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-2 - 2 * η) := by
    have hexp : (ρ * ((1 + η) * (k : ℝ) ^ (-η) / ((k : ℝ) + 1))) ^ 2 * 2 =
        2 * (ρ * (1 + η)) ^ 2 * (k : ℝ) ^ (-(2 * η)) / ((k : ℝ) + 1) ^ 2 := by
      rw [← hpow]; field_simp; ring
    have hk2 : (k : ℝ) ^ (2 : ℕ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (k : ℝ) ^ (2 : ℕ) := by positivity
    have hshift : (k : ℝ) ^ (-2 - 2 * η) =
        (k : ℝ) ^ (-(2 * η)) / (k : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_sub hk0]
      congr 1
      push_cast
      ring
    rw [hexp, hshift]
    refine div_le_div_of_nonneg_left ?_ hpos hk2
    positivity
  rw [hid]
  exact hstep.trans hfinal

end
end GaloisForLFunctions.BezoutValuationIncidence
