import GaloisForLFunctions.BezoutValuationIncidence.DilationSuccessorFiberReciprocity
import GaloisForLFunctions.BezoutValuationIncidence.ChineseRemainderBezoutPeriodicityAndSawtoothDefect
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds

/-!
# Successor sectors, arithmetic resonance, and the harmonic mode

For a least positive successor seed `p*a=q*b+1`, every positive solution is
`(a+q*t,b+p*t)`. This identifies the complete finite lag-one sector in the
integer dilation profile with a weighted reciprocal progression.

A complete modulus period has mass `r*μ(r)` when both scales are coprime to
`r`, and zero otherwise. The determinant-one equation proves this selector
through exact Fourier resonance. Subtracting its harmonic mode gives a
uniform explicit finite-horizon remainder, including the horizon correction.
The adjacent-scale capstone has no hypotheses.
-/

open scoped BigOperators
open Finset RHTower
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- A successor solution with least positive first coordinate parametrizes all positive solutions. -/
theorem successor_solution_parametrization {p q a b c d : ℕ}
    (hq : 0 < q) (haq : a ≤ q)
    (hab : p * a = q * b + 1) (hc : 1 ≤ c) (hcd : p * c = q * d + 1) :
    ∃ t : ℕ, c = a + q * t ∧ d = b + p * t := by
  have hg : dilationJumpGap p q (a, b) = 1 := by
    dsimp [dilationJumpGap]
    have he : (p : ℤ) * a = (q : ℤ) * b + 1 := by exact_mod_cast hab
    omega
  have hpq := (dilationJumpGap_one_coprime hg).1
  have hm : Nat.ModEq q a c := by
    apply Nat.ModEq.cancel_left_of_coprime hpq.symm
    change (p * a) % q = (p * c) % q
    rw [hab, hcd]
    simp
  have hac : a ≤ c := by
    by_cases hlt : a < q
    · have he : a = c % q := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using hm
      rw [he]
      exact Nat.mod_le _ _
    · have he : a = q := by omega
      have hqc : q ∣ c := by
        apply Nat.dvd_of_mod_eq_zero
        simpa [Nat.ModEq, he] using hm.symm
      simpa only [he] using Nat.le_of_dvd (by omega : 0 < c) hqc
  have hdvd : q ∣ c - a := (Nat.modEq_iff_dvd' hac).mp hm
  obtain ⟨t, ht⟩ := hdvd
  have hec : c = a + q * t := by omega
  refine ⟨t, hec, ?_⟩
  apply mul_left_cancel₀ (by omega : q ≠ 0)
  calc
    q * d = p * c - 1 := by omega
    _ = q * (b + p * t) := by
      rw [hec, Nat.mul_add, hab]
      have : (q * b + 1) + p * (q * t) = q * (b + p * t) + 1 := by ring
      omega

/-- Every pair of nontrivial coprime scales has a least positive successor seed. -/
theorem exists_successor_seed {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ q ∧ 1 ≤ b ∧ p * a = q * b + 1 := by
  have hcard := card_bezoutIntervalSet_period_eq_one 0
    (d₁ := q) (d₂ := p) hpq.symm (by omega) (by omega)
  obtain ⟨n, hn⟩ := Finset.card_pos.mp (by omega : 0 < (bezoutIntervalSet 0 (0 + q * p) q p).card)
  rw [mem_bezoutIntervalSet] at hn
  have hpa : p * ((n + 1) / p) = n + 1 := Nat.mul_div_cancel' hn.2.2
  have hqb : q * (n / q) = n := Nat.mul_div_cancel' hn.2.1
  have hnlt : n < q * p := by
    have hne : n ≠ q * p := by
      intro he
      have hd : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_left p q)).mpr (he ▸ hn.2.2)
      have := Nat.dvd_one.mp hd
      omega
    omega
  refine ⟨(n + 1) / p, n / q, ?_, ?_, ?_, by omega⟩
  · by_contra h
    have : (n + 1) / p = 0 := Nat.eq_zero_of_not_pos h
    rw [this, Nat.mul_zero] at hpa
    omega
  · by_contra h
    have hh : q + 1 ≤ (n + 1) / p := by omega
    have hl := Nat.mul_le_mul_left p hh
    nlinarith [hpa, hnlt]
  · by_contra h
    have : n / q = 0 := Nat.eq_zero_of_not_pos h
    rw [this, Nat.mul_zero] at hqb
    omega

/-- One positive successor seed resolves the complete finite profile sector into an arithmetic progression. -/
theorem ramanujanDilationLagSector_one_eq_seed_sum {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (r T : ℕ) :
    ramanujanDilationLagSector r p q (p * q * T) 1 =
      ∑ t ∈ range T,
        (d4BMRamanujanNaturalCoefficient (a + q * t) r).re *
          (d4BMRamanujanNaturalCoefficient (b + p * t) r).re *
          (1 / ((p * (a + q * t) : ℕ) : ℝ) - 1 / (((p * q * T : ℕ) : ℝ) + 1)) := by
  classical
  let S := (dilationJumpPairs (p * q * T) p q).filter (fun ab => dilationJumpGap p q ab = 1)
  have hbp : b < p := by
    have hpa := Nat.mul_le_mul_left p haq
    nlinarith [hab]
  have hdivp : p * q * T / p = q * T := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ hp]
  have hdivq : p * q * T / q = p * T := by
    rw [show p * q * T = q * (p * T) by ring, Nat.mul_div_cancel_left _ hq]
  have hmem (t : ℕ) (ht : t < T) : (a + q * t, b + p * t) ∈ S := by
    apply mem_filter.mpr
    constructor
    · apply mem_product.mpr
      rw [hdivp, hdivq]
      constructor <;> apply mem_Icc.mpr
      · constructor
        · omega
        · have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt ht)
          nlinarith
      · constructor
        · omega
        · have hh := Nat.mul_le_mul_left p (Nat.succ_le_of_lt ht)
          nlinarith
    · have he : p * (a + q * t) = q * (b + p * t) + 1 := by
        calc
          _ = p * a + p * q * t := by ring
          _ = _ := by rw [hab]; ring
      dsimp [dilationJumpGap]
      have hc : (p : ℤ) * (a + q * t) = (q : ℤ) * (b + p * t) + 1 := by exact_mod_cast he
      omega
  have hparam (cd : ℕ × ℕ) (hcd : cd ∈ S) :
      ∃ t < T, cd = (a + q * t, b + p * t) := by
    have hm := mem_product.mp (mem_filter.mp hcd).1
    have hc1 := (mem_Icc.mp hm.1).1
    have hc2 := (mem_Icc.mp hm.1).2
    rw [hdivp] at hc2
    have hg := (mem_filter.mp hcd).2
    have hcast : ((p * cd.1 : ℕ) : ℤ) - ((q * cd.2 : ℕ) : ℤ) = 1 := by
      simpa only [dilationJumpGap, Nat.cast_mul] using hg
    have he : p * cd.1 = q * cd.2 + 1 := by omega
    obtain ⟨t, hc, hd⟩ := successor_solution_parametrization hq haq hab hc1 he
    have ht : t < T := by
      by_contra h
      have hh := Nat.mul_le_mul_left q (by omega : T ≤ t)
      omega
    exact ⟨t, ht, Prod.ext hc hd⟩
  unfold ramanujanDilationLagSector
  change (∑ cd ∈ S, ramanujanJumpPairTerm r p q (p * q * T) cd) = _
  symm
  refine sum_nbij' (i := fun t => (a + q * t, b + p * t))
    (j := fun cd : ℕ × ℕ => (cd.1 - a) / q) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact hmem t (mem_range.mp ht)
  · intro cd hcd
    obtain ⟨t, ht, rfl⟩ := hparam cd hcd
    simpa [Nat.mul_div_cancel_left _ hq] using mem_range.mpr ht
  · intro t ht
    simp [Nat.mul_div_cancel_left _ hq]
  · intro cd hcd
    obtain ⟨t, ht, rfl⟩ := hparam cd hcd
    simp [Nat.mul_div_cancel_left _ hq]
  · intro t ht
    have hm := hmem t (mem_range.mp ht)
    rw [ramanujanJumpPairTerm_at_successor hp hq (mem_filter.mp hm).1 (mem_filter.mp hm).2]
    have he : p * (a + q * t) = q * (b + p * t) + 1 := by
      calc
        _ = p * a + p * q * t := by ring
        _ = _ := by rw [hab]; ring
    rw [he]

/-- The jump-amplitude product on one positive successor progression. -/
def successorFiberAmplitude (r p q a b t : ℕ) : ℝ :=
  (d4BMRamanujanNaturalCoefficient (a + q * t) r).re *
    (d4BMRamanujanNaturalCoefficient (b + p * t) r).re

/-- Natural Ramanujan coefficients are periodic, including the zero-modulus convention. -/
theorem ramanujanNaturalCoefficient_add_mul_modulus (n r k : ℕ) :
    d4BMRamanujanNaturalCoefficient (n + r * k) r =
      d4BMRamanujanNaturalCoefficient n r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr,
      d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr,
      Nat.gcd_add_mul_left_left]

/-- A full modulus period preserves the actual two jump amplitudes. -/
theorem successorFiberAmplitude_add_period (r p q a b t k : ℕ) :
    successorFiberAmplitude r p q a b (t + r * k) =
      successorFiberAmplitude r p q a b t := by
  unfold successorFiberAmplitude
  rw [show a + q * (t + r * k) = (a + q * t) + r * (q * k) by ring,
    show b + p * (t + r * k) = (b + p * t) + r * (p * k) by ring,
    ramanujanNaturalCoefficient_add_mul_modulus,
    ramanujanNaturalCoefficient_add_mul_modulus]

/-- Natural-index and residue-class presentations of one complete amplitude period agree. -/
theorem successorFiberAmplitude_sum_range_eq_zmod (Q : CGLPositiveModulus) (p q a b : ℕ) :
    (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) =
      ∑ t : ZMod Q.value, successorFiberAmplitude Q.value p q a b t.val := by
  classical
  symm
  refine sum_nbij' (i := fun t : ZMod Q.value => t.val)
    (j := fun t : ℕ => (t : ZMod Q.value)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact mem_range.mpr (ZMod.val_lt t)
  · intro t ht
    exact mem_univ _
  · intro t ht
    exact ZMod.natCast_zmod_val t
  · intro t ht
    exact ZMod.val_natCast_of_lt (mem_range.mp ht)
  · intro t ht
    rfl

private theorem sum_range_residue_blocks (r U : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ range (r * U), f n) = ∑ t ∈ range r, ∑ k ∈ range U, f (t + r * k) := by
  induction U with
  | zero => simp
  | succ U ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp [Finset.sum_range_succ, Finset.sum_add_distrib, Nat.add_comm]

/-- Exact residue-block decomposition of the actual successor sector, with its horizon correction. -/
theorem ramanujanDilationLagSector_one_eq_period_blocks
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (U : ℕ) :
    ramanujanDilationLagSector Q.value p q (p * q * (Q.value * U)) 1 =
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t *
        progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) U) -
      (U : ℝ) * (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) /
        (((p * q * (Q.value * U) : ℕ) : ℝ) + 1) := by
  rw [ramanujanDilationLagSector_one_eq_seed_sum hp hq ha haq hb hab]
  change (∑ n ∈ range (Q.value * U), successorFiberAmplitude Q.value p q a b n *
    (1 / ((p * (a + q * n) : ℕ) : ℝ) -
      1 / (((p * q * (Q.value * U) : ℕ) : ℝ) + 1))) = _
  rw [sum_range_residue_blocks]
  simp_rw [successorFiberAmplitude_add_period]
  have hinner (t : ℕ) :
      (∑ k ∈ range U, successorFiberAmplitude Q.value p q a b t *
        (1 / ((p * (a + q * (t + Q.value * k)) : ℕ) : ℝ) -
          1 / (((p * q * (Q.value * U) : ℕ) : ℝ) + 1))) =
      successorFiberAmplitude Q.value p q a b t *
        progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) U -
      (U : ℝ) * successorFiberAmplitude Q.value p q a b t /
        (((p * q * (Q.value * U) : ℕ) : ℝ) + 1) := by
    have hd (k : ℕ) : ((p * (a + q * (t + Q.value * k)) : ℕ) : ℝ) =
        (k : ℝ) * (p * q * Q.value : ℕ) + (p * (a + q * t) : ℕ) := by
      push_cast
      ring
    simp_rw [hd, mul_sub]
    rw [sum_sub_distrib, ← mul_sum]
    simp only [progressionHarmonicSum, sum_const, card_range, nsmul_eq_mul]
    ring
  simp_rw [hinner]
  rw [sum_sub_distrib]
  congr 1
  rw [← sum_div, ← mul_sum]

/-- Subtracting the exact harmonic mode leaves a uniformly bounded successor-sector remainder. -/
theorem abs_successor_sector_period_remainder_le
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (K : ℕ) :
    |ramanujanDilationLagSector Q.value p q (p * q * (Q.value * (K + 1))) 1 +
      ((K + 1 : ℕ) : ℝ) * (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) /
        (((p * q * (Q.value * (K + 1)) : ℕ) : ℝ) + 1) -
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) / ((p * q * Q.value : ℕ) : ℝ) * (harmonic K : ℝ)| ≤
      ∑ t ∈ range Q.value, |successorFiberAmplitude Q.value p q a b t| /
        ((p * (a + q * t) : ℕ) : ℝ) := by
  have hscale : ((∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) *
      ((harmonic K : ℝ) / ((p * q * Q.value : ℕ) : ℝ))) =
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) / ((p * q * Q.value : ℕ) : ℝ) * (harmonic K : ℝ) := by
    ring
  have he : ramanujanDilationLagSector Q.value p q (p * q * (Q.value * (K + 1))) 1 +
      ((K + 1 : ℕ) : ℝ) * (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) /
        (((p * q * (Q.value * (K + 1)) : ℕ) : ℝ) + 1) -
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) / ((p * q * Q.value : ℕ) : ℝ) * (harmonic K : ℝ) =
      ∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t *
        (progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) (K + 1) -
          (harmonic K : ℝ) / ((p * q * Q.value : ℕ) : ℝ)) := by
    rw [ramanujanDilationLagSector_one_eq_period_blocks Q hp hq ha haq hb hab]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hscale]
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro t ht
  have ht : t < Q.value := mem_range.mp ht
  have hd0 : 1 ≤ p * (a + q * t) := by
    have hpos : 0 < p * (a + q * t) := by positivity
    omega
  have hdL : p * (a + q * t) ≤ p * q * Q.value := by
    have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt ht)
    have hi : a + q * t ≤ q * Q.value := by nlinarith
    simpa only [mul_assoc] using Nat.mul_le_mul_left p hi
  rw [abs_mul]
  have hh := mul_le_mul_of_nonneg_left
    (abs_progressionHarmonicSum_succ_sub_harmonic_div_le hd0 hdL K)
    (abs_nonneg (successorFiberAmplitude Q.value p q a b t))
  simpa only [mul_one_div] using hh

/-- The successor determinant forces both scales to be units in every surviving Fourier mode. -/
theorem successor_character_resonance_forces_units
    (Q : CGLPositiveModulus) {p q a b : ℕ} (hab : p * a = q * b + 1)
    {u v : ZMod Q.value} (hu : IsUnit u) (hv : IsUnit v)
    (hz : u * q + v * p = 0) :
    Nat.Coprime p Q.value ∧ Nat.Coprime q Q.value := by
  have hd : (p : ZMod Q.value) * a = (q : ZMod Q.value) * b + 1 := by
    have hc := congrArg (fun n : ℕ => (n : ZMod Q.value)) hab
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hc
  have heU : (p : ZMod Q.value) * (u * a + v * b) = u := by
    linear_combination u * hd + (b : ZMod Q.value) * hz
  have heV : (q : ZMod Q.value) * (-(u * a + v * b)) = v := by
    linear_combination v * hd - (a : ZMod Q.value) * hz
  constructor
  · apply (ZMod.isUnit_iff_coprime p Q.value).mp
    exact isUnit_of_mul_isUnit_left (heU.symm ▸ hu)
  · apply (ZMod.isUnit_iff_coprime q Q.value).mp
    exact isUnit_of_mul_isUnit_left (heV.symm ▸ hv)

/-- If either scale is not invertible modulo the modulus, the complete successor mass vanishes. -/
theorem ramanujan_successor_fiber_sum_of_not_coprime
    (Q : CGLPositiveModulus) {p q a b : ℕ} (hab : p * a = q * b + 1)
    (hbad : ¬ (Nat.Coprime p Q.value ∧ Nat.Coprime q Q.value)) :
    (∑ t : ZMod Q.value,
      d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value *
        d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value) = 0 := by
  classical
  simp only [d4BMRamanujanNaturalCoefficient, dif_pos Q.positive,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
    cglRamanujanAdditiveSum]
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro u hu
  rw [sum_comm]
  apply sum_eq_zero
  intro v hv
  have hne : u * (q : ZMod Q.value) + v * p ≠ 0 := by
    intro hz
    exact hbad (successor_character_resonance_forces_units Q hab
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hz)
  have he (t : ZMod Q.value) :
      ZMod.stdAddChar (u * ((a : ZMod Q.value) + (q : ZMod Q.value) * t)) *
        ZMod.stdAddChar (v * ((b : ZMod Q.value) + (p : ZMod Q.value) * t)) =
        ZMod.stdAddChar (u * (a : ZMod Q.value) + v * (b : ZMod Q.value)) *
          ZMod.stdAddChar ((u * (q : ZMod Q.value) + v * (p : ZMod Q.value)) * t) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [← mul_sum]
  have hs := RHTower.Sieve.sum_stdAddChar_mul Q.value
    (u * (q : ZMod Q.value) + v * (p : ZMod Q.value))
  rw [if_neg hne] at hs
  have hs' : (∑ t : ZMod Q.value,
      ZMod.stdAddChar ((u * (q : ZMod Q.value) + v * (p : ZMod Q.value)) * t)) = 0 := by
    simpa only [mul_comm, Nat.cast_zero] using hs
  rw [hs', mul_zero]

/-- Exact complete successor mass for every modulus and every successor seed. -/
theorem ramanujan_successor_fiber_sum_classified
    (Q : CGLPositiveModulus) {p q a b : ℕ} (hab : p * a = q * b + 1) :
    (∑ t : ZMod Q.value,
      d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value *
        d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value) =
      if Nat.Coprime p Q.value ∧ Nat.Coprime q Q.value then
        (Q.value : ℂ) * (ArithmeticFunction.moebius Q.value : ℂ) else 0 := by
  split_ifs with h
  · exact ramanujan_successor_fiber_sum Q h.1 h.2 hab
  · exact ramanujan_successor_fiber_sum_of_not_coprime Q hab h

/-- The same arithmetic selector governs the real profile jump amplitudes. -/
theorem ramanujan_successor_fiber_re_sum_classified
    (Q : CGLPositiveModulus) {p q a b : ℕ} (hab : p * a = q * b + 1) :
    (∑ t : ZMod Q.value,
      (d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value).re *
        (d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value).re) =
      if Nat.Coprime p Q.value ∧ Nat.Coprime q Q.value then
        (Q.value : ℝ) * (ArithmeticFunction.moebius Q.value : ℝ) else 0 := by
  split_ifs with h
  · exact ramanujan_successor_fiber_re_sum Q h.1 h.2 hab
  · have hc := congrArg Complex.re
      (ramanujan_successor_fiber_sum_of_not_coprime Q hab h)
    have him (n : ℕ) : (d4BMRamanujanNaturalCoefficient n Q.value).im = 0 := by
      rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum Q.positive]
      simp
    simpa only [Complex.re_sum, Complex.mul_re, him, zero_mul, sub_zero,
      Complex.zero_re] using hc

/-- The signed mean surviving the exact successor Fourier resonance condition. -/
def successorSectorMean (r p q : ℕ) : ℝ :=
  if Nat.Coprime p r ∧ Nat.Coprime q r then (ArithmeticFunction.moebius r : ℝ) else 0

/-- The actual residue-period mass equals the explicit arithmetic selector times the period. -/
theorem successorFiberAmplitude_sum_range_selected
    (Q : CGLPositiveModulus) {p q a b : ℕ} (hab : p * a = q * b + 1) :
    (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) =
      (Q.value : ℝ) * successorSectorMean Q.value p q := by
  rw [successorFiberAmplitude_sum_range_eq_zmod]
  change (∑ t : ZMod Q.value,
    (d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value).re *
      (d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value).re) = _
  rw [ramanujan_successor_fiber_re_sum_classified Q hab]
  unfold successorSectorMean
  split_ifs <;> simp

/-- Every successor sector has the classified harmonic mode and a uniform explicit remainder. -/
theorem abs_successor_sector_selected_harmonic_remainder_le
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (K : ℕ) :
    |ramanujanDilationLagSector Q.value p q (p * q * (Q.value * (K + 1))) 1 +
      ((K + 1 : ℕ) : ℝ) * Q.value * successorSectorMean Q.value p q /
        (((p * q * (Q.value * (K + 1)) : ℕ) : ℝ) + 1) -
      successorSectorMean Q.value p q / ((p * q : ℕ) : ℝ) * (harmonic K : ℝ)| ≤
      ∑ t ∈ range Q.value, |successorFiberAmplitude Q.value p q a b t| /
        ((p * (a + q * t) : ℕ) : ℝ) := by
  have h := abs_successor_sector_period_remainder_le Q hp hq ha haq hb hab K
  rw [successorFiberAmplitude_sum_range_selected Q hab] at h
  have hs : (Q.value : ℝ) * successorSectorMean Q.value p q /
      ((p * q * Q.value : ℕ) : ℝ) =
      successorSectorMean Q.value p q / ((p * q : ℕ) : ℝ) := by
    have hpR : (p : ℝ) ≠ 0 := by positivity
    have hqR : (q : ℝ) ≠ 0 := by positivity
    have hrR : (Q.value : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt Q.positive
    push_cast
    field_simp
  rw [hs] at h
  simpa only [mul_assoc] using h

/-- Unconditional capstone for adjacent scales, with an explicit positive successor seed. -/
theorem consecutive_scale_successor_harmonic_coupling (r n K : ℕ) :
    let R := r + 2
    let p := n + 2
    let q := n + 3
    |ramanujanDilationLagSector R p q (p * q * (R * (K + 1))) 1 +
      ((K + 1 : ℕ) : ℝ) * R * successorSectorMean R p q /
        (((p * q * (R * (K + 1)) : ℕ) : ℝ) + 1) -
      successorSectorMean R p q / ((p * q : ℕ) : ℝ) * (harmonic K : ℝ)| ≤
      ∑ t ∈ range R, |successorFiberAmplitude R p q p (n + 1) t| /
        ((p * (p + q * t) : ℕ) : ℝ) := by
  dsimp only
  exact abs_successor_sector_selected_harmonic_remainder_le
    ⟨r + 2, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by ring) K

end GaloisForLFunctions.BezoutValuationIncidence
