import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCharacterWindowsAreGradedByParity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.JointPeriodicWindowMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries

/-!
# Primitive character windows are graded by conductor

A primitive-character Fourier coefficient, computed at any common period,
can be nonzero only at a frequency whose reduced denominator is the conductor.
Distinct conductors therefore have disjoint spectra. For nonprincipal primitive
characters, their exact critical-curve Weil cross term vanishes at second order, including the literal tilted spline
on every positive canonical critical schedule.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem sum_period_blocks (f : ℕ → ℂ) (q d : ℕ) :
    (∑ n ∈ range (q*d), f n) = ∑ l ∈ range d, ∑ b ∈ range q, f (b+q*l) := by
  induction d with
  | zero => simp only [mul_zero, range_zero, sum_empty]
  | succ d ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply sum_congr rfl
    intro b _
    rw [Nat.add_comm]

/-- Passing to a multiple period inserts zero Fourier modes between the old modes. -/
theorem twistCoeff_mul_period {χ : ℕ → ℝ} {q d : ℕ}
    (hq : 0<q) (hd : 0<d) (hper : ∀ n, χ (n+q)=χ n) (k : ℕ) :
    twistCoeff χ (q*d) k =
      if d ∣ k then (d : ℂ) * twistCoeff χ q (k/d) else 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hphase (b l : ℕ) :
      Complex.exp (2*Real.pi*Complex.I*((k : ℂ)*(b+q*l)/(q*d))) =
        Complex.exp (2*Real.pi*Complex.I*((k : ℂ)*b/(q*d))) *
          Complex.exp (2*Real.pi*Complex.I*((l : ℂ)*k/d)) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp [hqC, hdC]
  have hsum : (∑ l ∈ range d,
      Complex.exp (2*Real.pi*Complex.I*((l : ℂ)*k/d))) =
        if d ∣ k then (d : ℂ) else 0 := by
    simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using
      (sum_range_cexp_int hd (k : ℤ))
  have hfactor : twistCoeff χ (q*d) k =
      (∑ b ∈ range q, (χ b : ℂ)*
        Complex.exp (2*Real.pi*Complex.I*((k : ℂ)*b/(q*d)))) *
          (if d ∣ k then (d : ℂ) else 0) := by
    unfold twistCoeff
    rw [sum_period_blocks, sum_comm]
    simp_rw [periodic_add_mul hper, Nat.cast_add, Nat.cast_mul, hphase,
      ← mul_assoc, ← Finset.mul_sum, hsum]
    rw [Finset.sum_mul]
  rw [hfactor]
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left j hd]
    unfold twistCoeff
    rw [mul_comm (d : ℂ)]
    congr 1
    apply sum_congr rfl
    intro b _
    congr 2
    push_cast
    field_simp [hqC, hdC]
  · exact mul_zero _

/-- Primitive character Fourier support consists of reduced residues. -/
theorem coprime_of_twistCoeff_charTwist_ne_zero {q : ℕ} [NeZero q]
    (c : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (j : ℕ)
    (hne : twistCoeff (charTwist c ψ) q j ≠ 0) : Nat.Coprime j q := by
  by_contra hj
  have hz : ψ (j : ZMod q) = 0 :=
    MulChar.map_nonunit ψ (fun h => hj ((ZMod.isUnit_iff_coprime j q).mp h))
  apply hne
  rw [twistCoeff_charTwist c hψ, hz]
  simp only [map_zero, zero_mul, mul_zero, add_zero, zero_div]

/-- A nonzero primitive-character Fourier mode has its conductor as reduced denominator. -/
theorem reduced_denominator_of_charTwist_ne_zero {q M : ℕ} [NeZero q]
    (hM : 0<M) (hqM : q ∣ M) (c : ℂ) {ψ : DirichletCharacter ℂ q}
    (hψ : ψ.IsPrimitive) (k : ℕ)
    (hne : twistCoeff (charTwist c ψ) M k ≠ 0) : M / Nat.gcd M k = q := by
  obtain ⟨d, rfl⟩ := hqM
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hd : 0<d := by
    by_contra hd
    have hz : d=0 := by omega
    simp only [hz, mul_zero, lt_self_iff_false] at hM
  have hper (n : ℕ) : charTwist c ψ (n+q) = charTwist c ψ n := by
    simp [charTwist]
  rw [twistCoeff_mul_period hq hd hper] at hne
  have hdk : d ∣ k := by
    by_contra h
    exact hne (if_neg h)
  rw [if_pos hdk] at hne
  have hj := coprime_of_twistCoeff_charTwist_ne_zero c hψ (k/d)
    (fun h => hne (by rw [h, mul_zero]))
  obtain ⟨j, rfl⟩ := hdk
  rw [Nat.mul_div_cancel_left j hd] at hj
  rw [Nat.mul_comm q d, Nat.gcd_mul_left, hj.symm.gcd_eq_one, mul_one,
    Nat.mul_div_cancel_left q hd]

/-- Primitive characters of distinct conductors have disjoint cross spectra at every common period. -/
theorem crossPower_charTwist_distinct_conductors {q₁ q₂ M : ℕ}
    [NeZero q₁] [NeZero q₂] (hM : 0<M) (h₁ : q₁ ∣ M) (h₂ : q₂ ∣ M)
    (hq : q₁ ≠ q₂) (c₁ c₂ : ℂ) {ψ₁ : DirichletCharacter ℂ q₁}
    {ψ₂ : DirichletCharacter ℂ q₂} (hp₁ : ψ₁.IsPrimitive) (hp₂ : ψ₂.IsPrimitive)
    (k : ℕ) : crossPower (charTwist c₁ ψ₁) (charTwist c₂ ψ₂) M k = 0 := by
  by_cases hz₁ : twistCoeff (charTwist c₁ ψ₁) M k = 0
  · simp only [crossPower, hz₁, zero_mul, Complex.zero_re, zero_div]
  by_cases hz₂ : twistCoeff (charTwist c₂ ψ₂) M k = 0
  · simp only [crossPower, hz₂, map_zero, mul_zero, Complex.zero_re, zero_div]
  exact (hq ((reduced_denominator_of_charTwist_ne_zero hM h₁ c₁ hp₁ k hz₁).symm.trans
    (reduced_denominator_of_charTwist_ne_zero hM h₂ c₂ hp₂ k hz₂))).elim

/-- Distinct primitive conductors are orthogonal in the complete critical-curve second order. -/
theorem cross_layer_charTwist_distinct_conductors {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {φ h : ℝ → ℝ} {A : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (c₁ c₂ : ℂ) {ψ₁ : DirichletCharacter ℂ q₁} {ψ₂ : DirichletCharacter ℂ q₂}
    (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive)
    (hq₁ : 1<q₁) (hq₂ : 1<q₂) (hne : q₁ ≠ q₂) :
    Tendsto (fun N : ℕ => (c N)⁻¹ *
        (weilCross (atomicTest N (twistedWeights h (charTwist c₁ ψ₁) N) (atomDilate φ (c N / N)))
          (atomicTest N (twistedWeights h (charTwist c₂ ψ₂) N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop (𝓝 0) := by
  have hM : 0<q₁*q₂ := Nat.mul_pos (by omega) (by omega)
  have h₁ := (meanZeroTwist_charTwist c₁ (ne_one_of_isPrimitive hψ₁ hq₁)).of_dvd
    hM (dvd_mul_right q₁ q₂)
  have h₂ := (meanZeroTwist_charTwist c₂ (ne_one_of_isPrimitive hψ₂ hq₂)).of_dvd
    hM (dvd_mul_left q₂ q₁)
  have hlim := cross_layer_criticalCurve hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit h₁ h₂
  simp_rw [crossPower_charTwist_distinct_conductors hM (dvd_mul_right q₁ q₂)
    (dvd_mul_left q₂ q₁) hne c₁ c₂ hψ₁ hψ₂, zero_mul, tsum_zero, mul_zero, zero_mul] at hlim
  exact hlim

/-- For the literal tilted spline, distinct primitive conductors decouple at every positive
critical multiple. All profile-tail and curve inputs are supplied by the source theorems. -/
theorem cross_layer_charTwist_distinct_conductors_tilted
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] {h : ℝ → ℝ} {A K : ℝ}
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hK : 0<K)
    (c₁ c₂ : ℂ) {ψ₁ : DirichletCharacter ℂ q₁} {ψ₂ : DirichletCharacter ℂ q₂}
    (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive)
    (hq₁ : 1<q₁) (hq₂ : 1<q₂) (hne : q₁ ≠ q₂) :
    Tendsto (fun N : ℕ => (canonicalCriticalCurve K N)⁻¹ *
      (weilCross
        (atomicTest N (twistedWeights h (charTwist c₁ ψ₁) N)
          (atomDilate tiltedUnitSpline (canonicalCriticalCurve K N / N)))
        (atomicTest N (twistedWeights h (charTwist c₂ ψ₂) N)
          (atomDilate tiltedUnitSpline (canonicalCriticalCurve K N / N)))) /
        ∫ u, atomDilate tiltedUnitSpline (canonicalCriticalCurve K N / N) u ^ 2)
      atTop (𝓝 0) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit : Tendsto (fun N : ℕ =>
      canonicalCriticalCurve K N ^ ((7 : ℝ)+1) / Real.log N) atTop (𝓝 K) := by
    refine (tendsto_canonicalCriticalCurve_pow_eight hK).congr fun N => ?_
    rw [show (7 : ℝ)+1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := cross_layer_charTwist_distinct_conductors contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num)
    hC tiltedUnitSpline_decay (β := 7) (by norm_num)
    ArithmeticDegenerationTheory.tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline
    hh hA hsupp (one_le_canonicalCriticalCurve K) hK hcrit c₁ c₂ hψ₁ hψ₂ hq₁ hq₂ hne
  exact hlim.congr fun N => by ring


end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
