import GaloisForLFunctions.ArithmeticIncidencePositivity.QuarticGaugeSurplusPotential

/-!
# The first prime window for odd tests

Let `P` be an even plateau gauge vanishing outside `(−R, R)` with `2R < log 3`. Only the prime `2`
acts: the prime jumps of the gauge representation reduce to
`Λ(2)/√2 · ∫ P(x) P(x + log 2)(F(x) − F(x + log 2))²` (`signedJumpEnergy_eq_arch_add_two`) and the
prime part of the potential to `Λ(2)/√2 · (P(x + log 2) + P(x − log 2))` (`profilePrimeSum_eq_two`).
For a test with `P = 1` on its support the two combine into an autocorrelation
(`gaugeJumpProfile_sub_primePotential_eq`):

    ∫ P(x)P(x + L)(F(x) − F(x + L))² − ∫ F² P (P(· + L) + P(· − L)) = −2 ∫ F(x) F(x + L) dx.

For an odd test supported in `[−r, r]` the product `F(x)F(x + L)` lives on the crossing pairs
`(−a, L − a)` of the edge strip `S = [L − r, r]`, and `∫ F(x) F(x + L) ≤ ∫_S F²`
(`integral_mul_shift_le_strip`): past `½ log 2` the atom `Λ(2)/√2` costs at most its own size per unit
of mass on the strip, and nothing elsewhere. The archimedean potential of the plateau
(`neg_poleFreeWeilOperator_add_primeSum_ge`) is unchanged by the prime.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- `Λ(2)/√2 = log 2/√2 ≤ 0.4902`. -/
theorem vonMangoldtAtom_two_bounds : 0 ≤ vonMangoldtAtom 2 ∧ vonMangoldtAtom 2 ≤ 4902 / 10000 := by
  unfold vonMangoldtAtom
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hs : (14142 / 10000 : ℝ) ≤ Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_two_gt_d9
  push_cast at hs ⊢
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- **Only the prime `2` jumps** in a window gauge with `2R < log 3`. -/
theorem signedJumpEnergy_eq_arch_add_two {M F : ℝ → ℝ} {R : ℝ} (hzero : ∀ y, R ≤ |y| → M y = 0)
    (hR : 2 * R < Real.log 3) :
    signedJumpEnergy M F = (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M F t) +
      vonMangoldtAtom 2 * gaugeJumpProfile M F (Real.log 2) := by
  unfold signedJumpEnergy
  congr 1
  rw [tsum_eq_single 2 (fun n hn => ?_)]
  · simp only [Nat.cast_ofNat]; rfl
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · unfold vonMangoldtAtom; rw [if_neg (by omega), zero_mul]
    · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hlog : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) h3
      rw [show (∫ x, signedShiftJump M F (Real.log n) x) = gaugeJumpProfile M F (Real.log n) from rfl,
        gaugeJumpProfile_eq_zero_of_ge hzero (by linarith), mul_zero]

/-- **Only the prime `2` acts on the potential** of a window gauge with `2R < log 3`. -/
theorem profilePrimeSum_eq_two {M : ℝ → ℝ} {R x : ℝ} (hsupp : ∀ y, R ≤ |y| → M y = 0)
    (hR : 2 * R < Real.log 3) (hx : |x| < R) :
    profilePrimeSum M x = vonMangoldtAtom 2 * (M (x + Real.log 2) + M (x - Real.log 2)) := by
  unfold profilePrimeSum
  rw [tsum_eq_single 2 (fun n hn => ?_)]
  · norm_num
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · unfold vonMangoldtAtom; rw [if_neg (by omega), zero_mul]
    · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hlog : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) h3
      have hx1 := le_abs_self x
      have hx2 := neg_abs_le x
      rw [hsupp (x + Real.log n) ?_, hsupp (x - Real.log n) ?_, add_zero, mul_zero]
      · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith

/-- **The plateau potential with the prime returned.** At a plateau point,
`−𝒲M(x) + (prime part) ≥ Ω(R − x) + Ω(R + x) − 2E(0) − (γ + log π)`, with no restriction on `R`. -/
theorem neg_poleFreeWeilOperator_add_primeSum_ge {M : ℝ → ℝ} {K R : ℝ} (hMc : Continuous M)
    (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|) (hle : ∀ y, M y ≤ 1)
    (hsupp : ∀ y, R ≤ |y| → M y = 0) {x : ℝ} (hx : |x| < R) (hMx : M x = 1) :
    archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
        2 * archConstantReal ≤ -poleFreeWeilOperator M x + profilePrimeSum M x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  obtain ⟨hIa, -⟩ := integral_one_sided_window_ge ha
  obtain ⟨hIb, -⟩ := integral_one_sided_window_ge hb
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) ≤
        profileArchTerm M x u := by
    intro u hu
    have hω := archLevyDensity_pos hu
    have h1 : M (x + u) ≤ if u ≤ R - x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_pos (by linarith [le_abs_self x] : 0 < x + u)]; linarith)).le
    have h2 : M (x - u) ≤ if u ≤ R + x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_neg (by linarith [neg_abs_le x] : x - u < 0)]; linarith)).le
    unfold profileArchTerm
    rw [hMx]
    have hm1 := mul_le_mul_of_nonneg_left h1 hω.le
    have hm2 := mul_le_mul_of_nonneg_left h2 hω.le
    split_ifs at hm1 hm2 ⊢ <;> nlinarith
  have hmono := setIntegral_mono_on (f := fun u =>
      (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u))
    (hIa.add hIb) (integrableOn_profileArchTerm hMc hLip x) measurableSet_Ioi hpt
  rw [integral_add hIa hIb, integral_one_sided_window_eq ha, integral_one_sided_window_eq hb] at hmono
  unfold poleFreeWeilOperator
  rw [hMx]
  linarith

/-- The prime part of the potential of an even gauge is even. -/
theorem profilePrimeSum_neg {M : ℝ → ℝ} (hMe : ∀ y, M (-y) = M y) (x : ℝ) :
    profilePrimeSum M (-x) = profilePrimeSum M x := by
  unfold profilePrimeSum
  refine tsum_congr fun n => ?_
  rw [show -x + Real.log n = -(x - Real.log n) by ring,
    show -x - Real.log n = -(x + Real.log n) by ring, hMe, hMe]
  ring

/-- **The prime atom on a test.** If `M = 1` on the support of `F`, the prime jump at shift `L` minus
the prime potential is `−2 ∫ F(x) F(x + L) dx`. -/
theorem gaugeJumpProfile_sub_primePotential_eq {M F : ℝ → ℝ} (hM : Continuous M) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hFM : ∀ x, F x ≠ 0 → M x = 1) (L : ℝ) :
    gaugeJumpProfile M F L - ∫ x, F x ^ 2 * M x * (M (x + L) + M (x - L)) =
      -2 * ∫ x, F x * F (x + L) := by
  have hFs : HasCompactSupport fun x => F (x + L) :=
    hFc.comp_homeomorph (Homeomorph.addRight L)
  have hpt1 : ∀ x, signedShiftJump M F L x =
      F x ^ 2 * M (x + L) + F (x + L) ^ 2 * M x - 2 * (F x * F (x + L)) := fun x => by
    unfold signedShiftJump
    by_cases h1 : F x = 0
    · by_cases h2 : F (x + L) = 0
      · rw [h1, h2]; ring
      · rw [h1, hFM _ h2]; ring
    · by_cases h2 : F (x + L) = 0
      · rw [h2, hFM _ h1]; ring
      · rw [hFM _ h1, hFM _ h2]; ring
  have hpt2 : ∀ x, F x ^ 2 * M x * (M (x + L) + M (x - L)) =
      F x ^ 2 * M (x + L) + F x ^ 2 * M (x - L) := fun x => by
    by_cases h1 : F x = 0
    · rw [h1]; ring
    · rw [hFM _ h1]; ring
  have i1 : Integrable fun x => F x ^ 2 * M (x + L) :=
    ((hF.pow 2).mul (hM.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (by have := hFc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num); exact this.mul_right)
  have i2 : Integrable fun x => F (x + L) ^ 2 * M x :=
    (((hF.comp (continuous_id.add continuous_const)).pow 2).mul hM).integrable_of_hasCompactSupport
      (by have := hFs.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num); exact this.mul_right)
  have i3 : Integrable fun x => F x * F (x + L) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have i4 : Integrable fun x => F x ^ 2 * M (x - L) :=
    ((hF.pow 2).mul (hM.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (by have := hFc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num); exact this.mul_right)
  have htr : (∫ x, F (x + L) ^ 2 * M x) = ∫ x, F x ^ 2 * M (x - L) := by
    have := integral_add_right_eq_self (μ := volume) (fun x => F x ^ 2 * M (x - L)) L
    simp only [add_sub_cancel_right] at this
    exact this
  unfold gaugeJumpProfile
  simp_rw [hpt1, hpt2]
  have i12 : Integrable fun x => F x ^ 2 * M (x + L) + F (x + L) ^ 2 * M x := i1.add i2
  rw [integral_sub i12 (i3.const_mul 2), integral_add i1 i2, integral_add i1 i4,
    MeasureTheory.integral_const_mul, htr]
  ring

/-- **The odd strip bound.** For an odd `F` supported in `[−r, r]`,
`∫ F(x) F(x + L) dx ≤ ∫_{[L − r, r]} F²`. -/
theorem integral_mul_shift_le_strip {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) {r L : ℝ} (hsupp : ∀ x, r < |x| → F x = 0) :
    (∫ x, F x * F (x + L)) ≤ ∫ x in Icc (L - r) r, F x ^ 2 := by
  set S := Icc (L - r) r with hS
  set g : ℝ → ℝ := S.indicator fun x => F x ^ 2 with hg
  have hgi : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hF.pow 2).integrableOn_Icc
  have hpt : ∀ x, F x * F (x + L) ≤ 1 / 2 * g (-x) + 1 / 2 * g (x + L) := by
    intro x
    by_cases h : F x * F (x + L) = 0
    · rw [h]
      have h1 : 0 ≤ g (-x) := Set.indicator_nonneg (fun y _ => sq_nonneg _) _
      have h2 : 0 ≤ g (x + L) := Set.indicator_nonneg (fun y _ => sq_nonneg _) _
      linarith
    · have h1 : F x ≠ 0 := left_ne_zero_of_mul h
      have h2 : F (x + L) ≠ 0 := right_ne_zero_of_mul h
      have hx : |x| ≤ r := not_lt.mp fun hh => h1 (hsupp x hh)
      have hxL : |x + L| ≤ r := not_lt.mp fun hh => h2 (hsupp _ hh)
      rw [abs_le] at hx hxL
      have m1 : -x ∈ S := ⟨by linarith [hxL.2], by linarith [hx.1]⟩
      have m2 : x + L ∈ S := ⟨by linarith [hx.1], hxL.2⟩
      rw [hg, Set.indicator_of_mem m1, Set.indicator_of_mem m2, hodd, neg_sq]
      nlinarith [sq_nonneg (F x - F (x + L))]
  have hi1 : Integrable fun x => g (-x) := hgi.comp_neg
  have hi2 : Integrable fun x => g (x + L) := hgi.comp_add_right L
  have hi3 : Integrable fun x => F x * F (x + L) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsum : Integrable fun x => 1 / 2 * g (-x) + 1 / 2 * g (x + L) :=
    (hi1.const_mul (1 / 2)).add (hi2.const_mul (1 / 2))
  have hmono := integral_mono hi3 hsum hpt
  rw [integral_add (hi1.const_mul (1 / 2)) (hi2.const_mul (1 / 2)), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_neg_eq_self (fun x => g x) volume,
    integral_add_right_eq_self (μ := volume) (fun x => g x) L, hg,
    integral_indicator measurableSet_Icc] at hmono
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
