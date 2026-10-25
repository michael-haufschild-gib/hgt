import GaloisForLFunctions.BezoutValuationIncidence.FixedStripsControlAllVaughanFluctuationReceivers
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicRemaindersInAllVaughanRows
import GaloisForLFunctions.BezoutValuationIncidence.PronicGramErrorsAroundASmoothRankOneTerm

/-!
Uniform power errors in the smooth-subtracted Vaughan Gram are equivalent
to a fixed zero-free strip. Receiver power bounds control every matrix entry;
the extreme cutoff reads the harmonic sum in the converse direction.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A fixed strip gives one common power saving for all five smooth Vaughan remainders. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_power_of_fixed_strip
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hΘ : zetaZeroAbscissa < 1) :
    ∃ γ B : ℝ, 0 < γ ∧ ε + γ < 1 / 2 ∧ 0 ≤ B ∧
      ∀ U V T : ℕ, 1 ≤ T → ∀ i : Fin 5,
        pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n i) T ≤
          B * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  obtain ⟨γ, C, hγ, hεγ, hC, hsrc⟩ :=
    exists_uniform_vaughan_source_pronicNorm_power_of_fixed_strip hε hε2 hΘ
  let K : ℝ := Real.sqrt (1 + 1 / ε) *
    (floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|)
  have hε1 : ε < 1 := by linarith only [hε2]
  have hK : 0 ≤ K :=
    (pronicNorm_nonneg (subHalfRemainder ε) 0).trans (pronicNorm_subHalfRemainder_le hε hε1 0)
  refine ⟨γ, 4 * C + K + 1 / 2, hγ, hεγ, by positivity, fun U V T hT i => ?_⟩
  let P : ℝ := Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ)))
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hP1 : 1 ≤ P := by
    have hp := Real.one_le_rpow (by exact_mod_cast hT : (1 : ℝ) ≤ T)
      (by linarith only [hεγ] : 0 ≤ 1 - 2 * (ε + γ))
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
  have hI : pronicNorm (pmBezoutInteriorPrefix ε) T ≤ C * P := (hsrc U V T hT).2.2
  have h0 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 0) T ≤ C * P := by
    have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 0) =
        patternPrefix ε (Sieve.truncatedMoebius U) := by
      funext n
      change pmPronicVaughanCentredPiece ε U V n 0 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
          (n : ℝ) ^ (1 - ε) = _
      simp only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
        pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε]
    rw [heq]
    exact (hsrc U V T hT).2.1
  have h1 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 1) T ≤ C * P := by
    have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 1) =
        patternPrefix ε (Sieve.truncatedMoebius V) := by
      funext n
      change pmPronicVaughanCentredPiece ε V U n 0 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
          (n : ℝ) ^ (1 - ε) = _
      simp only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
        pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε]
    rw [heq]
    exact (hsrc V U T hT).2.1
  have h2 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) T ≤ (K + C) * P := by
    let f : ℕ → ℝ := fun n =>
      -(deningerHarmonicPartial U * deningerHarmonicPartial V) * subHalfRemainder ε n
    have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
        (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
    have hunit : pronicNorm f T ≤ K := by
      dsimp only [f]
      rw [pronicNorm_smul, abs_neg]
      simpa only [one_mul] using mul_le_mul hcoeff (pronicNorm_subHalfRemainder_le hε hε1 T)
        (pronicNorm_nonneg _ _) zero_le_one
    have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) =
        fun n => f n + (-1) * pmVaughanConvolutionFluctuationPrefix ε U V n := by
      funext n
      rw [pmPronicVaughanSmoothRemainder_smallSmall_eq hε]
      dsimp only [f]
      ring
    rw [heq]
    have h := pronicNorm_add_le f (fun n => (-1) * pmVaughanConvolutionFluctuationPrefix ε U V n) T
    have hneg : pronicNorm (fun n => (-1) * pmVaughanConvolutionFluctuationPrefix ε U V n) T =
        pronicNorm (pmVaughanConvolutionFluctuationPrefix ε U V) T := by
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul]
    rw [hneg] at h
    exact h.trans ((add_le_add
      (hunit.trans (le_mul_of_one_le_right hK hP1)) (hsrc U V T hT).1).trans_eq (by ring))
  have h4 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 4) T ≤ (1 / 2) * P := by
    have hbound : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 4) T ≤ 1 / 2 := by
      apply pronicNorm_le_of_abs_le (by norm_num)
      intro n
      change |pmPronicVaughanCentredPiece ε U V n 4 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
          (n : ℝ) ^ (1 - ε)| ≤ 1 / 2
      simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece] using
        abs_pmPronicVaughanPiece_pole_sub_mean_le hε.le U V n
    exact hbound.trans (le_mul_of_one_le_right (by norm_num) hP1)
  fin_cases i
  · exact h0.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hK]) hP)
  · exact h1.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hK]) hP)
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith only [hC]) hP)
  · exact (pronicNorm_pmPronicVaughanSmoothRemainder_large_le ε U V T).trans
      ((add_le_add hI (add_le_add h0 (add_le_add h1 (add_le_add h2 h4)))).trans_eq (by ring))
  · exact h4.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hK]) hP)

private theorem abs_vaughan_smooth_power_coefficient_le (ε : ℝ) (U V : ℕ) (i : Fin 5) :
    |subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      pmPronicVaughanSmoothSigns i| ≤ |subHalfZetaCoeff ε| := by
  have hs : |pmPronicVaughanSmoothSigns i| ≤ 1 := by
    fin_cases i <;> norm_num [pmPronicVaughanSmoothSigns]
  have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
      (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
  have hK : |subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
      |subHalfZetaCoeff ε| := by
    rw [mul_assoc, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hcoeff
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans hK

/-- A fixed zero-free strip supplies a uniform power error for the full smooth Vaughan Gram law. -/
theorem exists_uniform_pmPronicVaughanResidualGramError_power_of_fixed_strip
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hΘ : zetaZeroAbscissa < 1) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanResidualGramError ε U V T i j| ≤ C * (T : ℝ) ^ (-γ) := by
  obtain ⟨γ, B, hγ, hεγ, hB, hR⟩ :=
    exists_uniform_pmPronicVaughanSmoothRemainder_power_of_fixed_strip hε hε2 hΘ
  obtain ⟨D, hD, herror⟩ := exists_smooth_power_pronicEnergy_bounded_error hε hε2
  let β : ℝ := 1 - 2 * ε
  let c : ℝ := |subHalfZetaCoeff ε|
  let H : ℝ := Real.sqrt (1 + 1 / β)
  have hβ : 0 < β := by dsimp only [β]; linarith only [hε2]
  have hβγ : 0 < β - γ := by dsimp only [β]; linarith only [hεγ, hγ]
  have hc : 0 ≤ c := abs_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  refine ⟨γ, 2 * c * H * B + B ^ 2 + c ^ 2 * D, hγ, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with T hT U V i j
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  let P : ℝ := (T : ℝ) ^ β
  let R : ℝ := (T : ℝ) ^ (1 - 2 * (ε + γ))
  let Q : ℝ := (T : ℝ) ^ (β - γ)
  let h : ℕ → ℝ := fun n => (n : ℝ) ^ (1 - ε)
  let r : Fin 5 → ℕ → ℝ := fun k n => pmPronicVaughanSmoothRemainder ε U V n k
  let a : Fin 5 → ℝ := fun k =>
    subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      pmPronicVaughanSmoothSigns k
  have hP : 0 < P := Real.rpow_pos_of_pos hT0 β
  have hR0 : 0 ≤ R := Real.rpow_nonneg hT0.le _
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hT1 hβγ.le
  have hRQ : R ≤ Q := Real.rpow_le_rpow_of_exponent_le hT1
    (by dsimp only [β]; linarith only [hγ])
  have hcross : Real.sqrt P * Real.sqrt R = Q := by
    dsimp only [P, R, Q]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le,
      ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
    congr 1
    dsimp only [β]
    ring
  have ha (k : Fin 5) : |a k| ≤ c := abs_vaughan_smooth_power_coefficient_le ε U V k
  have hnorm : pronicNorm h T ≤ H * Real.sqrt P := pronicNorm_smooth_power_le hε hε2 hT
  have hr (k : Fin 5) : pronicNorm (r k) T ≤ B * Real.sqrt R := hR U V T hT k
  have hGram : pmPronicVaughanCentredGram ε U V T i j =
      ∑ n ∈ Icc 1 T, (a i * h n + r i n) * (a j * h n + r j n) /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    unfold pmPronicVaughanCentredGram
    apply sum_congr rfl
    intro n _hn
    simp only [a, h, r, pmPronicVaughanSmoothRemainder, pronicSeq, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  have hpair := abs_pronicGram_sub_rankOne_le (a i) (a j) h (r i) (r j) T
  rw [← hGram] at hpair
  have hmixed (k l : Fin 5) :
      |a k| * pronicNorm h T * pronicNorm (r l) T ≤ c * H * B * Q := by
    calc
      _ ≤ (c * (H * Real.sqrt P)) * (B * Real.sqrt R) :=
        mul_le_mul (mul_le_mul (ha k) hnorm (pronicNorm_nonneg _ _) hc)
          (hr l) (pronicNorm_nonneg _ _) (by positivity)
      _ = c * H * B * (Real.sqrt P * Real.sqrt R) := by ring
      _ = _ := by rw [hcross]
  have hres : pronicNorm (r i) T * pronicNorm (r j) T ≤ B ^ 2 * Q := by
    calc
      _ ≤ (B * Real.sqrt R) * (B * Real.sqrt R) :=
        mul_le_mul (hr i) (hr j) (pronicNorm_nonneg _ _) (by positivity)
      _ = B ^ 2 * R := by rw [← pow_two, mul_pow, Real.sq_sqrt hR0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hRQ (sq_nonneg B)
  have hmass : |a i * a j| ≤ c ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (ha i) (ha j) (abs_nonneg _) hc
  have hsmooth : |a i * a j * (pronicNorm h T ^ 2 - P / β)| ≤ c ^ 2 * D * Q := by
    rw [abs_mul]
    exact (mul_le_mul hmass (herror T hT) (abs_nonneg _) (sq_nonneg c)).trans
      (le_mul_of_one_le_right (by positivity) hQ1)
  have heq : pmPronicVaughanCentredGram ε U V T i j - a i * a j * P / β =
      (pmPronicVaughanCentredGram ε U V T i j - a i * a j * pronicNorm h T ^ 2) +
        a i * a j * (pronicNorm h T ^ 2 - P / β) := by ring
  have hfinal : |pmPronicVaughanCentredGram ε U V T i j - a i * a j * P / β| ≤
      (2 * c * H * B + B ^ 2 + c ^ 2 * D) * Q := by
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add
      (hpair.trans (add_le_add (add_le_add (hmixed i j) (hmixed j i)) hres))
      hsmooth).trans_eq (by ring))
  have hrel : |pmPronicVaughanCentredGram ε U V T i j / P - a i * a j / β| ≤
      (2 * c * H * B + B ^ 2 + c ^ 2 * D) * (T : ℝ) ^ (-γ) := by
    rw [show pmPronicVaughanCentredGram ε U V T i j / P - a i * a j / β =
      (pmPronicVaughanCentredGram ε U V T i j - a i * a j * P / β) / P by
        field_simp [hP.ne', hβ.ne'] <;> ring,
      abs_div, abs_of_pos hP]
    refine (div_le_div_of_nonneg_right hfinal hP.le).trans_eq ?_
    dsimp only [Q, P]
    rw [mul_div_assoc, ← Real.rpow_sub hT0, show β - γ - β = -γ by ring]
  have hmodel : a i * a j =
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j := by
    dsimp only [a]
    ring
  rw [hmodel] at hrel
  simpa only [pmPronicVaughanResidualGramError, ← deningerHarmonicPartial_eq_sum_Icc,
    div_mul_eq_mul_div, P, β] using hrel

/-- Two extreme-cutoff residual entries already force a fixed strip from any common power bound. -/
theorem zetaZeroAbscissa_lt_one_of_extreme_vaughan_residual_power
    {ε δ C : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hE : ∀ᶠ T : ℕ in atTop,
      |pmPronicVaughanResidualGramError ε 1 T T 2 3| ≤ C * (T : ℝ) ^ (-δ) ∧
      |pmPronicVaughanResidualGramError ε 1 T T 2 2| ≤ C * (T : ℝ) ^ (-δ)) :
    zetaZeroAbscissa < 1 := by
  let k : ℝ := (pmPowerDampedDivisorDensity ε).re * (subHalfZetaCoeff ε) ^ 2 / (1 - 2 * ε)
  have hk : 0 < k := div_pos (mul_pos (pmPowerDampedDivisorDensity_re_pos hε)
    (sq_pos_of_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2]))))
      (by linarith only [hε2])
  let B : ℝ := C * (1 + |(pmPowerDampedDivisorDensity ε).re - 1|) / k
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let η : ℝ := min (δ / 2) (1 / 2)
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hevent : ∀ᶠ T : ℕ in atTop, ∀ _i : Unit,
      |deningerHarmonicPartial T| ≤ Real.sqrt B * (T : ℝ) ^ (1 - (1 + η)) := by
    filter_upwards [hE, eventually_ge_atTop 1] with T hET hT _i
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hid : k * deningerHarmonicPartial T ^ 2 =
        pmPronicVaughanResidualGramError ε 1 T T 2 3 -
          ((pmPowerDampedDivisorDensity ε).re - 1) *
            pmPronicVaughanResidualGramError ε 1 T T 2 2 := by
      rw [pmPronicVaughanResidualGramError_harmonic_identity hε,
        ← deningerHarmonicPartial_eq_sum_Icc]
      dsimp only [k]
      ring
    have hbound : k * deningerHarmonicPartial T ^ 2 ≤
        C * (1 + |(pmPowerDampedDivisorDensity ε).re - 1|) * (T : ℝ) ^ (-δ) := by
      calc
        _ = |pmPronicVaughanResidualGramError ε 1 T T 2 3 -
            ((pmPowerDampedDivisorDensity ε).re - 1) *
              pmPronicVaughanResidualGramError ε 1 T T 2 2| := by
          rw [← hid, abs_of_nonneg (mul_nonneg hk.le (sq_nonneg _))]
        _ ≤ |pmPronicVaughanResidualGramError ε 1 T T 2 3| +
            |((pmPowerDampedDivisorDensity ε).re - 1) *
              pmPronicVaughanResidualGramError ε 1 T T 2 2| := abs_sub _ _
        _ ≤ C * (T : ℝ) ^ (-δ) + |(pmPowerDampedDivisorDensity ε).re - 1| *
            (C * (T : ℝ) ^ (-δ)) := by
          rw [abs_mul]
          exact add_le_add hET.1 (mul_le_mul_of_nonneg_left hET.2 (abs_nonneg _))
        _ = _ := by ring
    have hsq : deningerHarmonicPartial T ^ 2 ≤ B * (T : ℝ) ^ (-δ) := by
      have hdiv := (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hbound)
      exact hdiv.trans_eq (by dsimp only [B]; ring)
    have hsqrt : |deningerHarmonicPartial T| ≤ Real.sqrt B * (T : ℝ) ^ (-δ / 2) := by
      have h := Real.sqrt_le_sqrt hsq
      have hroot : Real.sqrt ((T : ℝ) ^ (-δ)) = (T : ℝ) ^ (-δ / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le,
          show -δ * (1 / 2) = -δ / 2 by ring]
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hB, hroot] at h
      exact h
    refine hsqrt.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg B))
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hηδ])
  have hlinear (_i : Unit) (n : ℕ) (hn : 1 ≤ n) :
      |deningerHarmonicPartial n| ≤ (1 : ℝ) * n := by
    simpa only [one_mul] using (abs_deningerHarmonicPartial_le_one n).trans
      (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  obtain ⟨K, hK, hglobal⟩ := exists_uniform_rpow_bound_of_eventually
    (f := fun _i : Unit => deningerHarmonicPartial) (ε := 1 + η)
    (by positivity) (by norm_num) (Real.sqrt_nonneg B) hlinear hevent
  apply zetaZeroAbscissa_lt_one_of_harmonic_power hη hη1 hK
  intro n hn
  simpa only [show 1 - (1 + η) = -η by ring] using hglobal () n hn

/-- A uniform power rate in the complete smooth Vaughan Gram law is exactly a fixed zero-free strip. -/
theorem zetaZeroAbscissa_lt_one_iff_uniform_pmPronicVaughanResidualGramError_power
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    zetaZeroAbscissa < 1 ↔ ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ i j : Fin 5,
        |pmPronicVaughanResidualGramError ε U V T i j| ≤ C * (T : ℝ) ^ (-δ) := by
  constructor
  · exact exists_uniform_pmPronicVaughanResidualGramError_power_of_fixed_strip hε hε2
  · rintro ⟨δ, C, hδ, hC, h⟩
    apply zetaZeroAbscissa_lt_one_of_extreme_vaughan_residual_power hε hε2 hδ hC
    exact h.mono fun T hT => ⟨hT 1 T 2 3, hT 1 T 2 2⟩

#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_power_of_fixed_strip
#print axioms exists_uniform_pmPronicVaughanResidualGramError_power_of_fixed_strip
#print axioms zetaZeroAbscissa_lt_one_of_extreme_vaughan_residual_power
#print axioms zetaZeroAbscissa_lt_one_iff_uniform_pmPronicVaughanResidualGramError_power
end GaloisForLFunctions.BezoutValuationIncidence
