import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ActualUpwardRowsHaveUniformConductorBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeilReplacementsHaveUniformConductorBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.DownwardRowsHaveUniformConductorBounds

/-!
# Complete residuals on growing logarithmic conductor families

The exact signed decomposition combines eight source terms. Their common
conductor constants give a quartic cost and retain the boundary, kernel and
harmonic-source decay rates. One eventual horizon covers every conductor in
a prescribed logarithmic range, uniformly in the permitted overlap.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem norm_add_sq_le_two_uniform {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

private theorem norm_four_sq_le_uniform {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h := norm_add_sq_le_two_uniform (a + b) (c + d)
  rw [← add_assoc] at h
  linarith only [h, norm_add_sq_le_two_uniform a b, norm_add_sq_le_two_uniform c d]

private theorem norm_eight_signed_sq_le_uniform {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have h := norm_add_sq_le_two_uniform (-p + s + c + -x) (q + y + z + -u)
  have h1 := norm_four_sq_le_uniform (-p) s c (-x)
  have h2 := norm_four_sq_le_uniform q y z (-u)
  rw [norm_neg, norm_neg] at h1
  rw [norm_neg] at h2
  linarith only [h, h1, h2]

private theorem conductor_power_rate_le {C c L N m : ℝ}
    (hC : 0 ≤ C) (hc : 1 ≤ c) (hm : 1 ≤ m) (hL : 0 ≤ L)
    {j k : ℕ} (hj : j ≤ 4) (hk : k ≤ 5) :
    C * m ^ j * c ^ k / L ≤ C * m ^ 4 *
      (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 / Real.sqrt L) := by
  have hm0 := zero_le_one.trans hm
  have hc0 := zero_le_one.trans hc
  calc
    _ ≤ C * m ^ 4 * c ^ 5 / L := by
      apply div_le_div_of_nonneg_right _ hL
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm hj) hC)
        (pow_le_pow_right₀ hc hk) (by positivity) (by positivity)
    _ = C * m ^ 4 * (c ^ 5 / L) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ c ^ 10 * (L / N) ^ 2)).trans
        (le_add_of_nonneg_right (by positivity))

private theorem inv_sqrt_totient_sq_le_one {m : ℕ} (hm : 0 < m) :
    (Real.sqrt (m.totient : ℝ))⁻¹ ^ 2 ≤ 1 := by
  have ht : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
  simpa only [one_div] using (div_le_one (zero_lt_one.trans_le ht)).mpr ht

/-- Every term of the complete signed residual shares a quartic conductor budget.
The waiting horizon is common to all conductors in any fixed logarithmic range. -/
theorem exists_completeWeil_uniform_conductor_residual_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 / Real.sqrt (Real.log N)) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_uniform_conductor_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cc, hCc, hcenter⟩ := exists_centerError_uniform_conductor_bound φ
  obtain ⟨Cx, hCx, hx⟩ := exists_crossError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cd, hCd, hdown⟩ := exists_fullNearGammaDownward_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenter_uniform_conductor_bound hM
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu) + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hup A hA, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hupN hN hlog
  intro m hm hmN c hc hlarge
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 := zero_le_one.trans hm1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 / Real.sqrt (Real.log N)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hthree : 3 * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 3 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hc2, hlarge]
  have hcN : c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have htwo : 2 * c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have hw : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hthree]
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * (m : ℝ) ^ 4 * R := by
    have hb := conductor_power_rate_le (N := (N : ℝ)) hCp.le hc hm1 hL0.le
      (j := 3) (k := 0) (by norm_num) (by norm_num)
    simp only [pow_zero, mul_one] at hb
    exact (hp m hm N).trans hb
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * (m : ℝ) ^ 4 * R := by
    have hm24 := pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 4)
    have hc210 := pow_le_pow_right₀ hc (by norm_num : 2 ≤ 10)
    have hL2 : 1 ≤ Real.log (N : ℝ) ^ 2 := one_le_pow₀ hlog
    have hscale := mul_le_mul_of_nonneg_left hL2 (pow_nonneg hc0.le 10)
    have hnum : Cs * (m : ℝ) ^ 2 * c ^ 2 ≤
        Cs * (m : ℝ) ^ 4 * (c ^ 10 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm24 hCs.le)
        (hc210.trans (by simpa only [mul_one] using hscale)) (sq_nonneg _) (by positivity)
    calc
      _ ≤ Cs * (m : ℝ) ^ 2 * c ^ 2 / (N : ℝ) ^ 2 := hs m hm N hN hlog c hc0 hcN
      _ ≤ (Cs * (m : ℝ) ^ 4 * (c ^ 10 * Real.log (N : ℝ) ^ 2)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = Cs * (m : ℝ) ^ 4 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
        rw [div_pow]; ring
      _ ≤ Cs * (m : ℝ) ^ 4 * R := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [R]
        have h1 : 0 ≤ c ^ 5 / Real.log N := by positivity
        have h3 : 0 ≤ c ^ 3 / Real.sqrt (Real.log N) := by positivity
        linarith only [h1, h3]
  have hc' := (hcenter m hm c N).trans
    (conductor_power_rate_le (N := (N : ℝ)) hCc hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 2 ≤ 5))
  have hx' := (hx m hm c hc0 N hN).trans
    (conductor_power_rate_le (N := (N : ℝ)) hCx hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 4 ≤ 5))
  have hq' := (hq m hm c hc0 N hN hcN).trans
    (conductor_power_rate_le (N := (N : ℝ)) hCq hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 4 ≤ 5))
  have hn' := (hnear m hm c hc N hN htwo).trans
    (conductor_power_rate_le (N := (N : ℝ)) hCn hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 5 ≤ 5))
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      Cd * (m : ℝ) ^ 4 * R := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hb := (hdown m hm c hc N hN hw).trans
      (conductor_power_rate_le (N := (N : ℝ)) hCd hc hm1 hL0.le
        (by norm_num : 4 ≤ 4) (by norm_num : 5 ≤ 5))
    exact (mul_le_mul (inv_sqrt_totient_sq_le_one hm) hb (sq_nonneg _) zero_le_one).trans_eq
      (by rw [one_mul])
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cu * (m : ℝ) ^ 4 * R := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have ht : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    have ht4 : (m.totient : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
      (pow_le_pow_left₀ (Nat.cast_nonneg m.totient) ht 2).trans
        (pow_le_pow_right₀ hm1 (by norm_num))
    have hb := (hupN m hm hmN c hc hlarge).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht4 hCu.le) hR)
    exact (mul_le_mul (inv_sqrt_totient_sq_le_one hm) hb (sq_nonneg _) zero_le_one).trans_eq
      (by rw [one_mul])
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm]
  have hsum := norm_eight_signed_sq_le_uniform
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  have hb := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
    (by norm_num : (0 : ℝ) ≤ 8))
  change _ ≤ K * (m : ℝ) ^ 4 * R
  calc
    _ ≤ 8 * (Cp * (m : ℝ) ^ 4 * R + Cs * (m : ℝ) ^ 4 * R +
        Cc * (m : ℝ) ^ 4 * R + Cx * (m : ℝ) ^ 4 * R + Cq * (m : ℝ) ^ 4 * R +
        Cd * (m : ℝ) ^ 4 * R + Cn * (m : ℝ) ^ 4 * R + Cu * (m : ℝ) ^ 4 * R) := hb
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu)) * (m : ℝ) ^ 4 * R := by ring
    _ ≤ K * (m : ℝ) ^ 4 * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 4)
      dsimp only [K]
      linarith only

/-- The explicit tilted spline has a common complete-residual bound on logarithmic conductor ranges. -/
theorem exists_tiltedUnitSpline_uniform_conductor_residual_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 / Real.sqrt (Real.log N)) :=
  exists_completeWeil_uniform_conductor_residual_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_uniform_conductor_residual_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_uniform_conductor_residual_bound
