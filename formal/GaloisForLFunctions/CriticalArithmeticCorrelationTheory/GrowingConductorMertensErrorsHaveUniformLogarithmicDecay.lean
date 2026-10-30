import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingConductorPrimeSourcesHaveUniformLogarithmicDecay
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ResidueMertensFinitePartsHaveLogarithmicRates

/-!
# Uniform residue Mertens errors on growing conductor families

Exact Abel transport removes each conductor's finite part before estimating
the source tail. Pointwise convergence identifies that finite part; the error
bound and starting horizon remain uniform over the growing family.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

private theorem integral_reciprocal_log_tail {p : ℕ} (hp : 0 < p)
    {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) :
    (∫ t in X..Y, 1 / (t * Real.log t ^ (p + 1))) ≤
      1 / ((p : ℝ) * Real.log X ^ p) := by
  have hd : ∀ t ∈ Set.uIcc X Y,
      HasDerivAt (fun u : ℝ => -(1 / ((p : ℝ) * Real.log u ^ p)))
        (1 / (t * Real.log t ^ (p + 1))) t := by
    intro t ht
    rw [Set.uIcc_of_le hXY] at ht
    exact HTGeometry.hasDerivAt_neg_inv_log_pow hp (hX.trans_le ht.1)
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ (p + 1))) (Set.uIcc X Y) := by
    intro t ht
    rw [Set.uIcc_of_le hXY] at ht
    have ht1 := hX.trans_le ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log ht0).pow (p + 1)))
      (mul_ne_zero ht0 (pow_ne_zero _ (Real.log_pos ht1).ne'))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have hnonneg : 0 ≤ 1 / ((p : ℝ) * Real.log Y ^ p) := by
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (Real.log_pos (hX.trans_le hXY)).le _))
  linarith only [hnonneg]

/-- One horizon controls the actual residue Mertens finite-part remainder
for every allowed modulus, larger endpoint, and signed residue pattern. -/
theorem eventually_conductor_uniform_residuePrimeRealError_log_bound
    {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    ∀ᶠ Y : ℝ in atTop, 1 < Real.log Y ∧ ∀ X : ℝ, Y ≤ X →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log Y ^ A → ∀ F : ZMod q → ℝ,
        |residuePrimeRealError q F X| ≤
          (2 / (Real.log Y) ^ k) * ∑ r : ZMod q, |F r| := by
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp
    (eventually_conductor_uniform_residueMangoldtReading_log_error hA (k + 2))
  filter_upwards [eventually_ge_atTop Z₀, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with Y hYZ₀ hY3 hlogY
  refine ⟨hlogY, ?_⟩
  intro X hYX q _ hq F
  let L : ℝ := ∑ r : ZMod q, |F r|
  let R : ℝ → ℝ := fun t => residueMangoldtReading q F t - primeClassKappa q F * t
  have hL : 0 ≤ L := sum_nonneg fun r _ => abs_nonneg _
  have hY0 : 0 < Y := by linarith only [hY3]
  have hX1 : 1 < X := lt_of_lt_of_le (by linarith only [hY3]) hYX
  have hX0 : 0 < X := zero_lt_one.trans hX1
  have hlogX : 1 < Real.log X := hlogY.trans_le (Real.log_le_log hY0 hYX)
  have hlogX0 : 0 < Real.log X := zero_lt_one.trans hlogX
  have hb (t : ℝ) (ht : X ≤ t) : |R t| ≤ (t / Real.log t ^ (k + 2)) * L := by
    have hqt : (q : ℝ) ≤ Real.log t ^ A := hq.trans
      (Real.rpow_le_rpow (zero_lt_one.trans hlogY).le
        (Real.log_le_log hY0 (hYX.trans ht)) hA)
    exact (hZ₀ t (hYZ₀.trans (hYX.trans ht))).2 t le_rfl q hqt F
  have hquot (t : ℝ) (ht : X ≤ t) : |R t / t| ≤ L / Real.log t ^ (k + 2) := by
    have ht0 := hX0.trans_le ht
    rw [abs_div, abs_of_pos ht0]
    calc
      _ ≤ (t / Real.log t ^ (k + 2) * L) / t :=
        div_le_div_of_nonneg_right (hb t ht) ht0.le
      _ = _ := by field_simp
  let D : ℝ := L / Real.log X ^ (k + 2) +
    L / ((k + 1 : ℕ) * Real.log X ^ (k + 1))
  have hlim : Tendsto (fun Z : ℝ =>
      |residuePrimeRealError q F Z| + L / Real.log Z ^ (k + 2) + D)
      atTop (𝓝 D) := by
    have hzero : Tendsto (fun Z : ℝ => L / Real.log Z ^ (k + 2)) atTop (𝓝 0) := by
      have h := ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).pow (k + 2)).const_mul L
      simpa only [Function.comp_def, inv_pow, zero_pow (by omega : k + 2 ≠ 0),
        mul_zero, div_eq_mul_inv] using h
    have h := ((tendsto_residuePrimeRealError F).abs.add hzero).add_const D
    simpa only [abs_zero, zero_add] using h
  have hbound : |residuePrimeRealError q F X| ≤ D := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop X] with Z hXZ
    have hZ0 : 0 < Z := hX0.trans_le hXZ
    have hc : ContinuousOn (fun t : ℝ => L * (1 / (t * Real.log t ^ (k + 2))))
        (Set.uIcc X Z) := by
      intro t ht
      rw [Set.uIcc_of_le hXZ] at ht
      have ht1 := hX1.trans_le ht.1
      have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
      exact (continuousAt_const.mul (continuousAt_const.div
        (continuousAt_id.mul ((Real.continuousAt_log ht0).pow (k + 2)))
        (mul_ne_zero ht0 (pow_ne_zero _ (Real.log_pos ht1).ne')))).continuousWithinAt
    have hpoint : ∀ t ∈ Set.Ioc X Z, ‖R t / t ^ 2‖ ≤
        L * (1 / (t * Real.log t ^ (k + 2))) := by
      intro t ht
      have ht0 := hX0.trans ht.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
      calc
        _ ≤ (t / Real.log t ^ (k + 2) * L) / t ^ 2 :=
          div_le_div_of_nonneg_right (hb t ht.1.le) (sq_nonneg t)
        _ = _ := by field_simp
    have hI : |∫ t in X..Z, R t / t ^ 2| ≤
        L / ((k + 1 : ℕ) * Real.log X ^ (k + 1)) := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hXZ (Filter.Eventually.of_forall hpoint) hc.intervalIntegrable
      rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hi
      have hj := mul_le_mul_of_nonneg_left
        (integral_reciprocal_log_tail (p := k + 1) (by omega) hX1 hXZ) hL
      exact hi.trans (by simpa only [Nat.add_assoc, div_eq_mul_inv, one_mul] using hj)
    have heq := residuePrimeRealError_sub_eq F hX1.le hXZ
    change residuePrimeRealError q F Z - residuePrimeRealError q F X =
      R Z / Z - R X / X + ∫ t in X..Z, R t / t ^ 2 at heq
    have htri : |residuePrimeRealError q F X| ≤
        |residuePrimeRealError q F Z| + |R Z / Z| + |R X / X| +
        |∫ t in X..Z, R t / t ^ 2| := by
      have h1 := abs_sub (residuePrimeRealError q F Z) (R Z / Z)
      have h2 := abs_add_le (residuePrimeRealError q F Z - R Z / Z) (R X / X)
      have h3 := abs_sub (residuePrimeRealError q F Z - R Z / Z + R X / X)
        (∫ t in X..Z, R t / t ^ 2)
      have hx : residuePrimeRealError q F X =
          residuePrimeRealError q F Z - R Z / Z + R X / X - ∫ t in X..Z, R t / t ^ 2 := by
        linarith only [heq]
      rw [hx]
      linarith only [h1, h2, h3]
    dsimp only [D]
    linarith only [htri, hquot Z hXZ, hquot X le_rfl, hI]
  have hpow (j : ℕ) : Real.log Y ^ k ≤ Real.log X ^ (k + j) := by
    calc
      _ ≤ Real.log X ^ k := pow_le_pow_left₀ (by linarith only [hlogY])
        (Real.log_le_log hY0 hYX) k
      _ ≤ Real.log X ^ (k + j) := pow_le_pow_right₀ hlogX.le (Nat.le_add_right k j)
  have hfirst : L / Real.log X ^ (k + 2) ≤ L / Real.log Y ^ k :=
    div_le_div_of_nonneg_left hL (pow_pos (by linarith only [hlogY]) _) (hpow 2)
  have hsecond : L / ((k + 1 : ℕ) * Real.log X ^ (k + 1)) ≤ L / Real.log Y ^ k := by
    apply div_le_div_of_nonneg_left hL (pow_pos (by linarith only [hlogY]) _)
    exact (hpow 1).trans (le_mul_of_one_le_left (pow_nonneg hlogX0.le _)
      (by exact_mod_cast (show 1 ≤ k + 1 by omega)))
  dsimp only [D] at hbound
  change _ ≤ (2 / Real.log Y ^ k) * L
  calc
    _ ≤ L / Real.log Y ^ k + L / Real.log Y ^ k := hbound.trans (add_le_add hfirst hsecond)
    _ = (2 / Real.log Y ^ k) * L := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_conductor_uniform_residuePrimeRealError_log_bound
