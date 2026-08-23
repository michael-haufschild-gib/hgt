import GaloisForLFunctions.RHTower.BaezDuarteMobiusSeries
import GaloisForLFunctions.RHTower.InfiniteMobiusSignedChannel

/-!
# The Báez--Duarte coefficient in the fixed safe Gibbs channel

At the safe exponent `σ = 2` the squarefree Möbius mass is a probability, the signed Möbius
weight is a unit vector, and the spectral feature `(Y_k)_n = √(P(n)) (1-n^{-2})^k` has the
Báez--Duarte coefficient as its coherent-source matrix coefficient.  The coefficient is therefore
exactly the length of the coherent component of the feature.
-/

namespace RHTower

open Real MeasureTheory ArithmeticFunction

noncomputable section

/-- The spectral multiplier `X(n) = 1 - n^{-2}` of the fixed safe Gibbs channel. -/
def bdSpectralValue (n : ℕ) : ℝ := 1 - ((n : ℝ) ^ 2)⁻¹

theorem bdSpectralValue_mem (n : ℕ) : 0 ≤ bdSpectralValue n ∧ bdSpectralValue n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    norm_num [bdSpectralValue]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
    constructor
    · rw [bdSpectralValue, sub_nonneg, inv_le_one_iff₀]
      right; exact hsq
    · rw [bdSpectralValue]
      have : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
      linarith

/-- The spectral feature vector `(Y_k)_n = √(P_*(n)) X(n)^k`. -/
def bdFeature (k : ℕ) (n : ℕ) : ℂ :=
  ((Real.sqrt (squarefreeMobiusProbability 2 n) * bdSpectralValue n ^ k : ℝ) : ℂ)

theorem norm_bdFeature_sq (k n : ℕ) :
    ‖bdFeature k n‖ ^ 2 = squarefreeMobiusProbability 2 n * bdSpectralValue n ^ (2 * k) := by
  have hP : 0 ≤ squarefreeMobiusProbability 2 n :=
    squarefreeMobiusProbability_nonneg (by norm_num) n
  have hX := (bdSpectralValue_mem n).1
  rw [bdFeature, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), mul_pow, Real.sq_sqrt hP, ← pow_mul]
  congr 1
  ring

theorem summable_norm_bdFeature_sq (k : ℕ) :
    Summable (fun n => ‖bdFeature k n‖ ^ 2) := by
  have hsum : Summable (squarefreeMobiusProbability 2) :=
    summable_squarefreeMobiusProbability (by norm_num : (1:ℝ) < 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  rw [norm_bdFeature_sq]
  have hP : 0 ≤ squarefreeMobiusProbability 2 n :=
    squarefreeMobiusProbability_nonneg (by norm_num) n
  have hX := bdSpectralValue_mem n
  nlinarith [pow_le_one₀ hX.1 hX.2 (n := 2 * k), pow_nonneg hX.1 (2 * k)]

/-- The feature vector as an element of the channel space. -/
def bdFeatureLp (k : ℕ) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨bdFeature k, HilbertSchmidt.memℓp_of_sq (summable_norm_bdFeature_sq k)⟩

theorem inner_signedWeight_bdFeature (k : ℕ) :
    (inner ℂ (infiniteMobiusSignedWeightLp 2 (by norm_num)) (bdFeatureLp k) : ℂ)
      = ∑' n : ℕ, ((moebius n : ℤ) : ℂ)
          * ((squarefreeMobiusProbability 2 n : ℝ) : ℂ)
          * (((bdSpectralValue n : ℝ) : ℂ)) ^ k := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  have hP : 0 ≤ squarefreeMobiusProbability 2 n :=
    squarefreeMobiusProbability_nonneg (by norm_num) n
  have hw : (infiniteMobiusSignedWeightLp 2 (by norm_num : (1:ℝ) < 2) : ℕ → ℂ) n
      = ((moebius n : ℤ) : ℂ) * ((Real.sqrt (squarefreeMobiusProbability 2 n) : ℝ) : ℂ) := rfl
  have hy : (bdFeatureLp k : ℕ → ℂ) n
      = ((Real.sqrt (squarefreeMobiusProbability 2 n) * bdSpectralValue n ^ k : ℝ) : ℂ) := rfl
  have hsq : (Real.sqrt (squarefreeMobiusProbability 2 n))
      * (Real.sqrt (squarefreeMobiusProbability 2 n)) = squarefreeMobiusProbability 2 n :=
    Real.mul_self_sqrt hP
  have hsqC : ((Real.sqrt (squarefreeMobiusProbability 2 n) : ℝ) : ℂ)
      * ((Real.sqrt (squarefreeMobiusProbability 2 n) : ℝ) : ℂ)
      = ((squarefreeMobiusProbability 2 n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
  rw [RCLike.inner_apply, hw, hy, map_mul, map_intCast, Complex.conj_ofReal]
  push_cast
  linear_combination (((moebius n : ℤ) : ℂ) * (((bdSpectralValue n : ℝ) : ℂ)) ^ k) * hsqC

/-- **Equation (7c)–(7d).**  The Báez--Duarte coefficient is the fixed safe-temperature
signed-channel matrix coefficient. -/
theorem bdCoeff_eq_channel (k : ℕ) :
    bdCoeff k = ((squarefreeMobiusTotal 2 : ℝ) : ℂ)
      * inner ℂ (infiniteMobiusSignedWeightLp 2 (by norm_num)) (bdFeatureLp k) := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  rw [inner_signedWeight_bdFeature, ← tsum_mul_left, bdCoeff_eq_tsum]
  refine tsum_congr fun n => ?_
  have hZP : squarefreeMobiusTotal 2 * squarefreeMobiusProbability 2 n
      = squarefreeMobiusMass 2 n := by
    rw [squarefreeMobiusProbability]
    field_simp
  by_cases hn : Squarefree n
  · have hmass : squarefreeMobiusMass 2 n = ((n : ℝ) ^ 2)⁻¹ := by
      rw [squarefreeMobiusMass, if_pos hn]
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; norm_num
      · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
          Real.rpow_natCast]
    have hX : bdSpectralValue n = 1 - ((n : ℝ) ^ 2)⁻¹ := rfl
    rw [bdMobiusTerm, hX]
    rw [show ((squarefreeMobiusTotal 2 : ℝ) : ℂ)
        * (((moebius n : ℤ) : ℂ) * ((squarefreeMobiusProbability 2 n : ℝ) : ℂ)
          * (((1 - ((n : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) ^ k)
        = ((moebius n : ℤ) : ℂ)
          * ((squarefreeMobiusTotal 2 * squarefreeMobiusProbability 2 n : ℝ) : ℂ)
          * (((1 - ((n : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) ^ k by push_cast; ring, hZP, hmass]
    push_cast
    ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn, bdMobiusTerm,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    push_cast
    ring

/-- **Equation (7f), projection form.**  The coherent component of the feature vector. -/
theorem projection_bdFeature (k : ℕ) :
    infiniteSignedChannelProjection (infiniteMobiusSignedWeightLp 2 (by norm_num))
        (bdFeatureLp k)
      = (bdCoeff k / ((squarefreeMobiusTotal 2 : ℝ) : ℂ))
          • infiniteMobiusSignedWeightLp 2 (by norm_num) := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hZC : ((squarefreeMobiusTotal 2 : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hZ
  rw [infiniteSignedChannelProjection, ContinuousLinearMap.comp_apply,
    infiniteSignedChannelAnalysis, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, infiniteSignedChannelSynthesis, innerSL_apply_apply]
  congr 1
  rw [bdCoeff_eq_channel k]
  field_simp

/-- **Equation (7f).**  The Báez--Duarte coefficient is exactly the length of the coherent
signed-source component of the spectral feature. -/
theorem norm_bdCoeff_eq_channel (k : ℕ) :
    ‖bdCoeff k‖ = squarefreeMobiusTotal 2
      * ‖infiniteSignedChannelProjection (infiniteMobiusSignedWeightLp 2 (by norm_num))
          (bdFeatureLp k)‖ := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  rw [projection_bdFeature, norm_smul, norm_infiniteMobiusSignedWeightLp, mul_one,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  field_simp

end

end RHTower
