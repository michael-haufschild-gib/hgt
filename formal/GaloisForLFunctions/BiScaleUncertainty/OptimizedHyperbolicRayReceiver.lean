import GaloisForLFunctions.BiScaleUncertainty.FourthMomentJumpReceiver

/-!
# Attained hyperbolic-ray certificate for signed source data

The fourth-moment transfer admits an explicit optimal scale along the collar's
hyperbolic profile. All source-frame errors remain. The resulting continuous,
nonnegative certificate transfers into the full original secant/plastic functional.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.HyperbolicRay
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ArithmeticMultiplierCollisions DyadicMultiplierFrame
open DyadicHyperbolicMoment FourthMomentJump
noncomputable section

def profile (y : ℝ) (i : ℕ) : ℝ := Real.cosh ((chainNode (Real.log 2) i - y) / 2)

def profileEnergy (N : ℕ) (y : ℝ) : ℝ := ∑ i ∈ Finset.range (N + 1), profile y i ^ 2

/-- Quadratic cost of the canonical hyperbolic ray. -/
def rayCost (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    fourthEnvelope f (1 / 2) (chainNode (Real.log 2) i - y) * profile y i ^ 3 / 2

/-- Linear gain after paying the entire signed-source frame penalty. -/
def rayGain (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 * profileEnergy N y -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 * max (frameGramUpper f N (profile y)) 0)

def optimalScale (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : ℝ :=
  max (rayGain f N y) 0 / (2 * rayCost f N y)

/-- Attained nonnegative certificate; total division also covers zero energy. -/
def optimizedCollar (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : ℝ :=
  max (rayGain f N y) 0 ^ 2 / (4 * rayCost f N y)

private theorem profile_pos (y : ℝ) (i : ℕ) : 0 < profile y i := Real.cosh_pos _

private theorem profileEnergy_nonneg (N : ℕ) (y : ℝ) : 0 ≤ profileEnergy N y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rayCost_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : 0 ≤ rayCost f N y :=
  Finset.sum_nonneg fun i _ => div_nonneg
    (mul_nonneg (fourthEnvelope_nonneg _ _ _) (pow_nonneg (profile_pos y i).le 3)) (by norm_num)

private theorem fourth_zero_second_zero (f : C_c(ℝ, ℝ))
    (hz : fourthEnergy f (1 / 2) = 0) : autocorr (sinhCompact (1 / 2) f) 0 = 0 := by
  have h := fourthEnergy_variance_identity f (1 / 2)
  rw [hz, mul_zero] at h
  nlinarith only [h, sourceVariance_nonneg f (1 / 2),
    sq_nonneg (autocorr (sinhCompact (1 / 2) f) 0)]

private theorem zero_data (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ)
    (hz : fourthEnergy f (1 / 2) = 0) : rayCost f N y = 0 ∧ rayGain f N y = 0 := by
  have hs := fourth_zero_second_zero f hz
  constructor
  · unfold rayCost fourthEnvelope
    rw [hz, hs]
    simp
  · unfold rayGain
    rw [hs]
    norm_num

theorem rayCost_pos (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ)
    (hT : 0 < fourthEnergy f (1 / 2)) : 0 < rayCost f N y := by
  have hH : 0 < fourthEnvelope f (1 / 2) (chainNode (Real.log 2) 0 - y) := by
    unfold fourthEnvelope
    exact add_pos_of_pos_of_nonneg (mul_pos hT (sq_pos_of_pos (Real.cosh_pos _)))
      (mul_nonneg (add_nonneg hT.le (autocorr_zero_nonneg _)) (sq_nonneg _))
  have hterm := div_pos (mul_pos hH (pow_pos (profile_pos y 0) 3)) (by norm_num : (0 : ℝ) < 2)
  unfold rayCost
  refine hterm.trans_le (Finset.single_le_sum
    (f := fun i : ℕ => fourthEnvelope f (1 / 2) (chainNode (Real.log 2) i - y) *
      profile y i ^ 3 / 2) ?_ (show 0 ∈ Finset.range (N + 1) by simp))
  intro i _
  exact div_nonneg (mul_nonneg (fourthEnvelope_nonneg f (1 / 2) _)
    (pow_nonneg (profile_pos y i).le 3)) (by norm_num)

theorem optimalScale_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : 0 ≤ optimalScale f N y :=
  div_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) (rayCost_nonneg f N y))

theorem optimizedCollar_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) : 0 ≤ optimizedCollar f N y :=
  div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (rayCost_nonneg f N y))

private theorem quadratic_max (A D : ℝ) (hD : 0 < D) :
    (max A 0 / (2 * D)) * A - (max A 0 / (2 * D)) ^ 2 * D = max A 0 ^ 2 / (4 * D) ∧
      ∀ l : ℝ, 0 ≤ l → l * A - l ^ 2 * D ≤ max A 0 ^ 2 / (4 * D) := by
  by_cases hA : 0 ≤ A
  · rw [max_eq_left hA]
    constructor
    · field_simp
      ring
    · intro l _
      apply (le_div_iff₀ (by positivity : 0 < 4 * D)).2
      nlinarith only [sq_nonneg (2 * D * l - A)]
  · rw [max_eq_right (le_of_not_ge hA)]
    constructor
    · simp
    · intro l hl
      simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div]
      exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos hl (le_of_not_ge hA)).trans
        (mul_nonneg (sq_nonneg l) hD.le))

/-- The explicit scale attains the best bound on this ray, including zero energy. -/
theorem optimalScale_attains (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    optimalScale f N y * rayGain f N y - optimalScale f N y ^ 2 * rayCost f N y =
      optimizedCollar f N y := by
  rcases eq_or_lt_of_le (fourthEnergy_nonneg f (1 / 2)) with hz | hp
  · obtain ⟨hD, hA⟩ := zero_data f N y hz.symm
    simp [optimalScale, optimizedCollar, hD, hA]
  · exact (quadratic_max _ _ (rayCost_pos f N y hp)).1

/-- No nonnegative scale on the same ray improves this certificate. -/
theorem ray_le_optimizedCollar (f : C_c(ℝ, ℝ)) (N : ℕ) (y l : ℝ) (hl : 0 ≤ l) :
    l * rayGain f N y - l ^ 2 * rayCost f N y ≤ optimizedCollar f N y := by
  rcases eq_or_lt_of_le (fourthEnergy_nonneg f (1 / 2)) with hz | hp
  · obtain ⟨hD, hA⟩ := zero_data f N y hz.symm
    simp [optimizedCollar, hD, hA]
  · exact (quadratic_max _ _ (rayCost_pos f N y hp)).2 l hl

private theorem gram_scale (g : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) (l : ℝ) :
    translationGramEnergy g (Finset.range (N + 1)) (fun i => l * w i) (chainNode (Real.log 2)) =
      l ^ 2 * translationGramEnergy g (Finset.range (N + 1)) w (chainNode (Real.log 2)) := by
  unfold translationGramEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem matched_weights (y l : ℝ) :
    variationalWeights (fun _ => 1) (chainNode (Real.log 2))
      (fun i => l * profile y i ^ 2 / 2) y = fun i => l * profile y i := by
  funext i
  unfold variationalWeights archSechHalfWeight profile
  field_simp [(Real.cosh_pos ((chainNode (Real.log 2) i - y) / 2)).ne']

private theorem matched_cost (f : C_c(ℝ, ℝ)) (N : ℕ) (y l : ℝ) :
    fourthCost f (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2))
      (fun i => l * profile y i ^ 2 / 2) y = l ^ 2 * rayCost f N y := by
  unfold fourthCost rayCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold archSechHalfWeight profile
  field_simp [(Real.cosh_pos ((chainNode (Real.log 2) i - y) / 2)).ne']

/-- Every scale is a valid source-data collar lower bound; source correlations stay signed. -/
theorem odd_collar_ge_ray (f : C_c(ℝ, ℝ)) (N : ℕ) (y l : ℝ) (hl : 0 ≤ l) :
    l * rayGain (oddCompactSource f) N y - l ^ 2 * rayCost (oddCompactSource f) N y ≤
      secantJumpCollar (oddCompactSource f) (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) y := by
  let F := oddCompactSource f
  let R := autocorr (sinhCompact (1 / 2) F) 0
  let G := translationGramEnergy (sinhCompact (1 / 2) F) (Finset.range (N + 1))
    (profile y) (chainNode (Real.log 2))
  have hg := secantJumpCollar_ge_fourthGram F (Finset.range (N + 1)) (fun _ => 1)
    (chainNode (Real.log 2)) (fun i => l * profile y i ^ 2 / 2) y
  have hu := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    ((odd_sinhGram_le_frameGramUpper f N (profile y)).trans (le_max_left _ 0))
    (autocorr_zero_nonneg (sinhCompact (1 / 2) F)))
  have hs : (∑ i ∈ Finset.range (N + 1), l * profile y i *
      Real.cosh ((chainNode (Real.log 2) i - y) / 2)) = l * profileEnergy N y := by
    rw [profileEnergy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by dsimp [profile]; ring
  unfold fourthGramBound at hg
  rw [matched_weights, matched_cost, gram_scale, hs] at hg
  change R * (l * profileEnergy N y) - Real.sqrt (R * (l ^ 2 * G)) -
    l ^ 2 * rayCost F N y ≤ _ at hg
  rw [show R * (l ^ 2 * G) = l ^ 2 * (R * G) by ring,
    Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl] at hg
  have h := mul_le_mul_of_nonneg_left hu hl
  change l * Real.sqrt (R * G) ≤ _ at h
  change l * rayGain F N y - l ^ 2 * rayCost F N y ≤ _
  unfold rayGain
  change l * (R * profileEnergy N y - _) - l ^ 2 * rayCost F N y ≤ _
  nlinarith only [hg, h]

/-- Unconditional, explicit nonnegative collar bound for every canonical odd source. -/
theorem odd_collar_ge_optimized (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    optimizedCollar (oddCompactSource f) N y ≤
      secantJumpCollar (oddCompactSource f) (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) y := by
  rw [← optimalScale_attains]
  exact odd_collar_ge_ray f N y _ (optimalScale_nonneg _ _ _)

theorem continuous_optimizedCollar (f : C_c(ℝ, ℝ)) (N : ℕ) :
    Continuous (optimizedCollar f N) := by
  rcases eq_or_lt_of_le (fourthEnergy_nonneg f (1 / 2)) with hz | hp
  · have he : optimizedCollar f N = fun _ => 0 := by
      funext y
      obtain ⟨hD, hA⟩ := zero_data f N y hz.symm
      simp [optimizedCollar, hD, hA]
    rw [he]
    exact continuous_const
  · have hc (i : ℕ) : Continuous (fun y => profile y i) := by unfold profile; fun_prop
    have hB : Continuous (profileEnergy N) :=
      continuous_finsetSum _ fun i _ => (hc i).pow 2
    have hD : Continuous (rayCost f N) := continuous_finsetSum _ fun i _ =>
      (((continuous_fourthEnvelope f (1 / 2)).comp (by fun_prop)).mul ((hc i).pow 3)).div_const 2
    have hA : Continuous (rayGain f N) := (continuous_const.mul hB).sub
      (Real.continuous_sqrt.comp (continuous_const.mul
        ((continuous_frameGramUpper_of_weights f N profile hc).max continuous_const)))
    exact ((hA.max continuous_const).pow 2).div (continuous_const.mul hD)
      (fun y => (mul_pos (by norm_num) (rayCost_pos f N y hp)).ne')

theorem optimizedCollar_pos_iff_gain (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    0 < optimizedCollar f N y ↔ 0 < rayGain f N y := by
  rcases eq_or_lt_of_le (fourthEnergy_nonneg f (1 / 2)) with hz | hp
  · obtain ⟨hD, hA⟩ := zero_data f N y hz.symm
    simp [optimizedCollar, hD, hA]
  · constructor
    · intro h
      by_contra hn
      have hA : rayGain f N y ≤ 0 := le_of_not_gt hn
      simp [optimizedCollar, max_eq_right hA] at h
    · intro h
      exact div_pos (sq_pos_of_pos (h.trans_le (le_max_left _ _)))
        (mul_pos (by norm_num) (rayCost_pos f N y hp))

/-- Exact activation criterion retaining every signed source-frame correction. -/
theorem optimizedCollar_pos_iff (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    0 < optimizedCollar f N y ↔
      autocorr (sinhCompact (1 / 2) f) 0 * max (frameGramUpper f N (profile y)) 0 <
        (autocorr (sinhCompact (1 / 2) f) 0 * profileEnergy N y) ^ 2 := by
  rw [optimizedCollar_pos_iff_gain, rayGain, sub_pos]
  exact Real.sqrt_lt (mul_nonneg (autocorr_zero_nonneg _) (le_max_right _ _))
    (mul_nonneg (autocorr_zero_nonneg _) (profileEnergy_nonneg N y))

/-- Secondary source-zero specialization of the signed activation law. -/
theorem optimizedCollar_pos_iff_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ)
    (hR : 0 < autocorr (sinhCompact (1 / 2) f) 0)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    0 < optimizedCollar f N y ↔
      frameRadius f < autocorr (sinhCompact (1 / 2) f) 0 * (profileEnergy N y - 1) := by
  have hB : 0 < profileEnergy N y :=
    (sq_pos_of_pos (profile_pos y 0)).trans_le
      (Finset.single_le_sum (fun i _ => sq_nonneg (profile y i)) (by simp))
  rw [optimizedCollar_pos_iff, frameGramUpper_of_double_zeros f N _ hz]
  change autocorr (sinhCompact (1 / 2) f) 0 *
    max ((autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f) * profileEnergy N y) 0 <
      (autocorr (sinhCompact (1 / 2) f) 0 * profileEnergy N y) ^ 2 ↔ _
  have hρ : 0 ≤ frameRadius f := Real.sqrt_nonneg _
  rw [max_eq_left (mul_nonneg (add_nonneg hR.le hρ) hB.le)]
  set R := autocorr (sinhCompact (1 / 2) f) 0
  set B := profileEnergy N y
  rw [show R * ((R + frameRadius f) * B) = (R * B) * (R + frameRadius f) by ring,
    show (R * B) ^ 2 = (R * B) * (R * B) by ring]
  constructor
  · intro h
    by_contra hn
    have hp := mul_nonneg (mul_pos hR hB).le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [h, hp]
  · intro h
    have hp := mul_pos (mul_pos hR hB) (sub_pos.mpr h)
    nlinarith only [hp]

private theorem integral_collar_le_energy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, secantJumpCollar f (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) (-y)) ≤ biScaleSecantEnergy f := by
  have hd : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have ht := intervalIntegral_periodic_collar_sum_eq (continuous_secantJumpIntegrand f)
    0 (Real.log 2) (N + 1)
  simp only [zero_add] at ht
  have he : (fun y => secantJumpCollar f (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) (-y)) = fun y =>
      ∑ k ∈ Finset.range (N + 1), (autocorr f 0 - autocorr f ((k : ℝ) * Real.log 2 + y)) *
        archSechHalfWeight ((k : ℝ) * Real.log 2 + y) := by
    funext y
    simp [secantJumpCollar, chainNode, sub_neg_eq_add]
  rw [he, ← ht]
  unfold biScaleSecantEnergy
  rw [intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg (N + 1)) hd)]
  refine setIntegral_mono_set (integrableOn_secantJumpIntegrand_compact f) ?_ ?_
  · filter_upwards [] with x
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (archSechHalfWeight_pos x).le
  · exact Filter.Eventually.of_forall fun x hx => hx.1

/-- Full secant receiver with no free controls or source-zero hypothesis. -/
theorem odd_secantEnergy_ge_optimized (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) ≤
      biScaleSecantEnergy (oddCompactSource f) := by
  refine le_trans ?_ (integral_collar_le_energy (oddCompactSource f) N)
  exact intervalIntegral.integral_mono_on (μ := volume)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    (((continuous_optimizedCollar _ _).comp continuous_neg).intervalIntegrable _ _)
    (((continuous_secantJumpCollar _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (fun y _ => odd_collar_ge_optimized f N (-y))

/-- The full original plastic functional receives the attained collar certificate. -/
theorem odd_plasticCrossover_ge_optimized (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := odd_secantEnergy_ge_optimized f N
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hyperbolicMomentEnergy_oddSource]
  linarith only [h]

theorem odd_plasticCrossover_ge_optimized_momentBudget (f : C_c(ℝ, ℝ)) (N M : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * momentBudget (oddCompactSource f) M ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_moment_sq_le_budget f M
  linarith only [hp, hm]

theorem odd_logGrid_plasticCrossover_ge_optimized (f : C_c(ℝ, ℝ)) (N : ℕ)
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          frameRadius (oddCompactSource f)) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_logGrid_moment_sq_le_frame f hz
  nlinarith only [hp, hm]

end
end GaloisForLFunctions.BiScaleUncertainty.HyperbolicRay
