import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanBound
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactGrowthDetectsZeros
import GaloisForLFunctions.HTGeometry.StrictNaturalPowerGrowth
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnNestedWindowsTheCombFormTendsToWeilsFormOfTheStepPacket

/-!
# Power growth of the literal power comb

The polar and archimedean terms are compared with the centered arithmetic
contacts at the normalization of the actual finite comb.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry HodgeTheoryOfAFixedPart

/-- Strict growth threshold of the normalized finite power comb. -/
def PowerCombTailGrowth (a σ : ℝ) : Prop :=
  HTGeometry.StrictNaturalPowerGrowth (powerCombTail a) σ

/-- The normalization is the form of the literal coefficients `(N/n)^a`, divided by `N`. -/
theorem powerCombTail_eq_literal (a : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    powerCombTail a N = HodgeTheoryOfAFixedPart.combForm (Icc 1 N)
      (fun n => ((N : ℝ) / n) ^ a) / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (fun n : ℕ => ((N : ℝ) / n) ^ a) =
      fun n => (N : ℝ) ^ a * powerTailWeight a n := by
    funext n
    rw [powerTailWeight, Real.div_rpow hNp.le (Nat.cast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  rw [hw, ← HodgeTheoryOfAFixedPart.formBilin_self,
    formBilin_const_mul_left, formBilin_const_mul_right,
    HodgeTheoryOfAFixedPart.formBilin_self]
  unfold powerCombTail
  rw [Real.rpow_sub hNp, Real.rpow_one,
    show 2 * a = a + a by ring, Real.rpow_add hNp]
  ring

private theorem partialSumPowerBound_iff_strictGrowth (f : ℕ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    RHTower.PartialSumPowerBound f θ ↔
      StrictNaturalPowerGrowth (fun N => ∑ n ∈ range N, f n) θ :=
  (strictNaturalPowerGrowth_iff_succ (by simp) hθ).symm

/-- The archimedean part remains at the elementary exponent `1-2a`. -/
theorem strictGrowth_powerTailArchimedean {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    StrictNaturalPowerGrowth (powerTailArchimedean a) (1 - 2 * a) := by
  apply (strictNaturalPowerGrowth_iff_succ (by simp [powerTailArchimedean])
    (by linarith only [ha2])).mpr
  exact fun _ hδ => exists_powerTailArchimedean_bound ha ha2 hδ

/-- Centered contact partial sums carry the exact zero half-plane threshold. -/
theorem strictGrowth_centeredContact_iff_zeroHalfPlane {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    StrictNaturalPowerGrowth
      (fun N => ∑ n ∈ Icc 1 N, powerTailCenteredContact a n) (1 - 2 * a + σ) ↔
        RHTower.XiZeroHalfPlaneBound (1 / 2 - a + σ) := by
  have h := partialSumPowerBound_iff_strictGrowth (fun n => powerTailCenteredContact a (n + 1))
    (show 0 ≤ 1 - 2 * a + σ by linarith only [ha2, hσ])
  simp only [RHTower.sum_range_succ_eq_sourcePartialSum, RHTower.sourcePartialSum] at h
  exact h.symm.trans (partialSumPowerBound_centeredContact_iff_zeroHalfPlane ha ha2 hσ)

/-- The finite first degree differs from the pole coefficient by a power-series tail. -/
def powerTailPolarRemainder (a : ℝ) (N : ℕ) : ℝ :=
  2 * (degOne (Icc 1 N) (powerTailWeight a) - powerTailPole a) *
    degTwo (Icc 1 N) (powerTailWeight a)

private theorem powerTail_degOne (a : ℝ) (N : ℕ) :
    degOne (Icc 1 N) (powerTailWeight a) =
      ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n := by
  apply sum_congr rfl
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  simp only [powerTailWeight, div_eq_mul_inv]
  rw [← Real.rpow_neg_one, ← Real.rpow_add hnR]
  congr 1
  ring

private theorem powerTail_degTwo (a : ℝ) (N : ℕ) :
    degTwo (Icc 1 N) (powerTailWeight a) = powerTailPrefix a N := by
  simp only [degTwo, powerTailPrefix, Nat.floor_natCast]

/-- The polar truncation has the elementary size `N^(1-2a)`. -/
theorem abs_powerTailPolarRemainder_le {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {N : ℕ} (hN : 1 ≤ N) :
    |powerTailPolarRemainder a N| ≤
      (2 / (a * (1 - a))) * (N : ℝ) ^ (1 - 2 * a) := by
  have hb : 0 < 1 - a := by linarith only [ha2]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have htail := powerTailPole_sub_sum_bounds ha hN
  rw [← powerTail_degOne] at htail
  have hprefix := (powerTailPrefix_sub_integral_bounds ha
    (show a < 1 by linarith only [ha2]) hNp.le).2
  rw [← powerTail_degTwo] at hprefix
  have hdegree : 0 ≤ degTwo (Icc 1 N) (powerTailWeight a) :=
    sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [powerTailPolarRemainder, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_sub_comm, abs_of_nonneg htail.1, abs_of_nonneg hdegree]
  calc
    _ ≤ (2 * ((N : ℝ) ^ (-a) / a)) * ((N : ℝ) ^ (1 - a) / (1 - a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htail.2 (by norm_num))
        (by linarith only [hprefix]) hdegree (by positivity)
    _ = (2 / (a * (1 - a))) * ((N : ℝ) ^ (-a) * (N : ℝ) ^ (1 - a)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring

theorem strictGrowth_powerTailPolarRemainder {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    StrictNaturalPowerGrowth (powerTailPolarRemainder a) (1 - 2 * a) := by
  intro δ hδ
  have hb : 0 < 1 - a := by linarith only [ha2]
  refine ⟨2 / (a * (1 - a)), by positivity, fun N hN => ?_⟩
  exact (abs_powerTailPolarRemainder_le ha ha2 hN).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      (by linarith only [hδ])) (by positivity))

/-- The full comb differs from minus twice the centered contacts only by
the polar truncation and the archimedean term. -/
theorem combForm_powerTail_eq_centeredContact (a : ℝ) (N : ℕ) :
    HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a) +
        2 * (∑ n ∈ Icc 1 N, powerTailCenteredContact a n) =
      powerTailPolarRemainder a N + powerTailArchimedean a N := by
  have hsum : (∑ n ∈ Icc 1 N, powerTailCenteredContact a n) =
      (∑ n ∈ Icc 1 N, powerTailContactCoefficient a n) -
        powerTailPole a * degTwo (Icc 1 N) (powerTailWeight a) := by
    rw [sum_congr rfl (fun n hn => powerTailCenteredContact_apply a (by
      have := (mem_Icc.mp hn).1
      omega)), sum_sub_distrib, ← mul_sum]
    rfl
  rw [combForm_powerTailWeight_eq, hsum, powerTailPolarRemainder]
  ring

private theorem strictGrowth_combForm_iff_centeredContact {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    StrictNaturalPowerGrowth
      (fun N => HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a))
      (1 - 2 * a + σ) ↔
    StrictNaturalPowerGrowth
      (fun N => ∑ n ∈ Icc 1 N, powerTailCenteredContact a n) (1 - 2 * a + σ) := by
  let F := fun N => HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a)
  let B := fun N => ∑ n ∈ Icc 1 N, powerTailCenteredContact a n
  let E := fun N => powerTailPolarRemainder a N + powerTailArchimedean a N
  have hE : StrictNaturalPowerGrowth E (1 - 2 * a + σ) :=
    ((strictGrowth_powerTailPolarRemainder ha ha2).add
      (strictGrowth_powerTailArchimedean ha ha2)).mono (by linarith only [hσ])
  have he (N : ℕ) : E N = F N + 2 * B N := (combForm_powerTail_eq_centeredContact a N).symm
  change StrictNaturalPowerGrowth F _ ↔ StrictNaturalPowerGrowth B _
  constructor
  · intro hF
    have h := (hE.sub hF).const_mul (1 / 2)
    have hid : (fun N => (1 / 2 : ℝ) * (E N - F N)) = B := by
      funext N
      rw [he]
      ring
    simpa only [hid] using h
  · intro hB
    have h := hE.sub (hB.const_mul 2)
    have hid : (fun N => E N - 2 * B N) = F := by
      funext N
      rw [he]
      ring
    simpa only [hid] using h

/-- Normalization by `N^(2a-1)` translates the raw-comb growth exponent. -/
theorem powerCombTailGrowth_iff_unscaledGrowth (a σ : ℝ) :
    PowerCombTailGrowth a σ ↔
      StrictNaturalPowerGrowth
        (fun N => HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a))
        (1 - 2 * a + σ) := by
  have h := strictNaturalPowerGrowth_rpow_mul_iff
    (fun N => HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a))
    (1 - 2 * a + σ) (2 * a - 1)
  simpa only [show 1 - 2 * a + σ + (2 * a - 1) = σ by ring,
    PowerCombTailGrowth, powerCombTail] using h

/-- The actual power-comb growth threshold is exactly the rightmost zero
half-plane: exponent `σ` corresponds to `Re ρ ≤ 1-a+σ`. -/
theorem powerCombTailGrowth_iff_zeroHalfPlane {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    PowerCombTailGrowth a σ ↔ RHTower.XiZeroHalfPlaneBound (1 / 2 - a + σ) := by
  rw [powerCombTailGrowth_iff_unscaledGrowth,
    strictGrowth_combForm_iff_centeredContact ha ha2 hσ]
  exact strictGrowth_centeredContact_iff_zeroHalfPlane ha ha2 hσ

/-- RH is equivalent to subpolynomial growth of every positive subcritical
power tail of the actual comb. -/
theorem riemannHypothesis_iff_all_powerCombTails_subpolynomial :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 → PowerCombTailGrowth a 0 := by
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  constructor
  · intro h a ha ha2
    apply (powerCombTailGrowth_iff_zeroHalfPlane ha ha2 le_rfl).mpr
    intro ρ hρ
    have hh := h ρ hρ
    linarith only [hh, ha2]
  · intro h ρ hρ
    by_contra hbad
    have hρhalf : 1 / 2 < ρ.re := by simpa only [add_zero, not_le] using hbad
    let ε := min ((ρ.re - 1 / 2) / 2) (1 / 4)
    have hε : 0 < ε := lt_min (by linarith only [hρhalf]) (by norm_num)
    have hεsmall : ε ≤ 1 / 4 := min_le_right _ _
    have hεgap : ε ≤ (ρ.re - 1 / 2) / 2 := min_le_left _ _
    have ha : 0 < 1 / 2 - ε := by linarith only [hεsmall]
    have ha2 : 1 / 2 - ε < 1 / 2 := by linarith only [hε]
    have hb := (powerCombTailGrowth_iff_zeroHalfPlane ha ha2 le_rfl).mp
      (h (1 / 2 - ε) ha ha2) ρ hρ
    linarith only [hb, hεgap, hρhalf]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
