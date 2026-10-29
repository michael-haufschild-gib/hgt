import GaloisForLFunctions.RHTower.Zeta23TheoremASpectralSlack

/-!
# Displaced-pair thresholds at every subcritical bandwidth

For orthogonal hyperbolic pair blocks, the Frobenius constraint is
`2p(1+2η)² = (κ−1)N`. The true count, full spectral slack and off-line slack have
different exact thresholds. The formulas below keep the target proportion and
the Frobenius constant variable, then specialize to 70% and 75%.

For the zeta bandwidth parameter, `κ = 1/λ + λ/3` and `H(λ)=2−κ`.
These identities describe model blocks; they do not assert a displacement of zeta zeros.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Exact count, full-slack and off-line-slack tests for orthogonal hyperbolic pairs. -/
theorem hyperbolic_pair_thresholds {N p η κ θ : ℝ} (hp : 0 < p) (hη : 0 ≤ η)
    (hκ : 1 < κ) (hfrob : 2 * p * (1 + 2 * η)^2 = (κ - 1) * N) :
    (θ * N ≤ N - 2 * p ↔ κ - 1 ≤ (1 - θ) * (1 + 2 * η)^2) ∧
    ((θ + κ - 2) * N ≤ 4 * p * η * (1 + 2 * η) ↔
      θ + κ - 2 ≤ 2 * (1 - θ) * η) ∧
    ((θ + κ - 2) * N ≤ 4 * p * η * (1 + η) ↔
      κ - 1 ≤ (3 - 2 * θ - κ) * (1 + 2 * η)^2) := by
  have ha : 0 < κ - 1 := sub_pos.mpr hκ
  have hu : 0 < 1 + 2 * η := by linarith only [hη]
  have hcount : (κ - 1) * (N - 2 * p - θ * N) =
      (2 * p) * ((1 - θ) * (1 + 2 * η)^2 - (κ - 1)) := by
    calc _ = (1 - θ) * ((κ - 1) * N) - 2 * p * (κ - 1) := by ring
      _ = _ := by rw [← hfrob]; ring
  have hfull : (κ - 1) * (4 * p * η * (1 + 2 * η) - (θ + κ - 2) * N) =
      (2 * p * (1 + 2 * η)) * (2 * (1 - θ) * η - (θ + κ - 2)) := by
    calc _ = (κ - 1) * (4 * p * η * (1 + 2 * η)) -
        (θ + κ - 2) * ((κ - 1) * N) := by ring
      _ = _ := by rw [← hfrob]; ring
  have hoff : (κ - 1) * (4 * p * η * (1 + η) - (θ + κ - 2) * N) =
      p * ((3 - 2 * θ - κ) * (1 + 2 * η)^2 - (κ - 1)) := by
    calc _ = (κ - 1) * (4 * p * η * (1 + η)) -
        (θ + κ - 2) * ((κ - 1) * N) := by ring
      _ = _ := by rw [← hfrob]; ring
  constructor
  · rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left ha, hcount,
      mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) hp), sub_nonneg]
  constructor
  · rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left ha, hfull,
      mul_nonneg_iff_of_pos_left (mul_pos (mul_pos (by norm_num) hp) hu), sub_nonneg]
  · rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left ha, hoff,
      mul_nonneg_iff_of_pos_left hp, sub_nonneg]

/-- The asymptotic Frobenius coefficient corresponding to bandwidth `λ`. -/
def bandwidthFrobeniusConstant (lam : ℝ) : ℝ := 1 / lam + lam / 3

theorem bandwidthFrobeniusConstant_sub_Hfun (lam : ℝ) :
    Zeta23.Hfun lam = 2 - bandwidthFrobeniusConstant lam := by
  unfold Zeta23.Hfun bandwidthFrobeniusConstant
  ring

theorem bandwidthFrobeniusConstant_gt_one {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    1 < bandwidthFrobeniusConstant lam := by
  have hi : 1 < 1 / lam := (lt_div_iff₀ h0).mpr (by simpa using h1)
  unfold bandwidthFrobeniusConstant
  linarith only [hi, h0]

/-- Keeping the exact bandwidth coefficient gives the full threshold calculus on `[3/4,1)`. -/
theorem hyperbolic_pair_bandwidth_thresholds {N p η lam θ : ℝ}
    (hp : 0 < p) (hη : 0 ≤ η) (hlow : 3 / 4 ≤ lam) (hhigh : lam < 1)
    (hfrob : 2 * p * (1 + 2 * η)^2 = (bandwidthFrobeniusConstant lam - 1) * N) :
    (θ * N ≤ N - 2 * p ↔
      bandwidthFrobeniusConstant lam - 1 ≤ (1 - θ) * (1 + 2 * η)^2) ∧
    ((θ - Zeta23.Hfun lam) * N ≤ 4 * p * η * (1 + 2 * η) ↔
      θ - Zeta23.Hfun lam ≤ 2 * (1 - θ) * η) ∧
    ((θ - Zeta23.Hfun lam) * N ≤ 4 * p * η * (1 + η) ↔
      bandwidthFrobeniusConstant lam - 1 ≤
        (3 - 2 * θ - bandwidthFrobeniusConstant lam) * (1 + 2 * η)^2) := by
  have h := hyperbolic_pair_thresholds (θ := θ) hp hη
    (bandwidthFrobeniusConstant_gt_one (by linarith only [hlow]) hhigh) hfrob
  rw [bandwidthFrobeniusConstant_sub_Hfun,
    show θ - (2 - bandwidthFrobeniusConstant lam) =
      θ + bandwidthFrobeniusConstant lam - 2 by ring]
  exact h

/-- At 70%, the full-slack threshold is `(5/3)(κ−13/10)`; off-line slack has a
different threshold involving `8/5−κ`. -/
theorem hyperbolic_pair_seventy_percent {N p η κ : ℝ} (hp : 0 < p) (hη : 0 ≤ η)
    (hκ : 1 < κ) (hfrob : 2 * p * (1 + 2 * η)^2 = (κ - 1) * N) :
    ((7 / 10) * N ≤ N - 2 * p ↔ (10 / 3) * (κ - 1) ≤ (1 + 2 * η)^2) ∧
    ((κ - 13 / 10) * N ≤ 4 * p * η * (1 + 2 * η) ↔
      (5 / 3) * (κ - 13 / 10) ≤ η) ∧
    ((κ - 13 / 10) * N ≤ 4 * p * η * (1 + η) ↔
      κ - 1 ≤ (8 / 5 - κ) * (1 + 2 * η)^2) := by
  obtain ⟨hc, hf, ho⟩ := hyperbolic_pair_thresholds (θ := 7 / 10) hp hη hκ hfrob
  norm_num at hc hf ho
  have he : (7 / 10 : ℝ) + κ - 2 = κ - 13 / 10 := by ring
  rw [he] at hf ho
  refine ⟨hc.trans ?_, hf.trans ?_, ho.trans ?_⟩
  · constructor <;> intro h <;> linarith only [h]
  · constructor <;> intro h <;> linarith only [h]
  · constructor <;> intro h <;> linarith only [h]

/-- The 75% thresholds with a variable Frobenius coefficient. -/
theorem hyperbolic_pair_three_quarters {N p η κ : ℝ} (hp : 0 < p) (hη : 0 ≤ η)
    (hκ : 1 < κ) (hfrob : 2 * p * (1 + 2 * η)^2 = (κ - 1) * N) :
    ((3 / 4) * N ≤ N - 2 * p ↔ 4 * (κ - 1) ≤ (1 + 2 * η)^2) ∧
    ((κ - 5 / 4) * N ≤ 4 * p * η * (1 + 2 * η) ↔ 2 * κ - 5 / 2 ≤ η) ∧
    ((κ - 5 / 4) * N ≤ 4 * p * η * (1 + η) ↔
      κ - 1 ≤ (3 / 2 - κ) * (1 + 2 * η)^2) := by
  obtain ⟨hc, hf, ho⟩ := hyperbolic_pair_thresholds (θ := 3 / 4) hp hη hκ hfrob
  norm_num at hc hf ho
  have he : (3 / 4 : ℝ) + κ - 2 = κ - 5 / 4 := by ring
  rw [he] at hf ho
  refine ⟨hc.trans ?_, hf.trans ?_, ho.trans ?_⟩
  · constructor <;> intro h <;> linarith only [h]
  · constructor <;> intro h <;> linarith only [h]
  · constructor <;> intro h <;> linarith only [h]

/-- At the bandwidth-one limiting constant, the three 70% thresholds are
`(1+2η)²≥10/9`, `η≥1/18`, and `(1+2η)²≥5/4`. -/
theorem hyperbolic_pair_seventy_percent_at_four_thirds {N p η : ℝ}
    (hp : 0 < p) (hη : 0 ≤ η)
    (hfrob : 2 * p * (1 + 2 * η)^2 = (1 / 3) * N) :
    ((7 / 10) * N ≤ N - 2 * p ↔ (10 / 9) ≤ (1 + 2 * η)^2) ∧
    ((1 / 30) * N ≤ 4 * p * η * (1 + 2 * η) ↔ (1 / 18) ≤ η) ∧
    ((1 / 30) * N ≤ 4 * p * η * (1 + η) ↔ (5 / 4) ≤ (1 + 2 * η)^2) := by
  have hfrob' : 2 * p * (1 + 2 * η)^2 = ((4 / 3 : ℝ) - 1) * N := by
    norm_num
    exact hfrob
  obtain ⟨hc, hf, ho⟩ := hyperbolic_pair_seventy_percent hp hη (by norm_num) hfrob'
  norm_num at hc hf ho
  refine ⟨hc, hf, ho.trans ?_⟩
  constructor <;> intro h <;> linarith only [h]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.hyperbolic_pair_bandwidth_thresholds
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.hyperbolic_pair_seventy_percent_at_four_thirds
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.hyperbolic_pair_three_quarters
