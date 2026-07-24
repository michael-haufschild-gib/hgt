import GaloisForLFunctions.RHTower.XiWardEdgeImChannelGram
import GaloisForLFunctions.RHTower.XiWardEdgeEnergyMarginWindow

/-!
# Sharp 8π laws from the Gram lattice sum

The quadratic explicit formula makes every ordered pair's Gram term a lower
bound for the edge quadratic energy.  The diagonal term carries one pair's
FULL modulus-squared deposit `8π(1/x + x/(x²+b²)) ≥ 8π/x`, twice the
real-channel floor, so every 4π-budget law doubles: the completeness window
extends to the closed budget `8π`, the spectral gap widens to `(0, 8π]`,
the counting law charges `8π` per pair, and the height-window clearing
budget doubles.  The `8π` window is sharp relative to the per-pair deposit:
a single pair deposits exactly `8π(1/x + x/(x²+b²))`, which approaches
`8π` as `x → 1`, `b → ∞`. -/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- Every ordered pair's Gram term bounds the edge energy from below. -/
theorem gramTerm_le_xiWardEdgeQuadEnergy (q q' : XiRightUpperZeroCopy) :
    ENNReal.ofReal (xiPairGramTerm q q') ≤ xiWardEdgeQuadEnergy := by
  rw [xiWardEdgeQuadEnergy_eq_tsum_gram]
  exact ENNReal.le_tsum (q, q')

/-- The diagonal Gram entry dominates the full deposit head `8π/x`. -/
theorem eightPi_div_le_xiPairGramTerm_diag (q : XiRightUpperZeroCopy) :
    8 * π / ((xiRightCenteredZero q.1).re + 1 / 2) ≤
      xiPairGramTerm q q := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  unfold xiPairGramTerm
  have h1 : (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
      ((xiRightCenteredZero q.1).im - (xiRightCenteredZero q.1).im) ^ 2 =
      4 * ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 := by ring
  have h3 : 16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) *
      (1 / (4 * ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2)) =
      8 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    field_simp
    ring
  have h2 : 0 ≤ 16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) *
      (1 / ((((xiRightCenteredZero q.1).re + 1 / 2) +
          ((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
        ((xiRightCenteredZero q.1).im +
          (xiRightCenteredZero q.1).im) ^ 2)) := by positivity
  rw [mul_add, h1]
  linarith [h2, h3]

/-- **The sharp 8π edge completeness law**: for any fixed budget
`0 ≤ c ≤ 8π` the Riemann Hypothesis is equivalent to the edge
quadratic-energy law at budget `c`.  This doubles the closed 4π window:
one off-critical pair already deposits `8π/x > 8π`. -/
theorem riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw_sharp
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 8 * π) :
    RiemannHypothesis ↔ ContinuedXiWardEdgeQuadEnergyLaw c := by
  constructor
  · intro hRH
    have h0 := (riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw
      (le_refl 0) (by positivity : (0 : ℝ) ≤ 4 * π)).mp hRH
    unfold ContinuedXiWardEdgeQuadEnergyLaw at h0 ⊢
    rw [ENNReal.ofReal_zero] at h0
    exact h0.trans zero_le'

  · intro hlaw
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
    have hre := xiRightCenteredZero_re_pos q.1
    have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
    have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by linarith
    have hfloor : ENNReal.ofReal
        (8 * π / ((xiRightCenteredZero q.1).re + 1 / 2)) ≤
        xiWardEdgeQuadEnergy :=
      (ENNReal.ofReal_le_ofReal
        (eightPi_div_le_xiPairGramTerm_diag q)).trans
        (gramTerm_le_xiWardEdgeQuadEnergy q q)
    have hchain := hfloor.trans hlaw
    rw [ENNReal.ofReal_le_ofReal_iff hc0] at hchain
    have hgt : 8 * π < 8 * π /
        ((xiRightCenteredZero q.1).re + 1 / 2) := by
      rw [lt_div_iff₀ hx]
      nlinarith [pi_pos]
    linarith

/-- **Doubled spectral gap**: the edge quadratic energy is `0` or strictly
above `8π`; the interval `(0, 8π]` is forbidden. -/
theorem xiWardEdgeQuadEnergy_eq_zero_or_eightPi_lt :
    xiWardEdgeQuadEnergy = 0 ∨
      ENNReal.ofReal (8 * π) < xiWardEdgeQuadEnergy := by
  rcases isEmpty_or_nonempty XiRightUpperZeroCopy with hempty | ⟨⟨q⟩⟩
  · left
    rw [xiWardEdgeQuadEnergy_eq_tsum_gram]
    exact tsum_empty
  · right
    have hre := xiRightCenteredZero_re_pos q.1
    have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
    have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by linarith
    calc ENNReal.ofReal (8 * π)
        < ENNReal.ofReal (8 * π /
            ((xiRightCenteredZero q.1).re + 1 / 2)) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          rw [lt_div_iff₀ hx]
          nlinarith [pi_pos]
      _ ≤ ENNReal.ofReal (xiPairGramTerm q q) :=
          ENNReal.ofReal_le_ofReal (eightPi_div_le_xiPairGramTerm_diag q)
      _ ≤ xiWardEdgeQuadEnergy := gramTerm_le_xiWardEdgeQuadEnergy q q

/-- **Doubled counting law**: `N` distinct strict-right pairs force edge
energy at least `N·8π`. -/
theorem card_nsmul_eightPi_le_xiWardEdgeQuadEnergy
    (F : Finset XiRightUpperZeroCopy) :
    ENNReal.ofReal (8 * π * F.card) ≤ xiWardEdgeQuadEnergy := by
  rw [xiWardEdgeQuadEnergy_eq_tsum_gram]
  have h1 : ∑ q ∈ F, ENNReal.ofReal (xiPairGramTerm q q) ≤
      ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
        ENNReal.ofReal (xiPairGramTerm p.1 p.2) := by
    have hinjF : ∀ a ∈ F, ∀ b ∈ F,
        (fun q : XiRightUpperZeroCopy => (q, q)) a =
          (fun q : XiRightUpperZeroCopy => (q, q)) b → a = b := by
      intro a _ b _ h
      exact congrArg Prod.fst h
    calc ∑ q ∈ F, ENNReal.ofReal (xiPairGramTerm q q)
        = ∑ p ∈ F.image (fun q : XiRightUpperZeroCopy => (q, q)),
            ENNReal.ofReal (xiPairGramTerm p.1 p.2) :=
          (Finset.sum_image hinjF).symm
      _ ≤ ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
            ENNReal.ofReal (xiPairGramTerm p.1 p.2) :=
          ENNReal.sum_le_tsum _
  refine le_trans ?_ h1
  calc ENNReal.ofReal (8 * π * F.card)
      = ∑ _q ∈ F, ENNReal.ofReal (8 * π) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          show (8 * π * (F.card : ℝ)) = (F.card : ℝ) * (8 * π) from by
            ring,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (F.card : ℝ)),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ q ∈ F, ENNReal.ofReal (xiPairGramTerm q q) :=
        Finset.sum_le_sum fun q _ => ENNReal.ofReal_le_ofReal
          (eightPi_le_xiPairGramTerm_diag q)

/-- **Doubled height-window clearing**: an edge energy certificate at
budget `8π(1 + m(T))` clears the strict-right divisor up to height `T`. -/
theorem height_lt_abs_im_of_xiWardEdgeQuadEnergy_le_eightPi {T : ℝ}
    (hlaw : xiWardEdgeQuadEnergy ≤
      ENNReal.ofReal (8 * π * (1 + xiWardZeroFreeMargin T)))
    (q : XiRightUpperZeroCopy) :
    T < |(xiRightCenteredZero q.1).im| := by
  by_contra hle
  push Not at hle
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) hle
  have hanti : xiWardZeroFreeMargin T ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im := by
    apply xiWardZeroFreeMargin_anti
    rwa [abs_of_nonneg hT0]
  have hre := xiRightCenteredZero_re_pos q.1
  have hM := xiRightCenteredZero_re_le_half_sub_margin q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hmb := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hmbh := xiWardZeroFreeMargin_le_half (xiRightCenteredZero q.1).im
  have h1mb : 0 < 1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
    by linarith
  have hx1m : (xiRightCenteredZero q.1).re + 1 / 2 ≤
      1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im := by linarith
  have hfloor : ENNReal.ofReal (8 * π /
      (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im)) ≤
      xiWardEdgeQuadEnergy := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      ((ENNReal.ofReal_le_ofReal
        (eightPi_div_le_xiPairGramTerm_diag q)).trans
        (gramTerm_le_xiWardEdgeQuadEnergy q q))
    exact div_le_div₀ (by positivity) le_rfl hx hx1m
  have hmT := xiWardZeroFreeMargin_pos T
  have hchain := hfloor.trans hlaw
  rw [ENNReal.ofReal_le_ofReal_iff
    (by nlinarith [pi_pos] : (0 : ℝ) ≤
      8 * π * (1 + xiWardZeroFreeMargin T))] at hchain
  have hbudget := fourPi_margin_budget_lt_floor T
  have h1mT : 0 < 1 - xiWardZeroFreeMargin T := by
    have := xiWardZeroFreeMargin_le_half T
    linarith
  have hTfloor : 8 * π / (1 - xiWardZeroFreeMargin T) ≤
      8 * π / (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) :=
    div_le_div₀ (by positivity) le_rfl h1mb (by linarith)
  have hdouble : 8 * π * (1 + xiWardZeroFreeMargin T) <
      8 * π / (1 - xiWardZeroFreeMargin T) := by
    have h4 := fourPi_margin_budget_lt_floor T
    have he : 8 * π / (1 - xiWardZeroFreeMargin T) =
        2 * (4 * π / (1 - xiWardZeroFreeMargin T)) := by
      field_simp
      norm_num
    rw [he]
    nlinarith [h4]
  linarith

end

end RHTower
