import GaloisForLFunctions.SquareRootThreshold.AnExplicitClusterDetectorConstant
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount

/-!
# A sharper cluster-detector constant

The detector at aperture `4((n+1) log(10⁶/δ) + log(240(|γ|+3)))` needs a count `n` of the distinct zeros
in a window of length `200` around `γ`. Summing the unit-window bound over `200` windows gives
`n ≤ 96000 log(|γ|+3)`. The explicit Riemann–von Mangoldt count gives `n ≤ 282 log(|γ|+3)` from height
`110`, because the window length enters only through the slope `1/(2π)`. The detector constant drops
from `480000` to `1200`.
-/

noncomputable section
open Complex Set Metric
open scoped ComplexConjugate

namespace GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower Zeta23

/-- Distinct zeros in a window of length `200` above height `110`. -/
theorem zeta_Nd_window_le {γ : ℝ} (hγ : 110 ≤ γ) :
    (zetaZeroConfig.Nd (γ - 100) (γ + 100) : ℝ) ≤ 282 * Real.log (γ + 3) := by
  have hfin : (zetaZeroConfig.window (γ - 100) (γ + 100)).Finite :=
    zetaZeroConfig.finite_window (γ - 100) (γ + 100)
  have hNd : zetaZeroConfig.Nd (γ - 100) (γ + 100) = hfin.toFinset.card := by
    rw [ZeroConfig.Nd, Set.ncard_eq_toFinset_card _ hfin]
  have hcount := ZeroConfigurationGeometry.card_le_sharp_explicit (γ - 100) (γ + 100)
    (by linarith only [hγ]) (by linarith only [hγ]) hfin.toFinset (fun z hz => by
      rw [Set.Finite.mem_toFinset] at hz
      exact ⟨hz.1, hz.2.1.le, hz.2.2⟩)
  rw [hNd]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (γ + 3) := ⟨_, rfl⟩
  rw [← hL]
  have hL4 : 4 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith only [hγ])]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 4 ≤ (2.72 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith only [Real.exp_one_lt_d9]) 4
    have h5 : (2.72 : ℝ) ^ 4 ≤ 60 := by norm_num
    linarith only [h3, h4, h5, hγ]
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hy : Real.log (γ + 100 + 2) ≤ L + 7 / 10 := by
    have h1 : Real.log (γ + 100 + 2) ≤ Real.log (2 * (γ + 3)) :=
      Real.log_le_log (by linarith only [hγ]) (by linarith only [hγ])
    rw [Real.log_mul (by norm_num) (by linarith only [hγ]), ← hL] at h1
    linarith only [h1, hlog2]
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hy2 : Real.log ((γ + 100 + 2) / (2 * Real.pi)) ≤ L + 7 / 10 := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hy
    exact div_le_self (by linarith only [hγ]) hpi
  have hfrac : 6 / (γ - 100 - 2) ≤ 3 / 4 := by
    rw [div_le_iff₀ (by linarith only [hγ])]
    linarith only [hγ]
  have hL0 : 0 ≤ L + 7 / 10 + 3 / 4 := by linarith only [hL4]
  have hdiv : (Real.log ((γ + 100 + 2) / (2 * Real.pi)) + 6 / (γ - 100 - 2)) / (2 * Real.pi) ≤
      (L + 7 / 10 + 3 / 4) / 6 := by
    calc _ ≤ (L + 7 / 10 + 3 / 4) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right (by linarith only [hy2, hfrac]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hL0 (by norm_num) (by linarith only [Real.pi_gt_three])
  have hw : γ + 100 - (γ - 100) + 3 = 203 := by ring
  rw [hw] at hcount
  have hfirst := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 203 by norm_num)
  linarith only [hcount, hfirst, hy, hL4]

/-- A high off-line zero has a detector at aperture `1200 log(|γ|+3) log(10⁶/δ)`. -/
theorem not_hodgeIndex_of_sharp_explicit_aperture {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|)
    (hγ : 110 ≤ |ρ.im|) {a : ℝ}
    (hsize : 1200 * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / δ) ≤ a) :
    ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  -- Reduce to a positive ordinate by conjugation.
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ zetaZeroConfig.carrier, σ.re = ρ.re ∧ σ.im = |ρ.im| := by
    rcases le_total 0 ρ.im with h | h
    · exact ⟨ρ, hρ, rfl, (abs_of_nonneg h).symm⟩
    · exact ⟨conj ρ, conj_mem_zetaZeroConfig hρ, Complex.conj_re ρ, by
        rw [Complex.conj_im, abs_of_nonpos h]⟩
  have hγσ : 110 ≤ σ.im := by rw [hσim]; exact hγ
  have hreσ : δ ≤ |σ.re - 1 / 2| := by rwa [hσre]
  have habs : |σ.im| = σ.im := abs_of_nonneg (by linarith only [hγσ])
  have hst := zetaZeroConfig.strip ρ hρ
  have hδ2 : δ ≤ 1 / 2 := by
    apply hre.trans
    rw [abs_le]
    constructor <;> linarith only [hst.1, hst.2]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (σ.im + 3) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (10 ^ 6 / δ) := ⟨_, rfl⟩
  have hL4 : 4 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith only [hγσ])]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 4 ≤ (2.72 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith only [Real.exp_one_lt_d9]) 4
    have h5 : (2.72 : ℝ) ^ 4 ≤ 60 := by norm_num
    linarith only [h3, h4, h5, hγσ]
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]
    have he : Real.exp 1 ≤ 10 ^ 6 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith only [Real.exp_one_lt_d9, hδ2, hδ, Real.exp_pos 1]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr he
  have hn := zeta_Nd_window_le hγσ
  rw [← hL] at hn
  apply not_hodgeIndex_below_nyquist_horizon zetaZeroConfig (A₀ := 240)
    (by norm_num) zeta_unit_count_le_240 hσ hδ hreσ (by rw [habs]; linarith only [hγσ]) le_rfl
  rw [habs, ← hΛ]
  have hlog240 : Real.log 240 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 6
    have h5 : (240 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    linarith only [h3, h5, h6]
  have hG : Real.log (240 * (σ.im + 3)) ≤ 6 + L := by
    rw [Real.log_mul (by norm_num) (by linarith only [hγσ]), ← hL]
    linarith only [hlog240]
  have hNΛ : ((zetaZeroConfig.Nd (σ.im - 100) (σ.im + 100) : ℝ) + 1) * Λ ≤ (282 * L + L) * Λ :=
    mul_le_mul_of_nonneg_right (by linarith only [hn, hL4]) (by linarith only [hΛ1])
  have hLΛ : L ≤ L * Λ := le_mul_of_one_le_right (by linarith only [hL4]) hΛ1
  have hsize' : 1200 * L * Λ ≤ a := by
    rw [hL, hΛ, hσim]
    exact hsize
  have hpos : 0 ≤ L * Λ := by nlinarith only [hL4, hΛ1]
  nlinarith only [hNΛ, hG, hLΛ, hpos, hsize', hL4]

/-- **The sharper exponential corridor.** A positive Hodge level `a` confines every zero of height at
least `110` to depth below `10⁶ exp(−a/(1200 log(|γ|+3)))`. -/
theorem depth_lt_sharp_explicit_of_hodgeIndex {a : ℝ}
    (hodge : HodgeIndexAtLevel zetaZeroConfig a) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) (hγ : 110 ≤ |ρ.im|) :
    |ρ.re - 1 / 2| < 10 ^ 6 * Real.exp (-(a / (1200 * Real.log (|ρ.im| + 3)))) := by
  let δ := |ρ.re - 1 / 2|
  let K := 1200 * Real.log (|ρ.im| + 3)
  have hK : 0 < K := mul_pos (by norm_num) (Real.log_pos (by linarith only [hγ]))
  have hE : 0 < 10 ^ 6 * Real.exp (-(a / K)) := by positivity
  by_contra h
  have hge : 10 ^ 6 * Real.exp (-(a / K)) ≤ δ := not_lt.mp h
  have hδ : 0 < δ := hE.trans_le hge
  have hdiv : 10 ^ 6 / δ ≤ Real.exp (a / K) := by
    rw [div_le_iff₀ hδ]
    have hh := mul_le_mul_of_nonneg_right hge (Real.exp_pos (a / K)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hh
    simpa only [mul_comm] using hh
  have hlog := Real.log_le_log (by positivity : 0 < 10 ^ 6 / δ) hdiv
  rw [Real.log_exp, le_div_iff₀ hK] at hlog
  exact not_hodgeIndex_of_sharp_explicit_aperture hδ hρ le_rfl hγ
    (by change K * Real.log (10 ^ 6 / δ) ≤ a; linarith only [hlog]) hodge

end GaloisForLFunctions.SquareRootThreshold
