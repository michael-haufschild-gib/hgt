import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.HTGeometry.GammaLogDeriv

/-!
# The anomaly window and the resonant range of the archimedean phase

Let `Ω(τ) = Re ψ(¼ + iτ/2) − log π` (`EF.gammaBracket`), the derivative of the archimedean phase
`2θ(τ)`.  `Ω` is even, nondecreasing in `|τ|`, negative at `0` with `e^{|Ω(0)|} = 8π e^{γ+π/2}`.

* **Anomaly window** (`exists_anomaly_window`): `Ω < 0` exactly on an interval `|τ| < t₀`, with
  `0 < t₀ ≤ 20`.
* **Resonant range** (`exists_gammaBracket_eq_neg_log_iff`): the phase `2θ(τ) + τ log n` is
  stationary somewhere, i.e. `Ω(τ) = −log n` is solvable, iff `n ≤ e^{|Ω(0)|} = 8π e^{γ+π/2}`.
* **Resonances lie in `|τ| < 2π`** (`abs_lt_two_pi_of_gammaBracket_eq_neg_log`): for `n ≥ 2` every
  stationary point has `|τ| < 2π`, because `Ω(2π) > −log 2` (`neg_log_two_lt_gammaBracket_two_pi`,
  from `ψ(z + 10) = ψ(z) + Σ_{k<10} 1/(z + k)` and `‖ψ(w) − log w‖ ≤ 3/‖w‖`).
-/

open Complex Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower.ArchimedeanResonance

open ArchimedeanAnomaly

noncomputable section

/-- `Re ψ(z) ≥ log ‖z‖ − 3/‖z‖` on `Re z > 0`, `‖z‖ ≥ 2`. -/
theorem log_norm_sub_le_re_digamma {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    Real.log ‖z‖ - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
  have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hre hz
  have h1 : |(Complex.digamma z - Complex.log z).re| ≤ 3 / ‖z‖ :=
    (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re, Complex.log_re] at h1
  linarith [neg_abs_le ((Complex.digamma z).re - Real.log ‖z‖)]

theorem gammaBracket_twenty_pos : 0 < EF.gammaBracket 20 := by
  set z : ℂ := 1 / 4 + I * ((20 : ℝ) : ℂ) / 2 with hz
  have hre : z.re = 1 / 4 := by simp [hz]
  have him : z.im = 10 := by simp [hz]; norm_num
  have hn : 10 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [him, abs_of_pos (by norm_num : (0 : ℝ) < 10)] at this
    exact this
  have hd := log_norm_sub_le_re_digamma (by rw [hre]; norm_num) (by linarith)
  have hlog : Real.log 10 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) hn
  have h3 : 3 / ‖z‖ ≤ 3 / 10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have hl10 : 2 < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos 1]
  have hpi : Real.log π < 3 / 2 := by
    have h4 : Real.log π < Real.log 4 := Real.log_lt_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  unfold EF.gammaBracket
  rw [← hz]
  linarith

/-- **The anomaly window**: `Ω < 0` exactly on `|τ| < t₀`, for some `0 < t₀ ≤ 20`. -/
theorem exists_anomaly_window :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 20 ∧ ∀ t : ℝ, EF.gammaBracket t < 0 ↔ |t| < t₀ := by
  set S : Set ℝ := {t | 0 ≤ t ∧ 0 ≤ EF.gammaBracket t} with hS
  have hcont := WeilHerglotz.continuous_gammaBracket
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const hcont)
  have h20 : (20 : ℝ) ∈ S := ⟨by norm_num, gammaBracket_twenty_pos.le⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hne : S.Nonempty := ⟨20, h20⟩
  set t₀ := sInf S
  have ht₀S : t₀ ∈ S := hclosed.csInf_mem hne hbdd
  have hΩ0 : EF.gammaBracket 0 < 0 := by
    rw [gammaBracket_zero_eq]
    have hγ : 0 < Real.eulerMascheroniConstant :=
      Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num)
    have hl : 0 < Real.log (8 * π) := Real.log_pos (by nlinarith [Real.pi_gt_three])
    linarith [Real.pi_pos]
  have ht₀pos : 0 < t₀ := by
    rcases ht₀S.1.eq_or_lt with h | h
    · exfalso
      have := ht₀S.2
      rw [← h] at this
      linarith
    · exact h
  refine ⟨t₀, ht₀pos, csInf_le hbdd h20, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · by_contra hge
    push Not at hge
    have := gammaBracket_mono (show |t₀| ≤ |t| by rwa [abs_of_pos ht₀pos])
    linarith [ht₀S.2]
  · by_contra hge
    push Not at hge
    have habs : |t| ∈ S := by
      refine ⟨abs_nonneg t, ?_⟩
      have := gammaBracket_mono (show |t| ≤ |(|t|)| by rw [abs_abs])
      linarith
    have := csInf_le hbdd habs
    linarith

/-- **The resonant range.**  `Ω(τ) = −log n` has a solution iff `n ≤ e^{|Ω(0)|} = 8π e^{γ+π/2}`. -/
theorem exists_gammaBracket_eq_neg_log_iff {n : ℕ} (hn : 1 ≤ n) :
    (∃ τ : ℝ, EF.gammaBracket τ = -Real.log n) ↔
      (n : ℝ) ≤ 8 * π * Real.exp (Real.eulerMascheroniConstant + π / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have habs : |EF.gammaBracket 0| = -EF.gammaBracket 0 := by
    rw [abs_of_neg]
    rw [gammaBracket_zero_eq]
    have hγ : 0 < Real.eulerMascheroniConstant :=
      Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num)
    have hl : 0 < Real.log (8 * π) := Real.log_pos (by nlinarith [Real.pi_gt_three])
    linarith [Real.pi_pos]
  rw [← exp_abs_gammaBracket_zero, habs, ← Real.log_le_iff_le_exp hn0]
  constructor
  · rintro ⟨τ, hτ⟩
    have := gammaBracket_zero_le τ
    linarith
  · intro h
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    obtain ⟨τ, -, hτ⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 20 by norm_num)
      WeilHerglotz.continuous_gammaBracket.continuousOn
      (show -Real.log n ∈ Icc (EF.gammaBracket 0) (EF.gammaBracket 20) from
        ⟨by linarith, by linarith [gammaBracket_twenty_pos]⟩)
    exact ⟨τ, hτ⟩

/-- `Σ_{k<10} (k + ¼)/((k + ¼)² + 9.85) < 1.19`. -/
theorem sum_ten_lt :
    ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 985 / 100) < 119 / 100 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `Ω(2π) > −log 2`. -/
theorem neg_log_two_lt_gammaBracket_two_pi : -Real.log 2 < EF.gammaBracket (2 * π) := by
  set z₀ : ℂ := 1 / 4 + π * I with hz₀
  have harg : (1 / 4 + I * ((2 * π : ℝ) : ℂ) / 2 : ℂ) = z₀ := by rw [hz₀]; push_cast; ring
  have hpole : ∀ k : ℕ, z₀ ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.im h
    simp [hz₀, Real.pi_ne_zero] at this
  have hrec := HTGeometry.digamma_add_nat z₀ hpole 10
  set w : ℂ := z₀ + (10 : ℕ) with hw
  have hwre : w.re = 41 / 4 := by simp [hw, hz₀]; norm_num
  have hwn : 41 / 4 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_pos (by norm_num : (0 : ℝ) < 41 / 4)] at this
    exact this
  have hd := log_norm_sub_le_re_digamma (by rw [hwre]; norm_num) (by linarith)
  have hlog : Real.log (41 / 4) ≤ Real.log ‖w‖ := Real.log_le_log (by norm_num) hwn
  have h3 : 3 / ‖w‖ ≤ 3 / (41 / 4) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hwn
  -- the ten correction terms
  have hπ2 : (985 / 100 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hterm : ∀ k : ℕ, ((z₀ + k)⁻¹).re ≤ ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 985 / 100) := by
    intro k
    have hre : (z₀ + k).re = (k : ℝ) + 1 / 4 := by simp [hz₀]; ring
    have him : (z₀ + k).im = π := by simp [hz₀]
    rw [Complex.inv_re, Complex.normSq_apply, hre, him]
    have hk : (0 : ℝ) < (k : ℝ) + 1 / 4 := by positivity
    rw [show ((k : ℝ) + 1 / 4) * ((k : ℝ) + 1 / 4) + π * π = ((k : ℝ) + 1 / 4) ^ 2 + π ^ 2 by ring]
    exact div_le_div_of_nonneg_left hk.le (by positivity) (by linarith)
  have hsum : (∑ i ∈ Finset.range 10, (z₀ + (i : ℂ))⁻¹).re < 119 / 100 := by
    rw [Complex.re_sum]
    exact lt_of_le_of_lt (Finset.sum_le_sum fun k _ => hterm k) sum_ten_lt
  have hre_rec : (Complex.digamma z₀).re = (Complex.digamma w).re -
      (∑ i ∈ Finset.range 10, (z₀ + (i : ℂ))⁻¹).re := by
    rw [hw, hrec, Complex.add_re]; ring
  -- `log(41/4) − log π > 1` since `41/(4π) > 3 > e`
  have hlogπ : 1 < Real.log (41 / 4) - Real.log π := by
    rw [← Real.log_div (by norm_num) Real.pi_ne_zero, Real.lt_log_iff_exp_lt (by positivity)]
    have he := Real.exp_one_lt_d9
    rw [lt_div_iff₀ Real.pi_pos]
    have h1 := mul_lt_mul_of_pos_right he Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hl2 := Real.log_two_gt_d9
  unfold EF.gammaBracket
  rw [harg, hre_rec]
  norm_num at h3
  linarith

/-- **Every resonance lies in the window `|τ| < 2π`** (for `n ≥ 2`). -/
theorem abs_lt_two_pi_of_gammaBracket_eq_neg_log {n : ℕ} (hn : 2 ≤ n) {τ : ℝ}
    (hτ : EF.gammaBracket τ = -Real.log n) : |τ| < 2 * π := by
  by_contra hge
  push Not at hge
  have hmono := gammaBracket_mono (show |2 * π| ≤ |τ| by
    rwa [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)])
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  linarith [neg_log_two_lt_gammaBracket_two_pi]

end

end RHTower.ArchimedeanResonance
