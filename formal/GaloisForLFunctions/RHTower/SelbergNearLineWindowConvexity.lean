import GaloisForLFunctions.RHTower.SelbergNearLineWindowBounds
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.HTGeometry.StripSquareMeanConvexity

/-!
# Three-lines for one Gaussian window of the mollified tail

Fix a window `[τ − H, τ + H]` above height `1`. If every translate of the window on the left line
`Re z = σ_L` has windowed mean square at most `S_L`, then on any center line
`1/2 ≤ σ₀ ≤ 1` the tail `f_N = ζΨ_N − 1 − P_N` satisfies

`∫_{τ−H}^{τ+H} ‖f_N(σ₀+it)‖² dt ≤ 2e² S_L^{1−λ} (16H/N²)^λ`,  `λ = (σ₀−σ_L)/(3−σ_L)`
(`integral_hbMollifiedTail_window_le`).

The right line `Re z = 3` supplies `16H/N²` (the tail beyond the von Mangoldt head is `O(1/N)`
there), the Gaussian makes the field bounded on the strip, and the pole at `s = 1` is cleared by
`(z−1)/z`.

The left-line hypothesis is discharged window by window (`integral_nearLineWindowField_left_near_le`)
from three mean squares on `Re s = σ_L`: that of `ζΨ_N` (the mollified gate), that of `1`, and that
of the von Mangoldt head `P_N`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

theorem continuousAt_hbMollifiedTail {N : ℕ} {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt (hbMollifiedTail N) z := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  unfold hbMollifiedTail
  exact (((differentiableAt_riemannZeta hz).continuousAt.mul
    (differentiable_edPoly _ hs z).continuousAt).sub continuousAt_const).sub
    (differentiable_edPoly _ hs z).continuousAt

theorem continuousOn_normSq_hbMollifiedTail_line (N : ℕ) (σ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => ‖hbMollifiedTail N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Icc a b) := by
  intro t ht
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  have hc : ContinuousAt (fun t : ℝ => hbMollifiedTail N ((σ : ℂ) + (t : ℂ) * I)) t :=
    ContinuousAt.comp (g := hbMollifiedTail N) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (continuousAt_hbMollifiedTail hne) (by fun_prop)
  exact (hc.norm.pow 2).continuousWithinAt

/-- **Three-lines for one window.** -/
theorem integral_hbMollifiedTail_window_le {N : ℕ} (hN : 2 ≤ N) {H τ σL σ₀ SL CW : ℝ}
    (hH : 6 ≤ H) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hσL : 1 / 4 ≤ σL) (hσL₀ : σL ≤ σ₀) (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀' : σ₀ ≤ 1)
    (hτ : 1 + H ≤ τ) (hSL : 0 < SL)
    (hleft : ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ ((σL : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SL) :
    ∫ t in (τ - H)..(τ + H), ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.exp 2 *
        (SL ^ (1 - (σ₀ - σL) / (3 - σL)) * (16 * H / N ^ 2) ^ ((σ₀ - σL) / (3 - σL))) := by
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlu : σL < 3 := by linarith
  set F : ℂ → ℂ := nearLineWindowField N H τ with hF
  have hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := differentiableOn_nearLineWindowField N H τ
  have hsub : closure (Complex.HadamardThreeLines.verticalStrip σL 3) ⊆ {z : ℂ | 0 < z.re} := by
    rw [GaloisForLFunctions.HTGeometry.closure_verticalStrip hlu]
    intro z hz
    have : z.re ∈ Icc σL 3 := hz
    show 0 < z.re
    linarith [this.1]
  have hdc : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip σL 3) :=
    (hFd.mono hsub).diffContOnCl
  have hM : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip σL 3,
      ‖F z‖ ≤ Real.exp 1 * (CW * N * ((1 + |τ|) * (1 + H))) := by
    intro z hz
    have : z.re ∈ Icc σL 3 := hz
    exact norm_nearLineWindowField_le (by linarith) hCW hW (by linarith [this.1]) this.2
  have hSR : 0 < 16 * H / N ^ 2 := by positivity
  have hright : ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖F (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 16 * H / N ^ 2 :=
    fun y => integral_nearLineWindowField_three_le hN hH y
  have hthree := GaloisForLFunctions.HTGeometry.integral_normSq_le_of_three_lines
    (F := F) (l := σL) (u := 3) (σ := σ₀) (A := τ - H) (B := τ + H) hlu hσL₀ (by linarith)
    (by linarith) hdc hM hSL hSR hleft hright
  -- the tail is dominated by the windowed field on the center line
  have hab : τ - H ≤ τ + H := by linarith
  have hpos : 0 < τ - H := by linarith
  have hint1 : IntervalIntegrable
      (fun t : ℝ => ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume (τ - H) (τ + H) :=
    (continuousOn_normSq_hbMollifiedTail_line N σ₀ hpos).intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable
      (fun t : ℝ => 2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume (τ - H) (τ + H) :=
    (continuous_const.mul ((continuous_nearLineWindowField_line N H τ
      (by linarith : (0 : ℝ) < σ₀)).norm.pow 2)).intervalIntegrable _ _
  have hpt : ∀ t ∈ Icc (τ - H) (τ + H),
      ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t ht
    refine normSq_hbMollifiedTail_le_window hH0 hσ₀ hσ₀' ?_ ?_
    · exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [abs_of_pos (by linarith [ht.1])]
      linarith [ht.1]
  calc ∫ t in (τ - H)..(τ + H), ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ ∫ t in (τ - H)..(τ + H), 2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    _ = 2 * Real.exp 2 * ∫ t in (τ - H)..(τ + H), ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)

/-- **One left window near the center.** On `Re s = σ_L ∈ [3/8, 1/2]`, the windowed field is at most
`18` times `‖ζΨ_N‖² + 1 + ‖P_N‖²`, so its mean square over `[α, α + 2H]` is controlled by the three
corresponding mean squares. -/
theorem integral_nearLineWindowField_left_near_le {N : ℕ} {H τ σL α G P : ℝ} (hH : 3 ≤ H)
    (hσL : 3 / 8 ≤ σL) (hσL' : σL ≤ 1 / 2) (hα : 2 ≤ α)
    (hG : ∫ u in α..(α + 2 * H), ‖riemannZeta ((σL : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ G)
    (hP : ∫ u in α..(α + 2 * H),
        ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ P) :
    ∫ u in α..(α + 2 * H), ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      18 * (G + 2 * H + P) := by
  have hH0 : 0 < H := by linarith
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hab : α ≤ α + 2 * H := by linarith
  set Z : ℝ → ℂ := fun u => riemannZeta ((σL : ℂ) + (u : ℂ) * I) *
    edPoly (hbCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I) with hZ
  set Q : ℝ → ℂ := fun u =>
    edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I) with hQ
  have hne : ∀ u ∈ Icc α (α + 2 * H), ((σL : ℂ) + (u : ℂ) * I) ≠ 1 := by
    intro u hu h
    have := congrArg Complex.im h
    simp at this
    linarith [hu.1]
  have hZc : ContinuousOn (fun u => ‖Z u‖ ^ 2) (Icc α (α + 2 * H)) := by
    intro u hu
    have hc : ContinuousAt Z u :=
      (ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (σL : ℂ) + (u : ℂ) * I)
        (differentiableAt_riemannZeta (hne u hu)).continuousAt (by fun_prop)).mul
        (ContinuousAt.comp (g := edPoly (hbCoeff N) (Finset.Icc 1 N))
          (f := fun u : ℝ => (σL : ℂ) + (u : ℂ) * I)
          (differentiable_edPoly _ hs _).continuousAt (by fun_prop))
    exact (hc.norm.pow 2).continuousWithinAt
  have hQc : Continuous fun u => ‖Q u‖ ^ 2 :=
    (((differentiable_edPoly _ hs).continuous.comp (by fun_prop)).norm.pow 2)
  have hint1 : IntervalIntegrable
      (fun u : ℝ => ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2) volume α
        (α + 2 * H) :=
    ((continuous_nearLineWindowField_line N H τ (by linarith : (0 : ℝ) < σL)).norm.pow 2
      ).intervalIntegrable _ _
  have hintZ : IntervalIntegrable (fun u => ‖Z u‖ ^ 2) volume α (α + 2 * H) :=
    hZc.intervalIntegrable_of_Icc hab
  have hintQ : IntervalIntegrable (fun u => ‖Q u‖ ^ 2) volume α (α + 2 * H) :=
    hQc.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u => 18 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2)) volume α
      (α + 2 * H) :=
    ((hintZ.add intervalIntegrable_const).add hintQ).const_mul 18
  have hpt : ∀ u ∈ Icc α (α + 2 * H),
      ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
        18 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2) := by
    intro u hu
    set z : ℂ := (σL : ℂ) + (u : ℂ) * I with hzdef
    have hzre : z.re = σL := by simp [hzdef]
    have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
    unfold nearLineWindowField
    rw [norm_mul, mul_pow, nearLineField_eq hz0 (hne u hu), norm_mul, mul_pow]
    have hG2 : ‖nearLineGauss H τ z‖ ^ 2 ≤ 2 := by
      rw [hzdef, norm_nearLineGauss, ← Real.exp_nat_mul]
      have h1 : ((2 : ℕ) : ℝ) * ((σL ^ 2 - (u - τ) ^ 2) / H ^ 2) ≤ 1 / 2 := by
        push_cast
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (u - τ)]
      calc Real.exp (((2 : ℕ) : ℝ) * ((σL ^ 2 - (u - τ) ^ 2) / H ^ 2)) ≤ Real.exp (1 / 2) :=
            Real.exp_le_exp.mpr h1
        _ ≤ 2 := by
            have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
              rw [← Real.exp_nat_mul]; norm_num
            have hlt := Real.exp_one_lt_d9
            nlinarith [Real.exp_pos (1 / 2)]
    have hfac : ‖(z - 1) / z‖ ^ 2 ≤ 3 :=
      norm_sub_one_div_sq_le_three (by rw [hzre]; exact hσL) (by rw [hzre]; exact hσL')
    have htail : ‖hbMollifiedTail N z‖ ^ 2 ≤ 3 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2) := by
      have htri : ‖hbMollifiedTail N z‖ ≤ ‖Z u‖ + 1 + ‖Q u‖ := by
        unfold hbMollifiedTail
        have h1 := norm_sub_le (riemannZeta z * edPoly (hbCoeff N) (Finset.Icc 1 N) z - 1)
          (edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z)
        have h2 := norm_sub_le (riemannZeta z * edPoly (hbCoeff N) (Finset.Icc 1 N) z) 1
        rw [norm_one] at h2
        simp only [hZ, hQ, ← hzdef]
        linarith
      have hsq : (‖Z u‖ + 1 + ‖Q u‖) ^ 2 ≤ 3 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Z u‖ - 1), sq_nonneg (‖Z u‖ - ‖Q u‖), sq_nonneg (‖Q u‖ - 1)]
      exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans hsq
    have h0 : 0 ≤ ‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2 := by positivity
    calc ‖nearLineGauss H τ z‖ ^ 2 * (‖(z - 1) / z‖ ^ 2 * ‖hbMollifiedTail N z‖ ^ 2)
        ≤ 2 * (3 * (3 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2))) := by
          gcongr
      _ = 18 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2) := by ring
  calc ∫ u in α..(α + 2 * H), ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2
      ≤ ∫ u in α..(α + 2 * H), 18 * (‖Z u‖ ^ 2 + 1 + ‖Q u‖ ^ 2) :=
        intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    _ = 18 * ((∫ u in α..(α + 2 * H), ‖Z u‖ ^ 2) + 2 * H +
          ∫ u in α..(α + 2 * H), ‖Q u‖ ^ 2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (hintZ.add intervalIntegrable_const) hintQ, intervalIntegral.integral_add hintZ
          intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ 18 * (G + 2 * H + P) := by
        have := add_le_add (add_le_add_right hG (2 * H)) hP
        linarith

end RHTower
