import GaloisForLFunctions.RHTower.FiniteEulerStageNearLineStrip

/-!
# Euler stages repel above the horizon

A repulsion law along the Euler-depth deformation. The finite Euler stage
`Λ_X(s) = A_X(s) + A_X(1 − s)`, `A_X(s) = Γ_ℝ(s) exp(Σ_{n ≤ X} Λ(n) n^{−s}/log n)`, is real on the
critical line, where it equals `2 Re A_X(½ + it)` (`eulerStage_linePt`). Its zeros there are the
heights where the phase of `A_X` crosses `π/2 + πℤ`, and the phase moves with the speed
`Re L_X(½ + it)`, `L_X = A_X'/A_X = ψ_ℝ − Σ_{n ≤ X} Λ(n) n^{−s}` (`stageSpeed`).

* **The phase law** (`stageLine_eq_mul_exp`). `A_X(½+it) = A_X(½+it₀) exp(i Θ(t))` with
  `Θ(t) = ∫_{t₀}^t L_X(½+iτ) dτ`: the quotient has derivative zero.
* **Gaps from the phase** (`eulerStage_ne_zero_of_phase_lt`, `exists_eulerStage_zero_of_phase_ge`).
  After a zero, `Λ_X` has no zero on the line before the phase has turned by `π`, and it has one
  by the time the phase has turned by `π`.
* **Simplicity** (`eulerStage_deriv_ne_zero`). At a zero on the line with positive phase speed,
  `Λ_X'(½+it₀) = −2i Im A_X(½+it₀) Re L_X(½+it₀) ≠ 0`.
* **The speed above the horizon** (`re_stageSpeed_ge`, `re_stageSpeed_le`). For `|τ| ≥ 4`,
  `(log(|τ|/2π) − 6/|τ| − W)/2 ≤ Re L_X(½+iτ) ≤ (log((|τ|+1)/2π) + 6/|τ| + W)/2` with the prime
  weight `W = W(X, 0) = 2 Σ_{n ≤ X} Λ(n)/√n`.
* **The repulsion law** (`eulerStage_deriv_ne_zero_above_horizon`,
  `eulerStage_ne_zero_of_lt_gap`, `exists_eulerStage_zero_within`). Above the horizon
  `log(t₀/2π) > 6/t₀ + W`, every zero of `Λ_X` on the line is simple, the zero after a zero `t₀`
  lies at distance at least `π/M` and at most `π/m`, where
  `m = (log(t₀/2π) − 6/t₀ − W)/2` and `M = (log((t₀+5)/2π) + 6/t₀ + W)/2 + 1`.

Together with the zero-free strip `eulerStage_ne_zero_near_line`, the configuration of `Λ_X` above
the horizon is on the line and forms a phase lattice with local spacing `2π/log(t/2π)` up to the
prime weight. The horizon `t ≈ 2π e^{W}` recedes as `X` grows: the law holds exactly where the
archimedean speed dominates the prime weight, and says nothing below that scale.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open _root_.RHTower

/-- The point `½ + it` of the critical line. -/
def linePt (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I

theorem linePt_re (t : ℝ) : (linePt t).re = 1 / 2 := by simp [linePt]

theorem linePt_im (t : ℝ) : (linePt t).im = t := by simp [linePt]

theorem one_sub_linePt (t : ℝ) : 1 - linePt t = conj (linePt t) :=
  Complex.ext (by norm_num [linePt]) (by norm_num [linePt])

theorem continuous_linePt : Continuous linePt :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem hasDerivAt_linePt (t : ℝ) : HasDerivAt linePt I t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add ((1 / 2 : ℝ) : ℂ)
  simp only [id, Complex.ofReal_one, one_mul] at h
  exact h

/-- The half `A_X` along the critical line. -/
def stageLine (X : ℕ) (t : ℝ) : ℂ := eulerStageHalf X (linePt t)

/-- The phase speed: the logarithmic derivative `L_X` along the critical line. -/
def stageSpeed (X : ℕ) (t : ℝ) : ℂ := eulerStageLogDeriv X (linePt t)

theorem linePt_re_pos (t : ℝ) : 0 < (linePt t).re := by rw [linePt_re]; norm_num

theorem stageLine_ne_zero (X : ℕ) (t : ℝ) : stageLine X t ≠ 0 :=
  eulerStageHalf_ne_zero X (linePt_re_pos t)

/-- On the critical line the finite Euler stage is `2 Re A_X`. -/
theorem eulerStage_linePt (X : ℕ) (t : ℝ) :
    eulerStage X (linePt t) = ((2 * (stageLine X t).re : ℝ) : ℂ) := by
  rw [eulerStage, one_sub_linePt, eulerStageHalf_conj, add_conj, stageLine]

theorem hasDerivAt_eulerStageHalf' (X : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (eulerStageHalf X) (eulerStageHalf X s * eulerStageLogDeriv X s) s :=
  hasDerivAt_eulerStageHalf X hs

theorem hasDerivAt_stageLine (X : ℕ) (t : ℝ) :
    HasDerivAt (stageLine X) (I * stageLine X t * stageSpeed X t) t := by
  have h := (hasDerivAt_eulerStageHalf' X (linePt_re_pos t)).comp t (hasDerivAt_linePt t)
  refine h.congr_deriv ?_
  simp only [stageLine, stageSpeed]
  ring

theorem continuous_stageLine (X : ℕ) : Continuous (stageLine X) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_stageLine X t).continuousAt

/-- The phase speed is continuous: `L_X = A_X'/A_X` with `A_X` holomorphic and zero-free on
`Re s > 0`. -/
theorem continuous_stageSpeed (X : ℕ) : Continuous (stageSpeed X) := by
  set U : Set ℂ := {s | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (eulerStageHalf X) U := fun s hs =>
    (hasDerivAt_eulerStageHalf' X hs).differentiableAt.differentiableWithinAt
  have hq : ContinuousOn (fun s => deriv (eulerStageHalf X) s / eulerStageHalf X s) U :=
    ((hd.deriv hUo).continuousOn).div hd.continuousOn fun s hs => eulerStageHalf_ne_zero X hs
  have hcont := hq.comp_continuous continuous_linePt linePt_re_pos
  refine hcont.congr fun t => ?_
  show deriv (eulerStageHalf X) (linePt t) / eulerStageHalf X (linePt t) =
    eulerStageLogDeriv X (linePt t)
  rw [(hasDerivAt_eulerStageHalf' X (linePt_re_pos t)).deriv,
    mul_div_cancel_left₀ _ (eulerStageHalf_ne_zero X (linePt_re_pos t))]

/-! ### The phase law -/

/-- The phase integral `Θ(t) = ∫_{t₀}^t L_X(½ + iτ) dτ`. -/
def stagePhase (X : ℕ) (t₀ t : ℝ) : ℂ := ∫ τ in t₀..t, stageSpeed X τ

theorem hasDerivAt_stagePhase (X : ℕ) (t₀ τ : ℝ) :
    HasDerivAt (stagePhase X t₀) (stageSpeed X τ) τ :=
  ((continuous_stageSpeed X).integral_hasStrictDerivAt t₀ τ).hasDerivAt

/-- **The phase law.** `A_X(½+it) = A_X(½+it₀) · exp(i Θ(t))`. -/
theorem stageLine_eq_mul_exp (X : ℕ) (t₀ t : ℝ) :
    stageLine X t = stageLine X t₀ * cexp (I * stagePhase X t₀ t) := by
  set k : ℝ → ℂ := fun τ => stageLine X τ * cexp (-(I * stagePhase X t₀ τ)) with hk
  have hkd : ∀ τ, HasDerivAt k 0 τ := by
    intro τ
    have := (hasDerivAt_stageLine X τ).mul
      (((hasDerivAt_stagePhase X t₀ τ).const_mul I).neg.cexp)
    refine this.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun τ => (hkd τ).differentiableAt)
    (fun τ => (hkd τ).deriv) t t₀
  have h0 : stagePhase X t₀ t₀ = 0 := intervalIntegral.integral_same
  simp only [hk, h0, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  calc stageLine X t
      = stageLine X t * cexp (-(I * stagePhase X t₀ t)) * cexp (I * stagePhase X t₀ t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [hconst]

theorem re_stagePhase (X : ℕ) (t₀ t : ℝ) :
    (stagePhase X t₀ t).re = ∫ τ in t₀..t, (stageSpeed X τ).re := by
  rw [stagePhase, ← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    ((continuous_stageSpeed X).intervalIntegrable _ _)]
  simp only [Complex.reCLM_apply]

theorem continuous_re_stageSpeed (X : ℕ) : Continuous fun τ => (stageSpeed X τ).re :=
  Complex.continuous_re.comp (continuous_stageSpeed X)

/-- After a zero `t₀` on the line, `Re A_X(½+it) = −b e^{−Im Θ(t)} sin(Re Θ(t))`, with
`b = Im A_X(½+it₀)`. -/
theorem re_stageLine_of_zero {X : ℕ} {t₀ : ℝ} (h0 : (stageLine X t₀).re = 0) (t : ℝ) :
    (stageLine X t).re = -(stageLine X t₀).im * Real.exp (-(stagePhase X t₀ t).im) *
      Real.sin (stagePhase X t₀ t).re := by
  have hc : stageLine X t₀ = (((stageLine X t₀).im : ℝ) : ℂ) * I :=
    Complex.ext (by simp [h0]) (by simp)
  set b := (stageLine X t₀).im with hb
  rw [stageLine_eq_mul_exp X t₀ t, hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul, one_mul, mul_one, sub_zero,
    zero_sub, add_zero, zero_add]
  ring

theorem stageLine_re_eq_zero_of_eulerStage {X : ℕ} {t : ℝ} (h : eulerStage X (linePt t) = 0) :
    (stageLine X t).re = 0 := by
  rw [eulerStage_linePt] at h
  have := Complex.ofReal_eq_zero.mp h
  linarith

/-- **No zero before a half turn.** After a zero `t₀` on the line, if the phase speed is positive on
`(t₀, t)` and turns by less than `π`, then `Λ_X(½+it) ≠ 0`. -/
theorem eulerStage_ne_zero_of_phase_lt {X : ℕ} {t₀ t : ℝ} (h0 : eulerStage X (linePt t₀) = 0)
    (ht : t₀ < t) (hpos : ∀ τ ∈ Ioo t₀ t, 0 < (stageSpeed X τ).re)
    (hlt : ∫ τ in t₀..t, (stageSpeed X τ).re < Real.pi) :
    eulerStage X (linePt t) ≠ 0 := by
  have hre0 := stageLine_re_eq_zero_of_eulerStage h0
  have hb : (stageLine X t₀).im ≠ 0 := fun h => stageLine_ne_zero X t₀ (Complex.ext hre0 h)
  have hint : 0 < ∫ τ in t₀..t, (stageSpeed X τ).re :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_re_stageSpeed X).intervalIntegrable _ _) hpos ht
  have hsin : 0 < Real.sin (stagePhase X t₀ t).re := by
    rw [re_stagePhase]; exact Real.sin_pos_of_pos_of_lt_pi hint hlt
  have hexp := Real.exp_pos (-(stagePhase X t₀ t).im)
  rw [eulerStage_linePt, Ne, Complex.ofReal_eq_zero, re_stageLine_of_zero hre0]
  intro h
  have hprod : (stageLine X t₀).im * Real.exp (-(stagePhase X t₀ t).im) *
      Real.sin (stagePhase X t₀ t).re = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hb h2
    · exact hexp.ne' h2
  · exact hsin.ne' h1

/-- **A zero in every half turn.** If the phase turns by at least `π` on `[t₀, t]`, then `Λ_X` has
a zero on the line at a height in `[t₀, t]`. -/
theorem exists_eulerStage_zero_of_phase_ge {X : ℕ} {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hge : Real.pi ≤ ∫ τ in t₀..t, (stageSpeed X τ).re) :
    ∃ τ ∈ Icc t₀ t, eulerStage X (linePt τ) = 0 := by
  have hcθ : Continuous fun τ => (stagePhase X t₀ τ).re :=
    Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun τ =>
      (hasDerivAt_stagePhase X t₀ τ).continuousAt)
  have h0 : stagePhase X t₀ t₀ = 0 := intervalIntegral.integral_same
  obtain ⟨τ₁, hτ₁, hθ⟩ : ∃ τ₁ ∈ Icc t₀ t, (stagePhase X t₀ τ₁).re = Real.pi :=
    intermediate_value_Icc ht hcθ.continuousOn
      ⟨by simp only [h0, Complex.zero_re]; exact Real.pi_pos.le, by rw [re_stagePhase]; exact hge⟩
  -- at `τ₁` the phase has turned by `π`, so `Re A_X` has changed sign
  have hflip : (stageLine X τ₁).re =
      -Real.exp (-(stagePhase X t₀ τ₁).im) * (stageLine X t₀).re := by
    rw [stageLine_eq_mul_exp X t₀ τ₁]
    have he : cexp (I * stagePhase X t₀ τ₁) = -((Real.exp (-(stagePhase X t₀ τ₁).im) : ℝ) : ℂ) :=
      Complex.ext (by simp [Complex.exp_re, hθ]) (by simp [Complex.exp_im, hθ])
    rw [he]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hcre : ContinuousOn (fun τ => (stageLine X τ).re) (Icc t₀ τ₁) :=
    (Complex.continuous_re.comp (continuous_stageLine X)).continuousOn
  have hexp := Real.exp_pos (-(stagePhase X t₀ τ₁).im)
  have hsub : Icc t₀ τ₁ ⊆ Icc t₀ t := Icc_subset_Icc le_rfl hτ₁.2
  rcases le_total 0 (stageLine X t₀).re with hnn | hnp
  · obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc' hτ₁.1 hcre
      (show (0 : ℝ) ∈ Icc (stageLine X τ₁).re (stageLine X t₀).re from
        ⟨by rw [hflip]; nlinarith, hnn⟩)
    refine ⟨τ, hsub hτ, ?_⟩
    simp only at hτ0
    rw [eulerStage_linePt, hτ0, mul_zero, Complex.ofReal_zero]
  · obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc hτ₁.1 hcre
      (show (0 : ℝ) ∈ Icc (stageLine X t₀).re (stageLine X τ₁).re from
        ⟨hnp, by rw [hflip]; nlinarith⟩)
    refine ⟨τ, hsub hτ, ?_⟩
    simp only at hτ0
    rw [eulerStage_linePt, hτ0, mul_zero, Complex.ofReal_zero]

/-- **Zeros with positive phase speed are simple.** -/
theorem eulerStage_deriv_ne_zero {X : ℕ} {t₀ : ℝ} (h0 : eulerStage X (linePt t₀) = 0)
    (hpos : 0 < (stageSpeed X t₀).re) : deriv (eulerStage X) (linePt t₀) ≠ 0 := by
  have hre0 := stageLine_re_eq_zero_of_eulerStage h0
  have hb : (stageLine X t₀).im ≠ 0 := fun h => stageLine_ne_zero X t₀ (Complex.ext hre0 h)
  set s₀ := linePt t₀ with hs₀
  have h1s : 0 < (1 - s₀).re := by rw [hs₀, one_sub_linePt, conj_re, linePt_re]; norm_num
  have hA := hasDerivAt_eulerStageHalf' X (linePt_re_pos t₀)
  have hB := (hasDerivAt_eulerStageHalf' X h1s).comp s₀ ((hasDerivAt_id s₀).const_sub 1)
  have hΛ : HasDerivAt (eulerStage X) _ s₀ := hA.add hB
  -- along the line `Λ_X(½+it) = 2 Re A_X(½+it)`
  have hline := hΛ.comp t₀ (hasDerivAt_linePt t₀)
  have hre : HasDerivAt (fun t => ((2 * (stageLine X t).re : ℝ) : ℂ))
      (((2 * (I * stageLine X t₀ * stageSpeed X t₀).re : ℝ)) : ℂ) t₀ :=
    ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_stageLine X t₀)).const_mul
      2).ofReal_comp
  have hfun : (eulerStage X ∘ linePt) = fun t => ((2 * (stageLine X t).re : ℝ) : ℂ) :=
    funext fun t => eulerStage_linePt X t
  rw [hfun] at hline
  have huniq := hline.unique hre
  rw [hΛ.deriv]
  intro hD
  rw [hD, zero_mul] at huniq
  have hval : (I * stageLine X t₀ * stageSpeed X t₀).re =
      -(stageLine X t₀).im * (stageSpeed X t₀).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hre0]
    ring
  rw [hval] at huniq
  have h2 : 2 * (-(stageLine X t₀).im * (stageSpeed X t₀).re) = 0 := by exact_mod_cast huniq.symm
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb (neg_eq_zero.mp h')
    · exact hpos.ne' h'

/-! ### The phase speed above the horizon -/

theorem eulerStageWeight_zero (X : ℕ) : eulerStageWeight X 0 =
    2 * ∑ n ∈ Finset.range (X + 1),
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [eulerStageWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [zero_sub]
  ring

theorem eulerStageWeight_zero_nonneg (X : ℕ) : 0 ≤ eulerStageWeight X 0 := by
  rw [eulerStageWeight_zero]
  exact mul_nonneg two_pos.le (Finset.sum_nonneg fun n _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- Lower bound for the phase speed. -/
theorem re_stageSpeed_ge (X : ℕ) {τ : ℝ} (hτ : 4 ≤ |τ|) :
    (Real.log (|τ| / (2 * Real.pi)) - 6 / |τ| - eulerStageWeight X 0) / 2 ≤
      (stageSpeed X τ).re := by
  have h := re_eulerStageLogDeriv_ge X (σ := 1 / 2) (τ := τ) (by norm_num) hτ
  rw [stageSpeed, linePt, eulerStageWeight_zero]
  linarith

/-- Upper bound for the phase speed. -/
theorem re_stageSpeed_le (X : ℕ) {τ : ℝ} (hτ : 4 ≤ |τ|) :
    (stageSpeed X τ).re ≤
      (Real.log ((|τ| + 1) / (2 * Real.pi)) + 6 / |τ| + eulerStageWeight X 0) / 2 := by
  set z : ℂ := linePt τ / 2 with hz
  have hzre : 0 < z.re := by rw [hz, Complex.div_ofNat_re, linePt_re]; norm_num
  have hnorm_ge : |τ| / 2 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rwa [hz, Complex.div_ofNat_im, linePt_im, abs_div, abs_two] at h
  have hnorm_le : ‖z‖ ≤ (|τ| + 1) / 2 := by
    have hl : ‖linePt τ‖ ≤ 1 / 2 + |τ| := by
      calc ‖linePt τ‖ ≤ ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = 1 / 2 + |τ| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [hz, norm_div, Complex.norm_two]
    linarith
  have hz2 : 2 ≤ ‖z‖ := by linarith
  have hst := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2
  have hdig : (Complex.digamma z).re ≤ Real.log ‖z‖ + 3 / ‖z‖ := by
    have := (Complex.re_le_norm (Complex.digamma z - Complex.log z)).trans hst
    rw [Complex.sub_re, Complex.log_re] at this
    linarith
  have hlog : Real.log ‖z‖ ≤ Real.log ((|τ| + 1) / 2) := Real.log_le_log (by linarith) hnorm_le
  have hinv : 3 / ‖z‖ ≤ 6 / |τ| := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hsplit : Real.log ((|τ| + 1) / (2 * Real.pi)) =
      Real.log ((|τ| + 1) / 2) - Real.log Real.pi := by
    rw [show (|τ| + 1) / (2 * Real.pi) = ((|τ| + 1) / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  -- the prime part is at most `Σ Λ(n)/√n`
  have hprime : -(∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-linePt τ)).re ≤
      ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-linePt τ)‖ =
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ,
          Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, linePt_re]
      have := Complex.abs_re_le_norm
        ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-linePt τ))
      rw [hnorm] at this
      linarith [neg_abs_le ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-linePt τ)).re]
  rw [stageSpeed, eulerStageLogDeriv, Complex.sub_re, eulerStageWeight_zero]
  have harch : (Complex.digamma (linePt τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      ((Complex.digamma z).re - Real.log Real.pi) / 2 := by
    rw [hz]; simp [Complex.sub_re]; ring
  rw [harch]
  linarith

/-! ### The repulsion law above the horizon -/

theorem horizon_mono {t₀ τ : ℝ} (ht₀ : 4 ≤ t₀) (hτ : t₀ ≤ τ) :
    Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ ≤ Real.log (|τ| / (2 * Real.pi)) - 6 / |τ| := by
  have hτ0 : 0 < τ := by linarith
  rw [abs_of_pos hτ0]
  have h1 : Real.log (t₀ / (2 * Real.pi)) ≤ Real.log (τ / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hτ (by positivity))
  have h2 : 6 / τ ≤ 6 / t₀ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hτ
  linarith

/-- **Zeros above the horizon are simple.** -/
theorem eulerStage_deriv_ne_zero_above_horizon {X : ℕ} {t₀ t : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi))) (ht : t₀ ≤ t)
    (h0 : eulerStage X (linePt t) = 0) : deriv (eulerStage X) (linePt t) ≠ 0 := by
  refine eulerStage_deriv_ne_zero h0 ?_
  have hτ : 4 ≤ |t| := by rw [abs_of_pos (by linarith)]; linarith
  have := re_stageSpeed_ge X hτ
  have := horizon_mono ht₀ ht
  linarith

/-- **The gap after a zero is at least `π/M`.** Above the horizon, after a zero `t₀` of `Λ_X` on the
line there is no zero at heights in `(t₀, t₀ + π/M)`, where
`M = (log((t₀ + 5)/2π) + 6/t₀ + W(X, 0))/2 + 1`. -/
theorem eulerStage_ne_zero_of_lt_gap {X : ℕ} {t₀ t : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi)))
    (h0 : eulerStage X (linePt t₀) = 0) (ht : t₀ < t)
    (hgap : t < t₀ + Real.pi /
      ((Real.log ((t₀ + 5) / (2 * Real.pi)) + 6 / t₀ + eulerStageWeight X 0) / 2 + 1)) :
    eulerStage X (linePt t) ≠ 0 := by
  set M := (Real.log ((t₀ + 5) / (2 * Real.pi)) + 6 / t₀ + eulerStageWeight X 0) / 2 + 1 with hM
  have hlog5 : 0 < Real.log ((t₀ + 5) / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr (by nlinarith [Real.pi_lt_four]))
  have hM1 : 1 ≤ M := by
    have := eulerStageWeight_zero_nonneg X
    have : 0 < 6 / t₀ := by positivity
    rw [hM]; linarith
  have hπM : Real.pi / M ≤ Real.pi := div_le_self Real.pi_pos.le hM1
  have hpos : ∀ τ ∈ Ioo t₀ t, 0 < (stageSpeed X τ).re := fun τ hτ => by
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1]
    have := re_stageSpeed_ge X hτa
    have := horizon_mono ht₀ hτ.1.le
    linarith
  have hle : ∀ τ ∈ Icc t₀ t, (stageSpeed X τ).re ≤ M := fun τ hτ => by
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos hτ0]; linarith [hτ.1]
    have h := re_stageSpeed_le X hτa
    rw [abs_of_pos hτ0] at h
    have h1 : Real.log ((τ + 1) / (2 * Real.pi)) ≤ Real.log ((t₀ + 5) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right (by linarith [hτ.2, Real.pi_lt_four]) (by positivity))
    have h2 : 6 / τ ≤ 6 / t₀ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hτ.1
    rw [hM]; linarith
  refine eulerStage_ne_zero_of_phase_lt h0 ht hpos ?_
  have hint := intervalIntegral.integral_mono_on (μ := volume) ht.le
    ((continuous_re_stageSpeed X).intervalIntegrable _ _) intervalIntegrable_const hle
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hM0 : 0 < M := by linarith
  have : (t - t₀) * M < Real.pi := by
    have := (lt_div_iff₀ hM0).mp (show t - t₀ < Real.pi / M by linarith)
    linarith
  linarith

/-- **The gap after any height is at most `π/m`.** Above the horizon, every window
`[t₀, t₀ + π/m]` of the line contains a zero of `Λ_X`, where
`m = (log(t₀/2π) − 6/t₀ − W(X, 0))/2 > 0`. -/
theorem exists_eulerStage_zero_within {X : ℕ} {t₀ : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi))) :
    ∃ τ ∈ Icc t₀ (t₀ + Real.pi /
      ((Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - eulerStageWeight X 0) / 2)),
      eulerStage X (linePt τ) = 0 := by
  set m := (Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - eulerStageWeight X 0) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hlen : 0 ≤ Real.pi / m := (div_pos Real.pi_pos hm0).le
  refine exists_eulerStage_zero_of_phase_ge (by linarith) ?_
  have hge : ∀ τ ∈ Icc t₀ (t₀ + Real.pi / m), m ≤ (stageSpeed X τ).re := fun τ hτ => by
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1]
    have := re_stageSpeed_ge X hτa
    have := horizon_mono ht₀ hτ.1
    rw [hm]; linarith
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    intervalIntegrable_const
    ((continuous_re_stageSpeed X).intervalIntegrable _ _) hge
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left,
    div_mul_cancel₀ _ hm0.ne'] at hint
  exact hint

end GaloisForLFunctions.ZeroConfigurationGeometry
