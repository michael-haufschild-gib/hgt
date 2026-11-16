import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.ThePositiveEulerTwinsHaveNoRealZero
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerLogarithmicSigns

/-!
# Beyond-the-wall prime continuation fails on the prime-two deformations and positive Euler twins

For any logarithmic Euler sequence `c : ℕ → ℂ` (where `c(n) log n` plays the role of the von
Mangoldt sequence), define the model beyond-the-wall prime-pole balance on `F ∈ H`:

  `modelWallPrimeBalance c F p = Σ_{n ≥ 2} (c(n) log n / √n) e^{p log n} H_{log n}(p) + L F(-½)/(p + ½)`,

and the arithmetic property `ModelBeyondTheWallPrimeContinuation c` asserting that
`modelWallPrimeBalance c F` extends holomorphically from `Re p < -½` to `Re p < 0` for every
`F ∈ H`. For `c = eulerLogDirichletCoeff`, `c(n) log n = Λ(n)` and this property is identically
`ZetaBeyondTheWallPrimeContinuation`, which excludes the critical state.

* **General finite-factor refutation (`not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff`).**
  Whenever `p` is prime and the local roots satisfy `‖β‖ < √p < ‖α‖ < p`, the `β`-series is
  holomorphic on all of `Re q < 0`, while clearing `ξ(½ + q)(1 - α p^{q - ½})` on `F = probe 5`
  produces a Leibniz derivative term `(ξ · f_α)'(q) / (5 + q)` at `q_* = ½ - log α / log p ∈
  {-½ < Re q < 0}`, forcing analytic order one lower than any holomorphic continuation can match
  — unconditionally, whether or not `ζ(½ - q_*)` vanishes.
* **Prime-two deformations (`primeTwo_not_modelBeyondTheWallPrimeContinuation`).** Fails for every
  `½ < θ < 1`.
* **Positive Euler twins (`exists_positive_euler_twin_failing_beyondTheWallContinuation`).** Beyond
  every finite prefix `N` and for every `½ < σ < 1`, a twin with bounded positive multiplicative
  ordinary coefficients `≥ 1`, agreement with `ζ` through `N`, reflected entire completion,
  strictly positive real-axis values, and passive contractive scattering unconditionally violates
  `ModelBeyondTheWallPrimeContinuation`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
  SelbergClass.PositiveFiniteEuler BlackHoleRingdown BlackHoleRingdown.PositiveEulerHorizon

/-! ### Parameterized beyond-the-wall prime-pole balance -/

/-- The generalized prime-power atom `(c(n) log n) / √n` for `n ≥ 2` attached to a logarithmic
Euler sequence `c : ℕ → ℂ`. -/
def modelAtom (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n then c n * (Real.log n : ℂ) / (Real.sqrt n : ℂ) else 0

/-- The prime heads `Ŝ_c F(p)` attached to a logarithmic Euler sequence `c`. -/
def modelPrimeHead (c : ℕ → ℂ) (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' n : ℕ, modelAtom c n * (cexp (p * Real.log n) * levyHead F p (Real.log n))

/-- The beyond-the-wall prime-pole balance `Φ_c(F, p) = Ŝ_c F(p) + L F(-½)/(p + ½)`. -/
def modelWallPrimeBalance (c : ℕ → ℂ) (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  modelPrimeHead c F p + negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

/-- **Model beyond-the-wall prime-pole continuation:** for every `F ∈ H`, `modelWallPrimeBalance c F`
extends holomorphically from `Re p < -½` to `Re p < 0`. -/
def ModelBeyondTheWallPrimeContinuation (c : ℕ → ℂ) : Prop :=
  ∀ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
      EqOn H (modelWallPrimeBalance c F) {p : ℂ | p.re < -(1 / 2)}

theorem modelAtom_eulerLogDirichletCoeff (n : ℕ) :
    modelAtom RHTower.eulerLogDirichletCoeff n = (vonMangoldtAtom n : ℂ) := by
  unfold modelAtom vonMangoldtAtom
  split_ifs with hn
  · have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlog_ne : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
    rw [RHTower.eulerLogDirichletCoeff, ← Complex.natCast_log, div_mul_cancel₀ _ hlog_ne,
      Complex.ofReal_div]
  · simp

theorem modelWallPrimeBalance_eulerLogDirichletCoeff (F : ℝ → ℝ) :
    modelWallPrimeBalance RHTower.eulerLogDirichletCoeff F = wallPrimeBalance F := by
  funext p
  unfold modelWallPrimeBalance wallPrimeBalance modelPrimeHead primeHead
  simp_rw [modelAtom_eulerLogDirichletCoeff]

/-- For `ζ`'s canonical Euler-log sequence, `ModelBeyondTheWallPrimeContinuation` is identically
`ZetaBeyondTheWallPrimeContinuation`. -/
theorem modelBeyondTheWallPrimeContinuation_zeta_iff :
    ModelBeyondTheWallPrimeContinuation RHTower.eulerLogDirichletCoeff ↔
      ZetaBeyondTheWallPrimeContinuation := by
  constructor <;> intro h F hF <;>
    simpa only [HasBeyondTheWallPrimeContinuation,
      modelWallPrimeBalance_eulerLogDirichletCoeff] using h F hF

/-! ### Explicit evaluation on `probe 5` for single-prime logarithmic terms -/

private theorem cexp_mul_levyHead_probe_five {q : ℂ} (hq : -4 < q.re) {L : ℝ} (hL : 0 ≤ L) :
    cexp (q * L) * levyHead (probe 5) q L =
      (cexp (q * L) - cexp ((-5 : ℂ) * L)) / ((5 : ℂ) + q) := by
  have h5q : (5 : ℂ) + q ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  have hhead : levyHead (probe 5) q L =
      (1 - cexp (-(((5 : ℂ) + q) * L))) / ((5 : ℂ) + q) := by
    unfold levyHead
    have hsplit : (∫ u in Ici (-L), cexp (q * u) * (probe 5 u : ℂ)) =
        ∫ u in Ico (-L) 0, cexp (((5 : ℂ) + q) * u) := by
      rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Ico]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      rcases lt_or_ge u 0 with hu | hu
      · by_cases hLu : -L ≤ u
        · rw [indicator_of_mem (mem_Ici.mpr hLu), indicator_of_mem (mem_Ico.mpr ⟨hLu, hu⟩),
            probe_of_neg hu, Complex.ofReal_exp, ← Complex.exp_add]
          congr 1; push_cast; ring
        · rw [indicator_of_notMem (show u ∉ Ici (-L) by simp [hLu]),
            indicator_of_notMem (show u ∉ Ico (-L) 0 by simp [hLu])]
      · rw [indicator_of_notMem (show u ∉ Ico (-L) 0 by simp [hu])]
        by_cases hLu : -L ≤ u
        · rw [indicator_of_mem (mem_Ici.mpr hLu), probe_of_nonneg hu,
            Complex.ofReal_zero, mul_zero]
        · rw [indicator_of_notMem (show u ∉ Ici (-L) by simp [hLu])]
    rw [hsplit, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -L ≤ 0)]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -L) (b := (0 : ℝ))
      (f := fun u : ℝ => cexp (((5 : ℂ) + q) * u) / ((5 : ℂ) + q))
      (f' := fun u : ℝ => cexp (((5 : ℂ) + q) * u))
      (fun u _ => by
        have hd := (((hasDerivAt_id u).ofReal_comp.const_mul ((5 : ℂ) + q)).cexp).div_const
          ((5 : ℂ) + q)
        simpa [mul_div_cancel_right₀ _ h5q] using hd)
      ((by fun_prop : Continuous fun u : ℝ => cexp (((5 : ℂ) + q) * u)).intervalIntegrable
        (-L) (0 : ℝ))
    rw [hFTC]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_neg, mul_neg]
    ring
  rw [hhead, mul_div_assoc', mul_sub, mul_one, ← Complex.exp_add]
  have hexp : q * (L : ℂ) + -(((5 : ℂ) + q) * L) = (-5 : ℂ) * L := by ring
  rw [hexp]

private theorem laplace_probe_five {q : ℂ} (hq : -4 < q.re) :
    negativeHalfLineLaplace (cx (probe 5)) q = 1 / ((5 : ℂ) + q) := by
  unfold negativeHalfLineLaplace cx
  have h1 : (∫ u : ℝ, cexp (q * u) * (probe 5 u : ℂ)) =
      ∫ u in Iio (0 : ℝ), cexp (((5 : ℂ) + q) * u) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rcases lt_or_ge u 0 with hu | hu
    · rw [indicator_of_mem (mem_Iio.mpr hu), probe_of_neg hu, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; push_cast; ring
    · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) by simp [hu]), probe_of_nonneg hu,
        Complex.ofReal_zero, mul_zero]
  rw [h1, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic (by simp; linarith) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem hasSum_modelPrimeHead_powerLogCoeff {p : ℕ} (hp : p.Prime) {γ : ℂ}
    (hγ : ‖γ‖ < p) {q : ℂ} (hq4 : -4 < q.re) (hq : q.re < -(1 / 2)) :
    let w₁ := γ * cexp ((q - 1 / 2) * Real.log p)
    let w₂ := γ * cexp (-(11 / 2 : ℂ) * Real.log p)
    HasSum (fun n : ℕ => modelAtom (powerLogCoeff p γ) n *
        (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)))
      ((-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
        (w₁ / (1 - w₁) - w₂ / (1 - w₂))) := by
  intro w₁ w₂
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hw₁_lt : ‖w₁‖ < 1 := by
    dsimp [w₁]
    rw [norm_mul, Complex.norm_exp]
    have hre : ((q - 1 / 2) * (Real.log p : ℂ)).re = (q.re - 1 / 2) * Real.log p := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, re_one_half]
    rw [hre]
    calc ‖γ‖ * Real.exp ((q.re - 1 / 2) * Real.log p)
        < (p : ℝ) * Real.exp ((q.re - 1 / 2) * Real.log p) :=
          mul_lt_mul_of_pos_right hγ (Real.exp_pos _)
      _ = Real.exp ((q.re + 1 / 2) * Real.log p) := by
          conv_lhs => lhs; rw [← Real.exp_log hp0]
          rw [← Real.exp_add]; congr 1; ring
      _ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hl)
  have hw₂_lt : ‖w₂‖ < 1 := by
    dsimp [w₂]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(11 / 2 : ℂ) * (Real.log p : ℂ)).re = -(11 / 2 : ℝ) * Real.log p := by
      have h11 : (-(11 / 2 : ℂ)).re = -(11 / 2 : ℝ) := by norm_num
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, h11]
    rw [hre]
    calc ‖γ‖ * Real.exp (-(11 / 2 : ℝ) * Real.log p)
        ≤ (p : ℝ) * Real.exp (-(11 / 2 : ℝ) * Real.log p) :=
          mul_le_mul_of_nonneg_right hγ.le (Real.exp_pos _).le
      _ = Real.exp (-(9 / 2 : ℝ) * Real.log p) := by
          conv_lhs => lhs; rw [← Real.exp_log hp0]
          rw [← Real.exp_add]; congr 1; ring
      _ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by norm_num) hl)
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun a b hab =>
    Nat.succ.inj ((pow_right_strictMono₀ hp.one_lt).injective hab)
  have hvanish : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => p ^ (k + 1)) →
      modelAtom (powerLogCoeff p γ) n *
        (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) = 0 := by
    intro n hn
    rcases lt_or_ge n 2 with hlt2 | hge2
    · simp [modelAtom, not_le.mpr hlt2]
    · have hnot_pow : ¬ ∃ k : ℕ, p ^ k = n := by
        rintro ⟨k, rfl⟩
        rcases k with _ | k
        · simp at hge2
        · exact hn ⟨k, rfl⟩
      have hp0_coeff : powerLogCoeff p γ n = 0 := Function.extend_apply' _ _ _ hnot_pow
      simp [modelAtom, hp0_coeff]
  rw [← hinj.hasSum_iff hvanish]
  have hgeom1 : HasSum (fun k : ℕ => w₁ ^ (k + 1)) (w₁ / (1 - w₁)) := by
    simpa [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hw₁_lt).mul_left w₁
  have hgeom2 : HasSum (fun k : ℕ => w₂ ^ (k + 1)) (w₂ / (1 - w₂)) := by
    simpa [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hw₂_lt).mul_left w₂
  refine ((hgeom1.sub hgeom2).mul_left (-(Real.log p : ℂ) / ((5 : ℂ) + q))).congr_fun fun k => ?_
  set m := k + 1
  have hm_pos : 0 < m := Nat.succ_pos k
  have hpm_ge2 : 2 ≤ p ^ m :=
    hp.two_le.trans (Nat.le_self_pow hm_pos.ne' p)
  have hlog_pm : Real.log ((p ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hsqrt_pm : (Real.sqrt ((p ^ m : ℕ) : ℝ) : ℂ) =
      cexp ((1 / 2 : ℂ) * (m : ℂ) * Real.log p) := by
    have hpos : (0 : ℝ) < (p ^ m : ℕ) := by positivity
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, hlog_pm]
    congr 1; push_cast; ring
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
  have hatom : modelAtom (powerLogCoeff p γ) (p ^ m) =
      -(Real.log p : ℂ) * γ ^ m * cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) := by
    unfold modelAtom
    rw [if_pos hpm_ge2, powerLogCoeff_pow hp.one_lt γ m, hlog_pm, hsqrt_pm,
      Complex.ofReal_mul, Complex.ofReal_natCast, div_eq_mul_inv _ (cexp _), ← Complex.exp_neg]
    field_simp [hm_ne]
  dsimp only [Function.comp_apply]
  change modelAtom (powerLogCoeff p γ) (p ^ m) *
      (cexp (q * Real.log ((p ^ m : ℕ) : ℝ)) *
        levyHead (probe 5) q (Real.log ((p ^ m : ℕ) : ℝ))) =
    -(Real.log p : ℂ) / ((5 : ℂ) + q) * (w₁ ^ m - w₂ ^ m)
  rw [hatom, cexp_mul_levyHead_probe_five hq4 (Real.log_natCast_nonneg _), hlog_pm]
  have hw₁_m : w₁ ^ m = γ ^ m * cexp (((q - 1 / 2) * Real.log p) * (m : ℂ)) := by
    dsimp [w₁]; rw [mul_pow, ← Complex.exp_nat_mul]; congr 2; ring
  have hw₂_m : w₂ ^ m = γ ^ m * cexp ((-(11 / 2 : ℂ) * Real.log p) * (m : ℂ)) := by
    dsimp [w₂]; rw [mul_pow, ← Complex.exp_nat_mul]; congr 2; ring
  rw [hw₁_m, hw₂_m]
  have he1 : cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) *
      cexp (q * (((m : ℝ) * Real.log p : ℝ) : ℂ)) =
      cexp (((q - 1 / 2) * Real.log p) * (m : ℂ)) := by
    rw [← Complex.exp_add]; congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]; ring
  have he2 : cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) *
      cexp ((-5 : ℂ) * (((m : ℝ) * Real.log p : ℝ) : ℂ)) =
      cexp ((-(11 / 2 : ℂ) * Real.log p) * (m : ℂ)) := by
    rw [← Complex.exp_add]; congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]; ring
  have h5q : (5 : ℂ) + q ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  calc -(Real.log p : ℂ) * γ ^ m * cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) *
          ((cexp (q * (((m : ℝ) * Real.log p : ℝ) : ℂ)) -
            cexp ((-5 : ℂ) * (((m : ℝ) * Real.log p : ℝ) : ℂ))) / ((5 : ℂ) + q))
      = (-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
          (γ ^ m * (cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) *
              cexp (q * (((m : ℝ) * Real.log p : ℝ) : ℂ))) -
            γ ^ m * (cexp (-((1 / 2 : ℂ) * (m : ℂ) * Real.log p)) *
              cexp ((-5 : ℂ) * (((m : ℝ) * Real.log p : ℝ) : ℂ)))) := by
          field_simp [h5q]
    _ = _ := by rw [he1, he2]

/-! ### General finite-factor refutation theorem -/

private theorem analyticOrderAt_leibniz_obstruction {f g r : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hr : AnalyticAt ℂ r z)
    (hfz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) (hgz : g z ≠ 0) :
    analyticOrderAt (fun w => f w * r w + g w * deriv f w) z + 1 =
      analyticOrderAt f z := by
  have hd : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa only [hfz, sub_zero] using hf.analyticOrderAt_deriv_add_one
  have hdne : analyticOrderAt (deriv f) z ≠ ⊤ := fun h =>
    hfinite (by rw [← hd, h, top_add])
  have hgd : analyticOrderAt (g * deriv f) z = analyticOrderAt (deriv f) z := by
    rw [analyticOrderAt_mul hg hf.deriv, hg.analyticOrderAt_eq_zero.mpr hgz, zero_add]
  have hlt : analyticOrderAt (g * deriv f) z < analyticOrderAt (f * r) z := by
    rw [hgd, analyticOrderAt_mul hf hr]
    apply lt_of_lt_of_le _ le_self_add
    rw [← hd]
    exact (ENat.add_one_le_iff hdne).mp le_rfl
  change analyticOrderAt (f * r + g * deriv f) z + 1 = _
  rw [analyticOrderAt_add_eq_right_of_lt hlt, hgd, hd]

/-- **General finite-factor refutation:** for every prime `p` and local roots `α, β` with
`‖β‖ < √p < ‖α‖ < p`, `ModelBeyondTheWallPrimeContinuation (eulerLogCoeff p α β)` is
unconditionally false. -/
theorem not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff {p : ℕ} (hp : p.Prime)
    {α β : ℂ} (hβ : ‖β‖ < Real.sqrt p) (hα_lo : Real.sqrt p < ‖α‖) (hα_hi : ‖α‖ < p) :
    ¬ ModelBeyondTheWallPrimeContinuation (eulerLogCoeff p α β) := by
  intro hmodel
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hlC : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hα_pos : 0 < ‖α‖ := (Real.sqrt_pos.mpr hp0).trans hα_lo
  have hα_ne : α ≠ 0 := norm_pos_iff.mp hα_pos
  -- The off-line pole location `q_* ∈ {-1/2 < Re q < 0}`
  set qstar : ℂ := 1 / 2 - Complex.log α / (Real.log p : ℂ)
  have hqstar_re : -(1 / 2 : ℝ) < qstar.re ∧ qstar.re < 0 := by
    have hre : qstar.re = 1 / 2 - Real.log ‖α‖ / Real.log p := by
      dsimp [qstar]
      rw [re_one_half, Complex.div_ofReal_re, Complex.log_re]
    have hlog_lo : (1 / 2 : ℝ) * Real.log p < Real.log ‖α‖ := by
      have := Real.log_lt_log (Real.sqrt_pos.mpr hp0) hα_lo
      rwa [Real.log_sqrt hp0.le, div_eq_inv_mul, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
    have hlog_hi : Real.log ‖α‖ < Real.log p := Real.log_lt_log hα_pos hα_hi
    rw [hre]
    constructor
    · have : Real.log ‖α‖ / Real.log p < 1 := (div_lt_one hl).mpr hlog_hi
      linarith
    · have : 1 / 2 < Real.log ‖α‖ / Real.log p := (lt_div_iff₀ hl).mpr (by linarith)
      linarith
  -- Local analytic factors `f₁(q) = ξ(1/2 + q)` and `f₂(q) = 1 - α exp((q - 1/2) log p)`
  let f₁ : ℂ → ℂ := fun q => xi (1 / 2 + q)
  let f₂ : ℂ → ℂ := fun q => 1 - α * cexp ((q - 1 / 2) * Real.log p)
  let F₁₂ : ℂ → ℂ := fun q => f₁ q * f₂ q
  have hf₁_diff : Differentiable ℂ f₁ := differentiable_xi_half_add
  have hf₂_diff : Differentiable ℂ f₂ := by
    intro q
    exact (differentiableAt_const 1).sub
      (((differentiableAt_id.sub_const (1 / 2 : ℂ)).mul_const (Real.log p : ℂ)).cexp.const_mul α)
  have hf₂_deriv : ∀ q : ℂ, deriv f₂ q =
      -(Real.log p : ℂ) * α * cexp ((q - 1 / 2) * Real.log p) := by
    intro q
    have hd : HasDerivAt f₂
        (0 - α * (cexp ((q - 1 / 2) * Real.log p) * ((1 - 0) * (Real.log p : ℂ)))) q :=
      (hasDerivAt_const q (1 : ℂ)).sub
        ((((hasDerivAt_id q).sub (hasDerivAt_const q (1 / 2 : ℂ))).mul_const
          (Real.log p : ℂ)).cexp.const_mul α)
    rw [hd.deriv]; ring
  have hf₂_qstar : f₂ qstar = 0 := by
    dsimp [f₂, qstar]
    have hexp_arg : ((1 / 2 - Complex.log α / (Real.log p : ℂ)) - 1 / 2) * (Real.log p : ℂ) =
        -Complex.log α := by field_simp [hlC]; ring
    rw [hexp_arg, Complex.exp_neg, Complex.exp_log hα_ne, mul_inv_cancel₀ hα_ne, sub_self]
  have hF₁₂_qstar : F₁₂ qstar = 0 := by dsimp [F₁₂]; rw [hf₂_qstar, mul_zero]
  have hf₂_order_ne_top : analyticOrderAt f₂ qstar ≠ ⊤ := by
    intro htop
    have hderiv_ne : deriv f₂ qstar ≠ 0 := by
      rw [hf₂_deriv qstar]
      have hexp_eq : α * cexp ((qstar - 1 / 2) * Real.log p) = 1 :=
        (sub_eq_zero.mp hf₂_qstar).symm
      rw [mul_assoc, hexp_eq, mul_one]
      exact neg_ne_zero.mpr hlC
    have hev : f₂ =ᶠ[𝓝 qstar] 0 := analyticOrderAt_eq_top.mp htop
    exact hderiv_ne (by simpa [Pi.zero_def] using hev.deriv_eq)
  have hF₁₂_order_ne_top : analyticOrderAt F₁₂ qstar ≠ ⊤ := by
    change analyticOrderAt (f₁ * f₂) qstar ≠ ⊤
    rw [analyticOrderAt_mul (hf₁_diff.analyticAt qstar) (hf₂_diff.analyticAt qstar)]
    have hf₁_ne : analyticOrderAt f₁ qstar ≠ ⊤ := by
      have hcomp : analyticOrderAt f₁ qstar = analyticOrderAt xi (1 / 2 + qstar) := by
        apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun q : ℂ => 1 / 2 + q)
          (by fun_prop)
        simp
      rw [hcomp]; exact xi_order_ne_top _
    exact WithTop.add_ne_top.mpr ⟨hf₁_ne, hf₂_order_ne_top⟩
  -- The `β`-denominator never vanishes on `Re q < 0`
  let wβ : ℂ → ℂ := fun q => β * cexp ((q - 1 / 2) * Real.log p)
  have hwβ_lt_one : ∀ q : ℂ, q.re < 0 → ‖wβ q‖ < 1 := by
    intro q hq
    dsimp [wβ]
    rw [norm_mul, Complex.norm_exp]
    have hre : ((q - 1 / 2) * (Real.log p : ℂ)).re = (q.re - 1 / 2) * Real.log p := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, re_one_half]
    rw [hre]
    have hsqrt_eq : Real.sqrt p = Real.exp ((1 / 2 : ℝ) * Real.log p) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]; ring_nf
    calc ‖β‖ * Real.exp ((q.re - 1 / 2) * Real.log p)
        ≤ Real.sqrt p * Real.exp ((q.re - 1 / 2) * Real.log p) :=
          mul_le_mul_of_nonneg_right hβ.le (Real.exp_pos _).le
      _ = Real.exp (q.re * Real.log p) := by
          rw [hsqrt_eq, ← Real.exp_add]; congr 1; ring
      _ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hq hl)
  -- Apply `hmodel` to `probe 5 ∈ H`
  have hd5 : CriticalHalfLineEnergyDomain (probe 5) :=
    criticalHalfLineEnergyDomain_probe (by norm_num)
  obtain ⟨H, hH, heqH⟩ := hmodel (probe 5) hd5
  -- Compare on the convex strip `V = {-2 < Re q < 0}`
  set V := {q : ℂ | -2 < q.re ∧ q.re < 0}
  have hV_open : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV_conv : Convex ℝ V :=
    (convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_re_lt 0)
  let cα : ℂ := α * cexp (-(11 / 2 : ℂ) * Real.log p)
  let cβ : ℂ := β * cexp (-(11 / 2 : ℂ) * Real.log p)
  let Rreg : ℂ → ℂ := fun q =>
    regularRemainder (probe 5) q +
      (-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
        (wβ q / (1 - wβ q) - cα / (1 - cα) - cβ / (1 - cβ))
  let LHS : ℂ → ℂ := fun q => F₁₂ q * (archimedeanWallTail (probe 5) q + H q)
  let RHS : ℂ → ℂ := fun q => F₁₂ q * Rreg q + (1 / ((5 : ℂ) + q)) * deriv F₁₂ q
  have hLHS_diff : DifferentiableOn ℂ LHS V := by
    refine (hf₁_diff.mul hf₂_diff).differentiableOn.mul ?_
    exact ((differentiableOn_archimedeanWallTail hd5).mono fun q (hq : q ∈ V) =>
      show q.re < 5 / 2 by linarith [hq.2]).add (hH.mono fun q (hq : q ∈ V) => hq.2)
  have hRreg_diff : DifferentiableOn ℂ Rreg V := by
    intro q hq
    have h5q : (5 : ℂ) + q ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith [hq.1]
    have h1wβ : 1 - wβ q ≠ 0 := fun e => by
      have := hwβ_lt_one q hq.2
      rw [sub_eq_zero.mp e |>.symm, norm_one] at this
      exact lt_irrefl 1 this
    have hwβ_d : DifferentiableAt ℂ wβ q :=
      (((differentiableAt_id.sub_const (1 / 2 : ℂ)).mul_const
        (Real.log p : ℂ)).cexp).const_mul β
    exact ((differentiableAt_regularRemainder hd5 hq.1).add
      (((differentiableAt_const _).div ((differentiableAt_const _).add differentiableAt_id)
        h5q).mul (((hwβ_d.div ((differentiableAt_const 1).sub hwβ_d) h1wβ).sub
          (differentiableAt_const _)).sub (differentiableAt_const _)))).differentiableWithinAt
  have hRHS_diff : DifferentiableOn ℂ RHS V := by
    refine ((hf₁_diff.mul hf₂_diff).differentiableOn.mul hRreg_diff).add ?_
    refine (DifferentiableOn.div (differentiableOn_const 1)
      ((differentiableOn_const 5).add differentiableOn_id) fun q hq e => ?_).mul
      (fun q _ => (((hf₁_diff.mul hf₂_diff).analyticAt q).deriv).differentiableAt.differentiableWithinAt)
    have := congrArg Complex.re e; simp at this; linarith [hq.1]
  -- Show `LHS =ᶠ[𝓝 (-1)] RHS` using the explicit series on `-2 < Re q < -1/2`
  have hm1_in : (-1 : ℂ) ∈ V := ⟨by simp, by simp⟩
  have hev_m1 : LHS =ᶠ[𝓝 (-1 : ℂ)] RHS := by
    set W := {q : ℂ | -2 < q.re ∧ q.re < -(1 / 2)}
    have hW_open : IsOpen W :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hW_open.mem_nhds ⟨by simp, by simp; norm_num⟩] with q hq
    have hq4 : -4 < q.re := by linarith [hq.1]
    have hqh : q.re < -(1 / 2) := hq.2
    have h5q : (5 : ℂ) + q ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith [hq.1]
    -- Split `modelPrimeHead (eulerLogCoeff p α β)` into zeta + α + β
    have hs_zeta : Summable fun n : ℕ => modelAtom RHTower.eulerLogDirichletCoeff n *
        (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) := by
      simp_rw [modelAtom_eulerLogDirichletCoeff]
      exact Summable.of_norm_bounded (summable_primeHead_bound (F := probe 5) hqh)
        (fun n => norm_primeHead_term_le hd5 hq4 le_rfl n)
    have hs_α := hasSum_modelPrimeHead_powerLogCoeff hp hα_hi hq4 hqh
    have hs_β := hasSum_modelPrimeHead_powerLogCoeff hp (hβ.trans (by
      rw [Real.sqrt_lt' hp0]; nlinarith [hpR])) hq4 hqh
    have hsplit_atom : ∀ n : ℕ, modelAtom (eulerLogCoeff p α β) n *
        (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) =
        modelAtom RHTower.eulerLogDirichletCoeff n *
          (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) +
        modelAtom (powerLogCoeff p α) n *
          (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) +
        modelAtom (powerLogCoeff p β) n *
          (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n)) := by
      intro n
      unfold modelAtom eulerLogCoeff
      simp only [Pi.add_apply]
      split_ifs
      · ring
      · ring
    have hsum_all := ((hs_zeta.hasSum.add hs_α).add hs_β).congr_fun fun n => hsplit_atom n
    have hbal_eq : H q = wallPrimeBalance (probe 5) q +
        (-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
          ((α * cexp ((q - 1 / 2) * Real.log p)) / f₂ q - cα / (1 - cα) +
            (wβ q / (1 - wβ q) - cβ / (1 - cβ))) := by
      rw [heqH hqh]
      unfold modelWallPrimeBalance modelPrimeHead wallPrimeBalance
      rw [hsum_all.tsum_eq]
      have hzeta_tsum : (∑' n : ℕ, modelAtom RHTower.eulerLogDirichletCoeff n *
          (cexp (q * Real.log n) * levyHead (probe 5) q (Real.log n))) = primeHead (probe 5) q := by
        unfold primeHead; simp_rw [modelAtom_eulerLogDirichletCoeff]
      rw [hzeta_tsum]
      dsimp [f₂, wβ, cα, cβ]
      ring
    -- Clear `F₁₂ q = f₁ q * f₂ q`
    have hxi_ne : f₁ q ≠ 0 := xi_ne_zero_of_half_le_abs_re (by have := neg_le_abs q.re; linarith)
    have hf₂_ne : f₂ q ≠ 0 := by
      dsimp [f₂]
      intro e
      have h1 : α * cexp ((q - 1 / 2) * Real.log p) = 1 := (sub_eq_zero.mp e).symm
      have hn := congrArg norm h1
      rw [norm_one, norm_mul, Complex.norm_exp] at hn
      have hre : ((q - 1 / 2) * (Real.log p : ℂ)).re = (q.re - 1 / 2) * Real.log p := by
        simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, re_one_half]
      rw [hre] at hn
      have hlt1 : ‖α‖ * Real.exp ((q.re - 1 / 2) * Real.log p) < 1 := by
        calc ‖α‖ * Real.exp ((q.re - 1 / 2) * Real.log p)
            < (p : ℝ) * Real.exp ((q.re - 1 / 2) * Real.log p) :=
              mul_lt_mul_of_pos_right hα_hi (Real.exp_pos _)
          _ = Real.exp ((q.re + 1 / 2) * Real.log p) := by
              conv_lhs => lhs; rw [← Real.exp_log hp0]
              rw [← Real.exp_add]; congr 1; ring
          _ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hl)
      linarith
    have hderiv_f1 : deriv f₁ q = deriv xi (1 / 2 + q) := by
      simpa only [Function.comp_def, one_mul, mul_one] using
        ((xi_differentiable (1 / 2 + q)).hasDerivAt.comp q
          ((hasDerivAt_id q).const_add (1 / 2 : ℂ))).deriv
    have hCR : f₁ q * (archimedeanWallTail (probe 5) q + wallPrimeBalance (probe 5) q) =
        f₁ q * regularRemainder (probe 5) q + (1 / ((5 : ℂ) + q)) * deriv f₁ q := by
      rw [← globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance hd5 hqh,
        ← clearedRemainder_eq hd5 hxi_ne, clearedRemainder_of_gt hq.1,
        laplace_probe_five hq4, hderiv_f1]
    have hderiv_prod : deriv F₁₂ q = deriv f₁ q * f₂ q + f₁ q * deriv f₂ q :=
      deriv_mul (hf₁_diff q) (hf₂_diff q)
    dsimp [LHS, RHS, F₁₂, Rreg]
    rw [hbal_eq, hderiv_prod, hf₂_deriv q]
    have hmul_f1 : f₁ q * f₂ q * (archimedeanWallTail (probe 5) q +
        (wallPrimeBalance (probe 5) q + (-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
          ((α * cexp ((q - 1 / 2) * Real.log p)) / f₂ q - cα / (1 - cα) +
            (wβ q / (1 - wβ q) - cβ / (1 - cβ))))) =
        f₂ q * (f₁ q * (archimedeanWallTail (probe 5) q + wallPrimeBalance (probe 5) q)) +
        f₁ q * (-(Real.log p : ℂ) / ((5 : ℂ) + q)) *
          (f₂ q * ((α * cexp ((q - 1 / 2) * Real.log p)) / f₂ q) +
            f₂ q * (wβ q / (1 - wβ q) - cα / (1 - cα) - cβ / (1 - cβ))) := by ring
    rw [hmul_f1, hCR, mul_div_cancel₀ _ hf₂_ne]
    field_simp [h5q]
    ring
  -- Analytic continuation to `qstar ∈ V` and order comparison
  have hLHS_an : AnalyticOnNhd ℂ LHS V := hLHS_diff.analyticOnNhd hV_open
  have hRHS_an : AnalyticOnNhd ℂ RHS V := hRHS_diff.analyticOnNhd hV_open
  have hEqV := hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hV_conv.isPreconnected
    hm1_in hev_m1
  have hqstar_in : qstar ∈ V := ⟨by linarith [hqstar_re.1], hqstar_re.2⟩
  have hev_qstar : LHS =ᶠ[𝓝 qstar] RHS :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨V, hV_open.mem_nhds hqstar_in, hEqV⟩
  have hF₁₂_an : AnalyticAt ℂ F₁₂ qstar := (hf₁_diff.mul hf₂_diff).analyticAt qstar
  have hg_an : AnalyticAt ℂ (fun q : ℂ => 1 / ((5 : ℂ) + q)) qstar :=
    analyticAt_const.div (analyticAt_const.add analyticAt_id)
      (by intro e; have := congrArg Complex.re e; simp at this; linarith [hqstar_re.1])
  have hr_an : AnalyticAt ℂ Rreg qstar := hRreg_diff.analyticAt (hV_open.mem_nhds hqstar_in)
  have hK_an : AnalyticAt ℂ (fun q : ℂ => archimedeanWallTail (probe 5) q + H q) qstar :=
    (((differentiableOn_archimedeanWallTail hd5).mono fun q (hq : q ∈ V) =>
      show q.re < 5 / 2 by linarith [hq.2]).add (hH.mono fun q (hq : q ∈ V) => hq.2)).analyticAt
      (hV_open.mem_nhds hqstar_in)
  have hord_RHS := analyticOrderAt_leibniz_obstruction hF₁₂_an hg_an hr_an hF₁₂_qstar
    hF₁₂_order_ne_top (one_div_ne_zero fun e => by
      have := congrArg Complex.re e; simp at this; linarith [hqstar_re.1])
  have hord_LHS : analyticOrderAt F₁₂ qstar ≤ analyticOrderAt LHS qstar := by
    change analyticOrderAt F₁₂ qstar ≤
      analyticOrderAt (F₁₂ * fun q => archimedeanWallTail (probe 5) q + H q) qstar
    rw [analyticOrderAt_mul hF₁₂_an hK_an]
    exact le_self_add
  rw [analyticOrderAt_congr hev_qstar] at hord_LHS
  change analyticOrderAt RHS qstar + 1 = analyticOrderAt F₁₂ qstar at hord_RHS
  have hfin_RHS : analyticOrderAt RHS qstar ≠ ⊤ := fun htop =>
    hF₁₂_order_ne_top (by rw [← hord_RHS, htop, top_add])
  exact not_lt_of_ge hord_LHS ((ENat.add_one_le_iff hfin_RHS).mp hord_RHS.le)

/-! ### Unconditional failure on prime-two deformations and positive Euler twins -/

/-- **Unconditional failure on every prime-two deformation (`½ < θ < 1`):** the logarithmic Euler
sequence `c = eulerLogCoeff 2 (2^θ) (2^{1 - θ})` of `normalizedPrimeTwoZeta θ` satisfies
`exp L(c, s) = normalizedPrimeTwoZeta θ s` on `Re s > 1`, yet fails
`ModelBeyondTheWallPrimeContinuation c`. -/
theorem primeTwo_not_modelBeyondTheWallPrimeContinuation {θ : ℝ}
    (hθ_lo : 1 / 2 < θ) (hθ_hi : θ < 1) :
    let α : ℂ := ((2 : ℝ) ^ θ : ℝ)
    let β : ℂ := ((2 : ℝ) ^ (1 - θ) : ℝ)
    (∀ s : ℂ, 1 < s.re → LSeriesSummable (logarithmicCoeffs Nat.prime_two α β) s ∧
      Complex.exp (LSeries (logarithmicCoeffs Nat.prime_two α β) s) =
        normalizedPrimeTwoZeta θ s) ∧
    ¬ ModelBeyondTheWallPrimeContinuation (eulerLogCoeff 2 α β) := by
  intro α β
  have hα_pos : 0 < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hβ_pos : 0 < (2 : ℝ) ^ (1 - θ) := Real.rpow_pos_of_pos (by norm_num) (1 - θ)
  have hα_norm : ‖α‖ = (2 : ℝ) ^ θ := by
    dsimp [α]; rw [Complex.norm_real, Real.norm_of_nonneg hα_pos.le]
  have hβ_norm : ‖β‖ = (2 : ℝ) ^ (1 - θ) := by
    dsimp [β]; rw [Complex.norm_real, Real.norm_of_nonneg hβ_pos.le]
  have hsqrt2 : Real.sqrt (2 : ℕ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Nat.cast_ofNat, Real.sqrt_eq_rpow]
  have hα_lt2 : ‖α‖ < (2 : ℕ) := by
    rw [hα_norm, Nat.cast_ofNat]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hθ_hi |>.trans_eq
      (Real.rpow_one 2)
  have hβ_lt_sqrt : ‖β‖ < Real.sqrt (2 : ℕ) := by
    rw [hβ_norm, hsqrt2]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
  have hsqrt_lt_α : Real.sqrt (2 : ℕ) < ‖α‖ := by
    rw [hα_norm, hsqrt2]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hθ_lo
  refine ⟨fun s hs => ?_,
    not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff Nat.prime_two
      hβ_lt_sqrt hsqrt_lt_α hα_lt2⟩
  have hadd : α + β = -((-primeTwoTrace θ : ℝ) : ℂ) := by
    dsimp [α, β, primeTwoTrace]; push_cast; ring
  have hmul : α * β = (2 : ℕ) := by
    dsimp [α, β]
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show θ + (1 - θ) = 1 by ring, Real.rpow_one]
    norm_num
  exact ⟨logarithmicCoeffs_summable Nat.prime_two hα_lt2.le
      (hβ_lt_sqrt.le.trans (by rw [hsqrt2]; exact (Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 2))) hs,
    (logarithmicCoeffs_exp Nat.prime_two hadd hmul hα_lt2.le
      (hβ_lt_sqrt.le.trans (by rw [hsqrt2]; exact (Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 2))) hs).trans rfl⟩

/-- **Unconditional failure on positive Euler twins beyond every finite prefix:** for every `N`
and every `σ ∈ (½, 1)`, there exists a prime `p > N` whose positive passive Euler twin retains
bounded positive multiplicative ordinary coefficients `≥ 1` matching `ζ` through `N`, an entire
reflection-symmetric completion strictly positive on the entire real axis, and contractive
scattering, while having a negative even prime-power logarithmic coefficient and unconditionally
violating `ModelBeyondTheWallPrimeContinuation`. -/
theorem exists_positive_euler_twin_failing_beyondTheWallContinuation (N : ℕ)
    (σ : Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ (p : ℕ) (hp : p.Prime) (A : ℝ) (α β : ℂ), N < p ∧ 0 ≤ A ∧
      (arithmeticCoeffs p A).IsMultiplicative ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (arithmeticCoeffs p A n).im = 0 ∧
        1 ≤ (arithmeticCoeffs p A n).re ∧ ‖arithmeticCoeffs p A n‖ ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n ≤ N → arithmeticCoeffs p A n = 1) ∧
      Differentiable ℂ (completedXi p A) ∧
      (∀ s : ℂ, completedXi p A (1 - s) = completedXi p A s) ∧
      (∀ x : ℝ, 0 < (completedXi p A (x : ℂ)).re) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖reducedScattering p A w‖ ≤ 1) ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (logarithmicCoeffs hp α β) s ∧
        Complex.exp (LSeries (logarithmicCoeffs hp α β) s) =
          localFactor p A s * riemannZeta s) ∧
      (∃ k ∈ ({2, 4, 6, 8} : Finset ℕ), (eulerLogCoeff p α β (p ^ k)).re < 0) ∧
      ¬ ModelBeyondTheWallPrimeContinuation (eulerLogCoeff p α β) := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  let r : ℝ := (p : ℝ) ^ (σ : ℝ)
  let u : ℝ := (p : ℝ) ^ (1 - (σ : ℝ))
  have hr : 1 < r := Real.one_lt_rpow hpR (by linarith only [σ.property.1])
  have hu : 1 < u := Real.one_lt_rpow hpR (sub_pos.mpr σ.property.2)
  have hru : r * u = p := by
    dsimp only [r, u]
    rw [← Real.rpow_add hp0, show (σ : ℝ) + (1 - (σ : ℝ)) = 1 by ring, Real.rpow_one]
  let A : ℝ := r + u
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hr, hu]
  let α : ℂ := -(r : ℂ)
  let β : ℂ := -(u : ℂ)
  have hadd : α + β = -(A : ℂ) := by dsimp [α, β, A]; push_cast; ring
  have hmul : α * β = p := by
    dsimp [α, β]
    rw [neg_mul_neg, ← Complex.ofReal_mul, hru, Complex.ofReal_natCast]
  have hsqrt_p : Real.sqrt p = (p : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow p
  have hα_norm : ‖α‖ = r := by
    dsimp [α]; rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hr).le]
  have hβ_norm : ‖β‖ = u := by
    dsimp [β]; rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hu).le]
  have hβ_lt_sqrt : ‖β‖ < Real.sqrt p := by
    rw [hβ_norm, hsqrt_p]
    exact (Real.rpow_lt_rpow_left_iff hpR).mpr (by linarith [σ.property.1])
  have hsqrt_lt_α : Real.sqrt p < ‖α‖ := by
    rw [hα_norm, hsqrt_p]
    exact (Real.rpow_lt_rpow_left_iff hpR).mpr σ.property.1
  have hα_lt_p : ‖α‖ < p := by
    rw [hα_norm]
    exact ((Real.rpow_lt_rpow_left_iff hpR).mpr σ.property.2).trans_eq (Real.rpow_one _)
  have hβ_le_p : ‖β‖ ≤ p := by
    refine hβ_lt_sqrt.le.trans ?_
    rw [hsqrt_p]
    exact (Real.rpow_le_rpow_of_exponent_le hpR.le (by norm_num)).trans_eq (Real.rpow_one _)
  refine ⟨p, hp, A, α, β, by omega, hA,
    arithmeticCoeffs_isMultiplicative hp A,
    ⟨1 + A + p, fun n hn => ?_⟩,
    fun n hn hnN => ?_,
    differentiable_completedXi hp.ne_zero A,
    completedXi_one_sub p A,
    positiveEuler_completedXi_real_pos hp.pos hA,
    fun w hw => norm_reducedScattering_le_one hp.one_lt hr hu hru hw,
    fun s hs => ⟨logarithmicCoeffs_summable hp hα_lt_p.le hβ_le_p hs,
      logarithmicCoeffs_exp hp hadd hmul hα_lt_p.le hβ_le_p hs⟩,
    exists_negative_even_eulerLogCoeff hp hadd hmul,
    not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff hp hβ_lt_sqrt hsqrt_lt_α hα_lt_p⟩
  · have hb := coeff_bounds (p := p) hA hn
    rw [arithmeticCoeffs_apply, Complex.ofReal_im, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hb.1)]
    exact ⟨rfl, hb⟩
  · rw [arithmeticCoeffs_apply, coeff_eq_one_of_lt hn (by omega), Complex.ofReal_one]

end GaloisForLFunctions.ExclusionOfTheCriticalState
