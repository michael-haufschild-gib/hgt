import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Selectivity of odd-window positivity: the shifted pair `ζ(s − a) ζ(s + a)`

The completed product `Λ(s − a) Λ(s + a)` has the zeros `ρ ± a` of `ζ` shifted off the line, the
Dirichlet coefficients, functional equation and Euler product of an `L`-function, and the Weil
functional `g ↦ W_ζ(e^{a·} g) + W_ζ(e^{−a·} g)`. On the autocorrelation `A_F` of a real test this is
`2 W_ζ(cosh(a·) A_F)`, and since `A_{F cosh(a·)} − A_{F sinh(a·)} = cosh(a·) A_F`
(`autoCorr_cosh_sub_autoCorr_sinh`) its zero form is

    Ẑ_a(F) = 2 (Ẑ(F cosh(a·)) − Ẑ(F sinh(a·)))        (`shiftedPairZeroForm`).

**Exact comparison** (`shiftedPairZeroForm_eq`). For `F ∈ C²_c` supported in an interval `[−r, r]`,
`2r < log 2`, the Markov-window representation of `Ẑ` in one plateau gauge gives

    Ẑ_a(F) = 2 Ẑ(F) + 4 ∫_0^∞ (cosh(at) − 1) (2 cosh(t/2) − ω(t)) A_F(t) dt.

The weight `2 cosh(t/2) − ω(t)` is the regular screw kernel: negative below the plastic threshold
`t_* = log ρ` (`ρ³ = ρ + 1`), positive beyond it.

**Selectivity** (`exists_odd_shiftedPairZeroForm_neg`). For every `r` with `t_* < 2r` there is an odd
`F ∈ C²_c` supported in `[−r, r]` whose shifted-pair zero form is negative for every large `a`: two
opposite bumps separated by a distance in `(t_*, min(2r, log 2))` make the cross term
`−(cosh(at) − 1) κ(t) X(t)` dominate, while the self terms carry the negative kernel below `t_*`.
Hence odd-sector positivity on `[−r, r]` for any `r > t_*/2` is not a consequence of the structural
properties `ζ(s − a) ζ(s + a)` shares with `ζ`: it detects the position of the zeros. Combined with the
folded odd plateau (`fullZeroForm_ge_of_odd_support_le`), on every window `[−r, r]` with
`t_*/2 < r ≤ 7/25` the odd form of `ζ` is coercive while that of `ζ(s − a) ζ(s + a)` is not
(`odd_window_selective`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyCoshCrossover
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The shifted pair zero form -/

/-- The zero form of `ζ(s − a) ζ(s + a)`: `Ẑ_a(F) = 2(Ẑ(F cosh(a·)) − Ẑ(F sinh(a·)))`. -/
def shiftedPairZeroForm (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  2 * (fullZeroForm (fun x => F x * Real.cosh (a * x)) -
    fullZeroForm (fun x => F x * Real.sinh (a * x)))

/-- `A_{F cosh(a·)}(t) − A_{F sinh(a·)}(t) = cosh(at) A_F(t)`: the shifted pair acts on the
autocorrelation as the weight `cosh(a·)`. -/
theorem autoCorr_cosh_sub_autoCorr_sinh {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (a t : ℝ) :
    autoCorr (fun x => F x * Real.cosh (a * x)) t - autoCorr (fun x => F x * Real.sinh (a * x)) t =
      Real.cosh (a * t) * autoCorr F t := by
  unfold autoCorr
  have hc1 : Continuous fun x => F x * Real.cosh (a * x) * (F (x + t) * Real.cosh (a * (x + t))) := by
    fun_prop
  have hc2 : Continuous fun x => F x * Real.sinh (a * x) * (F (x + t) * Real.sinh (a * (x + t))) := by
    fun_prop
  have hs : HasCompactSupport fun x => F x * Real.cosh (a * x) *
      (F (x + t) * Real.cosh (a * (x + t))) := hFc.mul_right.mul_right
  have hs2 : HasCompactSupport fun x => F x * Real.sinh (a * x) *
      (F (x + t) * Real.sinh (a * (x + t))) := hFc.mul_right.mul_right
  rw [← integral_sub (hc1.integrable_of_hasCompactSupport hs)
    (hc2.integrable_of_hasCompactSupport hs2), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have h := Real.cosh_sub (a * (x + t)) (a * x)
  rw [show a * (x + t) - a * x = a * t by ring] at h
  rw [h]
  ring

/-! ### The Markov-window representation of the full zero form -/

section Window

variable {G P : ℝ → ℝ} {R : ℝ}

/-- **The full zero form in a plateau gauge.** For `G ∈ C²_c` with `G = P G`, `P` a window gauge
vanishing outside `(−R, R)`, `2R < log 2`:
`Ẑ(G) = ∫_0^∞ ω I_P(G) + ∫ G² P(−𝒲P) + 2∫G²(∫P cosh) − 2∫_0^∞ cosh(t/2) I_P(G)`. -/
theorem fullZeroForm_eq_window (hG : ContDiff ℝ 2 G) (hGc : HasCompactSupport G)
    (hPd : ContDiff ℝ 2 P) (hPcs : HasCompactSupport P) (hle : ∀ y, P y ≤ 1)
    (hnn : ∀ y, 0 ≤ P y) (hzero : ∀ y, R ≤ |y| → P y = 0) (hlog : 2 * R < Real.log 2)
    (hGP : ∀ x, G x ≠ 0 → P x = 1) :
    fullZeroForm G = (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P G t) +
      (∫ x, G x ^ 2 * P x * -poleFreeWeilOperator P x) +
      (2 * (∫ x, G x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2)) -
        2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile P G t) := by
  have hGB : ∀ x, G x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    have := hzero x (not_le.mp h).le
    rw [hGP x hx] at this
    norm_num at this
  have hPB : ∀ x, P x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hE := two_mul_expMoments_eq_gauge hG.continuous hPd.continuous hGB hPB hGP
  rw [fullZeroForm_eq_markovEnergy_add_expMoments hG.continuous hGc,
    markovEnergy_eq_gauge_window hG hGc hPd hPcs hle hnn hzero hGP,
    signedJumpEnergy_eq_arch_of_window hzero hlog]
  linarith [hE]

end Window

/-! ### The exact comparison with `ζ` -/

/-- The jump profile of `F cosh(a·)` minus that of `F sinh(a·)` is the jump profile of `F` minus
`2(cosh(at) − 1) A_F(t)`, for `F = P F`. -/
theorem gaugeJumpProfile_cosh_sub_sinh {F P : ℝ → ℝ} {B : ℝ} (hF : Continuous F)
    (hFB : ∀ x, F x ≠ 0 → |x| ≤ B) (hP : Continuous P) (hFP : ∀ x, F x ≠ 0 → P x = 1) (a t : ℝ) :
    gaugeJumpProfile P (fun x => F x * Real.cosh (a * x)) t -
        gaugeJumpProfile P (fun x => F x * Real.sinh (a * x)) t =
      gaugeJumpProfile P F t - 2 * (Real.cosh (a * t) - 1) * autoCorr F t := by
  unfold gaugeJumpProfile autoCorr signedShiftJump
  have hbox : ∀ g : ℝ → ℝ, HasCompactSupport fun x => P x * P (x + t) *
      (F x * g x - F (x + t) * g (x + t)) ^ 2 := fun g => by
    refine HasCompactSupport.intro (isCompact_Icc (a := -|B| - |t|) (b := |B| + |t|)) fun x hx => ?_
    have h1 : F x = 0 := by
      by_contra h
      exact hx ⟨by linarith [neg_abs_le x, (hFB x h).trans (le_abs_self B), abs_nonneg t],
        by linarith [le_abs_self x, (hFB x h).trans (le_abs_self B), abs_nonneg t]⟩
    have h2 : F (x + t) = 0 := by
      by_contra h
      have h3 := (hFB _ h).trans (le_abs_self B)
      have h4 : |x| ≤ |x + t| + |t| := by
        have := abs_sub (x + t) t; rwa [add_sub_cancel_right] at this
      exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    rw [h1, h2]
    ring
  have hcont : ∀ g : ℝ → ℝ, Continuous g → Continuous fun x => P x * P (x + t) *
      (F x * g x - F (x + t) * g (x + t)) ^ 2 := fun g hg => by fun_prop
  have i1 := (hcont _ (by fun_prop : Continuous fun x => Real.cosh (a * x))).integrable_of_hasCompactSupport
    (μ := volume) (hbox fun x => Real.cosh (a * x))
  have i2 := (hcont _ (by fun_prop : Continuous fun x => Real.sinh (a * x))).integrable_of_hasCompactSupport
    (μ := volume) (hbox fun x => Real.sinh (a * x))
  have i3 : Integrable fun x => P x * P (x + t) * (F x - F (x + t)) ^ 2 := by
    have := (hcont _ continuous_const).integrable_of_hasCompactSupport (μ := volume)
      (hbox fun _ => (1 : ℝ))
    simpa using this
  have i4 : Integrable fun x => F x * F (x + t) := by
    refine (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -|B|) (b := |B|)) fun x hx => ?_
    have h1 : F x = 0 := by
      by_contra h
      exact hx ⟨by linarith [neg_abs_le x, (hFB x h).trans (le_abs_self B)],
        by linarith [le_abs_self x, (hFB x h).trans (le_abs_self B)]⟩
    simp [h1]
  rw [← integral_sub i1 i2, ← integral_const_mul, ← integral_sub i3 (i4.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc := Real.cosh_sub (a * (x + t)) (a * x)
  rw [show a * (x + t) - a * x = a * t by ring] at hc
  have hsq1 := Real.cosh_sq_sub_sinh_sq (a * x)
  have hsq2 := Real.cosh_sq_sub_sinh_sq (a * (x + t))
  have key : (F x * Real.cosh (a * x) - F (x + t) * Real.cosh (a * (x + t))) ^ 2 -
      (F x * Real.sinh (a * x) - F (x + t) * Real.sinh (a * (x + t))) ^ 2 =
        F x ^ 2 + F (x + t) ^ 2 - 2 * F x * F (x + t) * Real.cosh (a * t) := by
    rw [hc]
    linear_combination F x ^ 2 * hsq1 + F (x + t) ^ 2 * hsq2
  have hPP : (P x * P (x + t) - 1) * (F x * F (x + t)) = 0 := by
    by_cases h1 : F x = 0
    · rw [h1]; ring
    by_cases h2 : F (x + t) = 0
    · rw [h2]; ring
    rw [hFP x h1, hFP (x + t) h2]; ring
  have e : P x * P (x + t) * (F x * Real.cosh (a * x) - F (x + t) * Real.cosh (a * (x + t))) ^ 2 -
      P x * P (x + t) * (F x * Real.sinh (a * x) - F (x + t) * Real.sinh (a * (x + t))) ^ 2 =
        P x * P (x + t) * (F x ^ 2 + F (x + t) ^ 2 - 2 * F x * F (x + t) * Real.cosh (a * t)) := by
    rw [← key]; ring
  rw [e]
  linear_combination (2 - 2 * Real.cosh (a * t)) * hPP

/-! ### The comparison identity -/

section Comparison

variable {F : ℝ → ℝ} {r : ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
  (hsupp : ∀ x, r < |x| → F x = 0) (hr0 : 0 ≤ r) (hrlog : 2 * r < Real.log 2)

/-- The plateau radius used for the comparison: halfway between `r` and `log 2 / 2`. -/
def comparisonRadius (r : ℝ) : ℝ := (r + Real.log 2 / 2) / 2

include hF hFc hsupp hr0 hrlog in
/-- **Integrability and the exact comparison.** The correction
`t ↦ (cosh(at) − 1)(2cosh(t/2) − ω(t)) A_F(t)` is integrable on `(0, ∞)` and
`Ẑ_a(F) = 2Ẑ(F) + 4 ∫_0^∞ (cosh(at) − 1)(2cosh(t/2) − ω(t)) A_F(t) dt`. -/
theorem shiftedPairZeroForm_eq (a : ℝ) :
    IntegrableOn (fun t => (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
        autoCorr F t) (Ioi 0) ∧
      shiftedPairZeroForm a F = 2 * fullZeroForm F + 4 * ∫ t in Ioi (0 : ℝ),
        (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr F t := by
  set R := comparisonRadius r with hRdef
  have hrR : r < R := by
    rw [hRdef, comparisonRadius]; linarith
  have hlog : 2 * R < Real.log 2 := by
    rw [hRdef, comparisonRadius]; linarith
  set δ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hFP : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => plateauGauge_eq_one hδ (by
    rw [hδdef]
    by_contra h
    exact hx (hsupp x (by linarith)))
  have hFB : ∀ x, F x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hsupp x (by linarith [not_le.mp h]))
  have hR0 : 0 ≤ R := by linarith
  have hR1 : R ≤ 1 / 2 := by have := Real.log_two_lt_d9; linarith
  set G₁ : ℝ → ℝ := fun x => F x * Real.cosh (a * x) with hG₁
  set G₂ : ℝ → ℝ := fun x => F x * Real.sinh (a * x) with hG₂
  have hG₁d : ContDiff ℝ 2 G₁ := hF.mul (by fun_prop)
  have hG₂d : ContDiff ℝ 2 G₂ := hF.mul (by fun_prop)
  have hG₁c : HasCompactSupport G₁ := hFc.mul_right
  have hG₂c : HasCompactSupport G₂ := hFc.mul_right
  have hG₁P : ∀ x, G₁ x ≠ 0 → P x = 1 := fun x hx => hFP x (left_ne_zero_of_mul hx)
  have hG₂P : ∀ x, G₂ x ≠ 0 → P x = 1 := fun x hx => hFP x (left_ne_zero_of_mul hx)
  have hW₁ := fullZeroForm_eq_window hG₁d hG₁c hPd hPcs hP1 hP0 hPB hlog hG₁P
  have hW₂ := fullZeroForm_eq_window hG₂d hG₂c hPd hPcs hP1 hP0 hPB hlog hG₂P
  have hW := fullZeroForm_eq_window hF hFc hPd hPcs hP1 hP0 hPB hlog hFP
  -- integrability of the jump profiles against `ω` and `cosh`
  obtain ⟨K₁, -, hK₁⟩ := exists_lipschitz_bound_of_compactSupport (hG₁d.of_le (by norm_num)) hG₁c
  obtain ⟨K₂, -, hK₂⟩ := exists_lipschitz_bound_of_compactSupport (hG₂d.of_le (by norm_num)) hG₂c
  obtain ⟨K₀, -, hK₀⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hω₁ := integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hR0 hR1 hG₁d.continuous
    hPd.continuous hPcs (fun u v => hK₁ v u)
  have hω₂ := integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hR0 hR1 hG₂d.continuous
    hPd.continuous hPcs (fun u v => hK₂ v u)
  have hω₀ := integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hR0 hR1 hF.continuous
    hPd.continuous hPcs (fun u v => hK₀ v u)
  have hPB' : ∀ x, P x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hPB x (not_le.mp h).le)
  have hcI : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn
      (fun t => Real.cosh (t / 2) * gaugeJumpProfile P g t) (Ioi 0) := fun g hg =>
    ((integrable_gaugeJump_kernel hg hPd.continuous hPB').integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])).integrableOn
  have hc₁ := hcI G₁ hG₁d.continuous
  have hc₂ := hcI G₂ hG₂d.continuous
  have hc₀ := hcI F hF.continuous
  -- the pointwise jump identity
  have hjump : ∀ t, gaugeJumpProfile P G₁ t - gaugeJumpProfile P G₂ t - gaugeJumpProfile P F t =
      -(2 * (Real.cosh (a * t) - 1) * autoCorr F t) := fun t => by
    have := gaugeJumpProfile_cosh_sub_sinh hF.continuous hFB hPd.continuous hFP a t
    rw [← hG₁, ← hG₂] at this
    linarith
  -- the correction is a combination of integrable functions
  have hcomb : ∀ t, (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
      autoCorr F t = (1 / 2) * ((archLevyDensity t * gaugeJumpProfile P G₁ t -
        archLevyDensity t * gaugeJumpProfile P G₂ t - archLevyDensity t * gaugeJumpProfile P F t) -
        2 * (Real.cosh (t / 2) * gaugeJumpProfile P G₁ t - Real.cosh (t / 2) *
          gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t)) := fun t => by
    have h := hjump t
    have e1 : archLevyDensity t * gaugeJumpProfile P G₁ t - archLevyDensity t * gaugeJumpProfile P G₂ t -
        archLevyDensity t * gaugeJumpProfile P F t = archLevyDensity t *
          (gaugeJumpProfile P G₁ t - gaugeJumpProfile P G₂ t - gaugeJumpProfile P F t) := by ring
    have e2 : Real.cosh (t / 2) * gaugeJumpProfile P G₁ t - Real.cosh (t / 2) *
        gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t = Real.cosh (t / 2) *
          (gaugeJumpProfile P G₁ t - gaugeJumpProfile P G₂ t - gaugeJumpProfile P F t) := by ring
    rw [e1, e2, h]
    ring
  have hint : IntegrableOn (fun t => (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr F t) (Ioi 0) := by
    have : IntegrableOn (fun t => 1 / 2 * ((archLevyDensity t * gaugeJumpProfile P G₁ t -
        archLevyDensity t * gaugeJumpProfile P G₂ t - archLevyDensity t * gaugeJumpProfile P F t) -
        2 * (Real.cosh (t / 2) * gaugeJumpProfile P G₁ t - Real.cosh (t / 2) *
          gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t))) (Ioi 0) :=
      ((((hω₁.sub hω₂).sub hω₀).sub (((hc₁.sub hc₂).sub hc₀).const_mul 2)).const_mul (1 / 2))
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only
    rw [hcomb t]
  refine ⟨hint, ?_⟩
  -- the potentials cancel: `G₁² − G₂² = F²`
  have hsq : ∀ x, G₁ x ^ 2 - G₂ x ^ 2 = F x ^ 2 := fun x => by
    simp only [hG₁, hG₂]
    have := Real.cosh_sq_sub_sinh_sq (a * x)
    linear_combination F x ^ 2 * this
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * |R|) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith [le_abs_self R]))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  obtain ⟨KP, -, hKP⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hWc : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous (fun u v => hKP v u) hdec8).neg
  have hGc : Continuous fun x => ∫ y, P y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hPd.continuous hPcs)
    rw [e]
    fun_prop
  have hpotI : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun x => g x ^ 2 * P x * -poleFreeWeilOperator P x) := fun g hg hgc =>
    (((hg.pow 2).mul hPd.continuous).mul hWc).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hgc).mul_right.mul_right)
  have hmassI : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun x => g x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2)) := fun g hg hgc =>
    ((hg.pow 2).mul hGc).integrable_of_hasCompactSupport (hasCompactSupport_sq hgc).mul_right
  have hpot : (∫ x, G₁ x ^ 2 * P x * -poleFreeWeilOperator P x) -
      (∫ x, G₂ x ^ 2 * P x * -poleFreeWeilOperator P x) =
        ∫ x, F x ^ 2 * P x * -poleFreeWeilOperator P x := by
    rw [← integral_sub (hpotI G₁ hG₁d.continuous hG₁c) (hpotI G₂ hG₂d.continuous hG₂c)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← hsq x]; ring
  have hmass : (∫ x, G₁ x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2)) -
      (∫ x, G₂ x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2)) =
        ∫ x, F x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2) := by
    rw [← integral_sub (hmassI G₁ hG₁d.continuous hG₁c) (hmassI G₂ hG₂d.continuous hG₂c)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← hsq x]; ring
  -- the jump terms
  have hA : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P G₁ t -
      archLevyDensity t * gaugeJumpProfile P G₂ t - archLevyDensity t * gaugeJumpProfile P F t)
      (Ioi 0) := (hω₁.sub hω₂).sub hω₀
  have hA12 : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P G₁ t -
      archLevyDensity t * gaugeJumpProfile P G₂ t) (Ioi 0) := hω₁.sub hω₂
  have hB : IntegrableOn (fun t => Real.cosh (t / 2) * gaugeJumpProfile P G₁ t -
      Real.cosh (t / 2) * gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t)
      (Ioi 0) := (hc₁.sub hc₂).sub hc₀
  have hB12 : IntegrableOn (fun t => Real.cosh (t / 2) * gaugeJumpProfile P G₁ t -
      Real.cosh (t / 2) * gaugeJumpProfile P G₂ t) (Ioi 0) := hc₁.sub hc₂
  have hB2 : IntegrableOn (fun t => 2 * (Real.cosh (t / 2) * gaugeJumpProfile P G₁ t -
      Real.cosh (t / 2) * gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t))
      (Ioi 0) := hB.const_mul 2
  have hJω : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P G₁ t) -
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P G₂ t) -
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) =
        ∫ t in Ioi (0 : ℝ), (archLevyDensity t * gaugeJumpProfile P G₁ t -
          archLevyDensity t * gaugeJumpProfile P G₂ t - archLevyDensity t * gaugeJumpProfile P F t) := by
    rw [integral_sub hA12 hω₀, integral_sub hω₁ hω₂]
  have hJc : (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile P G₁ t) -
      (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile P G₂ t) -
      (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile P F t) =
        ∫ t in Ioi (0 : ℝ), (Real.cosh (t / 2) * gaugeJumpProfile P G₁ t -
          Real.cosh (t / 2) * gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t) := by
    rw [integral_sub hB12 hc₀, integral_sub hc₁ hc₂]
  have hcorr : (∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr F t) =
        (1 / 2) * ((∫ t in Ioi (0 : ℝ), (archLevyDensity t * gaugeJumpProfile P G₁ t -
          archLevyDensity t * gaugeJumpProfile P G₂ t - archLevyDensity t * gaugeJumpProfile P F t)) -
        2 * ∫ t in Ioi (0 : ℝ), (Real.cosh (t / 2) * gaugeJumpProfile P G₁ t -
          Real.cosh (t / 2) * gaugeJumpProfile P G₂ t - Real.cosh (t / 2) * gaugeJumpProfile P F t)) := by
    rw [← integral_const_mul 2, ← integral_sub hA hB2, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hcomb t
  unfold shiftedPairZeroForm
  rw [← hG₁, ← hG₂, hW₁, hW₂, hW, hcorr]
  linarith [hpot, hmass, hJω, hJc]

end Comparison

/-! ### Odd two-bump tests -/

/-- The bump `φ(x) = P_{w, w/2}(x − c)`: `1` on `|x − c| ≤ w/2`, `0` outside `(c − w, c + w)`. -/
def bumpAt (c w x : ℝ) : ℝ := plateauGauge w (w / 2) (x - c)

/-- The odd two-bump test `φ(x) − φ(−x)`. -/
def oddTwoBump (c w x : ℝ) : ℝ := bumpAt c w x - bumpAt c w (-x)

/-- The cross-correlation `X(t) = ∫ φ(−x) φ(x + t) dx` of the two bumps. -/
def bumpCrossCorr (c w t : ℝ) : ℝ := ∫ x, bumpAt c w (-x) * bumpAt c w (x + t)

section TwoBump

variable {c w : ℝ} (hw : 0 < w) (hwc : w < c)

theorem contDiff_bumpAt (c w : ℝ) : ContDiff ℝ 2 (bumpAt c w) :=
  (contDiff_plateauGauge w (w / 2)).comp (contDiff_id.sub contDiff_const)

theorem bumpAt_nonneg (c w x : ℝ) : 0 ≤ bumpAt c w x := plateauGauge_nonneg _ _ _

include hw in
theorem bumpAt_eq_zero {x : ℝ} (h : w ≤ |x - c|) : bumpAt c w x = 0 :=
  plateauGauge_eq_zero (by positivity) h

include hw in
theorem bumpAt_eq_one {x : ℝ} (h : |x - c| ≤ w / 2) : bumpAt c w x = 1 :=
  plateauGauge_eq_one (by positivity) (by linarith)

include hw in
theorem bumpAt_ne_zero_imp {x : ℝ} (h : bumpAt c w x ≠ 0) : |x - c| < w := by
  by_contra h'
  exact h (bumpAt_eq_zero hw (not_lt.mp h'))

include hw in
theorem hasCompactSupport_bumpAt : HasCompactSupport (bumpAt c w) :=
  HasCompactSupport.intro (isCompact_Icc (a := c - w) (b := c + w)) fun x hx => by
    refine bumpAt_eq_zero hw ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

theorem contDiff_oddTwoBump (c w : ℝ) : ContDiff ℝ 2 (oddTwoBump c w) :=
  (contDiff_bumpAt c w).sub ((contDiff_bumpAt c w).comp contDiff_neg)

include hw in
theorem hasCompactSupport_oddTwoBump : HasCompactSupport (oddTwoBump c w) :=
  (hasCompactSupport_bumpAt hw).sub ((hasCompactSupport_bumpAt hw).comp_homeomorph (Homeomorph.neg ℝ))

theorem oddTwoBump_neg (c w x : ℝ) : oddTwoBump c w (-x) = -oddTwoBump c w x := by
  unfold oddTwoBump; rw [neg_neg]; ring

include hw hwc in
theorem oddTwoBump_eq_zero {x : ℝ} (h : c + w < |x|) : oddTwoBump c w x = 0 := by
  have hc : 0 < c := by linarith
  unfold oddTwoBump
  have h1 := abs_sub_abs_le_abs_sub x c
  have h2 := abs_sub_abs_le_abs_sub (-x) c
  rw [abs_of_pos hc] at h1 h2
  rw [abs_neg] at h2
  rw [bumpAt_eq_zero hw (by linarith), bumpAt_eq_zero hw (by linarith), sub_zero]

include hw hwc in
/-- For `t > 0` the autocorrelation of the odd two-bump is `2 A_φ(t) − X(t)`. -/
theorem autoCorr_oddTwoBump {t : ℝ} (ht : 0 < t) :
    autoCorr (oddTwoBump c w) t = 2 * autoCorr (bumpAt c w) t - bumpCrossCorr c w t := by
  have hφ := (contDiff_bumpAt c w).continuous
  have hφc := hasCompactSupport_bumpAt hw (c := c)
  have hint : ∀ g h : ℝ → ℝ, Continuous g → Continuous h → HasCompactSupport g →
      Integrable fun x => g x * h x := fun g h hg hh hgc =>
    (hg.mul hh).integrable_of_hasCompactSupport hgc.mul_right
  have hc1 : Continuous fun x => bumpAt c w (x + t) := hφ.comp (continuous_id.add continuous_const)
  have hc2 : Continuous fun x => bumpAt c w (-x - t) := hφ.comp (continuous_neg.sub continuous_const)
  have hc3 : Continuous fun x => bumpAt c w (-x) := hφ.comp continuous_neg
  have i1 := hint (fun x => bumpAt c w x) (fun x => bumpAt c w (x + t)) hφ hc1 hφc
  have i2 := hint (fun x => bumpAt c w x) (fun x => bumpAt c w (-x - t)) hφ hc2 hφc
  have i3 := hint (fun x => bumpAt c w (-x)) (fun x => bumpAt c w (x + t)) hc3 hc1
    (hφc.comp_homeomorph (Homeomorph.neg ℝ))
  have i4 := hint (fun x => bumpAt c w (-x)) (fun x => bumpAt c w (-x - t)) hc3 hc2
    (hφc.comp_homeomorph (Homeomorph.neg ℝ))
  have h0 : ∀ x, bumpAt c w x * bumpAt c w (-x - t) = 0 := fun x => by
    by_cases h1 : bumpAt c w x = 0
    · rw [h1, zero_mul]
    · have h3 := bumpAt_ne_zero_imp hw h1
      have hx : c - w < x := by have := (abs_lt.mp h3).1; linarith
      rw [bumpAt_eq_zero hw (x := -x - t) (by rw [abs_of_neg (by linarith)]; linarith), mul_zero]
  have h4 : (∫ x, bumpAt c w (-x) * bumpAt c w (-x - t)) = autoCorr (bumpAt c w) t := by
    have e1 : (∫ x, bumpAt c w (-x) * bumpAt c w (-x - t)) =
        ∫ x, bumpAt c w x * bumpAt c w (x - t) :=
      integral_neg_eq_self (fun y => bumpAt c w y * bumpAt c w (y - t)) volume
    rw [e1, ← integral_add_right_eq_self (fun x => bumpAt c w x * bumpAt c w (x - t)) t]
    unfold autoCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
    ring
  unfold autoCorr oddTwoBump bumpCrossCorr
  have e : (fun x => (bumpAt c w x - bumpAt c w (-x)) * (bumpAt c w (x + t) - bumpAt c w (-(x + t)))) =
      fun x => bumpAt c w x * bumpAt c w (x + t) - bumpAt c w x * bumpAt c w (-x - t) -
        bumpAt c w (-x) * bumpAt c w (x + t) + bumpAt c w (-x) * bumpAt c w (-x - t) := by
    funext x; rw [show -(x + t) = -x - t by ring]; ring
  have i12 : Integrable fun x => bumpAt c w x * bumpAt c w (x + t) -
      bumpAt c w x * bumpAt c w (-x - t) := i1.sub i2
  have i123 : Integrable fun x => bumpAt c w x * bumpAt c w (x + t) -
      bumpAt c w x * bumpAt c w (-x - t) - bumpAt c w (-x) * bumpAt c w (x + t) := i12.sub i3
  rw [e, integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, h4]
  simp only [h0, integral_zero]
  unfold autoCorr
  ring

theorem autoCorr_bumpAt_nonneg (t : ℝ) : 0 ≤ autoCorr (bumpAt c w) t :=
  integral_nonneg fun _ => mul_nonneg (bumpAt_nonneg _ _ _) (bumpAt_nonneg _ _ _)

include hw in
theorem autoCorr_bumpAt_eq_zero {t : ℝ} (ht : 2 * w ≤ t) : autoCorr (bumpAt c w) t = 0 := by
  unfold autoCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  by_cases h1 : bumpAt c w x = 0
  · rw [h1, zero_mul]
  · have h3 := bumpAt_ne_zero_imp hw h1
    rw [bumpAt_eq_zero hw (x := x + t) (by
      rw [show x + t - c = (x - c) + t by ring]
      have := (abs_lt.mp h3).1
      rw [abs_of_pos (by linarith)]; linarith), mul_zero]

theorem bumpCrossCorr_nonneg (c w t : ℝ) : 0 ≤ bumpCrossCorr c w t :=
  integral_nonneg fun _ => mul_nonneg (bumpAt_nonneg _ _ _) (bumpAt_nonneg _ _ _)

include hw in
theorem bumpCrossCorr_eq_zero_of_lt {t : ℝ} (ht : t ≤ 2 * c - 2 * w) : bumpCrossCorr c w t = 0 := by
  unfold bumpCrossCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  by_cases h1 : bumpAt c w (-x) = 0
  · rw [h1, zero_mul]
  · have h3 := bumpAt_ne_zero_imp hw h1
    rw [bumpAt_eq_zero hw (x := x + t) (by
      have := (abs_lt.mp h3).1
      rw [abs_of_neg (by linarith)]; linarith), mul_zero]

include hw in
theorem bumpCrossCorr_eq_zero_of_gt {t : ℝ} (ht : 2 * c + 2 * w ≤ t) :
    bumpCrossCorr c w t = 0 := by
  unfold bumpCrossCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  by_cases h1 : bumpAt c w (-x) = 0
  · rw [h1, zero_mul]
  · have h3 := bumpAt_ne_zero_imp hw h1
    rw [bumpAt_eq_zero hw (x := x + t) (by
      have := (abs_lt.mp h3).2
      rw [abs_of_pos (by linarith)]; linarith), mul_zero]

include hw in
/-- `∫ X = (∫ φ)² ≥ w²`. -/
theorem integral_bumpCrossCorr_ge : w ^ 2 ≤ ∫ t, bumpCrossCorr c w t := by
  have hφ := (contDiff_bumpAt c w).continuous
  have hφc := hasCompactSupport_bumpAt hw (c := c)
  have hbox : Integrable (fun p : ℝ × ℝ => bumpAt c w (-p.2) * bumpAt c w (p.2 + p.1))
      ((volume : Measure ℝ).prod volume) := by
    refine integrable_prod_of_box (B := 2 * (|c| + w)) (by fun_prop) fun p hp => ?_
    have h1 : bumpAt c w (-p.2) ≠ 0 := left_ne_zero_of_mul hp
    have h2 : bumpAt c w (p.2 + p.1) ≠ 0 := right_ne_zero_of_mul hp
    have a1 := bumpAt_ne_zero_imp hw h1
    have a2 := bumpAt_ne_zero_imp hw h2
    rw [abs_lt] at a1 a2
    constructor <;> rw [abs_le] <;> constructor <;>
      linarith [neg_abs_le c, le_abs_self c]
  have hswap := integral_integral_swap (f := fun t x => bumpAt c w (-x) * bumpAt c w (x + t)) hbox
  have hin : ∀ x, (∫ t, bumpAt c w (-x) * bumpAt c w (x + t)) = bumpAt c w (-x) * ∫ t, bumpAt c w t := by
    intro x
    rw [integral_const_mul, integral_add_left_eq_self (fun t => bumpAt c w t) x]
  have hneg : (∫ x, bumpAt c w (-x)) = ∫ x, bumpAt c w x := integral_neg_eq_self _ _
  have hmass : w ≤ ∫ x, bumpAt c w x := by
    have hint : Integrable (bumpAt c w) := hφ.integrable_of_hasCompactSupport hφc
    have h1 : (∫ x in Icc (c - w / 2) (c + w / 2), (1 : ℝ)) ≤ ∫ x in Icc (c - w / 2) (c + w / 2), bumpAt c w x :=
      setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
        fun x hx => by
          rw [bumpAt_eq_one hw (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])]
    have h2 : (∫ x in Icc (c - w / 2) (c + w / 2), bumpAt c w x) ≤ ∫ x, bumpAt c w x :=
      setIntegral_le_integral hint (Eventually.of_forall fun x => bumpAt_nonneg _ _ _)
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc,
      max_eq_left (by linarith)] at h1
    linarith
  unfold bumpCrossCorr
  rw [hswap]
  simp_rw [hin]
  rw [integral_mul_const, hneg]
  nlinarith [hmass]

end TwoBump

/-! ### Selectivity past the plastic threshold -/

/-- The plastic threshold lies in `(1/10, log 2)`. -/
theorem screwSignThreshold_bounds :
    1 / 10 < GaloisForLFunctions.RHTower.screwSignThreshold ∧
      GaloisForLFunctions.RHTower.screwSignThreshold < Real.log 2 := by
  have hρ1 := plasticRoot_gt
  have hρ2 := plasticRoot_lt
  have hρ0 : 0 < GaloisForLFunctions.RHTower.plasticRoot := by linarith
  unfold GaloisForLFunctions.RHTower.screwSignThreshold
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hρ0
    have h2 : (GaloisForLFunctions.RHTower.plasticRoot)⁻¹ < 250 / 331 := by
      rw [inv_lt_comm₀ hρ0 (by norm_num)]; norm_num; linarith
    linarith
  · exact Real.log_lt_log hρ0 (by linarith)

/-- `2 cosh(t/2) − ω(t)` is monotone on `(0, ∞)`. -/
theorem screwWeight_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    2 * Real.cosh (s / 2) - archLevyDensity s ≤ 2 * Real.cosh (t / 2) - archLevyDensity t := by
  have h1 : Real.cosh (s / 2) ≤ Real.cosh (t / 2) := by
    rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have h2 : archLevyDensity t ≤ archLevyDensity s :=
    strictAntiOn_archLevyDensity.antitoneOn hs (show (0 : ℝ) < t by linarith) hst
  linarith

/-- `u²/2 ≤ cosh u − 1`. -/
theorem sq_div_two_le_cosh_sub_one {u : ℝ} (hu : 0 ≤ u) : u ^ 2 / 2 ≤ Real.cosh u - 1 := by
  have h := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring] at h
  have hc := Real.cosh_sq (u / 2)
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have hs2 : (u / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hs 2
  nlinarith

/-- **The shifted pair on the odd two-bump.** If the bumps have width `2w ≤ t_*` and separation
`t₁ = 2c − 2w > t_*`, with total support below `log 2`, then for `a ≥ 0`
`Ẑ_a(F) ≤ 2 Ẑ(F) − 2 a² t₁² κ(t₁) w²`, `κ(t) = 2cosh(t/2) − ω(t) > 0`. -/
theorem shiftedPairZeroForm_oddTwoBump_le {c w a : ℝ} (hw : 0 < w) (hwc : w < c)
    (hsmall : 2 * w ≤ GaloisForLFunctions.RHTower.screwSignThreshold)
    (hthr : GaloisForLFunctions.RHTower.screwSignThreshold < 2 * c - 2 * w)
    (hlog : 2 * (c + w) < Real.log 2) (ha : 0 ≤ a) :
    shiftedPairZeroForm a (oddTwoBump c w) ≤ 2 * fullZeroForm (oddTwoBump c w) -
      2 * a ^ 2 * (2 * c - 2 * w) ^ 2 *
        (2 * Real.cosh ((2 * c - 2 * w) / 2) - archLevyDensity (2 * c - 2 * w)) * w ^ 2 := by
  set t₁ := 2 * c - 2 * w with ht₁
  set κ₁ := 2 * Real.cosh (t₁ / 2) - archLevyDensity t₁ with hκ₁
  have ht₁0 : 0 < t₁ := by linarith
  have hκ₁0 : 0 < κ₁ := by
    have h := (GaloisForLFunctions.RHTower.screwRegularKernel_pos_iff ht₁0).mpr hthr
    rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht₁0] at h
    exact h
  have hc0 : 0 < c := by linarith
  set g : ℝ → ℝ := fun t => (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t)
    with hgdef
  -- the two comparison identities
  obtain ⟨hIF, hEF⟩ := shiftedPairZeroForm_eq (F := oddTwoBump c w) (r := c + w)
    (contDiff_oddTwoBump c w) (hasCompactSupport_oddTwoBump hw)
    (fun x hx => oddTwoBump_eq_zero hw hwc hx) (by linarith) hlog a
  obtain ⟨hIφ, -⟩ := shiftedPairZeroForm_eq (F := bumpAt c w) (r := c + w)
    (contDiff_bumpAt c w) (hasCompactSupport_bumpAt hw) (fun x hx => bumpAt_eq_zero hw (by
      have := abs_sub_abs_le_abs_sub x c
      rw [abs_of_pos hc0] at this; linarith)) (by linarith) hlog a
  -- the cross part
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), g t * autoCorr (oddTwoBump c w) t =
      2 * (g t * autoCorr (bumpAt c w) t) - g t * bumpCrossCorr c w t := fun t ht => by
    rw [autoCorr_oddTwoBump hw hwc ht]; ring
  have hIX : IntegrableOn (fun t => g t * bumpCrossCorr c w t) (Ioi 0) := by
    have h2 : IntegrableOn (fun t => 2 * (g t * autoCorr (bumpAt c w) t) -
        g t * autoCorr (oddTwoBump c w) t) (Ioi 0) := (hIφ.const_mul 2).sub hIF
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [hsplit t ht]; ring
  have hIφ2 : IntegrableOn (fun t => 2 * (g t * autoCorr (bumpAt c w) t)) (Ioi 0) :=
    hIφ.const_mul 2
  have hsum : (∫ t in Ioi (0 : ℝ), g t * autoCorr (oddTwoBump c w) t) =
      2 * (∫ t in Ioi (0 : ℝ), g t * autoCorr (bumpAt c w) t) -
        ∫ t in Ioi (0 : ℝ), g t * bumpCrossCorr c w t := by
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hIφ2 hIX, integral_const_mul]
  -- the self part is nonpositive: the kernel is negative below the plastic threshold
  have hself : (∫ t in Ioi (0 : ℝ), g t * autoCorr (bumpAt c w) t) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    by_cases h2w : t < 2 * w
    · have hk : 2 * Real.cosh (t / 2) - archLevyDensity t ≤ 0 := by
        have := two_mul_cosh_le_archLevyDensity_of_le_threshold ht0 (by linarith)
        linarith
      have hc1 : 0 ≤ Real.cosh (a * t) - 1 := by linarith [Real.one_le_cosh (a * t)]
      have hA := autoCorr_bumpAt_nonneg (c := c) (w := w) t
      simp only [hgdef]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc1 hk) hA
    · rw [autoCorr_bumpAt_eq_zero hw (not_lt.mp h2w), mul_zero]
  -- the cross part is at least `(cosh(a t₁) − 1) κ(t₁) ∫ X`
  have hXi : Integrable (fun t => bumpCrossCorr c w t) := by
    have hφ := (contDiff_bumpAt c w).continuous
    have hbox : Integrable (fun p : ℝ × ℝ => bumpAt c w (-p.2) * bumpAt c w (p.2 + p.1))
        ((volume : Measure ℝ).prod volume) := by
      refine integrable_prod_of_box (B := 2 * (|c| + w)) (by fun_prop) fun p hp => ?_
      have a1 := bumpAt_ne_zero_imp hw (left_ne_zero_of_mul hp)
      have a2 := bumpAt_ne_zero_imp hw (right_ne_zero_of_mul hp)
      rw [abs_lt] at a1 a2
      constructor <;> rw [abs_le] <;> constructor <;> linarith [neg_abs_le c, le_abs_self c]
    exact hbox.integral_prod_left
  have hXset : (∫ t in Ioi (0 : ℝ), bumpCrossCorr c w t) = ∫ t, bumpCrossCorr c w t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      bumpCrossCorr_eq_zero_of_lt hw (by rw [mem_Ioi, not_lt] at ht; linarith)
  have hcross : (Real.cosh (a * t₁) - 1) * κ₁ * ∫ t in Ioi (0 : ℝ), bumpCrossCorr c w t ≤
      ∫ t in Ioi (0 : ℝ), g t * bumpCrossCorr c w t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hXi.integrableOn.const_mul _) hIX measurableSet_Ioi fun t ht => ?_
    have hX0 := bumpCrossCorr_nonneg c w t
    by_cases hX : bumpCrossCorr c w t = 0
    · rw [hX]; simp
    · have h1 : t₁ < t := by
        by_contra h
        exact hX (bumpCrossCorr_eq_zero_of_lt hw (by rw [ht₁] at h; linarith))
      have hcosh : Real.cosh (a * t₁) - 1 ≤ Real.cosh (a * t) - 1 := by
        have : Real.cosh (a * t₁) ≤ Real.cosh (a * t) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by
            have : (0 : ℝ) < t := lt_trans ht₁0 h1; positivity)]
          exact mul_le_mul_of_nonneg_left h1.le ha
        linarith
      have hκ : κ₁ ≤ 2 * Real.cosh (t / 2) - archLevyDensity t := screwWeight_mono ht₁0 h1.le
      have hc1 : 0 ≤ Real.cosh (a * t₁) - 1 := by linarith [Real.one_le_cosh (a * t₁)]
      simp only [hgdef]
      have h3 : (Real.cosh (a * t₁) - 1) * κ₁ ≤
          (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) :=
        mul_le_mul hcosh hκ hκ₁0.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right h3 hX0]
  have hXw := integral_bumpCrossCorr_ge hw (c := c)
  have hquad := sq_div_two_le_cosh_sub_one (show 0 ≤ a * t₁ by positivity)
  rw [hEF, hsum]
  have hprod : (Real.cosh (a * t₁) - 1) * κ₁ * w ^ 2 ≤
      (Real.cosh (a * t₁) - 1) * κ₁ * ∫ t in Ioi (0 : ℝ), bumpCrossCorr c w t := by
    rw [hXset]
    exact mul_le_mul_of_nonneg_left hXw (mul_nonneg (by linarith [Real.one_le_cosh (a * t₁)]) hκ₁0.le)
  have hlow : (a * t₁) ^ 2 / 2 * κ₁ * w ^ 2 ≤ (Real.cosh (a * t₁) - 1) * κ₁ * w ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hquad hκ₁0.le) (sq_nonneg w)
  nlinarith [hself, hcross, hprod, hlow]

/-- **Selectivity of odd-window positivity.** For every `r` with `t_* < 2r` there is an odd
`F ∈ C²_c` supported in `[−r, r]` whose `ζ(s − a) ζ(s + a)` zero form is negative for every large
`a`. -/
theorem exists_odd_shiftedPairZeroForm_neg {r : ℝ}
    (hr : GaloisForLFunctions.RHTower.screwSignThreshold < 2 * r) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ x, F (-x) = -F x) ∧
      (∀ x, r < |x| → F x = 0) ∧ ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → shiftedPairZeroForm a F < 0 := by
  set ts := GaloisForLFunctions.RHTower.screwSignThreshold with hts
  obtain ⟨hts1, hts2⟩ := screwSignThreshold_bounds
  rw [← hts] at hts1 hts2
  set ε := min (2 * r) (Real.log 2) - ts with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact sub_pos.mpr (lt_min hr hts2)
  have hεle : ε ≤ Real.log 2 - ts := by rw [hεdef]; linarith [min_le_right (2 * r) (Real.log 2)]
  have hεr : ε ≤ 2 * r - ts := by rw [hεdef]; linarith [min_le_left (2 * r) (Real.log 2)]
  have hlog2 := Real.log_two_lt_d9
  set c := ts / 2 + ε / 4 with hc
  set w := ε / 16 with hw
  have hw0 : 0 < w := by positivity
  have hwc : w < c := by rw [hc, hw]; linarith
  have hsmall : 2 * w ≤ ts := by rw [hw]; linarith
  have hthr : ts < 2 * c - 2 * w := by rw [hc, hw]; linarith
  have hlog : 2 * (c + w) < Real.log 2 := by rw [hc, hw]; linarith
  have hsupp : c + w < r := by rw [hc, hw]; linarith
  refine ⟨oddTwoBump c w, contDiff_oddTwoBump c w, hasCompactSupport_oddTwoBump hw0,
    oddTwoBump_neg c w, fun x hx => oddTwoBump_eq_zero hw0 hwc (by linarith), ?_⟩
  set t₁ := 2 * c - 2 * w with ht₁
  set κ₁ := 2 * Real.cosh (t₁ / 2) - archLevyDensity t₁ with hκ₁
  have ht₁0 : 0 < t₁ := by linarith
  have hκ₁0 : 0 < κ₁ := by
    have h := (GaloisForLFunctions.RHTower.screwRegularKernel_pos_iff ht₁0).mpr hthr
    rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht₁0] at h
    exact h
  set Z := fullZeroForm (oddTwoBump c w) with hZ
  set D := t₁ ^ 2 * κ₁ * w ^ 2 with hD
  have hD0 : 0 < D := by positivity
  refine ⟨max 0 (Z / D) + 1, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := by linarith [le_max_left 0 (Z / D)]
  have ha0 : 0 ≤ a := by linarith
  have hle := shiftedPairZeroForm_oddTwoBump_le hw0 hwc hsmall hthr hlog ha0
  rw [← ht₁, ← hκ₁, ← hZ] at hle
  have hZD : Z / D < a ^ 2 := by
    have h1 : Z / D < a := by linarith [le_max_right 0 (Z / D)]
    nlinarith
  have hZ' : Z < a ^ 2 * D := by rwa [div_lt_iff₀ hD0] at hZD
  have : 2 * a ^ 2 * t₁ ^ 2 * κ₁ * w ^ 2 = 2 * (a ^ 2 * D) := by rw [hD]; ring
  linarith

/-- **ζ against ζ(s − a) ζ(s + a) on the odd windows past the plastic threshold.** For every
`r` with `t_* < 2r ≤ 14/25`, the odd zero form of `ζ` is coercive on `[−r, r]`
(`fullZeroForm_ge_of_odd_support_le`), while some odd test supported in `[−r, r]` has negative
zero form for `ζ(s − a) ζ(s + a)` at every large shift `a`. -/
theorem odd_window_selective {r : ℝ}
    (hr1 : GaloisForLFunctions.RHTower.screwSignThreshold < 2 * r) (hr2 : r ≤ 7 / 25) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
        (∀ x, r < |x| → F x = 0) → 1 / 40 * ∫ x, F x ^ 2 ≤ fullZeroForm F) ∧
      ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ x, F (-x) = -F x) ∧
        (∀ x, r < |x| → F x = 0) ∧ ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → shiftedPairZeroForm a F < 0 :=
  ⟨fun F hF hFc hodd hsupp => fullZeroForm_ge_of_odd_support_le hF hFc hodd fun x hx =>
      hsupp x (by linarith), exists_odd_shiftedPairZeroForm_neg hr1⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
