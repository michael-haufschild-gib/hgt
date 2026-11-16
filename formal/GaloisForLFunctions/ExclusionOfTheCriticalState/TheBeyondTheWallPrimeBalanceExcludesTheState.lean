import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheCriticalStateSeesALeftZero
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeHeadsAreHardyTransforms
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# The beyond-the-wall prime-pole balance excludes the critical state

Left of the zero strip (`Re p < -½`), Euler cancellation and removal of the first archimedean
exponential mode write the probe remainder of every energy-domain profile `F ∈ H` as

  `globalRemainder F p = J_{≥1} F(p) + Φ_F(p)`,

where `J_{≥1} F(p) = Σ_{k ≥ 0} L F(2(k + 1) + ½) / (2(k + 1) + ½ - p)` is the positive-charge-cancelled
archimedean resolvent tail and

  `Φ_F(p) = primeHead F p + L F(-½) / (p + ½)`

is the beyond-the-wall prime-pole balance — the Laplace transform on `Re p < -½` of the
right-of-wall prime-remainder wave `Σ_{n > e^v} Λ(n) n^{-½} F(v - log n) - ∫_{x > v} F(v - x) e^{x/2} dx`.

* **Strip-wide archimedean holomorphy (`differentiableOn_archimedeanWallTail`).** Because
  `|L F(r)| ≤ (2 ∫ F² + 1) / (4 √r)` for `r > 0`, the series `J_{≥1} F(p)` converges uniformly on
  compacta and is holomorphic throughout `Re p < 5/2`, across the entire critical strip.
* **Direct single-state exclusion (`criticalState_not_hasBeyondTheWallPrimeContinuation`).** Every
  critical half-line ground state `F` sees a left zero `z₀` (`-½ < Re z₀ < 0`, `L F(z₀) ≠ 0`). Any
  holomorphic continuation of `Φ_F` from `Re p < -½` to `Re p < 0` would give `clearedRemainder F`
  analytic order at least `ord_{1/2 + z₀}(ξ)` at `z₀`, contradicting its exact order drop
  `ord(clearedRemainder F, z₀) + 1 = ord(ξ, ½ + z₀)`.
* **Consequences and corollaries.** Holomorphic continuation of `Φ_F` to `Re p < 0` across `H`
  (`ZetaBeyondTheWallPrimeContinuation`), as well as continuation of the bare prime-head series
  `primeHead G` alone on the pole-neutral subspace `L G(-½) = 0` (`PurePrimeHeadContinuation`),
  excludes the critical state, is equivalent to its nonexistence (and to `RiemannHypothesis`),
  forbids sub-strip Hardy damping `e^{-δv} W_F(v) ∈ L²(0, ∞)` on `0 < δ ≤ ½` for any critical
  state, and is unconditionally sharp at the boundary `Re p = 0`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Strip-wide holomorphy of the charge-cancelled archimedean wall tail -/

/-- The positive-charge-cancelled archimedean resolvent tail
`J_{≥1} F(p) = Σ_{k ≥ 0} L F(2(k + 1) + ½) / (2(k + 1) + ½ - p)`. -/
def archimedeanWallTail (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' k : ℕ, negativeHalfLineLaplace (cx F) (2 * (k + 1) + 1 / 2) /
    ((2 * (k + 1) + 1 / 2 : ℂ) - p)

private theorem norm_laplace_pos_real_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {r : ℝ} (hr : 0 < r) :
    ‖negativeHalfLineLaplace (cx F) (r : ℂ)‖ ≤
      (2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt r) := by
  set s := Real.sqrt r
  have hs : 0 < s := Real.sqrt_pos.mpr hr
  have hs2 : s ^ 2 = r := Real.sq_sqrt hr.le
  have hdom : Integrable fun u : ℝ => (1 / (2 * s)) * F u ^ 2 + (s / 2) * probe (2 * r) u :=
    (hF.sq.const_mul _).add ((integrable_probe (by positivity)).const_mul _)
  have hpt : ∀ u : ℝ, ‖cexp ((r : ℂ) * u) * cx F u‖ ≤
      (1 / (2 * s)) * F u ^ 2 + (s / 2) * probe (2 * r) u := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.ofReal_re, Complex.norm_real,
        Real.norm_eq_abs, probe_of_neg hu]
      set X := |F u| / Real.sqrt s
      set Y := Real.sqrt s * Real.exp (r * u)
      have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
      have hXY : Real.exp (r * u) * |F u| = X * Y := by
        dsimp [X, Y]; field_simp [(Real.sqrt_pos.mpr hs).ne']
      have hX2 : (1 / (2 * s)) * F u ^ 2 = X ^ 2 / 2 := by
        dsimp [X]; rw [div_pow, sq_abs, hss]; ring
      have hY2 : (s / 2) * Real.exp ((2 * r) * u) = Y ^ 2 / 2 := by
        dsimp [Y]
        rw [mul_pow, hss, sq (Real.exp (r * u)), ← Real.exp_add,
          show r * u + r * u = (2 * r) * u by ring]
        ring
      rw [hXY, hX2, hY2]
      nlinarith [sq_nonneg (X - Y)]
    · simp [cx, hF.support u hu, probe_of_nonneg hu]
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add (hF.sq.const_mul _) ((integrable_probe (by positivity)).const_mul _),
    integral_const_mul, integral_const_mul, integral_probe (by positivity)]
  field_simp [hs.ne', hr.ne']
  nlinarith [hs2]

/-- The charge-cancelled archimedean resolvent tail `J_{≥1} F` is holomorphic across the entire
half-plane `Re p < 5/2`, covering the whole critical strip `|Re p| < ½`. -/
theorem differentiableOn_archimedeanWallTail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (archimedeanWallTail F) {p : ℂ | p.re < 5 / 2} := by
  intro p₀ hp₀
  have hp₀' : p₀.re < 5 / 2 := hp₀
  set σ := (p₀.re + 5 / 2) / 2
  have hσ5 : σ < 5 / 2 := by dsimp [σ]; linarith
  have hpσ : p₀.re < σ := by dsimp [σ]; linarith
  set δ := min (5 / 2 - σ) 1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hσ5) one_pos
  have hF2n : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  set C := (2 * (∫ u, F u ^ 2) + 1) / (4 * δ)
  have hsum : Summable fun k : ℕ => C * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have hr := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
    exact (hr.mul_left C).congr fun k => by push_cast; rfl
  have hU : IsOpen {p : ℂ | p.re < σ} := isOpen_lt Complex.continuous_re continuous_const
  have hd : DifferentiableOn ℂ (archimedeanWallTail F) {p : ℂ | p.re < σ} := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun k => ?_) hU
      (fun k p hp => ?_)
    · intro p hp
      have hp' : p.re < σ := hp
      have hne : (2 * ((k : ℂ) + 1) + 1 / 2) - p ≠ 0 := by
        intro e; have := congrArg Complex.re e; simp at this
        linarith [Nat.cast_nonneg (α := ℝ) k]
      exact ((differentiableAt_const _).div
        ((differentiableAt_const _).sub differentiableAt_id) hne).differentiableWithinAt
    · have hp' : p.re < σ := hp
      set rk : ℝ := 2 * ((k : ℝ) + 1) + 1 / 2
      have hrk_ge : (k : ℝ) + 1 ≤ rk := by
        dsimp [rk]; linarith [Nat.cast_nonneg (α := ℝ) k]
      have hrk_pos : 0 < rk := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hcast_rk : ((rk : ℝ) : ℂ) = 2 * ((k : ℂ) + 1) + 1 / 2 := by
        dsimp [rk]; push_cast; ring
      have hL := norm_laplace_pos_real_le hF hrk_pos
      rw [hcast_rk] at hL
      have hden : δ * ((k : ℝ) + 1) ≤ ‖(2 * ((k : ℂ) + 1) + 1 / 2) - p‖ := by
        have hre_le : δ * ((k : ℝ) + 1) ≤ ((2 * ((k : ℂ) + 1) + 1 / 2) - p).re := by
          rw [← hcast_rk, Complex.sub_re, Complex.ofReal_re]
          dsimp [rk]
          have hδ1 : δ ≤ 1 := min_le_right _ _
          have hδ2 : δ ≤ 5 / 2 - σ := min_le_left _ _
          nlinarith [Nat.cast_nonneg (α := ℝ) k]
        exact hre_le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
      have hsqrt_le : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt rk := Real.sqrt_le_sqrt hrk_ge
      have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
      rw [norm_div]
      calc ‖negativeHalfLineLaplace (cx F) (2 * ((k : ℂ) + 1) + 1 / 2)‖ /
              ‖(2 * ((k : ℂ) + 1) + 1 / 2) - p‖
          ≤ ((2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt rk)) / (δ * ((k : ℝ) + 1)) :=
            div_le_div₀ (by positivity) hL (by positivity) hden
        _ ≤ ((2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt ((k : ℝ) + 1))) / (δ * ((k : ℝ) + 1)) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num))
        _ = C * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            dsimp [C]
            rw [Real.sqrt_eq_rpow, div_div,
              show 4 * ((k : ℝ) + 1) ^ (1 / 2 : ℝ) * (δ * ((k : ℝ) + 1)) =
                (4 * δ) * (((k : ℝ) + 1) ^ (1 / 2 : ℝ) * ((k : ℝ) + 1) ^ (1 : ℝ)) by
                rw [Real.rpow_one]; ring,
              ← Real.rpow_add hk1_pos, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
              Real.rpow_neg hk1_pos.le, div_mul_eq_div_div, div_eq_mul_inv]
  exact (hd.differentiableAt (hU.mem_nhds hpσ)).differentiableWithinAt

/-! ### The beyond-the-wall prime-pole balance and right-of-wall wave -/

/-- The beyond-the-wall prime-pole balance `Φ_F(p) = Ŝ F(p) + L F(-½)/(p + ½)`. -/
def wallPrimeBalance (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  primeHead F p + negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

theorem differentiableOn_wallPrimeBalance {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (wallPrimeBalance F) {p : ℂ | p.re < -(1 / 2)} := by
  intro p hp
  have hp' : p.re < -(1 / 2) := hp
  have hS := (differentiableOn_primeHead hF).differentiableAt
    ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hp')
  have hP : DifferentiableAt ℂ
      (fun q : ℂ => negativeHalfLineLaplace (cx F) (-(1 / 2)) / (q + 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.add_const _)
      (by intro e; have := congrArg Complex.re e; simp at this; linarith)
  exact (hS.add hP).differentiableWithinAt

/-- Left of the strip (`Re p < -½`), `globalRemainder F p` splits cleanly into the strip-holomorphic
archimedean wall tail `J_{≥1} F(p)` and the beyond-the-wall prime-pole balance `Φ_F(p)`. -/
theorem globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : p.re < -(1 / 2)) :
    globalRemainder F p = archimedeanWallTail F p + wallPrimeBalance F p := by
  rw [globalRemainder, if_neg (not_lt.mpr hp.le), if_pos hp, leftRemainder_eq_resolvents hF hp]
  unfold archimedeanWallTail wallPrimeBalance
  ring

/-- The damped right-of-wall prime-remainder wave in `L²(0, ∞)` at margin `½ < c ≤ 4`:
the sum of translated prime profiles minus the `s = 1` exponential polar charge. -/
def wallPrimeWaveDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1 / 2 < c) : Lp ℂ 2 halfLineLaplaceMeasure :=
  let head : Lp ℂ 2 halfLineLaplaceMeasure := primeHeadProfileLp hF hc
  head -
    negativeHalfLineLaplace (cx F) (-(1 / 2)) •
      halfLineLaplaceFeature ((c - 1 / 2 : ℝ) : ℂ)
        (by simp only [Complex.ofReal_re]; linarith only [hc0])

/-- Left of the strip, `Φ_F(-(z + c))` is the exact half-line Laplace transform of
`wallPrimeWaveDatumLp`. -/
theorem laplaceRay_wallPrimeWaveDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1 / 2 < c) {z : ℂ} (hz : 0 < z.re) :
    laplaceRay (wallPrimeWaveDatumLp hF hc hc0) z = wallPrimeBalance F (-(z + c)) := by
  let head : Lp ℂ 2 halfLineLaplaceMeasure := primeHeadProfileLp hF hc
  have hm : 0 < ((c - 1 / 2 : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith only [hc0]
  rw [← halfLineLaplaceTransform_eq_laplaceRay _ hz]
  change inner ℂ (halfLineLaplaceFeature z hz)
    (head - negativeHalfLineLaplace (cx F) (-(1 / 2)) •
      halfLineLaplaceFeature ((c - 1 / 2 : ℝ) : ℂ) hm) = _
  rw [inner_sub_right, inner_smul_right]
  have hb : inner ℂ (halfLineLaplaceFeature z hz) head =
      primeHead F (-(z + c)) :=
    (halfLineLaplaceTransform_eq_laplaceRay head hz).trans (laplaceRay_primeHeadProfile hF hc hc0 hz)
  have hminus : inner ℂ (halfLineLaplaceFeature z hz)
      (halfLineLaplaceFeature ((c - 1 / 2 : ℝ) : ℂ) hm) = 1 / (z + ((c - 1 / 2 : ℝ) : ℂ)) := by
    simpa only [RCLike.star_def, Complex.conj_ofReal] using inner_halfLineLaplaceFeature hz hm
  rw [hb, hminus, wallPrimeBalance,
    show -(z + (c : ℂ)) + 1 / 2 = -(z + ((c - 1 / 2 : ℝ) : ℂ)) by push_cast; ring, div_neg]
  ring

/-- In logarithmic coordinates right of the wall (`x > v`), the exponential polar term
`L F(-½) e^{v/2}` is the continuum prime-number-theorem main term `∫_{x > v} F(v - x) e^{x/2} dx`. -/
theorem polarWallTerm_eq_continuumMainTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (v : ℝ) :
    negativeHalfLineLaplace (cx F) (-(1 / 2)) * (Real.exp (v / 2) : ℂ) =
      ∫ x in Ioi v, (F (v - x) : ℂ) * (Real.exp (x / 2) : ℂ) := by
  have h2 : (∫ u : ℝ, cexp (-(1 / 2 : ℂ) * u) * cx F u) =
      ∫ u in Iio (0 : ℝ), cexp (-(1 / 2 : ℂ) * u) * cx F u :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [cx, hF.support u (not_lt.mp hu), Complex.ofReal_zero, mul_zero]).symm
  unfold negativeHalfLineLaplace
  have hsub_set : (∫ x : ℝ, (Iio (0 : ℝ)).indicator
      (fun u => cexp (-(1 / 2 : ℂ) * u) * cx F u) (v - x)) =
      ∫ u in Iio (0 : ℝ), cexp (-(1 / 2 : ℂ) * u) * cx F u := by
    let g := (Iio (0 : ℝ)).indicator fun u : ℝ => cexp (-(1 / 2 : ℂ) * u) * cx F u
    have htr := integral_add_right_eq_self (μ := volume) (fun y : ℝ => g ((-1 : ℝ) * y)) (-v)
    have hmul := Measure.integral_comp_mul_left g (-1 : ℝ)
    simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at hmul
    rw [← integral_indicator measurableSet_Iio]
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (htr.trans hmul)
    dsimp only [g]
    congr 1; ring
  rw [h2, ← hsub_set, ← integral_mul_const]
  have hind : (fun x : ℝ => (Iio (0 : ℝ)).indicator
        (fun u => cexp (-(1 / 2 : ℂ) * u) * cx F u) (v - x) * (Real.exp (v / 2) : ℂ)) =
      (Ioi v).indicator fun x : ℝ => (F (v - x) : ℂ) * (Real.exp (x / 2) : ℂ) := by
    funext x
    by_cases hx : v < x
    · rw [indicator_of_mem (mem_Iio.mpr (sub_neg.mpr hx)), indicator_of_mem (mem_Ioi.mpr hx)]
      dsimp [cx]
      have hexp : cexp (-(1 / 2 : ℂ) * ((v - x : ℝ) : ℂ)) * (Real.exp (v / 2) : ℂ) =
          (Real.exp (x / 2) : ℂ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1; push_cast; ring
      calc cexp (-(1 / 2 : ℂ) * ((v - x : ℝ) : ℂ)) * (F (v - x) : ℂ) * (Real.exp (v / 2) : ℂ)
          = (F (v - x) : ℂ) * (cexp (-(1 / 2 : ℂ) * ((v - x : ℝ) : ℂ)) *
              (Real.exp (v / 2) : ℂ)) := by ring
        _ = (F (v - x) : ℂ) * (Real.exp (x / 2) : ℂ) := by rw [hexp]
    · rw [indicator_of_notMem (fun hm => hx (sub_neg.mp (mem_Iio.mp hm))),
        indicator_of_notMem (fun hm => hx (mem_Ioi.mp hm)), zero_mul]
  rw [hind, integral_indicator measurableSet_Ioi]

/-! ### The Q8 arithmetic property and its Hardy formulation -/

/-- **Beyond-the-wall prime-pole continuation** for a profile `F`: its prime-head balance
`Φ_F(p) = primeHead F p + L F(-½)/(p + ½)` extends holomorphically from `Re p < -½` across the
left half-strip to `Re p < 0`. -/
def HasBeyondTheWallPrimeContinuation (F : ℝ → ℝ) : Prop :=
  ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
    EqOn H (wallPrimeBalance F) {p : ℂ | p.re < -(1 / 2)}

/-- **The Q8 arithmetic property for `ζ`:** every half-line energy-domain profile admits
holomorphic continuation of its beyond-the-wall prime-pole balance to `Re p < 0`. -/
def ZetaBeyondTheWallPrimeContinuation : Prop :=
  ∀ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F → HasBeyondTheWallPrimeContinuation F

/-- **Pure prime-head continuation** on the pole-neutral subspace `L G(-½) = 0`, where the polar
term vanishes identically and `Φ_G(p) = primeHead G p` depends solely on `Λ(n)`. -/
def PurePrimeHeadContinuation : Prop :=
  ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
    negativeHalfLineLaplace (cx G) (-(1 / 2)) = 0 →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
      EqOn H (primeHead G) {p : ℂ | p.re < -(1 / 2)}

/-- **Sub-strip Hardy wave property:** `Φ_F` is represented on `Re p < -½` by a right-of-wall
profile `φ` whose damped waves `e^{-δv} φ(v)` remain in `L²(0, ∞)` throughout `0 < δ ≤ ½`. -/
def HasSubstripPrimeHardyWave (F : ℝ → ℝ) : Prop :=
  ∃ φ : ℝ → ℂ, (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → MemLp (rayDamp φ δ) 2 volume) ∧
    ∀ p : ℂ, p.re < -(1 / 2) → laplaceRay φ (-p) = wallPrimeBalance F p

/-- Sub-strip `L²(0, ∞)` Hardy damping across `0 < δ ≤ ½` implies holomorphic continuation of
`wallPrimeBalance F` to `Re p < 0`. -/
theorem hasBeyondTheWallPrimeContinuation_of_substripPrimeHardyWave {F : ℝ → ℝ}
    (hw : HasSubstripPrimeHardyWave F) : HasBeyondTheWallPrimeContinuation F := by
  obtain ⟨φ, hLp, heq⟩ := hw
  refine ⟨fun p => laplaceRay φ (-p), fun p₀ hp₀ => ?_, fun p hp => heq p hp⟩
  have hp₀' : p₀.re < 0 := hp₀
  set δ := min (-p₀.re / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hpδ : p₀.re < -δ := by
    have : δ ≤ -p₀.re / 2 := min_le_left _ _
    linarith
  let ψ : ℝ → ℂ := fun x => φ x * expRay (δ : ℂ) x
  have hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).mp (hLp δ hδ0 hδhalf)
  have hholo := (isHalfPlaneHardy_laplaceRay hψ).holo
  have hU : IsOpen {p : ℂ | p.re < -δ} := isOpen_lt Complex.continuous_re continuous_const
  have hcomp : DifferentiableOn ℂ (fun p : ℂ => laplaceRay ψ (-p - δ)) {p : ℂ | p.re < -δ} :=
    hholo.comp (differentiable_id.neg.sub_const (δ : ℂ)).differentiableOn
      fun p (hp : p.re < -δ) => by show 0 < (-p - (δ : ℂ)).re; simp; linarith
  have hcongr : EqOn (fun p : ℂ => laplaceRay ψ (-p - δ)) (fun p : ℂ => laplaceRay φ (-p))
      {p : ℂ | p.re < -δ} := by
    intro p _
    unfold laplaceRay ψ
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [expRay]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; ring
  exact ((hcomp.congr hcongr.symm).differentiableAt (hU.mem_nhds hpδ)).differentiableWithinAt

/-! ### Direct single-state exclusion and exact equivalences -/

/-- **General pole obstruction:** if `F ∈ H` sees a zero `z = centredZero c` with `Re z < δ`
(`δ ≤ 5/2`), then `wallPrimeBalance F` cannot extend holomorphically from `Re p < -½` to
`Re p < δ`. -/
theorem not_wallPrimeBalance_continues_of_seen_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {δ : ℝ} (hδ : δ ≤ 5 / 2)
    {c : XiZeroCopy} (hc : (centredZero c).re < δ)
    (hL : negativeHalfLineLaplace (cx F) (centredZero c) ≠ 0) :
    ¬ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < δ} ∧
      EqOn H (wallPrimeBalance F) {p : ℂ | p.re < -(1 / 2)} := by
  rintro ⟨H, hH, heqH⟩
  have hδ_gt : -(1 / 2 : ℝ) < δ := (abs_lt.mp (abs_re_centredZero_lt c)).1.trans hc
  set U := {p : ℂ | p.re < δ}
  have hU_open : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hU_pre : IsPreconnected U := (convex_halfSpace_re_lt δ).isPreconnected
  let G : ℂ → ℂ := fun p => xi (1 / 2 + p) * (archimedeanWallTail F p + H p)
  have hG_diff : DifferentiableOn ℂ G U :=
    differentiable_xi_half_add.differentiableOn.mul
      (((differentiableOn_archimedeanWallTail hF).mono fun p (hp : p.re < δ) =>
        show p.re < 5 / 2 by linarith).add hH)
  have hG_an : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hCR_an : AnalyticOnNhd ℂ (clearedRemainder F) U :=
    (differentiable_clearedRemainder hF).differentiableOn.analyticOnNhd hU_open
  have hp1_in : (-1 : ℂ) ∈ U := by show (-1 : ℂ).re < δ; simp; linarith
  have hev_eq : clearedRemainder F =ᶠ[𝓝 (-1 : ℂ)] G := by
    have hW_open : IsOpen {p : ℂ | p.re < -(1 / 2)} :=
      isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hW_open.mem_nhds (by simp; norm_num : (-1 : ℂ).re < -(1 / 2))] with p hp
    have hp' : p.re < -(1 / 2) := hp
    have hxi_ne : xi (1 / 2 + p) ≠ 0 :=
      xi_ne_zero_of_half_le_abs_re (by have := neg_le_abs p.re; linarith)
    rw [clearedRemainder_eq hF hxi_ne,
      globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance hF hp', ← heqH hp']
  have hEqOn := hCR_an.eqOn_of_preconnected_of_eventuallyEq hG_an hU_pre hp1_in hev_eq
  set z₀ := centredZero c
  have hz₀_in : z₀ ∈ U := hc
  have hz₀_eq : clearedRemainder F =ᶠ[𝓝 z₀] G :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU_open.mem_nhds hz₀_in, hEqOn⟩
  have hord_drop := analyticOrderAt_clearedRemainder_add_one hF (xi_centredZero c) hL
  have hord_xi : analyticOrderAt (fun p : ℂ => xi (1 / 2 + p)) z₀ =
      analyticOrderAt xi (1 / 2 + z₀) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun p : ℂ => 1 / 2 + p)
      (by fun_prop)
    simp
  have hK_an : AnalyticAt ℂ (fun p : ℂ => archimedeanWallTail F p + H p) z₀ :=
    (((differentiableOn_archimedeanWallTail hF).mono fun p (hp : p.re < δ) =>
      show p.re < 5 / 2 by linarith).add hH).analyticAt (hU_open.mem_nhds hz₀_in)
  have hord_ge : analyticOrderAt xi (1 / 2 + z₀) ≤ analyticOrderAt G z₀ := by
    rw [← hord_xi]
    change analyticOrderAt (fun p : ℂ => xi (1 / 2 + p)) z₀ ≤
      analyticOrderAt ((fun p : ℂ => xi (1 / 2 + p)) *
        fun p : ℂ => archimedeanWallTail F p + H p) z₀
    rw [analyticOrderAt_mul (differentiable_xi_half_add.analyticAt z₀) hK_an]
    exact le_self_add
  rw [← analyticOrderAt_congr hz₀_eq] at hord_ge
  have hfin : analyticOrderAt (clearedRemainder F) z₀ ≠ ⊤ := by
    intro htop
    exact xi_order_ne_top (1 / 2 + z₀) (by rw [← hord_drop, htop, top_add])
  exact not_lt_of_ge hord_ge ((ENat.add_one_le_iff hfin).mp hord_drop.le)

/-- **Direct single-state exclusion:** for any critical half-line ground state `F`, its own
beyond-the-wall prime-pole balance `wallPrimeBalance F` fails to extend holomorphically across
`-½ ≤ Re p < 0`. -/
theorem criticalState_not_hasBeyondTheWallPrimeContinuation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ¬ HasBeyondTheWallPrimeContinuation F := by
  obtain ⟨c, hc, hL, _⟩ := criticalState_exists_seen_left_centredZero hW ht hF
  exact not_wallPrimeBalance_continues_of_seen_zero
    (criticalHalfLineEnergyDomain_of_groundState hF) (by norm_num) hc hL

/-- For any critical half-line ground state `F`, the damped right-of-wall prime-remainder wave
cannot stay in `L²(0, ∞)` across `0 < δ ≤ ½`. -/
theorem criticalState_not_hasSubstripPrimeHardyWave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ¬ HasSubstripPrimeHardyWave F := fun hw =>
  criticalState_not_hasBeyondTheWallPrimeContinuation hW ht hF
    (hasBeyondTheWallPrimeContinuation_of_substripPrimeHardyWave hw)

/-- **Property ⇒ no state:** `ZetaBeyondTheWallPrimeContinuation` unconditionally excludes the
existence of a critical half-line ground state. -/
theorem no_criticalState_of_beyondTheWallPrimeContinuation
    (hprop : ZetaBeyondTheWallPrimeContinuation) :
    ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F := by
  rintro ⟨W₀, F, hW, ht, hF⟩
  exact criticalState_not_hasBeyondTheWallPrimeContinuation hW ht hF
    (hprop F (criticalHalfLineEnergyDomain_of_groundState hF))

/-- `ZetaBeyondTheWallPrimeContinuation` implies `RiemannHypothesis` via the ground-state
dichotomy. -/
theorem riemannHypothesis_of_beyondTheWallPrimeContinuation
    (hprop : ZetaBeyondTheWallPrimeContinuation) : RiemannHypothesis := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | hex
  · exact hRH
  · exact False.elim (no_criticalState_of_beyondTheWallPrimeContinuation hprop hex)

/-- Under `RiemannHypothesis`, `wallPrimeBalance F` extends holomorphically to `Re p < 0` for
every `F ∈ H` via `globalRemainder F p - archimedeanWallTail F p`. -/
theorem beyondTheWallPrimeContinuation_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ZetaBeyondTheWallPrimeContinuation := by
  intro F hF
  refine ⟨fun p => globalRemainder F p - archimedeanWallTail F p, fun p hp => ?_, fun p hp => ?_⟩
  · have hp' : p.re < 0 := hp
    have hxi_ne : xi (1 / 2 + p) ≠ 0 := by
      intro h0
      obtain ⟨c, hc⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
      have hre_half : (c.1 : ℂ).re = 1 / 2 := by
        have hζ : riemannZeta (c.1 : ℂ) = 0 :=
          (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (xiZeroCopy_re_pos c)
            (xiZeroCopy_ne_one c)).mp (xi_xiZeroCopy_eq_zero c)
        refine hRH _ hζ ?_ (xiZeroCopy_ne_one c)
        rintro ⟨n, hn⟩
        have hpos := xiZeroCopy_re_pos c
        rw [hn] at hpos
        simp at hpos
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have : (1 / 2 + p).re = 1 / 2 + p.re := re_one_half_add p
      rw [← hc, hre_half] at this
      linarith
    have hdiff_rem : DifferentiableAt ℂ (globalRemainder F) p := by
      refine differentiableAt_globalRemainder hF fun hp0 hz => hxi_ne ?_
      rw [xi_eq_half_mul_Gammaℝ_mul_zetaEntire (by rw [re_one_half_add]; linarith), hz]
      ring
    exact (hdiff_rem.sub
      ((differentiableOn_archimedeanWallTail hF).differentiableAt
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
          (by linarith : p.re < 5 / 2)))).differentiableWithinAt
  · dsimp only
    rw [globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance hF hp]
    ring

/-- **Exact equivalence with `RiemannHypothesis`.** -/
theorem zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis :
    ZetaBeyondTheWallPrimeContinuation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_beyondTheWallPrimeContinuation,
    beyondTheWallPrimeContinuation_of_riemannHypothesis⟩

/-- **Exact equivalence with exclusion of the critical state.** -/
theorem zetaBeyondTheWallPrimeContinuation_iff_no_criticalState :
    ZetaBeyondTheWallPrimeContinuation ↔
      ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F := by
  constructor
  · exact no_criticalState_of_beyondTheWallPrimeContinuation
  · intro hno
    rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | hex
    · exact beyondTheWallPrimeContinuation_of_riemannHypothesis hRH
    · exact False.elim (hno hex)

/-! ### Pole-neutral pure prime-head exclusion and boundary sharpness -/

private theorem laplace_causalTranslate_one {F : ℝ → ℝ} (_hF : CriticalHalfLineEnergyDomain F)
    {w : ℂ} (_hw : -4 < w.re) :
    negativeHalfLineLaplace (cx fun u => F (u + 1)) w =
      cexp (-w) * negativeHalfLineLaplace (cx F) w := by
  unfold negativeHalfLineLaplace cx
  have htr := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => cexp (w * ((u : ℂ) - 1)) * (F u : ℂ)) 1
  rw [← integral_const_mul]
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans
    (htr.trans (integral_congr_ae (Eventually.of_forall fun u => ?_)))
  · dsimp only
    congr 2; push_cast; ring
  · dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring

/-- **Pure prime-head exclusion:** holomorphic continuation of `primeHead G` alone on the
pole-neutral subspace `L G(-½) = 0` suffices to exclude the critical state directly (via the
charge-cancelled causal difference `G(u) = F(u + 1) - e^{1/2} F(u)`). -/
theorem no_criticalState_of_purePrimeHeadContinuation (hpure : PurePrimeHeadContinuation) :
    ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F := by
  rintro ⟨W₀, F, hW, ht, hF⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨c, hc, hLF, _⟩ := criticalState_exists_seen_left_centredZero hW ht hF
  have hc_lo := (abs_lt.mp (abs_re_centredZero_lt c)).1
  let G : ℝ → ℝ := fun u => F (u + 1) + (-Real.exp (1 / 2)) * F u
  have hdT : CriticalHalfLineEnergyDomain (fun u => F (u + 1)) := hd.causalTranslate zero_le_one
  have hdG : CriticalHalfLineEnergyDomain G := hdT.add_const_mul hd (-Real.exp (1 / 2))
  have hLap_lin : ∀ w : ℂ, -4 < w.re →
      negativeHalfLineLaplace (cx G) w =
        (cexp (-w) - (Real.exp (1 / 2) : ℂ)) * negativeHalfLineLaplace (cx F) w := by
    intro w hw
    have hiT : Integrable fun u : ℝ => cexp (w * u) * cx (fun v => F (v + 1)) u := by
      refine (integrable_abs_mul_exp_of_sq (c := w.re) hdT.meas hdT.support hdT.exponential
        (by linarith)).mono'
        (((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).measurable.mul
          (Complex.measurable_ofReal.comp hdT.meas)).aestronglyMeasurable)
        (Eventually.of_forall fun u => ?_)
      rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hiF : Integrable fun u : ℝ => cexp (w * u) * cx F u := by
      refine (integrable_abs_mul_exp_of_sq (c := w.re) hd.meas hd.support hd.exponential
        (by linarith)).mono'
        (((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).measurable.mul
          (Complex.measurable_ofReal.comp hd.meas)).aestronglyMeasurable)
        (Eventually.of_forall fun u => ?_)
      rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hsplit : (fun u : ℝ => cexp (w * u) * cx G u) = fun u : ℝ =>
        cexp (w * u) * cx (fun v => F (v + 1)) u +
          ((-Real.exp (1 / 2) : ℝ) : ℂ) * (cexp (w * u) * cx F u) := by
      funext u; dsimp [G, cx]; push_cast; ring
    unfold negativeHalfLineLaplace
    rw [integral_congr_ae (Eventually.of_forall (congrFun hsplit)),
      integral_add hiT (hiF.const_mul _), integral_const_mul]
    change negativeHalfLineLaplace (cx fun v => F (v + 1)) w +
        ((-Real.exp (1 / 2) : ℝ) : ℂ) * negativeHalfLineLaplace (cx F) w =
      (cexp (-w) - (Real.exp (1 / 2) : ℂ)) * negativeHalfLineLaplace (cx F) w
    rw [laplace_causalTranslate_one hd hw]
    push_cast; ring
  have hLG_half : negativeHalfLineLaplace (cx G) (-(1 / 2)) = 0 := by
    rw [hLap_lin (-(1 / 2)) (by rw [Complex.neg_re, re_one_half]; norm_num)]
    have he : cexp (- -(1 / 2 : ℂ)) = (Real.exp (1 / 2) : ℂ) := by
      rw [neg_neg, Complex.ofReal_exp]; push_cast; rfl
    rw [he, sub_self, zero_mul]
  have hLG_z : negativeHalfLineLaplace (cx G) (centredZero c) ≠ 0 := by
    rw [hLap_lin (centredZero c) (by linarith)]
    refine mul_ne_zero (sub_ne_zero.mpr fun heq => ?_) hLF
    have hn := congrArg norm heq
    rw [Complex.norm_exp, Complex.neg_re, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le] at hn
    exact (ne_of_lt (Real.exp_lt_exp.mpr (by linarith))) hn
  obtain ⟨H, hH, heqH⟩ := hpure G hdG hLG_half
  refine not_wallPrimeBalance_continues_of_seen_zero hdG (by norm_num) hc hLG_z ⟨H, hH, ?_⟩
  intro p hp
  rw [heqH hp, wallPrimeBalance, hLG_half, zero_div, add_zero]

/-- `PurePrimeHeadContinuation` is unconditionally equivalent to `ZetaBeyondTheWallPrimeContinuation`. -/
theorem purePrimeHeadContinuation_iff_zetaBeyondTheWallPrimeContinuation :
    PurePrimeHeadContinuation ↔ ZetaBeyondTheWallPrimeContinuation := by
  constructor
  · intro hpure
    exact zetaBeyondTheWallPrimeContinuation_iff_no_criticalState.mpr
      (no_criticalState_of_purePrimeHeadContinuation hpure)
  · intro hzeta G hG hLG0
    obtain ⟨H, hH, heq⟩ := hzeta G hG
    refine ⟨H, hH, fun p hp => ?_⟩
    rw [heq hp, wallPrimeBalance, hLG0, zero_div, add_zero]

/-- **Unconditional sharpness at `Re p = 0`:** for every `δ > 0`, `wallPrimeBalance F` fails to
continue holomorphically to `{p | Re p < δ}` already on `F = probe 5 ∈ H` (no assumption on RH). -/
theorem not_forall_wallPrimeBalance_continues_past_zero {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∀ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < δ} ∧
        EqOn H (wallPrimeBalance F) {p : ℂ | p.re < -(1 / 2)} := by
  intro hall
  set δ' := min δ 2
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'5 : δ' ≤ 5 / 2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨c₀⟩ : Nonempty XiZeroCopy := inferInstance
  have hex_c : ∃ c : XiZeroCopy, (centredZero c).re < δ' := by
    rcases le_or_gt (centredZero c₀).re 0 with hle | hgt
    · exact ⟨c₀, hle.trans_lt hδ'0⟩
    · have hxi_neg : xi (1 / 2 + -centredZero c₀) = 0 := by
        rw [show (1 : ℂ) / 2 + -centredZero c₀ = 1 - (1 / 2 + centredZero c₀) by ring,
          xi_one_sub]
        exact xi_centredZero c₀
      obtain ⟨c', hc'⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_neg
      refine ⟨c', ?_⟩
      have : centredZero c' = -centredZero c₀ := by rw [centredZero, hc']; ring
      rw [this]; simp; linarith
  obtain ⟨c, hc⟩ := hex_c
  have hd5 : CriticalHalfLineEnergyDomain (probe 5) :=
    criticalHalfLineEnergyDomain_probe (by norm_num)
  have hL5 : negativeHalfLineLaplace (cx (probe 5)) (centredZero c) ≠ 0 := by
    have hz_abs := abs_lt.mp (abs_re_centredZero_lt c)
    have hlap : negativeHalfLineLaplace (cx (probe 5)) (centredZero c) =
        1 / ((5 : ℂ) + centredZero c) := by
      unfold negativeHalfLineLaplace cx
      have h1 : (∫ u : ℝ, cexp (centredZero c * u) * (probe 5 u : ℂ)) =
          ∫ u in Iio (0 : ℝ), cexp (((5 : ℂ) + centredZero c) * u) := by
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
        integral_exp_mul_complex_Iic (by simp; linarith [hz_abs.1]) 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [hlap]
    exact one_div_ne_zero fun e => by
      have := congrArg Complex.re e; simp at this
      linarith [(abs_lt.mp (abs_re_centredZero_lt c)).1]
  obtain ⟨H, hH, heq⟩ := hall (probe 5) hd5
  exact not_wallPrimeBalance_continues_of_seen_zero hd5 hδ'5 hc hL5
    ⟨H, hH.mono fun p (hp : p.re < δ') => lt_of_lt_of_le hp (min_le_left _ _), heq⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
