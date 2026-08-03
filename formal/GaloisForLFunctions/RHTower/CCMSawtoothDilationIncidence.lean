import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import GaloisForLFunctions.RHTower.CCMSawtoothDilationMean

/-!
# The exact cofinal all-prime incidence of the dilated sawtooth

The averaging estimate of `CCMSawtoothDilationMean` is summed against the von Mangoldt weight.

* `endpointProfile`, `endpointProfile_mul_shift` — the normalized endpoint profile and the shift
  identity turning its correlation into the integer-dilated sawtooth product.
* `sum_one_div_Icc_le_log`, `sum_vonMangoldt_div_le_log_sq` — the visible arithmetic weight is at most
  `log² N`, with no error term: the harmonic bound follows from `log(N/(N+1)) ≤ -1/(N+1)`.
* `lseriesSummable_vonMangoldt_two`, `lseries_vonMangoldt_two`, `summable_vonMangoldt_div_sq`,
  `tendsto_sum_vonMangoldt_div_sq` — the Euler logarithmic-derivative moment `-ζ'(2)/ζ(2)`, its
  absolute convergence, and the convergence of its partial sums.
* `image_Ioo_exp_scale`, `integral_comp_exp_scale` — the change of variables `x = L e^s`, proved with
  the measurable substitution rule because the sawtooth factor is discontinuous.
* `additiveWeight`, `multiplicativeWeight`, `hasDerivAt_multiplicativeWeight` — the two coordinate
  readings of a weight.  A compactly supported additive weight induces a globally `C¹` multiplicative
  one, because it then vanishes on a whole neighbourhood of the origin.
* `abs_integral_weight_mul_dilate_le` — the averaging estimate in the card's additive coordinates:
  the error is at most `(1/(3L)) ∫ e^{-s}(|V'| + |V|)`.
* `abs_primeResponse_sub_main_le`, `abs_primeResponse_additive_sub_main_le` — the growing-cutoff
  synthesis: the exact Euler main term with error `log² N/(3L)` times the fixed additive integral.
* `tendsto_primeResponse_additive` — the limit: along any schedule with `log² N = o(L)` the finite
  prime response converges to the universal Euler scalar times the additive mean.
* `invSqWeight`, `abs_integral_invSqWeight_mul_sawDilate_sub_mean_le`,
  `abs_integral_expWeight_sawDilate_sub_mean_le` — the unweighted exterior half-line: on every window
  the exponentially weighted product has the exact mean `1/(12 n)` up to `4/(3L)`, uniformly in the
  dilation and in the outer endpoint.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set ArithmeticFunction Filter Topology

/-! ## The endpoint profile and the shift identity -/

/-- **Equation (10).**  The normalized leading endpoint profile. -/
def endpointProfile (L s : ℝ) : ℝ := Real.exp (-s / 2) * sawWave (L * Real.exp s)

/-- **Equation (15).**  A logarithmic shift by `log n` turns the profile correlation into the
integer-dilated sawtooth product, with the exact Euler weight `n^{-1/2}` and the exponential
density `e^{-s}`. -/
theorem endpointProfile_mul_shift {n : ℕ} (hn : 0 < n) (L s : ℝ) :
    endpointProfile L s * endpointProfile L (s + Real.log n)
      = (Real.sqrt n)⁻¹ * (Real.exp (-s) *
          (sawWave (L * Real.exp s) * sawWave ((n : ℝ) * (L * Real.exp s)))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp (s + Real.log n) = Real.exp s * (n : ℝ) := by
    rw [Real.exp_add, Real.exp_log hnpos]
  have hsq : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hinv : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (-(Real.log n / 2)) := by
    rw [hsq, Real.exp_neg]
  have harg : L * Real.exp (s + Real.log n) = (n : ℝ) * (L * Real.exp s) := by
    rw [hexp]; ring
  have hcoef : Real.exp (-s / 2) * Real.exp (-(s + Real.log n) / 2)
      = Real.exp (-(Real.log n / 2)) * Real.exp (-s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [endpointProfile, endpointProfile, harg, hinv,
    show Real.exp (-s / 2) * sawWave (L * Real.exp s) *
        (Real.exp (-(s + Real.log n) / 2) * sawWave ((n : ℝ) * (L * Real.exp s)))
      = (Real.exp (-s / 2) * Real.exp (-(s + Real.log n) / 2)) *
        (sawWave (L * Real.exp s) * sawWave ((n : ℝ) * (L * Real.exp s))) from by ring,
    hcoef]
  ring

/-! ## The arithmetic weight -/

/-- A harmonic bound with no error term: `∑_{2 ≤ n ≤ N} 1/n ≤ log N`, from
`log(N/(N+1)) ≤ -1/(N+1)`. -/
theorem sum_one_div_Icc_le_log : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ≤ Real.log N
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num
  | (N + 2), _ => by
    have hind := sum_one_div_Icc_le_log (N + 1) (by omega)
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) := by positivity
    have hpos2 : (0 : ℝ) < ((N : ℝ) + 2) := by positivity
    have hkey : (1 : ℝ) / ((N : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) := by
      have hratio : ((N : ℝ) + 1) / ((N : ℝ) + 2) > 0 := by positivity
      have h1 := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hpos2)] at h1
      have h2 : ((N : ℝ) + 1) / ((N : ℝ) + 2) - 1 = -(1 / ((N : ℝ) + 2)) := by
        field_simp
        ring
      rw [h2] at h1
      linarith
    have htop := Finset.sum_Icc_succ_top (a := 2) (b := N + 1)
      (by omega : 2 ≤ N + 1 + 1) (fun n => (1 : ℝ) / n)
    rw [htop]
    have hcast1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((N + 1 + 1 : ℕ) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [hcast2]
    rw [hcast1] at hind
    linarith

/-- **Equation (16).**  The visible von Mangoldt weight, divided by the radial index, is bounded by
the square of the logarithm of the cutoff. -/
theorem sum_vonMangoldt_div_le_log_sq {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ≤ Real.log N ^ 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hterm : ∀ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ≤ Real.log N * ((1 : ℝ) / n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
    have h2 : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn.2)
    rw [mul_one_div]
    gcongr
    linarith
  calc ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ)
      ≤ ∑ n ∈ Finset.Icc 2 N, Real.log N * ((1 : ℝ) / n) := Finset.sum_le_sum hterm
    _ = Real.log N * ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n := by rw [Finset.mul_sum]
    _ ≤ Real.log N * Real.log N :=
        mul_le_mul_of_nonneg_left (sum_one_div_Icc_le_log N hN) hlogN
    _ = Real.log N ^ 2 := by ring

/-- **Equation (17).**  The Euler logarithmic-derivative moment.  The full weight `Λ(n) n^{-2}` is
absolutely summable and sums to `-ζ'(2)/ζ(2)`. -/
theorem lseriesSummable_vonMangoldt_two :
    LSeriesSummable (fun n => (Λ n : ℂ)) 2 :=
  LSeriesSummable_vonMangoldt (by norm_num)

theorem lseries_vonMangoldt_two :
    LSeries (fun n => (Λ n : ℂ)) 2 = -deriv riemannZeta 2 / riemannZeta 2 :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by norm_num)

/-- **Equation (2).**  The mean of `S(x) S(nx)` over a period is `π²/(12 n)`. -/
theorem integral_sawWave_dilate {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), sawWave x * sawWave ((n : ℝ) * x))
      = 2 * Real.pi * (Real.pi ^ 2 / (12 * (n : ℝ))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpine : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  have hG : ∀ x : ℝ, sawWave x * sawWave ((n : ℝ) * x)
      = Real.pi ^ 2 * ((fun u : ℝ => sawUnit u * sawUnit ((n : ℝ) * u)) (x / (2 * Real.pi))) := by
    intro x
    rw [sawWave, sawWave]
    have hd : (n : ℝ) * x / (2 * Real.pi) = (n : ℝ) * (x / (2 * Real.pi)) := by ring
    rw [hd]
    ring
  simp_rw [hG]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u : ℝ => sawUnit u * sawUnit ((n : ℝ) * u)) hpine,
    zero_div, div_self hpine, smul_eq_mul, integral_sawUnit_dilate hn]
  ring

/-! ## The additive/multiplicative change of variables -/

theorem image_Ioo_exp_scale {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    (fun s => L * Real.exp s) '' Ioo a b = Ioo (L * Real.exp a) (L * Real.exp b) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by nlinarith [Real.exp_lt_exp.mpr hs.1, Real.exp_pos a, Real.exp_pos s],
      by nlinarith [Real.exp_lt_exp.mpr hs.2, Real.exp_pos b, Real.exp_pos s]⟩
  · intro hy
    have hea : (0 : ℝ) < Real.exp a := Real.exp_pos a
    have hypos : (0 : ℝ) < y := lt_trans (by positivity) hy.1
    have hdiv : (0 : ℝ) < y / L := by positivity
    refine ⟨Real.log (y / L), ⟨?_, ?_⟩, ?_⟩
    · have h1 : Real.exp a < y / L := by
        rw [lt_div_iff₀ hL, mul_comm]
        exact hy.1
      have := Real.log_lt_log hea h1
      rwa [Real.log_exp] at this
    · have h1 : y / L < Real.exp b := by
        rw [div_lt_iff₀ hL, mul_comm]
        exact hy.2
      have := Real.log_lt_log hdiv h1
      rwa [Real.log_exp] at this
    · show L * Real.exp (Real.log (y / L)) = y
      rw [Real.exp_log hdiv]
      field_simp

/-- **The change of variables `x = L e^s`.**  Only measurability of the integrand is used, so the
discontinuous sawtooth factor is admissible; the continuous substitution rule would not apply. -/
theorem integral_comp_exp_scale {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ) :
    (∫ x in (L * Real.exp a)..(L * Real.exp b), F x)
      = ∫ s in a..b, (L * Real.exp s) * F (L * Real.exp s) := by
  have hmono : L * Real.exp a ≤ L * Real.exp b := by
    have := Real.exp_le_exp.mpr hab
    nlinarith [Real.exp_pos a, Real.exp_pos b]
  have hderiv : ∀ s ∈ Ioo a b,
      HasDerivWithinAt (fun s => L * Real.exp s) (L * Real.exp s) (Ioo a b) s := by
    intro s _
    exact (((Real.hasDerivAt_exp s).const_mul L).hasDerivWithinAt)
  have hinj : InjOn (fun s => L * Real.exp s) (Ioo a b) := by
    intro u _ v _ huv
    have hmul : L * Real.exp u = L * Real.exp v := huv
    exact Real.exp_eq_exp.mp (mul_left_cancel₀ (ne_of_gt hL) hmul)
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun s => L * Real.exp s) (f' := fun s => L * Real.exp s) (s := Ioo a b)
    measurableSet_Ioo hderiv hinj F
  rw [image_Ioo_exp_scale hL a b] at hcov
  rw [intervalIntegral.integral_of_le hmono, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo, hcov]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
  rw [smul_eq_mul, abs_of_pos (by positivity)]

/-! ## The card's additive coordinates -/

/-- The additive weight attached to a multiplicative one, `V(s) = L e^s G(L e^s)`.  The card's `V` and
the multiplicative weight `G` determine each other; the averaging estimate is naturally a statement
about `G`, and `(6)` is its additive reading. -/
def additiveWeight (L : ℝ) (G : ℝ → ℝ) : ℝ → ℝ := fun s => (L * Real.exp s) * G (L * Real.exp s)

theorem hasDerivAt_additiveWeight {L : ℝ} {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (s : ℝ) : HasDerivAt (additiveWeight L G)
      (additiveWeight L G s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s)) s := by
  have hu : HasDerivAt (fun s : ℝ => L * Real.exp s) (L * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul L
  have hcomp : HasDerivAt (fun s : ℝ => G (L * Real.exp s))
      (G' (L * Real.exp s) * (L * Real.exp s)) s := (hG (L * Real.exp s)).comp s hu
  have hmul := hu.mul hcomp
  have heq : (L * Real.exp s) * G (L * Real.exp s)
      + (L * Real.exp s) * (G' (L * Real.exp s) * (L * Real.exp s))
      = additiveWeight L G s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s) := by
    rw [additiveWeight]
    ring
  rw [← heq]
  exact hmul

/-- The averaging integral in additive coordinates equals the multiplicative one. -/
theorem integral_additiveWeight_mul_comp {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b)
    (G h : ℝ → ℝ) :
    (∫ s in a..b, additiveWeight L G s * h (L * Real.exp s))
      = ∫ x in (L * Real.exp a)..(L * Real.exp b), G x * h x := by
  rw [integral_comp_exp_scale hL hab (fun x => G x * h x)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [additiveWeight]
  ring

/-- The total variation of the multiplicative weight, read additively.  This is exactly the shape of
the card's error bound `(6)`: `(1/L) ∫ e^{-s} |V'(s) - V(s)| ds`. -/
theorem integral_abs_deriv_comp_exp_scale {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b)
    (G' : ℝ → ℝ) :
    (∫ x in (L * Real.exp a)..(L * Real.exp b), |G' x|)
      = (1 / L) * ∫ s in a..b, Real.exp (-s) * ((L * Real.exp s) ^ 2 * |G' (L * Real.exp s)|) := by
  rw [integral_comp_exp_scale hL hab (fun x => |G' x|), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hexp : Real.exp s ≠ 0 := Real.exp_ne_zero s
  rw [Real.exp_neg]
  field_simp

/-- **Equations (5)--(6).**  In the card's additive coordinates, the averaging error against a weight
`V(s) = L e^s G(L e^s)` is at most `(1/(3L)) ∫ e^{-s} (|V'(s)| + |V(s)|) ds`, uniformly in the
dilation.  The constant `1/3` is the unit-normalization value of the card's `C₀`. -/
theorem abs_integral_additiveWeight_mul_sawDilateCentered_le {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {V V' G G' : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG'c : Continuous G') {CG : ℝ} (hG'b : ∀ x, |G' x| ≤ CG)
    (hV : V = additiveWeight L G) (hV' : ∀ s, HasDerivAt V (V' s) s)
    (hGa : G (L * Real.exp a) = 0) (hGb : G (L * Real.exp b) = 0) :
    |∫ s in a..b, V s *
        (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s)) - 1 / (12 * (n : ℝ)))|
      ≤ (1 / (3 * L)) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by
  have hmono : L * Real.exp a ≤ L * Real.exp b := by
    have := Real.exp_le_exp.mpr hab
    nlinarith [Real.exp_pos a, Real.exp_pos b]
  -- the derivative of the additive weight is forced
  have hVderiv : ∀ s : ℝ, V' s
      = additiveWeight L G s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s) := by
    intro s
    refine HasDerivAt.unique (hV' s) ?_
    rw [hV]
    exact hasDerivAt_additiveWeight hG s
  -- transfer the left side to multiplicative coordinates
  have hleft : (∫ s in a..b, V s *
      (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s)) - 1 / (12 * (n : ℝ))))
      = ∫ x in (L * Real.exp a)..(L * Real.exp b),
          G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))) := by
    rw [hV]
    exact integral_additiveWeight_mul_comp hL hab G
      (fun x => sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))
  rw [hleft]
  -- the multiplicative estimate
  have hest := abs_integral_weight_mul_sawDilateCentered_le hn hmono hG hG'c hG'b hGa hGb
  refine hest.trans ?_
  rw [integral_abs_deriv_comp_exp_scale hL hab G']
  -- compare the two additive integrands
  have hVc : Continuous V := by
    rw [hV]
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_additiveWeight hG s).continuousAt
  have hV'c : Continuous V' := by
    have hVc' : ∀ s : ℝ, V' s = V s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s) := by
      intro s
      rw [hVderiv s, hV]
    have : Continuous fun s : ℝ => V s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s) := by
      refine hVc.add ?_
      exact (((continuous_const.mul Real.continuous_exp).pow 2)).mul
        (hG'c.comp (continuous_const.mul Real.continuous_exp))
    exact this.congr fun s => (hVc' s).symm
  have hint1 : IntervalIntegrable
      (fun s => Real.exp (-s) * ((L * Real.exp s) ^ 2 * |G' (L * Real.exp s)|)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine (Real.continuous_exp.comp continuous_neg).mul ?_
    exact ((continuous_const.mul Real.continuous_exp).pow 2).mul
      ((continuous_abs.comp hG'c).comp (continuous_const.mul Real.continuous_exp))
  have hint2 : IntervalIntegrable
      (fun s => Real.exp (-s) * (|V' s| + |V s|)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (Real.continuous_exp.comp continuous_neg).mul
      ((continuous_abs.comp hV'c).add (continuous_abs.comp hVc))
  have hptw : ∀ s ∈ Icc a b,
      Real.exp (-s) * ((L * Real.exp s) ^ 2 * |G' (L * Real.exp s)|)
        ≤ Real.exp (-s) * (|V' s| + |V s|) := by
    intro s _
    have hkey : (L * Real.exp s) ^ 2 * |G' (L * Real.exp s)| = |V' s - V s| := by
      rw [hVderiv s, hV]
      have hc : additiveWeight L G s + (L * Real.exp s) ^ 2 * G' (L * Real.exp s)
          - additiveWeight L G s = (L * Real.exp s) ^ 2 * G' (L * Real.exp s) := by ring
      rw [hc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (L * Real.exp s) ^ 2)]
    rw [hkey]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.exp_pos _).le
  have hmul : (1 / 3) * ((1 / L) * ∫ s in a..b,
      Real.exp (-s) * ((L * Real.exp s) ^ 2 * |G' (L * Real.exp s)|))
      ≤ (1 / 3) * ((1 / L) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|)) := by
    have hmono2 := intervalIntegral.integral_mono_on hab hint1 hint2 hptw
    have hLinv : (0 : ℝ) ≤ 1 / L := by positivity
    nlinarith [hmono2]
  calc (1 / 3) * ((1 / L) * ∫ s in a..b,
        Real.exp (-s) * ((L * Real.exp s) ^ 2 * |G' (L * Real.exp s)|))
      ≤ (1 / 3) * ((1 / L) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|)) := hmul
    _ = (1 / (3 * L)) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by ring

/-! ## The multiplicative weight of a compactly supported additive weight -/

/-- The multiplicative weight `G(x) = V(log(x/L))/x` attached to an additive one. -/
def multiplicativeWeight (L : ℝ) (V : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if 0 < x then V (Real.log (x / L)) / x else 0

/-- Its derivative, `(V'(log(x/L)) - V(log(x/L)))/x²`. -/
def multiplicativeWeightDeriv (L : ℝ) (V V' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if 0 < x then (V' (Real.log (x / L)) - V (Real.log (x / L))) / x ^ 2 else 0

theorem additiveWeight_multiplicativeWeight {L : ℝ} (hL : 0 < L) (V : ℝ → ℝ) :
    additiveWeight L (multiplicativeWeight L V) = V := by
  funext s
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hlog : Real.log (L * Real.exp s / L) = s := by
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hL), mul_one, Real.log_exp]
  rw [additiveWeight, multiplicativeWeight, if_pos hpos, hlog]
  field_simp

/-- Left of the window the multiplicative weight vanishes identically, which is what makes it
differentiable at the origin. -/
theorem multiplicativeWeight_eq_zero_of_lt {L a : ℝ} (hL : 0 < L) {V : ℝ → ℝ}
    (hVa : ∀ s, s ≤ a → V s = 0) {x : ℝ} (hx : x < L * Real.exp a) :
    multiplicativeWeight L V x = 0 := by
  rw [multiplicativeWeight]
  by_cases hxp : 0 < x
  · rw [if_pos hxp]
    have hdiv : x / L < Real.exp a := by
      rw [div_lt_iff₀ hL, mul_comm]
      exact hx
    have hlog : Real.log (x / L) ≤ a := by
      have h1 : Real.log (x / L) < a := by
        have := Real.log_lt_log (by positivity) hdiv
        rwa [Real.log_exp] at this
      exact h1.le
    rw [hVa _ hlog, zero_div]
  · rw [if_neg hxp]

theorem multiplicativeWeightDeriv_eq_zero_of_lt {L a : ℝ} (hL : 0 < L) {V V' : ℝ → ℝ}
    (hVa : ∀ s, s ≤ a → V s = 0) (hV'a : ∀ s, s ≤ a → V' s = 0) {x : ℝ}
    (hx : x < L * Real.exp a) : multiplicativeWeightDeriv L V V' x = 0 := by
  rw [multiplicativeWeightDeriv]
  by_cases hxp : 0 < x
  · rw [if_pos hxp]
    have hdiv : x / L < Real.exp a := by
      rw [div_lt_iff₀ hL, mul_comm]
      exact hx
    have hlog : Real.log (x / L) ≤ a := by
      have h1 : Real.log (x / L) < a := by
        have := Real.log_lt_log (by positivity) hdiv
        rwa [Real.log_exp] at this
      exact h1.le
    rw [hVa _ hlog, hV'a _ hlog, sub_zero, zero_div]
  · rw [if_neg hxp]

/-- The chain rule for the multiplicative weight.  At the origin the weight vanishes on a whole
neighbourhood, which is why a compactly supported additive weight produces a globally `C¹`
multiplicative one. -/
theorem hasDerivAt_multiplicativeWeight {L a : ℝ} (hL : 0 < L) {V V' : ℝ → ℝ}
    (hV : ∀ s, HasDerivAt V (V' s) s) (hVa : ∀ s, s ≤ a → V s = 0)
    (hV'a : ∀ s, s ≤ a → V' s = 0) (x : ℝ) :
    HasDerivAt (multiplicativeWeight L V) (multiplicativeWeightDeriv L V V' x) x := by
  by_cases hx : 0 < x
  · have hxL : (0 : ℝ) < x / L := by positivity
    have hlogd : HasDerivAt (fun y : ℝ => Real.log (y / L)) x⁻¹ x := by
      have h1 : HasDerivAt (fun y : ℝ => y / L) (1 / L) x := by
        simpa using (hasDerivAt_id x).div_const L
      have h2 : HasDerivAt Real.log (x / L)⁻¹ (x / L) := Real.hasDerivAt_log (ne_of_gt hxL)
      have h3 := h2.comp x h1
      have hval : (x / L)⁻¹ * (1 / L) = x⁻¹ := by
        field_simp
      rw [← hval]
      exact h3
    have hVc : HasDerivAt (fun y : ℝ => V (Real.log (y / L)))
        (V' (Real.log (x / L)) * x⁻¹) x := (hV _).comp x hlogd
    have hdiv : HasDerivAt (fun y : ℝ => V (Real.log (y / L)) / y)
        ((V' (Real.log (x / L)) * x⁻¹ * x - V (Real.log (x / L)) * 1) / x ^ 2) x :=
      hVc.div (hasDerivAt_id x) (ne_of_gt hx)
    have heq : multiplicativeWeight L V =ᶠ[nhds x] fun y : ℝ => V (Real.log (y / L)) / y := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [multiplicativeWeight, if_pos hy]
    have hres := hdiv.congr_of_eventuallyEq heq
    rw [multiplicativeWeightDeriv, if_pos hx]
    have hval : (V' (Real.log (x / L)) * x⁻¹ * x - V (Real.log (x / L)) * 1) / x ^ 2
        = (V' (Real.log (x / L)) - V (Real.log (x / L))) / x ^ 2 := by
      rw [inv_mul_cancel_right₀ (ne_of_gt hx), mul_one]
    rw [← hval]
    exact hres
  · have hlt : x < L * Real.exp a := by
      have hp : (0 : ℝ) < L * Real.exp a := by positivity
      linarith [not_lt.mp hx]
    have heq : multiplicativeWeight L V =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hlt] with y hy
      exact multiplicativeWeight_eq_zero_of_lt hL hVa hy
    have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    rw [multiplicativeWeightDeriv_eq_zero_of_lt hL hVa hV'a hlt]
    exact hz

/-- The multiplicative derivative is bounded, with the window's left endpoint supplying the
denominator. -/
theorem abs_multiplicativeWeightDeriv_le {L a : ℝ} (hL : 0 < L) {V V' : ℝ → ℝ}
    (hVa : ∀ s, s ≤ a → V s = 0) (hV'a : ∀ s, s ≤ a → V' s = 0) {CV : ℝ}
    (hVb : ∀ s, |V s| ≤ CV) (hV'b : ∀ s, |V' s| ≤ CV) (x : ℝ) :
    |multiplicativeWeightDeriv L V V' x| ≤ (2 * CV) / (L * Real.exp a) ^ 2 := by
  have hpa : (0 : ℝ) < L * Real.exp a := by positivity
  have hCV : 0 ≤ CV := le_trans (abs_nonneg (V 0)) (hVb 0)
  by_cases hlt : x < L * Real.exp a
  · rw [multiplicativeWeightDeriv_eq_zero_of_lt hL hVa hV'a hlt, abs_zero]
    positivity
  · have hge : L * Real.exp a ≤ x := not_lt.mp hlt
    have hxp : (0 : ℝ) < x := lt_of_lt_of_le hpa hge
    rw [multiplicativeWeightDeriv, if_pos hxp, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have hnum : |V' (Real.log (x / L)) - V (Real.log (x / L))| ≤ 2 * CV := by
      calc |V' (Real.log (x / L)) - V (Real.log (x / L))|
          ≤ |V' (Real.log (x / L))| + |V (Real.log (x / L))| := abs_sub _ _
        _ ≤ CV + CV := add_le_add (hV'b _) (hVb _)
        _ = 2 * CV := by ring
    have hsq : (L * Real.exp a) ^ 2 ≤ x ^ 2 := by nlinarith
    calc |V' (Real.log (x / L)) - V (Real.log (x / L))| / x ^ 2
        ≤ (2 * CV) / x ^ 2 := by
          gcongr
      _ ≤ (2 * CV) / (L * Real.exp a) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

/-- The multiplicative derivative is continuous: away from the origin by the chain rule, and near the
origin because it vanishes identically there. -/
theorem continuous_multiplicativeWeightDeriv {L a : ℝ} (hL : 0 < L) {V V' : ℝ → ℝ}
    (hVc : Continuous V) (hV'c : Continuous V')
    (hVa : ∀ s, s ≤ a → V s = 0) (hV'a : ∀ s, s ≤ a → V' s = 0) :
    Continuous (multiplicativeWeightDeriv L V V') := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : 0 < x
  · have hxL : x / L ≠ 0 := by positivity
    have hdivc : ContinuousAt (fun y : ℝ => y / L) x := (continuous_id.div_const L).continuousAt
    have hl : ContinuousAt (fun y : ℝ => Real.log (y / L)) x := hdivc.log hxL
    have hnum : ContinuousAt
        (fun y : ℝ => V' (Real.log (y / L)) - V (Real.log (y / L))) x :=
      (hV'c.continuousAt.comp hl).sub (hVc.continuousAt.comp hl)
    have hform : ContinuousAt
        (fun y : ℝ => (V' (Real.log (y / L)) - V (Real.log (y / L))) / y ^ 2) x :=
      hnum.div ((continuous_pow 2).continuousAt) (by positivity)
    refine hform.congr ?_
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [multiplicativeWeightDeriv, if_pos hy]
  · have hlt : x < L * Real.exp a := by
      have hp : (0 : ℝ) < L * Real.exp a := by positivity
      linarith [not_lt.mp hx]
    refine (continuousAt_const (x := x) (y := (0 : ℝ))).congr ?_
    filter_upwards [eventually_lt_nhds hlt] with y hy
    exact (multiplicativeWeightDeriv_eq_zero_of_lt hL hVa hV'a hy).symm

theorem multiplicativeWeight_apply {L : ℝ} (hL : 0 < L) (V : ℝ → ℝ) (s : ℝ) :
    multiplicativeWeight L V (L * Real.exp s) = V s / (L * Real.exp s) := by
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hlog : Real.log (L * Real.exp s / L) = s := by
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hL), mul_one, Real.log_exp]
  rw [multiplicativeWeight, if_pos hpos, hlog]

/-- **Equations (5)--(6) exactly as stated.**  For a `C¹` additive weight vanishing outside `[a, b]`,
the averaging error against the integer-dilated sawtooth is at most
`(1/(3L)) ∫ e^{-s} (|V'(s)| + |V(s)|) ds`, uniformly in the dilation.  The multiplicative weight it
induces is globally `C¹` precisely because the additive one has compact support. -/
theorem abs_integral_weight_mul_dilate_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) {a b : ℝ}
    (hab : a ≤ b) {V V' : ℝ → ℝ} (hV : ∀ s, HasDerivAt V (V' s) s) (hV'c : Continuous V')
    {CV : ℝ} (hVb : ∀ s, |V s| ≤ CV) (hV'b : ∀ s, |V' s| ≤ CV)
    (hVleft : ∀ s, s ≤ a → V s = 0) (hV'left : ∀ s, s ≤ a → V' s = 0)
    (hVright : ∀ s, b ≤ s → V s = 0) :
    |∫ s in a..b, V s *
        (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s)) - 1 / (12 * (n : ℝ)))|
      ≤ (1 / (3 * L)) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun s => (hV s).continuousAt
  have hGd : ∀ x, HasDerivAt (multiplicativeWeight L V)
      (multiplicativeWeightDeriv L V V' x) x :=
    hasDerivAt_multiplicativeWeight hL hV hVleft hV'left
  have hG'c : Continuous (multiplicativeWeightDeriv L V V') :=
    continuous_multiplicativeWeightDeriv hL hVc hV'c hVleft hV'left
  have hG'bnd : ∀ x, |multiplicativeWeightDeriv L V V' x| ≤ (2 * CV) / (L * Real.exp a) ^ 2 :=
    abs_multiplicativeWeightDeriv_le hL hVleft hV'left hVb hV'b
  have hVeq : V = additiveWeight L (multiplicativeWeight L V) :=
    (additiveWeight_multiplicativeWeight hL V).symm
  have hGa : multiplicativeWeight L V (L * Real.exp a) = 0 := by
    rw [multiplicativeWeight_apply hL V a, hVleft a le_rfl, zero_div]
  have hGb : multiplicativeWeight L V (L * Real.exp b) = 0 := by
    rw [multiplicativeWeight_apply hL V b, hVright b le_rfl, zero_div]
  exact abs_integral_additiveWeight_mul_sawDilateCentered_le hn hL hab hGd hG'c hG'bnd hVeq hV
    hGa hGb

/-! ## The growing-cutoff synthesis -/

/-- **Equations (12)--(13) and (19).**  Summed against the visible von Mangoldt weight, the averaging
estimate produces the exact Euler main term `(1/12) ∑ Λ(n) n^{-2}` with an error at most
`log² N` times one third of the total variation of the weight.  Since the error does not depend on the
weight through anything but its total variation, letting the window widen so that `log² N` is small
against the weight's variation is exactly the card's condition `(13)`. -/
theorem abs_primeResponse_sub_main_le {N : ℕ} (hN : 1 ≤ N) {α β : ℝ} (hαβ : α ≤ β)
    {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hG'c : Continuous G')
    {CG : ℝ} (hG'b : ∀ x, |G' x| ≤ CG) (hGα : G α = 0) (hGβ : G β = 0) :
    |(∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) *
        ∫ x in α..β, G x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      - (1 / 12) * (∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ^ 2) * (∫ x in α..β, G x)|
      ≤ (1 / 3) * Real.log N ^ 2 * ∫ x in α..β, |G' x| := by
  classical
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  have hprod : ∀ n : ℕ, IntervalIntegrable
      (fun x => G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))) volume α β :=
    fun n => (intervalIntegrable_sawDilateCentered n α β).continuousOn_mul hGc.continuousOn
  have hvar : (0 : ℝ) ≤ ∫ x in α..β, |G' x| :=
    intervalIntegral.integral_nonneg hαβ fun x _ => abs_nonneg _
  have hsplit : ∀ n : ℕ, (∫ x in α..β, G x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      = (∫ x in α..β, G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
        + (1 / (12 * (n : ℝ))) * ∫ x in α..β, G x := by
    intro n
    have hpt : ∀ x : ℝ, G x * (sawUnit x * sawUnit ((n : ℝ) * x))
        = G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))
          + (1 / (12 * (n : ℝ))) * G x := fun x => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add (hprod n) ((hGc.intervalIntegrable α β).const_mul _),
      intervalIntegral.integral_const_mul]
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      Λ n / (n : ℝ) * ((∫ x in α..β,
          G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
        + (1 / (12 * (n : ℝ))) * ∫ x in α..β, G x)
      = Λ n / (n : ℝ) * (∫ x in α..β,
            G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
        + (1 / 12) * (Λ n / (n : ℝ) ^ 2) * (∫ x in α..β, G x) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hpos : 0 < n := by omega
      exact Nat.cast_ne_zero.mpr hpos.ne'
    have hcoef : Λ n / (n : ℝ) * (1 / (12 * (n : ℝ))) = (1 / 12) * (Λ n / (n : ℝ) ^ 2) := by
      rw [pow_two]
      field_simp
    rw [mul_add, ← mul_assoc, hcoef]
  simp_rw [hsplit]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hmain : (∑ n ∈ Finset.Icc 2 N,
      (1 / 12) * (Λ n / (n : ℝ) ^ 2) * (∫ x in α..β, G x))
      = (1 / 12) * (∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ^ 2) * (∫ x in α..β, G x) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hmain, add_sub_cancel_right]
  calc |∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) * (∫ x in α..β,
          G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))|
      ≤ ∑ n ∈ Finset.Icc 2 N, |Λ n / (n : ℝ) * (∫ x in α..β,
          G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) * ((1 / 3) * ∫ x in α..β, |G' x|) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hnpos : 0 < n := by omega
        have hw : 0 ≤ Λ n / (n : ℝ) := by
          have h1 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
          have h2 : (0 : ℝ) ≤ (n : ℝ) := by positivity
          positivity
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left
          (abs_integral_weight_mul_sawDilateCentered_le hnpos hαβ hG hG'c hG'b hGα hGβ) hw
    _ = (∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ)) * ((1 / 3) * ∫ x in α..β, |G' x|) := by
        rw [Finset.sum_mul]
    _ ≤ Real.log N ^ 2 * ((1 / 3) * ∫ x in α..β, |G' x|) := by
        refine mul_le_mul_of_nonneg_right (sum_vonMangoldt_div_le_log_sq hN) (by positivity)
    _ = (1 / 3) * Real.log N ^ 2 * ∫ x in α..β, |G' x| := by ring

/-! ## The growing-cutoff synthesis, in additive coordinates -/

theorem multiplicativeWeightDeriv_apply {L : ℝ} (hL : 0 < L) (V V' : ℝ → ℝ) (s : ℝ) :
    multiplicativeWeightDeriv L V V' (L * Real.exp s)
      = (V' s - V s) / (L * Real.exp s) ^ 2 := by
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hlog : Real.log (L * Real.exp s / L) = s := by
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hL), mul_one, Real.log_exp]
  rw [multiplicativeWeightDeriv, if_pos hpos, hlog]

/-- The total variation of the multiplicative weight is at most `(1/L) ∫ e^{-s}(|V'| + |V|)`, which is
the right-hand side of the card's `(6)`. -/
theorem integral_abs_multiplicativeWeightDeriv_le {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b)
    {V V' : ℝ → ℝ} (hV : ∀ s, HasDerivAt V (V' s) s) (hV'c : Continuous V')
    (hVleft : ∀ s, s ≤ a → V s = 0) (hV'left : ∀ s, s ≤ a → V' s = 0) :
    (∫ x in (L * Real.exp a)..(L * Real.exp b), |multiplicativeWeightDeriv L V V' x|)
      ≤ (1 / L) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun s => (hV s).continuousAt
  rw [integral_abs_deriv_comp_exp_scale hL hab (multiplicativeWeightDeriv L V V')]
  have hint1 : IntervalIntegrable (fun s => Real.exp (-s) *
      ((L * Real.exp s) ^ 2 * |multiplicativeWeightDeriv L V V' (L * Real.exp s)|)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine (Real.continuous_exp.comp continuous_neg).mul ?_
    refine ((continuous_const.mul Real.continuous_exp).pow 2).mul ?_
    exact (continuous_abs.comp
      (continuous_multiplicativeWeightDeriv hL hVc hV'c hVleft hV'left)).comp
      (continuous_const.mul Real.continuous_exp)
  have hint2 : IntervalIntegrable
      (fun s => Real.exp (-s) * (|V' s| + |V s|)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (Real.continuous_exp.comp continuous_neg).mul
      ((continuous_abs.comp hV'c).add (continuous_abs.comp hVc))
  have hptw : ∀ s ∈ Icc a b,
      Real.exp (-s) * ((L * Real.exp s) ^ 2 * |multiplicativeWeightDeriv L V V' (L * Real.exp s)|)
        ≤ Real.exp (-s) * (|V' s| + |V s|) := by
    intro s _
    have hpos : (0 : ℝ) < (L * Real.exp s) ^ 2 := by positivity
    have hkey : (L * Real.exp s) ^ 2 * |multiplicativeWeightDeriv L V V' (L * Real.exp s)|
        = |V' s - V s| := by
      rw [multiplicativeWeightDeriv_apply hL V V' s, abs_div, abs_of_pos hpos]
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.exp_pos _).le
  have hmono2 := intervalIntegral.integral_mono_on hab hint1 hint2 hptw
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  nlinarith [hmono2]

/-- **Equations (12)--(13) and (19), in the card's variables.**  The visible von Mangoldt weight
produces the exact Euler main term with an error at most `log² N / (3L)` times the fixed additive
integral `∫ e^{-s}(|V'| + |V|)`.  The card's condition `(13)`, `log² N = o(L)`, is exactly the
statement that this bound tends to zero. -/
theorem abs_primeResponse_additive_sub_main_le {N : ℕ} (hN : 1 ≤ N) {L : ℝ} (hL : 0 < L)
    {a b : ℝ} (hab : a ≤ b) {V V' : ℝ → ℝ} (hV : ∀ s, HasDerivAt V (V' s) s)
    (hV'c : Continuous V') {CV : ℝ} (hVb : ∀ s, |V s| ≤ CV) (hV'b : ∀ s, |V' s| ≤ CV)
    (hVleft : ∀ s, s ≤ a → V s = 0) (hV'left : ∀ s, s ≤ a → V' s = 0)
    (hVright : ∀ s, b ≤ s → V s = 0) :
    |(∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) *
        ∫ s in a..b, V s * (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s))))
      - (1 / 12) * (∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ^ 2) * (∫ s in a..b, V s)|
      ≤ (Real.log N ^ 2 / (3 * L)) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun s => (hV s).continuousAt
  have hmono : L * Real.exp a ≤ L * Real.exp b := by
    have := Real.exp_le_exp.mpr hab
    nlinarith [Real.exp_pos a, Real.exp_pos b]
  have hGd : ∀ x, HasDerivAt (multiplicativeWeight L V)
      (multiplicativeWeightDeriv L V V' x) x :=
    hasDerivAt_multiplicativeWeight hL hV hVleft hV'left
  have hG'c : Continuous (multiplicativeWeightDeriv L V V') :=
    continuous_multiplicativeWeightDeriv hL hVc hV'c hVleft hV'left
  have hG'bnd : ∀ x, |multiplicativeWeightDeriv L V V' x| ≤ (2 * CV) / (L * Real.exp a) ^ 2 :=
    abs_multiplicativeWeightDeriv_le hL hVleft hV'left hVb hV'b
  have hVeq : V = additiveWeight L (multiplicativeWeight L V) :=
    (additiveWeight_multiplicativeWeight hL V).symm
  have hGa : multiplicativeWeight L V (L * Real.exp a) = 0 := by
    rw [multiplicativeWeight_apply hL V a, hVleft a le_rfl, zero_div]
  have hGb : multiplicativeWeight L V (L * Real.exp b) = 0 := by
    rw [multiplicativeWeight_apply hL V b, hVright b le_rfl, zero_div]
  have hmul := abs_primeResponse_sub_main_le hN hmono hGd hG'c hG'bnd hGa hGb
  -- transfer the response and the mean
  have htrans : ∀ n : ℕ, (∫ s in a..b,
      V s * (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s))))
      = ∫ x in (L * Real.exp a)..(L * Real.exp b),
          multiplicativeWeight L V x * (sawUnit x * sawUnit ((n : ℝ) * x)) := by
    intro n
    have h := integral_additiveWeight_mul_comp hL hab (multiplicativeWeight L V)
      (fun x => sawUnit x * sawUnit ((n : ℝ) * x))
    rw [additiveWeight_multiplicativeWeight hL V] at h
    exact h
  have hmean : (∫ s in a..b, V s)
      = ∫ x in (L * Real.exp a)..(L * Real.exp b), multiplicativeWeight L V x := by
    have h := integral_additiveWeight_mul_comp hL hab (multiplicativeWeight L V)
      (fun _ : ℝ => (1 : ℝ))
    simp only [mul_one] at h
    rw [additiveWeight_multiplicativeWeight hL V] at h
    exact h
  simp only [htrans, hmean]
  refine hmul.trans ?_
  have hvar := integral_abs_multiplicativeWeightDeriv_le hL hab hV hV'c hVleft hV'left
  have hlogsq : (0 : ℝ) ≤ Real.log N ^ 2 := sq_nonneg _
  calc (1 / 3) * Real.log N ^ 2 *
        ∫ x in (L * Real.exp a)..(L * Real.exp b), |multiplicativeWeightDeriv L V V' x|
      ≤ (1 / 3) * Real.log N ^ 2 *
          ((1 / L) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|)) := by
        have hc : (0 : ℝ) ≤ (1 / 3) * Real.log N ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hvar hc
    _ = (Real.log N ^ 2 / (3 * L)) * ∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|) := by
        field_simp

/-! ## The limit form -/

/-- The Euler weight is absolutely summable as a real series. -/
theorem summable_vonMangoldt_div_sq : Summable (fun n : ℕ => Λ n / (n : ℝ) ^ 2) := by
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr lseriesSummable_vonMangoldt_two
  refine hnorm.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
    rw [hcast, Complex.cpow_natCast, norm_div, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]

theorem sum_Icc_eq_sum_range_vonMangoldt_div_sq (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ^ 2
      = ∑ n ∈ Finset.range (N + 1), Λ n / (n : ℝ) ^ 2 := by
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · intro n hn hnot
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hnot
    have hlt : n < 2 := by omega
    interval_cases n
    · simp
    · simp [vonMangoldt_apply_one]

/-- The partial sums of the Euler weight converge to its value `-ζ'(2)/ζ(2)`. -/
theorem tendsto_sum_vonMangoldt_div_sq :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ^ 2) atTop
      (nhds (∑' n : ℕ, Λ n / (n : ℝ) ^ 2)) := by
  have hsum := summable_vonMangoldt_div_sq.hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  exact Tendsto.congr (fun N => (sum_Icc_eq_sum_range_vonMangoldt_div_sq N).symm)
    (hsum.comp hshift)

/-- **Equation (14).**  Along any schedule with `log² N(L) = o(L)` the finite prime response converges
to the universal Euler scalar times the fixed additive mean.  The error term of `(12)` is what forces
the schedule condition, and nothing else about the schedule is used. -/
theorem tendsto_primeResponse_additive {a b : ℝ} (hab : a ≤ b) {V V' : ℝ → ℝ}
    (hV : ∀ s, HasDerivAt V (V' s) s) (hV'c : Continuous V') {CV : ℝ}
    (hVb : ∀ s, |V s| ≤ CV) (hV'b : ∀ s, |V' s| ≤ CV)
    (hVleft : ∀ s, s ≤ a → V s = 0) (hV'left : ∀ s, s ≤ a → V' s = 0)
    (hVright : ∀ s, b ≤ s → V s = 0)
    (Lseq : ℕ → ℝ) (Nseq : ℕ → ℕ) (hLpos : ∀ j, 0 < Lseq j) (hN1 : ∀ j, 1 ≤ Nseq j)
    (hN : Tendsto Nseq atTop atTop)
    (herr : Tendsto (fun j => Real.log (Nseq j) ^ 2 / Lseq j) atTop (nhds 0)) :
    Tendsto (fun j => ∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) *
        ∫ s in a..b, V s *
          (sawUnit (Lseq j * Real.exp s) * sawUnit ((n : ℝ) * (Lseq j * Real.exp s))))
      atTop (nhds ((1 / 12) * (∑' n : ℕ, Λ n / (n : ℝ) ^ 2) * ∫ s in a..b, V s)) := by
  have hMlim : Tendsto (fun j => (1 / 12) *
      (∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) ^ 2) * (∫ s in a..b, V s)) atTop
      (nhds ((1 / 12) * (∑' n : ℕ, Λ n / (n : ℝ) ^ 2) * ∫ s in a..b, V s)) :=
    ((tendsto_sum_vonMangoldt_div_sq.comp hN).const_mul (1 / 12)).mul_const _
  have hbound : ∀ j : ℕ, ‖(∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) *
        ∫ s in a..b, V s *
          (sawUnit (Lseq j * Real.exp s) * sawUnit ((n : ℝ) * (Lseq j * Real.exp s))))
      - (1 / 12) * (∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) ^ 2) * (∫ s in a..b, V s)‖
      ≤ (Real.log (Nseq j) ^ 2 / Lseq j) *
        ((∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|)) / 3) := by
    intro j
    rw [Real.norm_eq_abs]
    refine (abs_primeResponse_additive_sub_main_le (hN1 j) (hLpos j) hab hV hV'c hVb hV'b
      hVleft hV'left hVright).trans (le_of_eq ?_)
    have hL : Lseq j ≠ 0 := ne_of_gt (hLpos j)
    field_simp
  have hzero : Tendsto (fun j : ℕ => (∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) *
      ∫ s in a..b, V s *
        (sawUnit (Lseq j * Real.exp s) * sawUnit ((n : ℝ) * (Lseq j * Real.exp s))))
      - (1 / 12) * (∑ n ∈ Finset.Icc 2 (Nseq j), Λ n / (n : ℝ) ^ 2) * (∫ s in a..b, V s))
      atTop (nhds 0) := by
    refine squeeze_zero_norm hbound ?_
    simpa using herr.mul_const ((∫ s in a..b, Real.exp (-s) * (|V' s| + |V s|)) / 3)
  have hfinal := hzero.add hMlim
  simpa using hfinal

/-! ## The exterior inverse-square weight -/

/-- The exterior weight `L/x²`, which is the image of the density `e^{-s}` under `x = L e^s`. -/
def invSqWeight (L : ℝ) : ℝ → ℝ := fun x => L / x ^ 2

def invSqWeightDeriv (L : ℝ) : ℝ → ℝ := fun x => -(2 * L) / x ^ 3

theorem measurable_invSqWeightDeriv (L : ℝ) : Measurable (invSqWeightDeriv L) := by
  unfold invSqWeightDeriv
  fun_prop

theorem hasDerivAt_invSqWeight {L x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (invSqWeight L) (invSqWeightDeriv L x) x := by
  have hc : HasDerivAt (fun _ : ℝ => L) 0 x := hasDerivAt_const x L
  have hd : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ 1) x := by
    simpa using hasDerivAt_pow 2 x
  have h := hc.div hd (pow_ne_zero 2 hx)
  have hval : (0 * x ^ 2 - L * (2 * x ^ 1)) / (x ^ 2) ^ 2 = invSqWeightDeriv L x := by
    rw [invSqWeightDeriv]
    field_simp
    ring
  show HasDerivAt (fun y : ℝ => L / y ^ 2) (invSqWeightDeriv L x) x
  rw [← hval]
  exact h

theorem abs_invSqWeightDeriv_le {L T x : ℝ} (hL : 0 < L) (hx : x ∈ Icc L T) :
    |invSqWeightDeriv L x| ≤ 2 / L ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
  have hcube : L ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
  rw [invSqWeightDeriv, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
    abs_of_pos (by positivity : (0 : ℝ) < x ^ 3)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcube, hL.le]

/-- The total variation of the exterior weight on a window. -/
theorem integral_abs_invSqWeightDeriv {L T : ℝ} (hL : 0 < L) (hLT : L ≤ T) :
    (∫ x in L..T, |invSqWeightDeriv L x|) = 1 / L - L / T ^ 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hcongr : (∫ x in L..T, |invSqWeightDeriv L x|) = ∫ x in L..T, (2 * L) / x ^ 3 := by
    refine integral_congr_of_Ioo hLT fun x hx => ?_
    have hxpos : 0 < x := lt_trans hL hx.1
    rw [invSqWeightDeriv, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
      abs_of_pos (by positivity : (0 : ℝ) < x ^ 3)]
  rw [hcongr]
  have hd : ∀ x ∈ uIcc L T, HasDerivAt (fun y : ℝ => -(L / y ^ 2)) ((2 * L) / x ^ 3) x := by
    intro x hx
    rw [uIcc_of_le hLT] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have h := (hasDerivAt_invSqWeight (L := L) (ne_of_gt hxpos)).neg
    have hval : -invSqWeightDeriv L x = (2 * L) / x ^ 3 := by
      rw [invSqWeightDeriv]
      field_simp
    rw [← hval]
    exact h
  have hint : IntervalIntegrable (fun x : ℝ => (2 * L) / x ^ 3) volume L T := by
    refine intervalIntegrable_of_bound_on (by fun_prop) (C := 2 * L / L ^ 3) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hcube : L ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
    rw [abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcube, hL.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  field_simp
  ring

/-- The exterior weight integrates to `1 - L/T`. -/
theorem integral_invSqWeight {L T : ℝ} (hL : 0 < L) (hLT : L ≤ T) :
    (∫ x in L..T, invSqWeight L x) = 1 - L / T := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hd : ∀ x ∈ uIcc L T, HasDerivAt (fun y : ℝ => -(L / y)) (invSqWeight L x) x := by
    intro x hx
    rw [uIcc_of_le hLT] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hc : HasDerivAt (fun _ : ℝ => L) 0 x := hasDerivAt_const x L
    have h := (hc.div (hasDerivAt_id x) (ne_of_gt hxpos)).neg
    have hval : -((0 * x - L * 1) / x ^ 2) = invSqWeight L x := by
      rw [invSqWeight]
      field_simp
      ring
    rw [← hval]
    exact h
  have hint : IntervalIntegrable (invSqWeight L) volume L T := by
    refine intervalIntegrable_of_bound_on (by unfold invSqWeight; fun_prop)
      (C := L / L ^ 2) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hsq : L ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    rw [invSqWeight, abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hL.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  field_simp
  ring

/-- **Equation (18), on a finite window.**  The exponentially weighted dilated sawtooth product has
the exact mean `1/(12 n)` up to `4/(3L)`, uniformly in the dilation and in the outer endpoint.  The
integration by parts is the distributional one, so the discontinuity of the sawtooth costs nothing. -/
theorem abs_integral_invSqWeight_mul_sawDilate_sub_mean_le {n : ℕ} (hn : 0 < n) {L T : ℝ}
    (hL : 0 < L) (hLT : L ≤ T) :
    |(∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      - (1 / (12 * (n : ℝ))) * (1 - L / T)| ≤ 4 / (3 * L) := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hgm := measurable_sawDilateCentered n
  have hgb := abs_sawDilateCentered_le hn
  have hwint : IntervalIntegrable (invSqWeight L) volume L T := by
    refine intervalIntegrable_of_bound_on (by unfold invSqWeight; fun_prop)
      (C := L / L ^ 2) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hsq : L ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    rw [invSqWeight, abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hL.le]
  have hcent : IntervalIntegrable
      (fun x => invSqWeight L x *
        (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))) volume L T := by
    refine (intervalIntegrable_sawDilateCentered n L T).continuousOn_mul ?_
    refine ContinuousOn.mono (s := {x : ℝ | x ≠ 0}) ?_ ?_
    · unfold invSqWeight
      exact ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        fun x hx => pow_ne_zero 2 hx
    · intro x hx
      rw [uIcc_of_le hLT] at hx
      exact ne_of_gt (lt_of_lt_of_le hL hx.1)
  -- split off the mean
  have hsplit : (∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      = (∫ x in L..T, invSqWeight L x *
          (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
        + (1 / (12 * (n : ℝ))) * (1 - L / T) := by
    have hpt : ∀ x : ℝ, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))
        = invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))
          + (1 / (12 * (n : ℝ))) * invSqWeight L x := fun x => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add hcent (hwint.const_mul _),
      intervalIntegral.integral_const_mul, integral_invSqWeight hL hLT]
  rw [hsplit, add_sub_cancel_right]
  -- integration by parts
  have hibp := integral_deriv_mul_primitive hLT hgm hgb (measurable_invSqWeightDeriv L)
    (fun x hx => hasDerivAt_invSqWeight (ne_of_gt (lt_of_lt_of_le hL hx.1)))
    (fun x hx => abs_invSqWeightDeriv_le hL hx)
  simp only [integral_sawDilateCentered_eq n L] at hibp
  have hPbound : ∀ x : ℝ, |sawDilatePrimitive n x - sawDilatePrimitive n L| ≤ 2 / 3 := by
    intro x
    calc |sawDilatePrimitive n x - sawDilatePrimitive n L|
        ≤ |sawDilatePrimitive n x| + |sawDilatePrimitive n L| := abs_sub _ _
      _ ≤ 1 / 3 + 1 / 3 := add_le_add (abs_sawDilatePrimitive_le hn x)
          (abs_sawDilatePrimitive_le hn L)
      _ = 2 / 3 := by norm_num
  have hd'int : IntervalIntegrable (invSqWeightDeriv L) volume L T :=
    intervalIntegrable_of_bound_on (measurable_invSqWeightDeriv L) hLT
      (fun x hx => abs_invSqWeightDeriv_le hL hx)
  have hprod : IntervalIntegrable (fun x => invSqWeightDeriv L x *
      (sawDilatePrimitive n x - sawDilatePrimitive n L)) volume L T :=
    hd'int.mul_continuousOn
      (((continuous_sawDilatePrimitive n).sub continuous_const).continuousOn)
  have habs1 : |∫ x in L..T, invSqWeightDeriv L x *
      (sawDilatePrimitive n x - sawDilatePrimitive n L)| ≤ (2 / 3) * (1 / L - L / T ^ 2) := by
    calc |∫ x in L..T, invSqWeightDeriv L x *
          (sawDilatePrimitive n x - sawDilatePrimitive n L)|
        ≤ ∫ x in L..T, |invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)| :=
          intervalIntegral.abs_integral_le_integral_abs hLT
      _ ≤ ∫ x in L..T, (2 / 3) * |invSqWeightDeriv L x| := by
          refine intervalIntegral.integral_mono_on hLT hprod.abs (hd'int.abs.const_mul _) ?_
          intro x _
          rw [abs_mul]
          nlinarith [abs_nonneg (invSqWeightDeriv L x), hPbound x,
            abs_nonneg (sawDilatePrimitive n x - sawDilatePrimitive n L)]
      _ = (2 / 3) * (1 / L - L / T ^ 2) := by
          rw [intervalIntegral.integral_const_mul, integral_abs_invSqWeightDeriv hL hLT]
  have hwT : invSqWeight L T ≤ 1 / L := by
    rw [invSqWeight]
    have hsq : L ^ 2 ≤ T ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [hsq, hL.le]
  have hwTnn : 0 ≤ invSqWeight L T := by
    rw [invSqWeight]; positivity
  have hkey : (∫ x in L..T, invSqWeight L x *
      (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
      = invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)
        - ∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L) := by
    linarith [hibp]
  rw [hkey]
  have hvar : (0 : ℝ) ≤ 1 / L - L / T ^ 2 := by
    rw [← integral_abs_invSqWeightDeriv hL hLT]
    exact intervalIntegral.integral_nonneg hLT fun x _ => abs_nonneg _
  have hvarle : 1 / L - L / T ^ 2 ≤ 1 / L := by
    have hnn : (0 : ℝ) ≤ L / T ^ 2 := by positivity
    linarith
  calc |invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)
        - ∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)|
      ≤ |invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)|
        + |∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)| := abs_sub _ _
    _ ≤ (1 / L) * (2 / 3) + (2 / 3) * (1 / L) := by
        refine add_le_add ?_ (habs1.trans (by linarith [hvarle]))
        rw [abs_mul, abs_of_nonneg hwTnn]
        have hLpos : (0 : ℝ) < 1 / L := by positivity
        nlinarith [hPbound T, abs_nonneg (sawDilatePrimitive n T - sawDilatePrimitive n L),
          hwTnn, hwT]
    _ = 4 / (3 * L) := by
        field_simp
        ring

/-- The exterior weight is the multiplicative image of the exponential density. -/
theorem additiveWeight_invSqWeight {L : ℝ} (hL : 0 < L) :
    additiveWeight L (invSqWeight L) = fun s => Real.exp (-s) := by
  funext s
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hne : Real.exp s ≠ 0 := Real.exp_ne_zero s
  rw [additiveWeight, invSqWeight, Real.exp_neg]
  field_simp

theorem integral_expWeight_eq_invSqWeight {L : ℝ} (hL : 0 < L) {S : ℝ} (hS : 0 ≤ S) (h : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..S, Real.exp (-s) * h (L * Real.exp s))
      = ∫ x in L..(L * Real.exp S), invSqWeight L x * h x := by
  have hbase := integral_additiveWeight_mul_comp hL hS (invSqWeight L) h
  rw [additiveWeight_invSqWeight hL] at hbase
  rw [Real.exp_zero, mul_one] at hbase
  exact hbase

/-- **Equation (18), in the card's additive variable, on a finite window.**  The card's `O(1/L)` is
made explicit: the constant is `4/3`, uniformly in the dilation and in the outer endpoint. -/
theorem abs_integral_expWeight_sawDilate_sub_mean_le {n : ℕ} (hn : 0 < n) {L S : ℝ} (hL : 0 < L)
    (hS : 0 ≤ S) :
    |(∫ s in (0 : ℝ)..S,
        Real.exp (-s) * (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s))))
      - (1 / (12 * (n : ℝ))) * (1 - Real.exp (-S))| ≤ 4 / (3 * L) := by
  have hLS : L ≤ L * Real.exp S := by
    have h1 : (1 : ℝ) ≤ Real.exp S := Real.one_le_exp hS
    nlinarith
  have hratio : L / (L * Real.exp S) = Real.exp (-S) := by
    have hne : Real.exp S ≠ 0 := Real.exp_ne_zero S
    rw [Real.exp_neg]
    field_simp
  rw [integral_expWeight_eq_invSqWeight hL hS
    (fun x => sawUnit x * sawUnit ((n : ℝ) * x)), ← hratio]
  exact abs_integral_invSqWeight_mul_sawDilate_sub_mean_le hn hL hLS

/-! ## The exterior integrand on one period -/

/-- On the period `[k, k+1]` the slow factor `L x^{-2} S(x)` of the exterior integrand is smooth: the
sawtooth is affine there.  This is the piece on which the `O(1/n)` estimate is proved. -/
def exteriorPiece (L : ℝ) (k : ℤ) : ℝ → ℝ := fun x => (L / x ^ 2) * ((k : ℝ) + 1 / 2 - x)

def exteriorPieceDeriv (L : ℝ) (k : ℤ) : ℝ → ℝ :=
  fun x => (-(2 * L) / x ^ 3) * ((k : ℝ) + 1 / 2 - x) + (L / x ^ 2) * (-1)

theorem measurable_exteriorPieceDeriv (L : ℝ) (k : ℤ) : Measurable (exteriorPieceDeriv L k) := by
  unfold exteriorPieceDeriv
  fun_prop

theorem hasDerivAt_exteriorPiece {L : ℝ} (k : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (exteriorPiece L k) (exteriorPieceDeriv L k x) x := by
  have h1 : HasDerivAt (fun y : ℝ => L / y ^ 2) (-(2 * L) / x ^ 3) x :=
    hasDerivAt_invSqWeight hx
  have h2 : HasDerivAt (fun y : ℝ => (k : ℝ) + 1 / 2 - y) (-1) x := by
    have h := (hasDerivAt_const x ((k : ℝ) + 1 / 2)).fun_sub (hasDerivAt_id x)
    simpa using h
  exact h1.mul h2

theorem abs_exteriorPiece_le {L : ℝ} (hL : 0 < L) (k : ℤ) {x : ℝ}
    (hk : (k : ℝ) ≤ x) (hk1 : x ≤ (k : ℝ) + 1) (hx : 0 < x) :
    |exteriorPiece L k x| ≤ L / (2 * x ^ 2) := by
  have hb : |(k : ℝ) + 1 / 2 - x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [exteriorPiece, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < L / x ^ 2)]
  calc L / x ^ 2 * |(k : ℝ) + 1 / 2 - x| ≤ L / x ^ 2 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = L / (2 * x ^ 2) := by ring

theorem abs_exteriorPieceDeriv_le {L : ℝ} (hL : 0 < L) (k : ℤ) {x : ℝ}
    (hk : (k : ℝ) ≤ x) (hk1 : x ≤ (k : ℝ) + 1) (hx : 0 < x) :
    |exteriorPieceDeriv L k x| ≤ L / x ^ 3 + L / x ^ 2 := by
  have hb : |(k : ℝ) + 1 / 2 - x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h1 : |(-(2 * L) / x ^ 3) * ((k : ℝ) + 1 / 2 - x)| ≤ L / x ^ 3 := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
      abs_of_pos (by positivity : (0 : ℝ) < x ^ 3)]
    calc 2 * L / x ^ 3 * |(k : ℝ) + 1 / 2 - x| ≤ 2 * L / x ^ 3 * (1 / 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = L / x ^ 3 := by ring
  have h2 : |(L / x ^ 2) * (-1)| = L / x ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < L / x ^ 2)]
    simp
  rw [exteriorPieceDeriv]
  calc |(-(2 * L) / x ^ 3) * ((k : ℝ) + 1 / 2 - x) + (L / x ^ 2) * (-1)|
      ≤ |(-(2 * L) / x ^ 3) * ((k : ℝ) + 1 / 2 - x)| + |(L / x ^ 2) * (-1)| :=
          abs_add_le _ _
    _ ≤ L / x ^ 3 + L / x ^ 2 := by rw [h2] at *; linarith

/-- **The per-period `O(1/n)` estimate.**  On a sub-interval of one period, the exterior integrand
pairs the smooth slow factor against the dilated sawtooth, whose primitive is `O(1/n)`; the
distributional integration by parts turns this into a bound with the slow factor's boundary value and
total variation. -/
theorem abs_integral_exteriorPiece_mul_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) (k : ℤ)
    {c d : ℝ} (hcd : c ≤ d) (hc : 0 < c) (hkc : (k : ℝ) ≤ c) (hdk : d ≤ (k : ℝ) + 1) :
    |∫ x in c..d, exteriorPiece L k x * sawUnit ((n : ℝ) * x)|
      ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ 2) + ∫ x in c..d, (L / x ^ 3 + L / x ^ 2)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdpos : 0 < d := lt_of_lt_of_le hc hcd
  have hxpos : ∀ x ∈ Icc c d, 0 < x := fun x hx => lt_of_lt_of_le hc hx.1
  have hgm : Measurable fun x : ℝ => sawUnit ((n : ℝ) * x) :=
    measurable_sawUnit.comp (measurable_const_mul _)
  have hgb : ∀ x : ℝ, |sawUnit ((n : ℝ) * x)| ≤ 1 / 2 := fun x => abs_sawUnit_le _
  have hd'b : ∀ x ∈ Icc c d, |exteriorPieceDeriv L k x| ≤ L / c ^ 3 + L / c ^ 2 := by
    intro x hx
    have hxp := hxpos x hx
    refine (abs_exteriorPieceDeriv_le hL k (le_trans hkc hx.1) (le_trans hx.2 hdk) hxp).trans ?_
    have h3 : c ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
    have h2 : c ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    have hb3 : L / x ^ 3 ≤ L / c ^ 3 := by
      apply div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ 2 ≤ L / c ^ 2 := by
      apply div_le_div_of_nonneg_left hL.le (by positivity) h2
    linarith
  have hibp := integral_deriv_mul_primitive hcd hgm hgb (measurable_exteriorPieceDeriv L k)
    (fun x hx => hasDerivAt_exteriorPiece k (ne_of_gt (hxpos x hx))) hd'b
  have hd'int : IntervalIntegrable (exteriorPieceDeriv L k) volume c d :=
    intervalIntegrable_of_bound_on (measurable_exteriorPieceDeriv L k) hcd hd'b
  have hPb : ∀ x : ℝ, |∫ t in c..x, sawUnit ((n : ℝ) * t)| ≤ 1 / (4 * (n : ℝ)) :=
    fun x => abs_integral_sawUnit_comp_mul_le hn c x
  have hPcont : Continuous fun x : ℝ => ∫ t in c..x, sawUnit ((n : ℝ) * t) :=
    intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_sawUnit_comp_mul n a b) c
  have hprod : IntervalIntegrable
      (fun x => exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))) volume c d :=
    hd'int.mul_continuousOn hPcont.continuousOn
  have hboundfn : IntervalIntegrable (fun x : ℝ => L / x ^ 3 + L / x ^ 2) volume c d := by
    refine intervalIntegrable_of_bound_on (by fun_prop) (C := L / c ^ 3 + L / c ^ 2) hcd ?_
    intro x hx
    have hxp := hxpos x hx
    have h3 : c ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
    have h2 : c ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    rw [abs_of_pos (by positivity)]
    have hb3 : L / x ^ 3 ≤ L / c ^ 3 := div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ 2 ≤ L / c ^ 2 := div_le_div_of_nonneg_left hL.le (by positivity) h2
    linarith
  have hvar : (∫ x in c..d, |exteriorPieceDeriv L k x|)
      ≤ ∫ x in c..d, (L / x ^ 3 + L / x ^ 2) := by
    refine intervalIntegral.integral_mono_on hcd hd'int.abs hboundfn ?_
    intro x hx
    exact abs_exteriorPieceDeriv_le hL k (le_trans hkc hx.1) (le_trans hx.2 hdk) (hxpos x hx)
  have hterm2 : |∫ x in c..d, exteriorPieceDeriv L k x *
      (∫ t in c..x, sawUnit ((n : ℝ) * t))|
      ≤ (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ 3 + L / x ^ 2) := by
    calc |∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))|
        ≤ ∫ x in c..d, |exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))| :=
          intervalIntegral.abs_integral_le_integral_abs hcd
      _ ≤ ∫ x in c..d, (1 / (4 * (n : ℝ))) * |exteriorPieceDeriv L k x| := by
          refine intervalIntegral.integral_mono_on hcd hprod.abs (hd'int.abs.const_mul _) ?_
          intro x _
          rw [abs_mul]
          nlinarith [abs_nonneg (exteriorPieceDeriv L k x), hPb x,
            abs_nonneg (∫ t in c..x, sawUnit ((n : ℝ) * t))]
      _ = (1 / (4 * (n : ℝ))) * ∫ x in c..d, |exteriorPieceDeriv L k x| :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ 3 + L / x ^ 2) :=
          mul_le_mul_of_nonneg_left hvar (by positivity)
  have hterm1 : |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))|
      ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ 2)) := by
    rw [abs_mul]
    have hb1 := abs_exteriorPiece_le hL k (le_trans hkc hcd) hdk hdpos
    have hb2 := hPb d
    nlinarith [abs_nonneg (exteriorPiece L k d),
      abs_nonneg (∫ t in c..d, sawUnit ((n : ℝ) * t))]
  have hkey : (∫ x in c..d, exteriorPiece L k x * sawUnit ((n : ℝ) * x))
      = exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))
        - ∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t)) := by
    linarith [hibp]
  rw [hkey]
  calc |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))
        - ∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))|
      ≤ |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))|
        + |∫ x in c..d, exteriorPieceDeriv L k x *
            (∫ t in c..x, sawUnit ((n : ℝ) * t))| := abs_sub _ _
    _ ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ 2))
        + (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ 3 + L / x ^ 2) :=
        add_le_add hterm1 hterm2
    _ = (1 / (4 * (n : ℝ))) * (L / (2 * d ^ 2) + ∫ x in c..d, (L / x ^ 3 + L / x ^ 2)) := by
        ring

/-- On one period the exterior integrand is the piece integrand. -/
theorem invSqWeight_mul_sawDilate_eq_exteriorPiece {L : ℝ} (k : ℤ) {x : ℝ}
    (hx : x ∈ Ico ((k : ℝ)) ((k : ℝ) + 1)) (n : ℕ) :
    invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))
      = exteriorPiece L k x * sawUnit ((n : ℝ) * x) := by
  rw [invSqWeight, exteriorPiece, sawUnit_eq_of_mem_Ico_int k hx]
  ring

/-! ## The exterior tail bound over whole periods -/

theorem hasDerivAt_invPowPrimitive {L : ℝ} (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * (L / y ^ 2) + (-α) * (L / y))
      (L / x ^ 3 + α * (L / x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => L / y ^ 2) (-(2 * L) / x ^ 3) x :=
    hasDerivAt_invSqWeight hx
  have h2 : HasDerivAt (fun y : ℝ => L / y) ((0 * x - L * 1) / x ^ 2) x :=
    (hasDerivAt_const x L).div (hasDerivAt_id x) hx
  have h := (h1.const_mul (-(1 / 2) : ℝ)).add (h2.const_mul (-α))
  have hval : (-(1 / 2) : ℝ) * (-(2 * L) / x ^ 3) + (-α) * ((0 * x - L * 1) / x ^ 2)
      = L / x ^ 3 + α * (L / x ^ 2) := by
    field_simp
    ring
  rw [← hval]
  exact h

theorem integral_invPow {L c d α : ℝ} (hL : 0 < L) (hα : 0 ≤ α) (hc : 0 < c) (hcd : c ≤ d) :
    (∫ x in c..d, (L / x ^ 3 + α * (L / x ^ 2)))
      = (-(1 / 2) * (L / d ^ 2) + (-α) * (L / d))
        - (-(1 / 2) * (L / c ^ 2) + (-α) * (L / c)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => -(1 / 2) * (L / y ^ 2) + (-α) * (L / y)) (fun x hx => ?_) ?_
  · rw [uIcc_of_le hcd] at hx
    exact hasDerivAt_invPowPrimitive α (ne_of_gt (lt_of_lt_of_le hc hx.1))
  · refine intervalIntegrable_of_bound_on (by fun_prop)
      (C := L / c ^ 3 + α * (L / c ^ 2)) hcd ?_
    intro x hx
    have hxp : 0 < x := lt_of_lt_of_le hc hx.1
    have h3 : c ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
    have h2 : c ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    have hb3 : L / x ^ 3 ≤ L / c ^ 3 := div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ 2 ≤ L / c ^ 2 := div_le_div_of_nonneg_left hL.le (by positivity) h2
    rw [abs_of_pos (by positivity)]
    nlinarith [hb3, hb2, hα]

/-- **Equation (21), over one whole period.**  The boundary term of the per-period estimate is absorbed
by widening the weight `L x^{-3} + L x^{-2}` to `L x^{-3} + 2 L x^{-2}`, because over a full period
`∫ L x^{-2} = L/(k(k+1))` already dominates `L/(2(k+1)²)`. -/
theorem abs_integral_exteriorPiece_period_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) {k : ℤ}
    (hk : (0 : ℝ) < (k : ℝ)) :
    |∫ x in (k : ℝ)..((k : ℝ) + 1), exteriorPiece L k x * sawUnit ((n : ℝ) * x)|
      ≤ (1 / (4 * (n : ℝ))) * ∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ 3 + 2 * (L / x ^ 2)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcd : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have h := abs_integral_exteriorPiece_mul_le hn hL k hcd hk le_rfl le_rfl
  refine h.trans ?_
  have hone : (∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ 3 + L / x ^ 2))
      = ∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ 3 + 1 * (L / x ^ 2)) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hone, integral_invPow hL zero_le_one hk hcd,
    integral_invPow hL (by norm_num : (0 : ℝ) ≤ 2) hk hcd]
  have hgap : L / (2 * ((k : ℝ) + 1) ^ 2) ≤ L / (k : ℝ) - L / ((k : ℝ) + 1) := by
    rw [div_sub_div _ _ (ne_of_gt hk) (ne_of_gt hk1), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [hL.le, hk.le, sq_nonneg ((k : ℝ) - 1)]
  have hcoef : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
  have hstep : L / (2 * ((k : ℝ) + 1) ^ 2)
      + ((-(1 / 2) * (L / ((k : ℝ) + 1) ^ 2) + (-1 : ℝ) * (L / ((k : ℝ) + 1)))
        - (-(1 / 2) * (L / (k : ℝ) ^ 2) + (-1 : ℝ) * (L / (k : ℝ))))
      ≤ (-(1 / 2) * (L / ((k : ℝ) + 1) ^ 2) + (-2 : ℝ) * (L / ((k : ℝ) + 1)))
        - (-(1 / 2) * (L / (k : ℝ) ^ 2) + (-2 : ℝ) * (L / (k : ℝ))) := by
    nlinarith [hgap]
  exact mul_le_mul_of_nonneg_left hstep hcoef.le

theorem intervalIntegrable_invSqWeight_mul_sawDilate (L : ℝ) (n : ℕ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : IntervalIntegrable
      (fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) volume a b := by
  refine intervalIntegrable_of_bound_on (C := |L| / a ^ 2 * (1 / 4)) ?_ hab ?_
  · unfold invSqWeight
    exact (by fun_prop : Measurable fun x : ℝ => L / x ^ 2).mul
      (measurable_sawUnit.mul (measurable_sawUnit.comp (measurable_const_mul _)))
  · intro x hx
    have hxp : 0 < x := lt_of_lt_of_le ha hx.1
    have h2 : a ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
    have hw : |invSqWeight L x| ≤ |L| / a ^ 2 := by
      rw [invSqWeight, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
      exact div_le_div_of_nonneg_left (abs_nonneg L) (by positivity) h2
    have hs : |sawUnit x * sawUnit ((n : ℝ) * x)| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |sawUnit x| * |sawUnit ((n : ℝ) * x)| ≤ (1 / 2) * (1 / 2) :=
            mul_le_mul (abs_sawUnit_le x) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    rw [abs_mul]
    exact mul_le_mul hw hs (abs_nonneg _) (by positivity)

/-- **Equation (21), over a whole number of periods.**  The exterior response over an integer window
beyond `L` is `O(1/n)` with the absolute constant `5/8`, uniformly in the window and in `L`.  This is
the estimate the card obtains by Stieltjes integration by parts; here every period is handled by the
distributional integration by parts against the dilated primitive, whose sup norm is `O(1/n)`. -/
theorem abs_integral_invSqWeight_mul_sawDilate_int_window_le {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 < L) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (hLm : L ≤ (m : ℝ)) :
    |∫ x in (m : ℝ)..(M : ℝ), invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ 5 / (8 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmMr : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hcast : ∀ j : ℕ, ((m + (j + 1) : ℕ) : ℝ) = ((m + j : ℕ) : ℝ) + 1 := by
    intro j; push_cast; ring
  have hpos : ∀ j : ℕ, (0 : ℝ) < ((m + j : ℕ) : ℝ) := by
    intro j
    have : (0 : ℕ) < m + j := by omega
    exact_mod_cast this
  -- partition the window into periods
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((m + j : ℕ) : ℝ))
    (f := fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
    (n := M - m)
    (fun j _ => by
      rw [hcast j]
      exact intervalIntegrable_invSqWeight_mul_sawDilate L n (hpos j) (by linarith))
  have hpartB := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((m + j : ℕ) : ℝ))
    (f := fun x : ℝ => L / x ^ 3 + 2 * (L / x ^ 2))
    (n := M - m)
    (fun j _ => by
      rw [hcast j]
      refine intervalIntegrable_of_bound_on (by fun_prop)
        (C := L / ((m + j : ℕ) : ℝ) ^ 3 + 2 * (L / ((m + j : ℕ) : ℝ) ^ 2)) (by linarith) ?_
      intro x hx
      have hxp : 0 < x := lt_of_lt_of_le (hpos j) hx.1
      have h3 : ((m + j : ℕ) : ℝ) ^ 3 ≤ x ^ 3 := by gcongr; exact hx.1
      have h2 : ((m + j : ℕ) : ℝ) ^ 2 ≤ x ^ 2 := by gcongr; exact hx.1
      have hb3 : L / x ^ 3 ≤ L / ((m + j : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left hL.le (by positivity) h3
      have hb2 : L / x ^ 2 ≤ L / ((m + j : ℕ) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left hL.le (by positivity) h2
      rw [abs_of_pos (by positivity)]
      nlinarith [hb3, hb2])
  have hends : ((m + 0 : ℕ) : ℝ) = (m : ℝ) ∧ ((m + (M - m) : ℕ) : ℝ) = (M : ℝ) := by
    refine ⟨by norm_num, ?_⟩
    congr 1
    omega
  rw [hends.1, hends.2] at hpart hpartB
  -- bound each period
  have hpiece : ∀ j ∈ Finset.range (M - m),
      |∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
          invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
        ≤ (1 / (4 * (n : ℝ))) *
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ 3 + 2 * (L / x ^ 2)) := by
    intro j _
    set k : ℤ := ((m + j : ℕ) : ℤ) with hk
    have hkr : ((k : ℤ) : ℝ) = ((m + j : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [hcast j, ← hkr]
    have hcongr : (∫ x in (k : ℝ)..((k : ℝ) + 1),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
        = ∫ x in (k : ℝ)..((k : ℝ) + 1), exteriorPiece L k x * sawUnit ((n : ℝ) * x) := by
      refine integral_congr_of_Ioo (by linarith) fun x hx => ?_
      exact invSqWeight_mul_sawDilate_eq_exteriorPiece k ⟨hx.1.le, hx.2⟩ n
    rw [hcongr]
    exact abs_integral_exteriorPiece_period_le hn hL (by rw [hkr]; exact hpos j)
  -- assemble
  rw [← hpart]
  calc |∑ j ∈ Finset.range (M - m), ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ ∑ j ∈ Finset.range (M - m), |∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
          invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (M - m), (1 / (4 * (n : ℝ))) *
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ 3 + 2 * (L / x ^ 2)) :=
        Finset.sum_le_sum hpiece
    _ = (1 / (4 * (n : ℝ))) * ∑ j ∈ Finset.range (M - m),
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ 3 + 2 * (L / x ^ 2)) := by
        rw [Finset.mul_sum]
    _ = (1 / (4 * (n : ℝ))) * ∫ x in (m : ℝ)..(M : ℝ), (L / x ^ 3 + 2 * (L / x ^ 2)) := by
        rw [hpartB]
    _ ≤ 5 / (8 * (n : ℝ)) := by
        rw [integral_invPow hL (by norm_num : (0 : ℝ) ≤ 2) hmpos hmMr]
        have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hmpos hmMr
        have hb1 : L / (m : ℝ) ≤ 1 := by
          rw [div_le_one hmpos]; exact hLm
        have hb2 : L / (2 * (m : ℝ) ^ 2) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hLm, hmpos, one_le_two]
        have hnn1 : (0 : ℝ) ≤ L / (M : ℝ) := by positivity
        have hnn2 : (0 : ℝ) ≤ L / (2 * (M : ℝ) ^ 2) := by positivity
        have hnn3 : (0 : ℝ) ≤ L / (M : ℝ) ^ 2 := by positivity
        have hnn4 : (0 : ℝ) ≤ L / (m : ℝ) ^ 2 := by positivity
        have hkey : (-(1 / 2) * (L / (M : ℝ) ^ 2) + (-2 : ℝ) * (L / (M : ℝ)))
            - (-(1 / 2) * (L / (m : ℝ) ^ 2) + (-2 : ℝ) * (L / (m : ℝ))) ≤ 5 / 2 := by
          nlinarith [hb1, hb2, hnn1, hnn3, hnn4]
        have hcoef : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
        calc (1 / (4 * (n : ℝ))) * ((-(1 / 2) * (L / (M : ℝ) ^ 2) + (-2 : ℝ) * (L / (M : ℝ)))
              - (-(1 / 2) * (L / (m : ℝ) ^ 2) + (-2 : ℝ) * (L / (m : ℝ))))
            ≤ (1 / (4 * (n : ℝ))) * (5 / 2) := mul_le_mul_of_nonneg_left hkey hcoef.le
          _ = 5 / (8 * (n : ℝ)) := by ring

end GaloisForLFunctions.RHTower

end
