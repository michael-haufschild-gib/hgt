import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# The Weil form as a Markov form plus the pole plane

For a real test `g ∈ C²_c(ℝ)` whose autocorrelation vanishes at `log n` for `n > N`, the Weil
functional of `ζ` splits exactly (`weil_eq_markovForm_add_pole`) as

`W(g) = M_N(g) + ½⟨c, g⟩² − ½⟨s, g⟩²`,   `c = 2 cosh(u/2)`, `s = 2 sinh(u/2)`,

where the Markov form `M_N(g) = V_N ‖g‖² + J(g)` has the constant creation potential
`V_N = Ω(0) − 2 Σ_{2 ≤ n ≤ N} Λ(n)/√n` and the jump energy
`J(g) = ∫_0^∞ ω(x) ‖g − g(· + x)‖² dx + Σ_{2 ≤ n ≤ N} Λ(n) n^{-1/2} ‖g − g(· + log n)‖²`:
archimedean and prime jumps both enter with nonnegative jump measure.

* **Markov property.**  Normal contraction lowers the Markov form, `M_N(|g|) ≤ M_N(g)`
  (`markovForm_abs_le`), while the pole part `½⟨c, g⟩² − ½⟨s, g⟩² = 2⟨e^{u/2}, g⟩⟨e^{-u/2}, g⟩` is
  raised by it (`pole_le_pole_abs`): the pole is the only anti-Markovian term.
* **Capacity criterion.**  `W ≥ 0` on a family of tests iff `⟨s, g⟩² ≤ 2 (M_N + ½cc*)(g)` on it;
  hence `RH ⟺` this sinh-capacity bound at every level (`riemannHypothesis_iff_sinhCapacity`).  For a
  positive-definite Gram matrix `Q` of `M_N + ½cc*` the bound is `⟨s, Q⁻¹ s⟩ ≤ 2`
  (`forall_sq_dotProduct_le_iff`).
-/

open Complex MeasureTheory Set Filter Topology Matrix
open scoped Real
open Zeta23

namespace RHTower.WeilMarkovPole

noncomputable section

/-! ### The pieces of the Markov form -/

/-- The prime jump weight `Λ(n)/√n`. -/
def primeJumpWeight (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n

theorem primeJumpWeight_nonneg (n : ℕ) : 0 ≤ primeJumpWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- The archimedean jump energy `∫_0^∞ ω(x) ‖g − g(· + x)‖² dx`. -/
def levyJump (g : ℝ → ℝ) : ℝ :=
  (∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2)).toReal

/-- The prime jump energy `Σ_{2 ≤ n ≤ N} Λ(n) n^{-1/2} ‖g − g(· + log n)‖²`. -/
def primeJump (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, primeJumpWeight n * ∫ u, (g u - g (u + Real.log n)) ^ 2

/-- The creation potential `Ω(0) − 2 Σ_{2 ≤ n ≤ N} Λ(n)/√n`. -/
def creationPotential (N : ℕ) : ℝ :=
  EF.gammaBracket 0 - 2 * ∑ n ∈ Finset.Icc 2 N, primeJumpWeight n

/-- The Markov form `M_N(g) = V_N ‖g‖² + J(g)`. -/
def markovForm (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  creationPotential N * (∫ u, g u ^ 2) + levyJump g + primeJump N g

/-- `⟨2 cosh(u/2), g⟩`. -/
def coshPairing (g : ℝ → ℝ) : ℝ := ∫ u, g u * (2 * Real.cosh (u / 2))

/-- `⟨2 sinh(u/2), g⟩`. -/
def sinhPairing (g : ℝ → ℝ) : ℝ := ∫ u, g u * (2 * Real.sinh (u / 2))

/-! ### Integrability bookkeeping -/

theorem hasCompactSupport_comp_add {g : ℝ → ℝ} (hgc : HasCompactSupport g) (y : ℝ) :
    HasCompactSupport fun u => g (u + y) :=
  hgc.comp_homeomorph (Homeomorph.addRight y)

theorem integrable_mul_shift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (y : ℝ) :
    Integrable fun u => g u * g (u + y) :=
  (hg.mul (hg.comp (continuous_add_const y))).integrable_of_hasCompactSupport (hgc.mul_right)

theorem integrable_sq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable fun u => g u ^ 2 :=
  (hg.pow 2).integrable_of_hasCompactSupport (by
    simpa [sq] using hgc.mul_right (f' := g))

/-! ### The exact splitting -/

/-- The autocorrelation of a real test at `±log n`. -/
theorem weilTest_ofReal_log (g : ℝ → ℝ) (n : ℕ) :
    EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (Real.log n) =
        ((∫ u, g u * g (u + Real.log n) : ℝ) : ℂ) ∧
      EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (-Real.log n) =
        ((∫ u, g u * g (u + Real.log n) : ℝ) : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [RHTower.weilTest_ofReal_eq]
    congr 1
    have := integral_add_right_eq_self (μ := volume) (fun t => g t * g (t - Real.log n)) (Real.log n)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [add_sub_cancel_right]
    ring
  · rw [RHTower.weilTest_ofReal_eq]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_neg_eq_add]

/-- Some level `N` makes every node beyond `N` invisible to `g`. -/
theorem exists_level {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0 := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hb : ∀ u, g u ≠ 0 → |u| ≤ R := fun u hu => by
    have := hR (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  refine ⟨⌈Real.exp (R + R)⌉₊, fun n hn u => ?_⟩
  have hn' : Real.exp (R + R) < n := Nat.lt_of_ceil_lt hn
  have hpos : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
  have hlog : R + R < Real.log n := (Real.lt_log_iff_exp_lt hpos).mpr hn'
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  have a1 := hb _ h1
  have a2 := hb _ h2
  rw [abs_le] at a1 a2
  linarith [a1.1, a2.2]

theorem pole_eq_pairings (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    2 * ((∫ u, g u * Real.exp (u / 2)) * ∫ u, g u * Real.exp (-u / 2)) =
      coshPairing g ^ 2 / 2 - sinhPairing g ^ 2 / 2 := by
  have hp : Integrable fun u => g u * Real.exp (u / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hm : Integrable fun u => g u * Real.exp (-u / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hc : coshPairing g = (∫ u, g u * Real.exp (u / 2)) + ∫ u, g u * Real.exp (-u / 2) := by
    rw [coshPairing, ← integral_add hp hm]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [Real.cosh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  have hs : sinhPairing g = (∫ u, g u * Real.exp (u / 2)) - ∫ u, g u * Real.exp (-u / 2) := by
    rw [sinhPairing, ← integral_sub hp hm]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [Real.sinh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  rw [hc, hs]
  ring

/-- **Exact splitting** `W(g) = M_N(g) + ½⟨c, g⟩² − ½⟨s, g⟩²`. -/
theorem weil_eq_markovForm_add_pole {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re =
      markovForm N g + coshPairing g ^ 2 / 2 - sinhPairing g ^ 2 / 2 := by
  set k := EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) with hk
  have hc := hg.continuous
  set ρ : ℕ → ℝ := fun n => ∫ u, g u * g (u + Real.log n) with hρ
  have hρ0 : ∀ n, N < n → ρ n = 0 := fun n hn => by
    simp only [hρ]
    rw [show (fun u => g u * g (u + Real.log n)) = fun _ => (0 : ℝ) from funext (hN n hn),
      integral_zero]
  -- the prime sum is finite
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))) =
      ((∑ n ∈ Finset.Icc 2 N, primeJumpWeight n * (2 * ρ n) : ℝ) : ℂ) := by
    have hterm : ∀ n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) =
        (((if 2 ≤ n then primeJumpWeight n else 0) * (2 * ρ n) : ℝ) : ℂ) := fun n => by
      obtain ⟨e1, e2⟩ := weilTest_ofReal_log g n
      rw [hk, e1, e2, primeJumpWeight]
      push_cast
      ring
    simp_rw [hterm]
    rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [hρ0 n (by omega), mul_zero, mul_zero, Complex.ofReal_zero])]
    rw [← Complex.ofReal_sum]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun n => 2 ≤ n)]
    have hz : ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ 2 ≤ n),
        (if 2 ≤ n then primeJumpWeight n else 0) * (2 * ρ n) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Finset.mem_filter.mp hn).2, zero_mul]
    rw [hz, add_zero]
    have hset : (Finset.range (N + 1)).filter (fun n => 2 ≤ n) = Finset.Icc 2 N := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [hset]
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_Icc.mp hn).1]
  have hW : (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k).re =
      WeilOneSided.weilArchRe k - ∑ n ∈ Finset.Icc 2 N, primeJumpWeight n * (2 * ρ n) := by
    rw [weilFullFunctional, WeilOneSided.weilArchRe, hsum]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    ring
  rw [hW, hk, WeilLevyPole.weilArchRe_eq_levy_pole hg hgc,
    WeilLevyPole.integral_prod_cosh_eq hgc hc, markovForm, creationPotential, primeJump]
  have h0 : ArchimedeanAnomaly.autocorr g 0 = ∫ u, g u ^ 2 := by
    unfold ArchimedeanAnomaly.autocorr; congr 1; funext u; rw [add_zero, sq]
  have hprime : ∀ n, primeJumpWeight n * (2 * ρ n) =
      2 * primeJumpWeight n * (∫ u, g u ^ 2) -
        primeJumpWeight n * ∫ u, (g u - g (u + Real.log n)) ^ 2 := fun n => by
    rw [ArchimedeanAnomaly.integral_sub_shift_sq hgc hc, h0]
    simp only [hρ, ArchimedeanAnomaly.autocorr]
    ring
  simp_rw [hprime]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, levyJump]
  have hpole := pole_eq_pairings g hc hgc
  linarith [hpole]

/-! ### Markov property of `M_N`, anti-Markov property of the pole -/

theorem lintegral_levy_ne_top {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2) ≠ ⊤ := by
  set F : ℝ → ℂ := fun u => (g u : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hg.continuous
  have hFcs : HasCompactSupport F := hgc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hg
  have hF1 : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  have hFL2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  have hk : ∀ z : ℂ, paperFT (EF.weilTest F F) z = paperFT F z * (starRingEnd ℂ) (paperFT F
      ((starRingEnd ℂ) z)) :=
    EF.paperFT_weilTest hFc hFc hFcs hFcs
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [hk, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFcs hF2 hFcs
  have hintR : Integrable fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hreal, Complex.ofReal_re]
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) *
      ‖FourierTransform.fourier F ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * Real.pi)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have h := lintegral_archLevyDirichlet_ne_top hF1 hFL2 hint
  have hlev : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖F u - F (u + x)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2) := by
    refine lintegral_congr fun x => ?_
    congr 3
    funext u
    simp only [hFdef]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rwa [hlev] at h

theorem sq_abs_sub_abs_le (a b : ℝ) : (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs (a - b), ← sq_abs (|a| - |b|)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub a b) 2

theorem integrable_sub_shift_sq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y : ℝ) : Integrable fun u => (g u - g (u + y)) ^ 2 := by
  have h1 := integrable_sq hg hgc
  have h2 := integrable_mul_shift hg hgc y
  have h3 : Integrable fun u => g (u + y) ^ 2 :=
    integrable_sq (hg.comp (continuous_add_const y)) (hasCompactSupport_comp_add hgc y)
  refine ((h1.sub (h2.const_mul 2)).add h3).congr (ae_of_all _ fun u => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem integral_abs_sub_shift_sq_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y : ℝ) : ∫ u, (|g u| - |g (u + y)|) ^ 2 ≤ ∫ u, (g u - g (u + y)) ^ 2 := by
  have iD := integrable_sub_shift_sq hg hgc y
  have hcA : Continuous fun u => (|g u| - |g (u + y)|) ^ 2 := by fun_prop
  have iA : Integrable fun u => (|g u| - |g (u + y)|) ^ 2 :=
    iD.mono' hcA.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_abs_sub_abs_le _ _)
  exact integral_mono iA iD fun u => sq_abs_sub_abs_le _ _

/-- Normal contraction lowers the archimedean jump energy. -/
theorem levyJump_abs_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    levyJump (fun u => |g u|) ≤ levyJump g := by
  refine ENNReal.toReal_mono (lintegral_levy_ne_top hg hgc) (setLIntegral_mono' measurableSet_Ioi
    fun x hx => ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (integral_abs_sub_shift_sq_le hg.continuous hgc x)
    (archLevyDensity_pos hx).le

/-- Normal contraction lowers the prime jump energy. -/
theorem primeJump_abs_le (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    primeJump N (fun u => |g u|) ≤ primeJump N g :=
  Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
    (integral_abs_sub_shift_sq_le hg hgc _) (primeJumpWeight_nonneg n)

/-- **The Markov form is Markovian**: `M_N(|g|) ≤ M_N(g)`. -/
theorem markovForm_abs_le (N : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    markovForm N (fun u => |g u|) ≤ markovForm N g := by
  have hsq : ∫ u, |g u| ^ 2 = ∫ u, g u ^ 2 := by simp_rw [sq_abs]
  rw [markovForm, markovForm, hsq]
  linarith [levyJump_abs_le hg hgc, primeJump_abs_le N hg.continuous hgc]

/-- **The pole is anti-Markovian**: normal contraction raises `½⟨c, g⟩² − ½⟨s, g⟩²`. -/
theorem pole_le_pole_abs {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    coshPairing g ^ 2 / 2 - sinhPairing g ^ 2 / 2 ≤
      coshPairing (fun u => |g u|) ^ 2 / 2 - sinhPairing (fun u => |g u|) ^ 2 / 2 := by
  rw [← pole_eq_pairings g hg hgc, ← pole_eq_pairings _ hg.abs (hgc.comp_left abs_zero)]
  have hle : ∀ c : ℝ, |∫ u, g u * Real.exp (c * u)| ≤ ∫ u, |g u| * Real.exp (c * u) := fun c => by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have ha := hle (1 / 2)
  have hb := hle (-1 / 2)
  have e1 : ∀ h : ℝ → ℝ, (fun u => h u * Real.exp (1 / 2 * u)) = fun u => h u * Real.exp (u / 2) :=
    fun h => funext fun u => by rw [show 1 / 2 * u = u / 2 by ring]
  have e2 : ∀ h : ℝ → ℝ, (fun u => h u * Real.exp (-1 / 2 * u)) = fun u => h u * Real.exp (-u / 2) :=
    fun h => funext fun u => by rw [show -1 / 2 * u = -u / 2 by ring]
  rw [e1, e1 (fun u => |g u|)] at ha
  rw [e2, e2 (fun u => |g u|)] at hb
  have hab := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  rw [← abs_mul] at hab
  linarith [le_abs_self ((∫ u, g u * Real.exp (u / 2)) * ∫ u, g u * Real.exp (-u / 2))]

/-! ### The capacity criterion -/

/-- **Rank-one capacity form of positivity.**  `W ≥ 0` on a family of tests of level `N` iff the
sinh pairing is dominated by the Markov form plus the cosh direction. -/
theorem weil_nonneg_iff_sinhCapacity {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re ↔
      sinhPairing g ^ 2 ≤ 2 * (markovForm N g + coshPairing g ^ 2 / 2) := by
  rw [weil_eq_markovForm_add_pole hg hgc hN]
  constructor <;> intro h <;> linarith

/-- **RH is the sinh-capacity bound at every level.** -/
theorem riemannHypothesis_iff_sinhCapacity :
    RiemannHypothesis ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ N : ℕ,
      (∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) →
      sinhPairing g ^ 2 ≤ 2 * (markovForm N g + coshPairing g ^ 2 / 2) := by
  rw [WeilSpectral.riemannHypothesis_iff_real_weilPositive]
  constructor
  · intro h g hg hgc N hN
    exact (weil_nonneg_iff_sinhCapacity hg hgc hN).mp (h g hg hgc)
  · intro h g hg hgc
    obtain ⟨N, hN⟩ := exists_level hgc
    exact (weil_nonneg_iff_sinhCapacity hg hgc hN).mpr (h g hg hgc N hN)

/-- The Markov form plus the cosh direction is nonnegative wherever the sinh-capacity bound holds. -/
theorem markovForm_add_cosh_nonneg_of_sinhCapacity {N : ℕ} {g : ℝ → ℝ}
    (h : sinhPairing g ^ 2 ≤ 2 * (markovForm N g + coshPairing g ^ 2 / 2)) :
    0 ≤ markovForm N g + coshPairing g ^ 2 / 2 := by
  nlinarith [sq_nonneg (sinhPairing g)]

/-- **Finite-dimensional capacity.**  For a positive-definite `Q`,
`(s·x)² ≤ 2 x·Qx` for all `x` iff `s·Q⁻¹s ≤ 2`. -/
theorem forall_sq_dotProduct_le_iff {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m ℝ}
    (hQ : Q.PosDef) (s : m → ℝ) :
    (∀ x : m → ℝ, (s ⬝ᵥ x) ^ 2 ≤ 2 * (x ⬝ᵥ Q *ᵥ x)) ↔ s ⬝ᵥ Q⁻¹ *ᵥ s ≤ 2 := by
  have hdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hsymm : Qᵀ = Q := by
    have := hQ.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set y := Q⁻¹ *ᵥ s with hy
  have hQy : Q *ᵥ y = s := by rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  -- `y·(Qx) = s·x`
  have hswap : ∀ x : m → ℝ, y ⬝ᵥ (Q *ᵥ x) = s ⬝ᵥ x := fun x => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hQy]
  have hpsd : ∀ x : m → ℝ, 0 ≤ x ⬝ᵥ Q *ᵥ x := fun x => by
    have := hQ.posSemidef.dotProduct_mulVec_nonneg x
    simpa using this
  constructor
  · intro h
    have h1 := h y
    rw [hswap y] at h1
    have hσ : s ⬝ᵥ y = y ⬝ᵥ s := dotProduct_comm _ _
    have h0 : 0 ≤ y ⬝ᵥ Q *ᵥ y := hpsd y
    rw [hswap y] at h0
    nlinarith [h1, h0]
  · intro h x
    -- Cauchy–Schwarz in the `Q` inner product
    have hquad : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ Q *ᵥ y) * (t * t) + 2 * (y ⬝ᵥ Q *ᵥ x) * t + x ⬝ᵥ Q *ᵥ x := by
      intro t
      have := hpsd (x + t • y)
      have hyx : x ⬝ᵥ Q *ᵥ y = y ⬝ᵥ Q *ᵥ x := by
        rw [hswap x, hQy, dotProduct_comm]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      rw [hyx] at this
      linarith
    have hd := discrim_le_zero hquad
    rw [discrim, hswap x, hswap y] at hd
    have hx0 := hpsd x
    nlinarith [hd, hx0, mul_le_mul_of_nonneg_right h hx0]

end

end RHTower.WeilMarkovPole
