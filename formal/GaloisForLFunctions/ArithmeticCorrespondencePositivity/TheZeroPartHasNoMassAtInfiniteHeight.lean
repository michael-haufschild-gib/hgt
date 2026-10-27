import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros
import GaloisForLFunctions.RHTower.CramerZeroSumMeanSquare
import GaloisForLFunctions.RHTower.CausalLaplacePlancherel

/-!
# The zero part has no mass at infinite height

Under RH the zero part of the prime-error symbol on the line `Re s = ½ + c` is the Cauchy
transform `P_c(y) = Σ'_q b_q/(c + i(y − γ_q))`, `b_q = −1/ρ_q`, of the zeros
(`ThePrimeErrorSymbolSplitsAtTheZeros`). Its Abel mean square has no mass at infinite height:

* **Finite zero sums** (`integral_norm_sq_zeroSymbol`). For a finite set `F` of copies,
  `P_c^F` is the boundary Laplace transform of the causal wave
  `1_{u > 0} e^{−cu} Σ_{q ∈ F} b_q e^{iγ_q u}`, so
  `∫ ‖P_c^F‖² dy = 2π ∫_0^∞ e^{−2cu} ‖Σ_F b_q e^{iγ_q u}‖² du`.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open _root_.RHTower (XiZeroCopy laplaceBoundary zeroOrdinate)

/-- The residue weight `b_q = −1/ρ_q`. -/
def zeroWeight (q : XiZeroCopy) : ℂ := -(1 / (q.1 : ℂ))

/-- The causal damped pole wave `1_{u > 0} e^{(−c + iγ)u}`. -/
def poleWave (c γ : ℝ) : ℝ → ℂ :=
  Set.indicator (Ioi 0) fun u => Complex.exp ((-(c : ℂ) + (γ : ℂ) * I) * u)

/-- The zero wave `S_F(u) = Σ_{q ∈ F} b_q e^{iγ_q u}`. -/
def zeroWave (F : Finset XiZeroCopy) (u : ℝ) : ℂ :=
  ∑ q ∈ F, zeroWeight q * Complex.exp ((zeroOrdinate q : ℂ) * I * u)

/-- The causal damped zero wave `Σ_{q ∈ F} b_q 1_{u > 0} e^{(−c + iγ_q)u}`. -/
def causalWave (F : Finset XiZeroCopy) (c : ℝ) (u : ℝ) : ℂ :=
  ∑ q ∈ F, zeroWeight q * poleWave c (zeroOrdinate q) u

/-- The finite zero symbol `Σ_{q ∈ F} b_q/(c + i(y − γ_q))`. -/
def zeroSymbol (F : Finset XiZeroCopy) (c y : ℝ) : ℂ :=
  ∑ q ∈ F, zeroWeight q / ((c : ℂ) + ((y - zeroOrdinate q : ℝ) : ℂ) * I)

theorem integrable_poleWave {c : ℝ} (hc : 0 < c) (γ : ℝ) : Integrable (poleWave c γ) :=
  (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0)

theorem norm_poleWave_sq (c γ u : ℝ) :
    ‖poleWave c γ u‖ ^ 2 = Set.indicator (Ioi 0) (fun u => Real.exp (-(2 * c) * u)) u := by
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [poleWave, indicator_of_mem hu, indicator_of_mem hu, Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp
    ring
  · rw [poleWave, indicator_of_notMem hu, indicator_of_notMem hu]
    simp

theorem memLp_poleWave {c : ℝ} (hc : 0 < c) (γ : ℝ) : MemLp (poleWave c γ) 2 := by
  refine (memLp_two_iff_integrable_sq_norm (integrable_poleWave hc γ).aestronglyMeasurable).mpr ?_
  simp_rw [norm_poleWave_sq]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr
    (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < 2 * c) |>.congr_fun
      (fun u _ => by ring_nf) measurableSet_Ioi)

/-- `∫_0^∞ e^{−iyu} e^{(−c + iγ)u} du = 1/(c + i(y − γ))`. -/
theorem laplaceBoundary_poleWave {c : ℝ} (hc : 0 < c) (γ y : ℝ) :
    laplaceBoundary (poleWave c γ) y = 1 / ((c : ℂ) + ((y - γ : ℝ) : ℂ) * I) := by
  rw [laplaceBoundary]
  have hind : ∀ u : ℝ, Complex.exp (-((y : ℂ) * I) * (u : ℂ)) * poleWave c γ u =
      Set.indicator (Ioi 0)
        (fun u : ℝ => Complex.exp ((-(c : ℂ) + ((γ - y : ℝ) : ℂ) * I) * u)) u := by
    intro u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [poleWave, indicator_of_mem hu, indicator_of_mem hu, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [poleWave, indicator_of_notMem hu, indicator_of_notMem hu, mul_zero]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ioi,
    integral_exp_mul_complex_Ioi (by simp; linarith) 0]
  have hne : ((c : ℂ) + ((y - γ : ℝ) : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    show (-(c : ℂ) + ((γ - y : ℝ) : ℂ) * I) = -((c : ℂ) + ((y - γ : ℝ) : ℂ) * I) by
      push_cast; ring, div_neg, neg_div, neg_neg]

theorem integrable_causalWave {c : ℝ} (hc : 0 < c) (F : Finset XiZeroCopy) :
    Integrable (causalWave F c) :=
  integrable_finsetSum F fun _ _ => (integrable_poleWave hc _).const_mul _

theorem memLp_causalWave {c : ℝ} (hc : 0 < c) (F : Finset XiZeroCopy) :
    MemLp (causalWave F c) 2 :=
  memLp_finsetSum F fun _ _ => (memLp_poleWave hc _).const_mul _

/-- The finite zero symbol is the boundary Laplace transform of the causal zero wave. -/
theorem laplaceBoundary_causalWave {c : ℝ} (hc : 0 < c) (F : Finset XiZeroCopy) (y : ℝ) :
    laplaceBoundary (causalWave F c) y = zeroSymbol F c y := by
  rw [laplaceBoundary, zeroSymbol]
  simp_rw [causalWave, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have := laplaceBoundary_poleWave hc (zeroOrdinate q) y
    rw [laplaceBoundary] at this
    simp_rw [mul_left_comm _ (zeroWeight q)]
    rw [integral_const_mul, this]
    ring
  · intro q _
    exact ((integrable_poleWave hc _).const_mul _).bdd_mul (c := 1)
      (by fun_prop) (Eventually.of_forall fun u => by
        rw [Complex.norm_exp]; simp)

/-- On `u > 0` the causal wave is `e^{−cu} S_F(u)`. -/
theorem causalWave_eq (F : Finset XiZeroCopy) (c u : ℝ) :
    causalWave F c u =
      Set.indicator (Ioi 0) (fun u : ℝ => Complex.exp (-(c : ℂ) * u) * zeroWave F u) u := by
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, causalWave, zeroWave, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [poleWave, indicator_of_mem hu, mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  · rw [indicator_of_notMem hu, causalWave]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [poleWave, indicator_of_notMem hu, mul_zero]

/-- **Plancherel for finite zero sums.**
`∫ ‖P_c^F(y)‖² dy = 2π ∫_0^∞ e^{−2cu} ‖S_F(u)‖² du`. -/
theorem integral_norm_sq_zeroSymbol {c : ℝ} (hc : 0 < c) (F : Finset XiZeroCopy) :
    ∫ y : ℝ, ‖zeroSymbol F c y‖ ^ 2 =
      2 * Real.pi * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave F u‖ ^ 2 := by
  have h := _root_.RHTower.integral_norm_sq_laplaceBoundary (integrable_causalWave hc F)
    (memLp_causalWave hc F)
  simp_rw [laplaceBoundary_causalWave hc F] at h
  rw [h]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [causalWave_eq]
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu, norm_mul, mul_pow, Complex.norm_exp,
      ← Real.exp_nat_mul]
    congr 2
    simp
    ring
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]
    simp

/-! ### The high shells carry a vanishing Abel energy -/

theorem norm_zeroWeight_le (q : XiZeroCopy) : ‖zeroWeight q‖ ≤ 1 / |zeroOrdinate q| := by
  have h4 := _root_.RHTower.four_lt_abs_zeroOrdinate q
  rw [zeroWeight, norm_neg, norm_div, norm_one]
  exact one_div_le_one_div_of_le (by linarith) (Complex.abs_im_le_norm _)

theorem norm_zeroWave_le (F : Finset XiZeroCopy) (u : ℝ) :
    ‖zeroWave F u‖ ≤ ∑ q ∈ F, ‖zeroWeight q‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Under RH, `(e^u)^ρ = e^{u/2} e^{iγu}`. -/
theorem ofReal_exp_cpow (hRH : RiemannHypothesis) (q : XiZeroCopy) (u : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ (q.1 : ℂ) =
      ((Real.exp (u / 2) : ℝ) : ℂ) * Complex.exp ((zeroOrdinate q : ℂ) * I * u) := by
  have hre := _root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im (q.1 : ℂ)]
  rw [hre, zeroOrdinate]
  push_cast
  ring

/-- **Block energy of the high shells.** Under RH, for a finite set `G` of copies with
`|γ| ≥ 2^{k₀}`, `∫_a^{a + log 2} e^{−u} ‖S_G(u)‖² du ≤ C_tail τ(k₀) e^{−a}`. -/
theorem block_energy_le (hRH : RiemannHypothesis) {k₀ : ℕ} {G : Finset XiZeroCopy}
    (hG : ∀ q ∈ G, (2 : ℝ) ^ k₀ ≤ |zeroOrdinate q|) (a : ℝ) :
    ∫ u in a..a + Real.log 2, Real.exp (-u) * ‖zeroWave G u‖ ^ 2 ≤
      _root_.RHTower.cramerTailConstant * _root_.RHTower.cramerShellTail k₀ * Real.exp (-a) := by
  set g : ℝ → ℝ := fun x => ‖∑ q ∈ G, zeroWeight q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 with hg
  have hcomp : ∀ u : ℝ, (g ∘ Real.exp) u * Real.exp u = Real.exp (-u) * ‖zeroWave G u‖ ^ 2 := by
    intro u
    have hsum : (∑ q ∈ G, zeroWeight q * ((Real.exp u : ℝ) : ℂ) ^ (q.1 : ℂ)) =
        ((Real.exp (u / 2) : ℝ) : ℂ) * zeroWave G u := by
      rw [zeroWave, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ofReal_exp_cpow hRH]
      ring
    have hE : Real.exp u = Real.exp (u / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hE' : Real.exp (-u) = 1 / Real.exp (u / 2) ^ 2 := by rw [Real.exp_neg, hE, one_div]
    simp only [Function.comp_apply, hg]
    rw [hsum, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      hE', hE]
    have := Real.exp_pos (u / 2)
    field_simp
  have hgcont : ContinuousOn g (Real.exp '' Set.uIcc a (a + Real.log 2)) := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := hx
    have hx0 : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div (ContinuousAt.pow (ContinuousAt.norm ?_) 2)
      (continuousAt_id.pow 3) (pow_ne_zero 3 hx0)
    exact tendsto_finsetSum _ fun q _ =>
      continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0))
  have hcv := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := a + Real.log 2)
    (f := Real.exp) (f' := Real.exp) (g := g) (fun x _ => Real.hasDerivAt_exp x)
    Real.continuous_exp.continuousOn hgcont
  simp_rw [hcomp] at hcv
  rw [hcv, Real.exp_add, Real.exp_log two_pos, mul_comm (Real.exp a) 2]
  have h := _root_.RHTower.cramer_finite_zero_energy_tail hRH (Real.exp_pos a) zero_le_one G
    zeroWeight (fun q _ => norm_zeroWeight_le q) k₀ hG
  refine h.trans (le_of_eq ?_)
  rw [one_pow, mul_one, Real.exp_neg]
  ring

theorem continuous_zeroWave (F : Finset XiZeroCopy) : Continuous (zeroWave F) :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (by fun_prop)

/-- **The Abel energy of the high shells.** Under RH, for a finite set `G` of copies with
`|γ| ≥ 2^{k₀}` and `0 < c ≤ ½`, `2c ∫_0^∞ e^{−2cu} ‖S_G(u)‖² du ≤ 6 C_tail τ(k₀)`: summing the
block bounds over `[j log 2, (j + 1) log 2]` against `e^{−2cu}`. -/
theorem abel_tail_le (hRH : RiemannHypothesis) {k₀ : ℕ} {G : Finset XiZeroCopy}
    (hG : ∀ q ∈ G, (2 : ℝ) ^ k₀ ≤ |zeroOrdinate q|) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave G u‖ ^ 2 ≤
      6 * (_root_.RHTower.cramerTailConstant * _root_.RHTower.cramerShellTail k₀) := by
  set T₀ := _root_.RHTower.cramerTailConstant * _root_.RHTower.cramerShellTail k₀ with hT₀def
  have hT₀ : 0 ≤ T₀ := mul_nonneg _root_.RHTower.cramerTailConstant_nonneg
    (_root_.RHTower.cramerShellTail_nonneg k₀)
  have hℓ : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hℓ2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set f : ℝ → ℝ := fun u => Real.exp (-(2 * c) * u) * ‖zeroWave G u‖ ^ 2 with hf
  have hcont : Continuous f := by
    have := continuous_zeroWave G
    simp only [hf]
    fun_prop
  have hint : IntegrableOn f (Ioi 0) := by
    refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < 2 * c))).const_mul
      ((∑ q ∈ G, ‖zeroWeight q‖) ^ 2)) hcont.aestronglyMeasurable.restrict
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity), mul_comm ((∑ q ∈ G, ‖zeroWeight q‖) ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_zeroWave_le G u) 2) (Real.exp_pos _).le
  set r := Real.exp (-(2 * c * Real.log 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  -- one block
  have hblock : ∀ j : ℕ, ∫ u in ((j : ℝ) * Real.log 2)..(((j : ℝ) + 1) * Real.log 2), f u ≤
      2 * T₀ * r ^ j := by
    intro j
    have hb := block_energy_le hRH hG ((j : ℝ) * Real.log 2)
    rw [show (j : ℝ) * Real.log 2 + Real.log 2 = ((j : ℝ) + 1) * Real.log 2 by ring] at hb
    have hjj : (j : ℝ) * Real.log 2 ≤ ((j : ℝ) + 1) * Real.log 2 := by nlinarith
    have hgc : Continuous fun u : ℝ => Real.exp (-u) * ‖zeroWave G u‖ ^ 2 := by
      have := continuous_zeroWave G; fun_prop
    have hle : ∀ u ∈ Icc ((j : ℝ) * Real.log 2) (((j : ℝ) + 1) * Real.log 2),
        f u ≤ Real.exp ((1 - 2 * c) * (((j : ℝ) + 1) * Real.log 2)) *
          (Real.exp (-u) * ‖zeroWave G u‖ ^ 2) := by
      intro u hu
      simp only [hf]
      rw [← mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
      nlinarith [hu.2]
    calc ∫ u in ((j : ℝ) * Real.log 2)..(((j : ℝ) + 1) * Real.log 2), f u
        ≤ ∫ u in ((j : ℝ) * Real.log 2)..(((j : ℝ) + 1) * Real.log 2),
            Real.exp ((1 - 2 * c) * (((j : ℝ) + 1) * Real.log 2)) *
              (Real.exp (-u) * ‖zeroWave G u‖ ^ 2) :=
          intervalIntegral.integral_mono_on hjj (hcont.intervalIntegrable _ _)
            ((continuous_const.mul hgc).intervalIntegrable _ _) hle
      _ = Real.exp ((1 - 2 * c) * (((j : ℝ) + 1) * Real.log 2)) *
            ∫ u in ((j : ℝ) * Real.log 2)..(((j : ℝ) + 1) * Real.log 2),
              Real.exp (-u) * ‖zeroWave G u‖ ^ 2 := intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp ((1 - 2 * c) * (((j : ℝ) + 1) * Real.log 2)) *
            (T₀ * Real.exp (-((j : ℝ) * Real.log 2))) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = T₀ * Real.exp ((1 - 2 * c) * Real.log 2) * r ^ j := by
          rw [hr, ← Real.exp_nat_mul, hT₀def]
          have hE : Real.exp ((1 - 2 * c) * (((j : ℝ) + 1) * Real.log 2)) *
              Real.exp (-((j : ℝ) * Real.log 2)) = Real.exp ((1 - 2 * c) * Real.log 2) *
                Real.exp ((j : ℝ) * -(2 * c * Real.log 2)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (_root_.RHTower.cramerTailConstant *
            _root_.RHTower.cramerShellTail k₀) * hE
      _ ≤ 2 * T₀ * r ^ j := by
          have : Real.exp ((1 - 2 * c) * Real.log 2) ≤ 2 := by
            calc Real.exp ((1 - 2 * c) * Real.log 2) ≤ Real.exp (Real.log 2) :=
                  Real.exp_le_exp.mpr (by nlinarith)
              _ = 2 := Real.exp_log two_pos
          have hrj : 0 ≤ r ^ j := pow_nonneg hr0 j
          calc T₀ * Real.exp ((1 - 2 * c) * Real.log 2) * r ^ j ≤ T₀ * 2 * r ^ j := by gcongr
            _ = 2 * T₀ * r ^ j := by ring
  -- all blocks up to `n log 2`
  have hsum : ∀ n : ℕ, ∫ u in (0 : ℝ)..((n : ℝ) * Real.log 2), f u ≤ 2 * T₀ / (1 - r) := by
    intro n
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun j : ℕ => (j : ℝ) * Real.log 2) (f := f) (n := n)
      (fun k _ => hcont.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_succ] at hadj
    rw [← hadj]
    calc ∑ k ∈ Finset.range n, ∫ u in ((k : ℝ) * Real.log 2)..(((k : ℝ) + 1) * Real.log 2), f u
        ≤ ∑ k ∈ Finset.range n, 2 * T₀ * r ^ k := Finset.sum_le_sum fun k _ => hblock k
      _ = 2 * T₀ * ∑ k ∈ Finset.range n, r ^ k := by rw [Finset.mul_sum]
      _ ≤ 2 * T₀ * (1 - r)⁻¹ := by
          gcongr
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun _ _ => pow_nonneg hr0 _
      _ = 2 * T₀ / (1 - r) := by rw [div_eq_mul_inv]
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0 : ℝ) < Real.log 2))
  have hI : ∫ u in Ioi (0 : ℝ), f u ≤ 2 * T₀ / (1 - r) := le_of_tendsto' hlim hsum
  -- `1 − r ≥ x/(1 + x)` at `x = 2c log 2`
  have hx := Real.add_one_le_exp (2 * c * Real.log 2)
  have hrx : r * (1 + 2 * c * Real.log 2) ≤ 1 := by
    rw [hr, Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  have h1r : 0 < 1 - r := by linarith
  have hkey : 4 * c ≤ 6 * (1 - r) := by
    have hx0 : 0 < 1 + 2 * c * Real.log 2 := by nlinarith
    have h1 : 2 * c * Real.log 2 ≤ (1 - r) * (1 + 2 * c * Real.log 2) := by nlinarith
    have h2 : 1 + 2 * c * Real.log 2 ≤ 3 * Real.log 2 := by nlinarith
    have h3 : 4 * c * (1 + 2 * c * Real.log 2) ≤ 6 * (1 - r) * (1 + 2 * c * Real.log 2) := by
      nlinarith
    exact le_of_mul_le_mul_right h3 hx0
  calc 2 * c * ∫ u in Ioi (0 : ℝ), f u ≤ 2 * c * (2 * T₀ / (1 - r)) :=
        mul_le_mul_of_nonneg_left hI (by linarith)
    _ = (4 * c) * T₀ / (1 - r) := by ring
    _ ≤ 6 * (1 - r) * T₀ / (1 - r) := by gcongr
    _ = 6 * T₀ := by field_simp

/-! ### Finitely many zeros: the Abel mean is the diagonal -/

/-- `‖S_F(u)‖² = Σ_{q,q'} b_q b̄_{q'} e^{i(γ_q − γ_{q'})u}`. -/
theorem ofReal_norm_zeroWave_sq (F : Finset XiZeroCopy) (u : ℝ) :
    ((‖zeroWave F u‖ ^ 2 : ℝ) : ℂ) = ∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
      Complex.exp (((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I * u) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', zeroWave, map_sum, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : starRingEnd ℂ ((zeroOrdinate p.2 : ℂ) * I * (u : ℂ)) =
      -((zeroOrdinate p.2 : ℂ) * I * (u : ℂ)) := by
    simp [Complex.conj_ofReal]
  rw [this]
  have hE : Complex.exp ((zeroOrdinate p.1 : ℂ) * I * u) * Complex.exp (-((zeroOrdinate p.2 : ℂ) * I * u)) =
      Complex.exp (((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I * u) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hE]
  ring

/-- `e^{−2cu} e^{iΔu} = e^{(−2c + iΔ)u}`. -/
theorem ofReal_exp_mul_exp (c Δ u : ℝ) :
    ((Real.exp (-(2 * c) * u) : ℝ) : ℂ) * Complex.exp ((Δ : ℂ) * I * u) =
      Complex.exp ((-(2 * (c : ℂ)) + (Δ : ℂ) * I) * u) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∫_0^∞ e^{−2cu} e^{iΔu} du = 1/(2c − iΔ)`. -/
theorem integral_exp_damped {c : ℝ} (hc : 0 < c) (Δ : ℝ) :
    ∫ u in Ioi (0 : ℝ), ((Real.exp (-(2 * c) * u) : ℝ) : ℂ) * Complex.exp ((Δ : ℂ) * I * u) =
      1 / (2 * (c : ℂ) - (Δ : ℂ) * I) := by
  simp_rw [ofReal_exp_mul_exp]
  rw [integral_exp_mul_complex_Ioi (by simp; linarith) 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, show (-(2 * (c : ℂ)) + (Δ : ℂ) * I) = -(2 * (c : ℂ) - (Δ : ℂ) * I) by ring,
    div_neg, neg_div, neg_neg]

theorem integrableOn_exp_damped {c : ℝ} (hc : 0 < c) (Δ : ℝ) :
    IntegrableOn (fun u : ℝ => ((Real.exp (-(2 * c) * u) : ℝ) : ℂ) * Complex.exp ((Δ : ℂ) * I * u))
      (Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi (a := -(2 * (c : ℂ)) + (Δ : ℂ) * I)
    (by simp; linarith) 0).congr_fun (fun u _ => (ofReal_exp_mul_exp c Δ u).symm) measurableSet_Ioi

/-- The Abel mean of finitely many zeros with distinct ordinates is the diagonal:
`2c ∫_0^∞ e^{−2cu} ‖S_F(u)‖² du → Σ_{q ∈ F} ‖b_q‖²` as `c ↓ 0`. -/
theorem tendsto_abel_head (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, ∀ q' ∈ F, zeroOrdinate q = zeroOrdinate q' → q = q') :
    Tendsto (fun c : ℝ => 2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave F u‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∑ q ∈ F, ‖zeroWeight q‖ ^ 2)) := by
  -- the complex form
  have hform : ∀ c : ℝ, 0 < c →
      (((2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave F u‖ ^ 2 : ℝ)) : ℂ) =
        ∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
          (2 * (c : ℂ) / (2 * (c : ℂ) - ((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I)) := by
    intro c hc
    rw [Complex.ofReal_mul, ← integral_complex_ofReal]
    have hpt : ∀ u : ℝ, ((Real.exp (-(2 * c) * u) * ‖zeroWave F u‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
          (((Real.exp (-(2 * c) * u) : ℝ) : ℂ) *
            Complex.exp (((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I * u)) := by
      intro u
      rw [Complex.ofReal_mul, ofReal_norm_zeroWave_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun p _ => (integrableOn_exp_damped hc _).const_mul _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_exp_damped hc]
    push_cast
    ring
  -- the pointwise limits
  have hlim : Tendsto (fun c : ℝ => ∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
      (2 * (c : ℂ) / (2 * (c : ℂ) - ((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I)))
      (𝓝[>] 0) (𝓝 (∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
        (if p.1 = p.2 then 1 else 0))) := by
    refine tendsto_finsetSum _ fun p hp => (tendsto_const_nhds.mul ?_)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    by_cases heq : p.1 = p.2
    · rw [if_pos heq, heq, sub_self, Complex.ofReal_zero, zero_mul]
      simp only [sub_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with c hc
      have : (2 * (c : ℂ)) ≠ 0 := by
        have : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
        exact mul_ne_zero two_ne_zero this
      rw [div_self this]
    · rw [if_neg heq]
      have hΔ : zeroOrdinate p.1 - zeroOrdinate p.2 ≠ 0 := fun h =>
        heq (hF _ hp1 _ hp2 (sub_eq_zero.mp h))
      have hden : (2 * ((0 : ℝ) : ℂ) - ((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I) ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        exact hΔ (by linarith)
      have hc : ContinuousAt (fun c : ℝ => 2 * (c : ℂ) /
          (2 * (c : ℂ) - ((zeroOrdinate p.1 - zeroOrdinate p.2 : ℝ) : ℂ) * I)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) hden
      have := hc.tendsto
      simp only [Complex.ofReal_zero, mul_zero, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
  have hdiag : (∑ p ∈ F ×ˢ F, zeroWeight p.1 * starRingEnd ℂ (zeroWeight p.2) *
      (if p.1 = p.2 then (1 : ℂ) else 0)) = ((∑ q ∈ F, ‖zeroWeight q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_product]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    push_cast
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos hq, Complex.mul_conj']
  rw [hdiag] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp (hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (hform c hc).symm))
  simpa only [Function.comp_def, Complex.ofReal_re] using hre

/-! ### The zero part -/

/-- Under RH, `‖b_q‖² = 1/|ρ_q|²` is summable. -/
theorem summable_norm_zeroWeight_sq (hRH : RiemannHypothesis) :
    Summable fun q : XiZeroCopy => ‖zeroWeight q‖ ^ 2 := by
  refine _root_.RHTower.xiSpectralPoint_inv_sq_summable.of_nonneg_of_le (fun _ => by positivity)
    fun q => ?_
  have hh := (xiZeroCopy_facts hRH q).2.2
  rw [_root_.RHTower.norm_xiSpectralPoint, zeroWeight, norm_neg, norm_div, norm_one, div_pow,
    one_pow]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_half_le_norm hRH q) 2)

/-- `‖a + b‖² ≤ (1 + t)‖a‖² + (1 + 1/t)‖b‖²`. -/
theorem norm_add_sq_le_of_pos {a b : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖a + b‖ ^ 2 ≤ (1 + t) * ‖a‖ ^ 2 + (1 + 1 / t) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have h2 : 2 * ‖a‖ * ‖b‖ ≤ t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2 := by
    have := sq_nonneg (t * ‖a‖ - ‖b‖)
    have h3 : t * (2 * ‖a‖ * ‖b‖) ≤ t * (t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2) := by
      rw [mul_add, ← mul_assoc t (1 / t), mul_one_div_cancel ht.ne', one_mul]; nlinarith
    exact le_of_mul_le_mul_left h3 ht
  nlinarith

/-- Under RH, on the line `Re s = ½ + c` the zero part is `Σ'_q b_q/(c + i(y − γ_q))`, the limit
of the finite zero symbols over `|γ| ≤ N`. -/
theorem tendsto_zeroSymbol (hRH : RiemannHypothesis) {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2)
    (y : ℝ) :
    Tendsto (fun N : ℕ => zeroSymbol (_root_.RHTower.xiCopiesBelow N) c y) atTop
      (𝓝 (zeroPart (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) := by
  set s : ℂ := ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsre : 1 / 2 < s.re := by simp [hs]; linarith
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp [hs] at this; linarith
  have hterm : ∀ q : XiZeroCopy, -(1 / (q.1 : ℂ)) / (s - (q.1 : ℂ)) =
      zeroWeight q / ((c : ℂ) + ((y - zeroOrdinate q : ℝ) : ℂ) * I) := by
    intro q
    have hre := (xiZeroCopy_facts hRH q).1
    rw [zeroWeight]
    congr 1
    apply Complex.ext <;> simp [hs, hre, zeroOrdinate]
  have hsum := (summable_zeroPart_term hRH hsre hs1).hasSum
  have hmono : Monotone fun N : ℕ => _root_.RHTower.xiCopiesBelow N := fun a b hab q hq =>
    _root_.RHTower.mem_xiCopiesBelow.mpr
      ((_root_.RHTower.mem_xiCopiesBelow.mp hq).trans (by exact_mod_cast hab))
  have hcover : ∀ q : XiZeroCopy, ∃ N : ℕ, q ∈ _root_.RHTower.xiCopiesBelow N := fun q =>
    ⟨⌈|zeroOrdinate q|⌉₊, _root_.RHTower.mem_xiCopiesBelow.mpr (Nat.le_ceil _)⟩
  have h := (hsum : Tendsto _ atTop _).comp (tendsto_atTop_finset_of_monotone hmono hcover)
  rw [zeroPart]
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, zeroSymbol]
  exact Finset.sum_congr rfl fun q _ => hterm q

/-- **The zero part has no mass at infinite height.** Under RH with distinct ordinates for distinct
copies, for every `ε > 0` eventually as `c ↓ 0`,
`∫ ‖P_c(y)‖² dy ≤ π (Σ_q ‖b_q‖² + ε)/c`. -/
theorem eventually_lintegral_zeroPart_le (hRH : RiemannHypothesis)
    (hsimple : ∀ q q' : XiZeroCopy, zeroOrdinate q = zeroOrdinate q' → q = q') {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ), ∫⁻ y : ℝ, ENNReal.ofReal
      (‖zeroPart (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
        ENNReal.ofReal (Real.pi * ((∑' q : XiZeroCopy, ‖zeroWeight q‖ ^ 2) + ε) / c) := by
  set P := ∑' q : XiZeroCopy, ‖zeroWeight q‖ ^ 2 with hP
  have hP0 : 0 ≤ P := tsum_nonneg fun _ => by positivity
  set t : ℝ := ε / (4 * (P + ε + 1)) with ht
  have ht0 : 0 < t := by positivity
  have htP : t * (P + ε / 4) ≤ ε / 4 := by
    rw [ht, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- a shell index whose tail is negligible
  have hCt := _root_.RHTower.cramerTailConstant_nonneg
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (1 + 1 / t) * (6 * (_root_.RHTower.cramerTailConstant *
      _root_.RHTower.cramerShellTail k₀)) ≤ ε / 4 := by
    have hlim : Tendsto (fun k : ℕ => (1 + 1 / t) * (6 * (_root_.RHTower.cramerTailConstant *
        _root_.RHTower.cramerShellTail k))) atTop (𝓝 ((1 + 1 / t) * (6 * (_root_.RHTower.cramerTailConstant * 0)))) :=
      (_root_.RHTower.tendsto_cramerShellTail.const_mul _).const_mul _ |>.const_mul _
    simp only [mul_zero] at hlim
    exact (hlim.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).exists
  -- the head
  set head := (_root_.RHTower.xiCopiesBelow ((2 : ℝ) ^ k₀)).filter
    (fun q => |zeroOrdinate q| < (2 : ℝ) ^ k₀) with hhead
  have hheadP : ∑ q ∈ head, ‖zeroWeight q‖ ^ 2 ≤ P :=
    (summable_norm_zeroWeight_sq hRH).sum_le_tsum _ fun _ _ => by positivity
  have hH := (tendsto_abel_head head fun q _ q' _ h => hsimple q q' h).eventually
    (ge_mem_nhds (show ∑ q ∈ head, ‖zeroWeight q‖ ^ 2 < P + ε / 4 by linarith))
  filter_upwards [hH, self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)]
    with c hcH hc hc4
  have hc0 : (0 : ℝ) < c := hc
  have hc2 : c ≤ 1 / 2 := by linarith [hc4.2]
  -- uniform bound on the truncations `|γ| ≤ N`, `N ≥ 2^{k₀}`
  have hbound : ∀ N : ℕ, (2 : ℝ) ^ k₀ ≤ N →
      ∫ y : ℝ, ‖zeroSymbol (_root_.RHTower.xiCopiesBelow N) c y‖ ^ 2 ≤ Real.pi * (P + ε) / c := by
    intro N hN
    set FN := _root_.RHTower.xiCopiesBelow (N : ℝ)
    set tail := FN.filter (fun q => ¬ |zeroOrdinate q| < (2 : ℝ) ^ k₀)
    have hsplitF : FN.filter (fun q => |zeroOrdinate q| < (2 : ℝ) ^ k₀) = head := by
      ext q
      simp only [Finset.mem_filter, hhead, FN, _root_.RHTower.mem_xiCopiesBelow]
      constructor
      · rintro ⟨-, h⟩; exact ⟨h.le, h⟩
      · rintro ⟨-, h⟩; exact ⟨h.le.trans hN, h⟩
    have hwave : ∀ u, zeroWave FN u = zeroWave head u + zeroWave tail u := by
      intro u
      rw [zeroWave, zeroWave, zeroWave, ← hsplitF, Finset.sum_filter_add_sum_filter_not]
    have htail : ∀ q ∈ tail, (2 : ℝ) ^ k₀ ≤ |zeroOrdinate q| := fun q hq =>
      not_lt.mp (Finset.mem_filter.mp hq).2
    have hT := abel_tail_le hRH htail hc0 hc2
    -- integrability of the three Abel integrands
    have hI : ∀ G : Finset XiZeroCopy,
        IntegrableOn (fun u => Real.exp (-(2 * c) * u) * ‖zeroWave G u‖ ^ 2) (Ioi 0) := by
      intro G
      have := continuous_zeroWave G
      refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0
        (by linarith : (0 : ℝ) < 2 * c))).const_mul ((∑ q ∈ G, ‖zeroWeight q‖) ^ 2))
        (by fun_prop : Continuous fun u => Real.exp (-(2 * c) * u) * ‖zeroWave G u‖ ^ 2).aestronglyMeasurable.restrict
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg (by positivity), mul_comm ((∑ q ∈ G, ‖zeroWeight q‖) ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_zeroWave_le G u) 2) (Real.exp_pos _).le
    have hle : ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave FN u‖ ^ 2 ≤
        (1 + t) * (∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave head u‖ ^ 2) +
          (1 + 1 / t) * (∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave tail u‖ ^ 2) := by
      have hg : IntegrableOn (fun u => (1 + t) * (Real.exp (-(2 * c) * u) * ‖zeroWave head u‖ ^ 2) +
          (1 + 1 / t) * (Real.exp (-(2 * c) * u) * ‖zeroWave tail u‖ ^ 2)) (Ioi 0) :=
        ((hI head).const_mul _).add ((hI tail).const_mul _)
      have hmono := setIntegral_mono_on (hI FN) hg measurableSet_Ioi fun u _ => by
        rw [hwave]
        have := norm_add_sq_le_of_pos (a := zeroWave head u) (b := zeroWave tail u) ht0
        have he := (Real.exp_pos (-(2 * c) * u)).le
        nlinarith
      rw [integral_add ((hI head).const_mul _) ((hI tail).const_mul _), integral_const_mul,
        integral_const_mul] at hmono
      exact hmono
    rw [integral_norm_sq_zeroSymbol hc0]
    have hfin : 2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave FN u‖ ^ 2 ≤ P + ε := by
      calc 2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave FN u‖ ^ 2
          ≤ 2 * c * ((1 + t) * (∫ u in Ioi (0 : ℝ),
              Real.exp (-(2 * c) * u) * ‖zeroWave head u‖ ^ 2) +
            (1 + 1 / t) * (∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave tail u‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
        _ = (1 + t) * (2 * c * ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * c) * u) * ‖zeroWave head u‖ ^ 2) +
            (1 + 1 / t) * (2 * c * ∫ u in Ioi (0 : ℝ),
              Real.exp (-(2 * c) * u) * ‖zeroWave tail u‖ ^ 2) := by ring
        _ ≤ (1 + t) * (P + ε / 4) + (1 + 1 / t) *
            (6 * (_root_.RHTower.cramerTailConstant * _root_.RHTower.cramerShellTail k₀)) := by
            gcongr
        _ ≤ P + ε := by nlinarith
    rw [le_div_iff₀ hc0]
    nlinarith [Real.pi_pos]
  -- Fatou
  have hint : ∀ N : ℕ, Integrable fun y : ℝ =>
      ‖zeroSymbol (_root_.RHTower.xiCopiesBelow N) c y‖ ^ 2 := fun N => by
    have := _root_.RHTower.integrable_norm_sq_laplaceBoundary (integrable_causalWave hc0
      (_root_.RHTower.xiCopiesBelow N)) (memLp_causalWave hc0 _)
    simpa only [laplaceBoundary_causalWave hc0] using this
  have hfat := lintegral_liminf_le' (μ := volume) (u := atTop)
    (f := fun (N : ℕ) (y : ℝ) =>
      ENNReal.ofReal (‖zeroSymbol (_root_.RHTower.xiCopiesBelow N) c y‖ ^ 2))
    (fun N => (hint N).aemeasurable.ennreal_ofReal)
  have hpt : ∀ y : ℝ, liminf (fun N : ℕ =>
      ENNReal.ofReal (‖zeroSymbol (_root_.RHTower.xiCopiesBelow N) c y‖ ^ 2)) atTop =
      ENNReal.ofReal (‖zeroPart (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2) := fun y =>
    (((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp
      (tendsto_zeroSymbol hRH hc0 (by linarith [hc4.2]) y)).liminf_eq
  simp_rw [hpt] at hfat
  refine hfat.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
  filter_upwards [eventually_ge_atTop ⌈(2 : ℝ) ^ k₀⌉₊] with N hN
  have hN' : (2 : ℝ) ^ k₀ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint N) (Eventually.of_forall fun _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (hbound N hN')

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
