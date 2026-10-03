import GaloisForLFunctions.RHTower.WeilFractionalTwoSidedRigidity

/-!
# Linear lock phases are quantized

Let `G` be a Herglotz producer for the weights `lam`.  Suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iη(−τ)} e^{iβ₀C(−τ)} G(s)`,  `s = ½ + 2iτ`, `τ < 0`,

with a linear phase of slope `η` and a monotone perturbation `C(x) = O(x^α)`, `α < 1`.

**Theorem** (`linear_twist_quantization`).  Then `e^{−η/2}` is a natural number.  In particular
`η ≤ 0`: a linear lock phase of positive slope is impossible.

The linear phase may grow at the linear rate, which the monotone twist theorems
(`AbelianTwist.abelian_twist_power_rigidity`) cannot reach.

**Proof.**  On the line `e^{iη(−t)} = W(½ + 2it)` with `W(s) = e^{−(η/2)(s−½)}` entire and bounded on
the strip `½ ≤ Re s ≤ 3/2`.  So the reflected boundary value is `κ₀ e^{iβ₀C(−t)} (W F)(½+2it)`, and
`W F = Σ a(n) e^{η/4} e^{−(log n + η/2)s}` is a Dirichlet series with shifted frequencies.
* If `e^{−η/2} ∉ ℕ`, every frequency `log n + η/2` stays a fixed distance from `log‖ε + i‖ → 0`.
  The contour shift of `ε ∫_{t ≤ b} (W F)(½+2it) k(2t, ε + i) dt` to `Re s = 3/2` then has no
  resonant term, and the integral is `≪ ε^{1−ν} e^{bδ}` (`exists_norm_twistRadial_le`).
* The layer cake over the levels of `C` (`norm_setIntegral_twist_le_pow`) makes the twisted
  integral tend to zero.
* Hamburger's reflected identity (`PhaseLockRigidity.tendsto_lower_reflected_radial`) says the same
  radial limit is `β/π`, and `β = G(1)/2 ≠ 0`.  This is a contradiction.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### The linear twist -/

/-- `W_η(s) = e^{−(η/2)(s−½)}`. -/
def linTwist (η : ℝ) (s : ℂ) : ℂ := cexp (-(((η / 2 : ℝ) : ℂ) * (s - 1 / 2)))

theorem norm_linTwist (η : ℝ) (s : ℂ) :
    ‖linTwist η s‖ = Real.exp (-(η / 2 * (s.re - 1 / 2))) := by
  unfold linTwist
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem linTwist_lineS (η t : ℝ) : linTwist η (lineS t) = cexp (((η * (-t) : ℝ) : ℂ) * I) := by
  unfold linTwist
  rw [lineS_eq]
  congr 1
  push_cast
  ring

theorem norm_linTwist_lineS (η t : ℝ) : ‖linTwist η (lineS t)‖ = 1 := by
  rw [linTwist_lineS, Complex.norm_exp_ofReal_mul_I]

theorem norm_linTwist_strip_le (η : ℝ) {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) :
    ‖linTwist η s‖ ≤ Real.exp (|η| / 2) := by
  rw [norm_linTwist]
  apply Real.exp_le_exp.mpr
  have h1 : |η / 2 * (s.re - 1 / 2)| ≤ |η| / 2 := by
    rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re - 1 / 2)]
    have : |η| / 2 * (s.re - 1 / 2) ≤ |η| / 2 * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  linarith [neg_abs_le (η / 2 * (s.re - 1 / 2))]

theorem hasDerivAt_linTwist (η : ℝ) (s : ℂ) :
    HasDerivAt (linTwist η) (-(((η / 2 : ℝ) : ℂ)) * linTwist η s) s := by
  have h1 : HasDerivAt (fun z : ℂ => -(((η / 2 : ℝ) : ℂ) * (z - 1 / 2))) (-(((η / 2 : ℝ) : ℂ))) s := by
    have h0 := ((((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul
      (((η / 2 : ℝ) : ℂ))).const_mul (-1 : ℂ))
    refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun z => by simp
  have h2 := h1.cexp
  have e : (fun z : ℂ => cexp (-(((η / 2 : ℝ) : ℂ) * (z - 1 / 2)))) = linTwist η := rfl
  rw [e] at h2
  refine h2.congr_deriv ?_
  unfold linTwist
  ring

/-- The twisted producer `W_η G`. -/
def twistG (η : ℝ) (G : ℂ → ℂ) (s : ℂ) : ℂ := linTwist η s * G s

theorem prodF_twistG (η : ℝ) (G : ℂ → ℂ) (s : ℂ) :
    prodF (twistG η G) s = linTwist η s * prodF G s := by
  unfold prodF twistG; ring

theorem phiG_twistG (η : ℝ) (G : ℂ → ℂ) (t : ℝ) :
    phiG (twistG η G) t = linTwist η (lineS t) * phiG G t := by
  unfold phiG twistG; ring

theorem norm_phiG_twistG (η : ℝ) (G : ℂ → ℂ) (t : ℝ) :
    ‖phiG (twistG η G) t‖ = ‖phiG G t‖ := by
  rw [phiG_twistG, norm_mul, norm_linTwist_lineS, one_mul]

theorem continuousAt_twistG {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (η : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) : ContinuousAt (twistG η G) s :=
  (hasDerivAt_linTwist η s).continuousAt.mul (hGc s hs)

theorem hasDerivAt_twistG {Φ G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (η : ℝ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    HasDerivAt (twistG η G) ((Φ s - ((η / 2 : ℝ) : ℂ)) * twistG η G s) s := by
  have h := (hasDerivAt_linTwist η s).mul (hGd s hs)
  refine h.congr_deriv ?_
  unfold twistG
  ring


/-! ### The shifted right edge -/

theorem norm_linTwist_edgePt (η y : ℝ) : ‖linTwist η (edgePt y)‖ = Real.exp (-(η / 2)) := by
  rw [norm_linTwist, edgePt_re]; congr 1; ring

theorem continuous_linTwist (η : ℝ) : Continuous (linTwist η) := by
  unfold linTwist; fun_prop

/-- The `n`-th twisted right-edge term `∫_{y ≤ B} a(n) n^{−s} W_η(s) k_τ(s) dy`, `s = 3/2 + iy`. -/
def twEdgeTerm (a : ℕ → ℂ) (η : ℝ) (τ : ℂ) (B : ℝ) (n : ℕ) : ℂ :=
  ∫ y in Iic B, LSeries.term a (edgePt y) n * linTwist η (edgePt y) * offKernel τ (edgePt y)

/-- **Dirichlet expansion of the twisted right edge.** -/
theorem hasSum_twEdgeTerm {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -1) :
    HasSum (twEdgeTerm (dirichletExp (lamLog lam)) η τ B)
      (∫ y in Iic B, edgeIntegrand (twistG η G) τ (edgePt y)) := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  have hkint := integrableOn_offKernel_edgePt hτre hτ1 hB
  set c : ℝ := Real.exp (-(η / 2)) with hc
  have hWc : Continuous fun y : ℝ => linTwist η (edgePt y) :=
    (continuous_linTwist η).comp (by unfold edgePt; fun_prop)
  have hpt : ∀ n y, ‖LSeries.term a (edgePt y) n * linTwist η (edgePt y) * offKernel τ (edgePt y)‖ =
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * c * ‖offKernel τ (edgePt y)‖ := by
    intro n y
    rw [norm_mul, norm_mul, norm_term_edgePt, norm_linTwist_edgePt]
  have hFint : ∀ n, Integrable (fun y => LSeries.term a (edgePt y) n * linTwist η (edgePt y) *
      offKernel τ (edgePt y)) (volume.restrict (Iic B)) := by
    intro n
    refine (hkint.norm.const_mul (‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * c)).mono'
      (((continuous_term_edgePt a n).mul hWc).mul
        (continuous_offKernel_edgePt hτ0)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [hpt]
  have hFnorm : ∀ n, ∫ y in Iic B, ‖LSeries.term a (edgePt y) n * linTwist η (edgePt y) *
      offKernel τ (edgePt y)‖ =
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * c * ∫ y in Iic B, ‖offKernel τ (edgePt y)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1; funext y; rw [hpt]
  have hsum : Summable fun n => ∫ y in Iic B, ‖LSeries.term a (edgePt y) n *
      linTwist η (edgePt y) * offKernel τ (edgePt y)‖ := by
    simp only [hFnorm]; exact (hSa.mul_right c).mul_right _
  have hsumm : Summable (twEdgeTerm a η τ B) :=
    Summable.of_norm_bounded hsum fun n => norm_integral_le_integral_norm _
  have hedge : ∀ y, edgeIntegrand (twistG η G) τ (edgePt y) =
      ∑' n, LSeries.term a (edgePt y) n * linTwist η (edgePt y) * offKernel τ (edgePt y) := by
    intro y
    have h1 : 1 < (edgePt y).re := by rw [edgePt_re]; norm_num
    unfold edgeIntegrand
    rw [prodF_twistG, prodF_eq_zetaOf hsl hid hGd hG2 h1, ← (hLa _ h1).2, LSeries,
      ← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext n; ring
  have hint : ∫ y in Iic B, edgeIntegrand (twistG η G) τ (edgePt y) = ∑' n, twEdgeTerm a η τ B n := by
    simp only [hedge, twEdgeTerm]
    exact (integral_tsum_of_summable_integral_norm hFint hsum).symm
  rw [hint]
  exact hsumm.hasSum

/-- **The twisted terms are off-resonant integrals at the shifted frequencies `log n + η/2`.** -/
theorem norm_twEdgeTerm_le (a : ℕ → ℂ) (η : ℝ) {τ : ℂ} (hτ : 0 < τ.re) {n : ℕ} (hn : 1 ≤ n)
    (hne : Real.log ‖τ‖ ≠ Real.log n + η / 2) {B : ℝ} (hB : B ≤ -1) :
    ‖twEdgeTerm a η τ B n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(η / 2)) *
      (2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2)) /
        |Real.log ‖τ‖ - (Real.log n + η / 2)| +
          4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set ℓ : ℝ := Real.log n + η / 2 with hℓ
  have e1 : ∀ y, LSeries.term a (edgePt y) n * linTwist η (edgePt y) * offKernel τ (edgePt y) =
      (a n * ((Real.exp (η / 4) : ℝ) : ℂ)) *
        (cexp (-((ℓ : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) *
          offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    intro y
    rw [LSeries.term_of_ne_zero hn0, natCast_cpow_eq_exp hn]
    unfold linTwist edgePt
    rw [div_eq_mul_inv, ← Complex.exp_neg, Complex.ofReal_exp, mul_assoc, mul_assoc, mul_assoc,
      ← mul_assoc (cexp _), ← Complex.exp_add, ← mul_assoc (cexp _) (cexp _),
      ← Complex.exp_add]
    congr 2
    rw [hℓ]; push_cast; congr 1; ring
  simp only [twEdgeTerm, e1, integral_const_mul]
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_integral_edge_exp_le hτ hne hB)
    (norm_nonneg _)).trans (le_of_eq ?_)
  have hterm : ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ = ‖a n‖ * Real.exp (-(3 / 2 * Real.log n)) := by
    rw [LSeries.norm_term_eq, if_neg hn0, Complex.ofReal_re, Real.rpow_def_of_pos hnpos,
      Real.exp_neg, div_eq_mul_inv, mul_comm (Real.log n)]
  rw [hterm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (η / 4) * Real.exp (-(3 / 2 * ℓ)) =
      Real.exp (-(3 / 2 * Real.log n)) * Real.exp (-(η / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, hℓ]; congr 1; ring
  set R : ℝ := 2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2)) /
      |Real.log ‖τ‖ - ℓ| + 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi with hR
  calc ‖a n‖ * Real.exp (η / 4) * (Real.exp (-(3 / 2 * ℓ)) * R)
      = ‖a n‖ * (Real.exp (η / 4) * Real.exp (-(3 / 2 * ℓ))) * R := by ring
    _ = ‖a n‖ * Real.exp (-(3 / 2 * Real.log n)) * Real.exp (-(η / 2)) * R := by rw [hexp]; ring

/-- **Uniform separation of the shifted frequencies from `0`** when `e^{−η/2} ∉ ℕ`. -/
theorem exists_sep_of_nonres {η : ℝ} (hres : ∀ n : ℕ, (n : ℝ) ≠ Real.exp (-(η / 2))) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → d ≤ |Real.log n + η / 2| := by
  have hne : ∀ n : ℕ, 1 ≤ n → Real.log n + η / 2 ≠ 0 := by
    intro n hn h
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply hres n
    rw [← Real.exp_log hpos]; congr 1; linarith
  set N : ℕ := ⌈Real.exp (1 - η / 2)⌉₊ with hN
  obtain ⟨n₀, hn₀, hmin⟩ := (Finset.Icc 1 (N + 1)).exists_min_image
    (fun n : ℕ => |Real.log n + η / 2|) ⟨1, by simp⟩
  have hn₀1 : 1 ≤ n₀ := (Finset.mem_Icc.mp hn₀).1
  refine ⟨min 1 |Real.log n₀ + η / 2|, lt_min one_pos (abs_pos.mpr (hne n₀ hn₀1)), fun n hn => ?_⟩
  by_cases hnN : n ≤ N + 1
  · exact (min_le_right _ _).trans (hmin n (Finset.mem_Icc.mpr ⟨hn, hnN⟩))
  · push Not at hnN
    refine (min_le_left _ _).trans ?_
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 : Real.exp (1 - η / 2) ≤ n := by
      have := Nat.le_ceil (Real.exp (1 - η / 2))
      rw [← hN] at this
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
      linarith
    have h3 : 1 - η / 2 ≤ Real.log n := by
      rw [← Real.log_exp (1 - η / 2)]; exact Real.log_le_log (Real.exp_pos _) h1
    rw [abs_of_nonneg (by linarith)]
    linarith


/-! ### The radial bound without resonance -/

theorem edgeIntegrand_twistG (η : ℝ) (G : ℂ → ℂ) (τ s : ℂ) :
    edgeIntegrand (twistG η G) τ s = linTwist η s * edgeIntegrand G τ s := by
  unfold edgeIntegrand; rw [prodF_twistG]; ring

/-- **A separated twisted term.**  If every shifted frequency is at distance `≥ d/2` from
`log‖τ‖`, then `‖twEdgeTerm n‖ ≤ ‖a_n n^{−3/2}‖ e^{−η/2} ‖τ‖^{1/2}(4/d + 4/π) e^{Bδ}`,
`δ = Re τ/‖τ‖`. -/
theorem norm_twEdgeTerm_le_of_sep (a : ℕ → ℂ) (η : ℝ) {τ : ℂ} (hτre : 0 < τ.re)
    (hτ1 : 1 ≤ ‖τ‖) {d : ℝ} (hd0 : 0 < d)
    (hsep : ∀ n : ℕ, 1 ≤ n → d / 2 ≤ |Real.log ‖τ‖ - (Real.log n + η / 2)|)
    {B : ℝ} (hB : B ≤ -1) (n : ℕ) :
    ‖twEdgeTerm a η τ B n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (Real.exp (-(η / 2)) * ‖τ‖ ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) *
        Real.exp (B * (τ.re / ‖τ‖))) := by
  have hpi := Real.pi_pos
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hτpos]
    exact (le_abs_self _).trans (Complex.abs_re_le_norm τ)
  set A : ℝ := ((Real.pi : ℂ) * τ ^ 2).arg with hA
  have hAδ : 2 * δ ≤ Real.pi - A := by
    have h := abs_arg_pi_mul_sq_le hτre
    have := le_abs_self A
    linarith
  by_cases hn0 : n = 0
  · subst hn0
    have : twEdgeTerm a η τ B 0 = 0 := by simp [twEdgeTerm, LSeries.term]
    rw [this, norm_zero]; positivity
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hsepn := hsep n hn1
  have hne : Real.log ‖τ‖ ≠ Real.log n + η / 2 := by
    intro h; rw [h, sub_self, abs_zero] at hsepn; linarith
  refine (norm_twEdgeTerm_le a η hτre hn1 hne hB).trans ?_
  rw [← hA]
  have hinv : 1 / |Real.log ‖τ‖ - (Real.log n + η / 2)| ≤ 2 / d := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hsepn) hd0]; linarith
  have he1 : Real.exp (B * ((Real.pi - A) / 2)) ≤ Real.exp (B * δ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (Real.pi * B) ≤ Real.exp (B * δ) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have hτs : 0 ≤ ‖τ‖ ^ (1 / 2 : ℝ) := by positivity
  have hT0 : 0 ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := norm_nonneg _
  have hc : 0 ≤ Real.exp (-(η / 2)) := (Real.exp_pos _).le
  calc ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(η / 2)) *
        (2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - A) / 2)) /
          |Real.log ‖τ‖ - (Real.log n + η / 2)| +
          4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi)
      = ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(η / 2)) *
        (2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - A) / 2)) *
          (1 / |Real.log ‖τ‖ - (Real.log n + η / 2)|) +
          4 / Real.pi * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B)) := by ring
    _ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(η / 2)) *
        (2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * δ) * (2 / d) +
          4 / Real.pi * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * δ)) := by gcongr
    _ = _ := by ring

/-- **The separated right edge** sums to at most `S_a e^{−η/2} ‖τ‖^{1/2}(4/d + 4/π) e^{Bδ}`. -/
theorem norm_tsum_twEdgeTerm_le_of_sep {a : ℕ → ℂ}
    (hSa : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖) (η : ℝ) {τ : ℂ}
    (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {d : ℝ} (hd0 : 0 < d)
    (hsep : ∀ n : ℕ, 1 ≤ n → d / 2 ≤ |Real.log ‖τ‖ - (Real.log n + η / 2)|)
    {B : ℝ} (hB : B ≤ -1) :
    ‖∑' n, twEdgeTerm a η τ B n‖ ≤ (∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖) *
      (Real.exp (-(η / 2)) * ‖τ‖ ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) *
        Real.exp (B * (τ.re / ‖τ‖))) := by
  have hite := norm_twEdgeTerm_le_of_sep a η hτre hτ1 hd0 hsep hB
  have hite_summ : Summable fun n => ‖twEdgeTerm a η τ B n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hite (hSa.mul_right _)
  refine (norm_tsum_le_tsum_norm hite_summ).trans ?_
  rw [← tsum_mul_right]
  exact hite_summ.tsum_le_tsum hite (hSa.mul_right _)

/-- The norm `‖ε + i‖` is at most `1 + ε²/2`, so `0 ≤ log‖ε + i‖ ≤ ε²/2`. -/
theorem log_norm_eps_add_mI_le {ε : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    Real.log m ≤ Real.log ‖(ε : ℂ) + (m : ℂ) * I‖ ∧
      Real.log ‖(ε : ℂ) + (m : ℂ) * I‖ ≤ Real.log m + ε ^ 2 / 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτim : τ.im = m := by simp [hτ]
  have hτm : (m : ℝ) ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rwa [hτim, abs_of_nonneg (by linarith)] at h
  have hτsq : ‖τ‖ ^ 2 = ε ^ 2 + (m : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hτre, hτim]; ring
  have hmpos : (0 : ℝ) < m := by linarith
  refine ⟨Real.log_le_log hmpos hτm, ?_⟩
  have h2 : ‖τ‖ ≤ m * (1 + ε ^ 2 / 2) := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [hτsq]
    have e : ((m : ℝ) * (1 + ε ^ 2 / 2)) ^ 2 =
        (m : ℝ) ^ 2 + (m : ℝ) ^ 2 * ε ^ 2 + (m : ℝ) ^ 2 * (ε ^ 2) ^ 2 / 4 := by ring
    have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    rw [e]
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg (ε ^ 2)), sq_nonneg ε]
  have hτpos : 0 < ‖τ‖ := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hτpos hmpos)
  rw [Real.log_div hτpos.ne' hmpos.ne'] at h1
  have h3 : ‖τ‖ / m ≤ 1 + ε ^ 2 / 2 := by rw [div_le_iff₀ hmpos]; linarith
  linarith

/-- **Uniform separation at height `m`** when `m e^{−η/2} ∉ ℕ`. -/
theorem exists_sep_of_nonres_at {η : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hres : ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(η / 2))) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → d ≤ |Real.log n + η / 2 - Real.log m| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨d, hd0, hd⟩ := exists_sep_of_nonres (η := η - 2 * Real.log m) (fun n hn => hres n (by
    rw [hn, show -((η - 2 * Real.log m) / 2) = -(η / 2) + Real.log m by ring, Real.exp_add,
      Real.exp_log hm0]
    ring))
  refine ⟨d, hd0, fun n hn => ?_⟩
  have := hd n hn
  rwa [show Real.log n + (η - 2 * Real.log m) / 2 = Real.log n + η / 2 - Real.log m by ring] at this

/-- The final estimate in `exists_norm_twistRadial_le`. -/
theorem twistRadial_assemble {ε δ M b ν Sa c₂ d CFν c₁ τn K X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ0 : 0 < δ) (hM0 : 0 ≤ M) (hεδ : ε ≤ δ * M) (hb : b ≤ -1) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hτM : τn ≤ M) (hSa0 : 0 ≤ Sa) (hc₂ : 0 ≤ c₂) (hd : 0 ≤ 4 / d + 4 / Real.pi)
    (hC : 0 ≤ CFν * c₁)
    (hX : X ≤ Sa * (c₂ * τn ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) * Real.exp (2 * b * δ)) +
      CFν * c₁ * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * τn * Real.exp (2 * b * δ)))
    (hK : K = (1 / 2) * (Sa * c₂ * M ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) +
      CFν * c₁ * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (1 + 2 * M))) (hτn : 0 ≤ τn) :
    ε * (1 / 2 * X) ≤ K * ε ^ (1 - ν) * Real.exp (b * δ) := by
  have hpi := Real.pi_pos
  have hτs : τn ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hτn hτM (by norm_num)
  have hεs : ε ≤ ε ^ (1 - ν) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (1 - ν) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hpart2 := mul_rpow_exp_le_rpow hε hε1 hδ0 hM0 hεδ (by linarith : b ≤ 0) hν0.le hν1
  have he2 : Real.exp (2 * b * δ) ≤ Real.exp (b * δ) := Real.exp_le_exp.mpr (by nlinarith)
  have h1 : ε * Sa * (c₂ * τn ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) * Real.exp (2 * b * δ)) ≤
      ε ^ (1 - ν) * (Sa * c₂ * M ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi)) * Real.exp (b * δ) := by
    have : ε * Sa * (c₂ * τn ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) * Real.exp (2 * b * δ)) =
        ε * (Sa * c₂ * τn ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi)) * Real.exp (2 * b * δ) := by ring
    rw [this]
    gcongr
  have h2 : CFν * c₁ * (4 * Real.pi ^ (3 / 4 : ℝ) * τn) *
      (ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ))) ≤
      CFν * c₁ * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ)) := by
    gcongr
  have hX' : ε * X ≤ ε * (Sa * (c₂ * τn ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) *
      Real.exp (2 * b * δ)) + CFν * c₁ * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * τn *
        Real.exp (2 * b * δ))) := mul_le_mul_of_nonneg_left hX hε.le
  rw [hK]
  nlinarith

/-- **The radial bound for the twisted producer at height `m`, without resonance.**  If
`m e^{−η/2} ∉ ℕ`, then for `0 < ν ≤ 1` there are `K` and `ε₀ > 0` with
`‖ε ∫_{t ≤ b} (W_η F)(½+2it) k(2t, ε + im) dt‖ ≤ K ε^{1−ν} e^{bε/‖ε+im‖}` for `0 < ε ≤ ε₀` and
`b ≤ −1`. -/
theorem exists_norm_twistRadial_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {m : ℕ} (hm : 1 ≤ m) (hres : ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(η / 2))) {ν : ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ b : ℝ, b ≤ -1 →
      ‖(ε : ℂ) * ∫ t in Iic b, phiG (twistG η G) t *
        pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖ ≤
      K * ε ^ (1 - ν) * Real.exp (b * (ε / ‖(ε : ℂ) + (m : ℂ) * I‖)) := by
  have hpi := Real.pi_pos
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa_summ : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  set Sa : ℝ := ∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ with hSa
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun n => norm_nonneg _
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  obtain ⟨CFν, hCFν, hFν⟩ := exists_norm_prodF_le_rpow hsl hΦd hΦre hid hGc hGd hG2 hν0
  obtain ⟨d, hd0, hd⟩ := exists_sep_of_nonres_at hm hres
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set c₁ : ℝ := Real.exp (|η| / 2) with hc₁
  set c₂ : ℝ := Real.exp (-(η / 2)) with hc₂
  have hc₁0 : 0 < c₁ := Real.exp_pos _
  have hc₂0 : 0 < c₂ := Real.exp_pos _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = m + 1 := ⟨m + 1, rfl⟩
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; linarith
  set K : ℝ := (1 / 2) * (Sa * c₂ * M ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) +
    CFν * c₁ * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (1 + 2 * M)) with hK
  refine ⟨K, min 1 (Real.sqrt d), lt_min one_pos (Real.sqrt_pos.mpr hd0),
    fun ε hε hε0 b hb => ?_⟩
  have hε1 : ε ≤ 1 := hε0.trans (min_le_left _ _)
  have hεd : ε ^ 2 ≤ d := by
    have h := hε0.trans (min_le_right _ _)
    calc ε ^ 2 ≤ Real.sqrt d ^ 2 := pow_le_pow_left₀ hε.le h 2
      _ = d := Real.sq_sqrt hd0.le
  obtain ⟨hlog0, hlog1⟩ := log_norm_eps_add_mI_le (ε := ε) hm
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτim : τ.im = m := by simp [hτ]
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rw [hτim, abs_of_nonneg (by linarith)] at h; linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hM]; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  have hsep : ∀ n : ℕ, 1 ≤ n → d / 2 ≤ |Real.log ‖τ‖ - (Real.log n + η / 2)| := by
    intro n hn
    have h := hd n hn
    have e : Real.log ‖τ‖ - (Real.log n + η / 2) =
        (Real.log ‖τ‖ - Real.log m) - (Real.log n + η / 2 - Real.log m) := by ring
    rw [e]
    have h4 := abs_sub_abs_le_abs_sub (Real.log n + η / 2 - Real.log m)
      (Real.log ‖τ‖ - Real.log m)
    rw [abs_sub_comm (Real.log n + η / 2 - Real.log m) (Real.log ‖τ‖ - Real.log m)] at h4
    have h5 : |Real.log ‖τ‖ - Real.log m| ≤ ε ^ 2 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  set δ : ℝ := ε / ‖τ‖ with hδ
  have hδ' : τ.re / ‖τ‖ = δ := by rw [hτre]
  have hδ0 : 0 < δ := div_pos hε hτpos
  have hεδ : ε ≤ δ * M := by
    rw [hδ, div_mul_eq_mul_div, le_div_iff₀ hτpos]; nlinarith
  -- the contour shift for the twisted producer
  have hF' : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (twistG η G) ((x : ℂ) + (y : ℂ) * I)‖ ≤ (c₁ * CF) * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    rw [prodF_twistG, norm_mul, mul_assoc]
    exact mul_le_mul (norm_linTwist_strip_le η (by simpa using hx1) (by simpa using hx2))
      (hF x y hx1 hx2 hy) (norm_nonneg _) hc₁0.le
  have hFν' : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (twistG η G) ((x : ℂ) + (y : ℂ) * I)‖ ≤ (CFν * c₁) * (1 + |y|) ^ ν := by
    intro x y hx1 hx2 hy
    rw [prodF_twistG, norm_mul, mul_comm CFν c₁, mul_assoc]
    exact mul_le_mul (norm_linTwist_strip_le η (by simpa using hx1) (by simpa using hx2))
      (hFν x y hx1 hx2 hy) (norm_nonneg _) hc₁0.le
  have hedge' : ∀ y : ℝ, 1 ≤ |y| →
      ‖edgeIntegrand (twistG η G) τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (c₂ * Real.exp S) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro y hy
    rw [edgeIntegrand_twistG, norm_mul, mul_assoc]
    have hW : ‖linTwist η (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ = c₂ := norm_linTwist_edgePt η y
    rw [hW]
    exact mul_le_mul_of_nonneg_left
      (norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1 hy) hc₂0.le
  have hfint' : IntegrableOn (fun t => phiG (twistG η G) t * pairKernel (2 * t) τ) (Iic b) := by
    have h := (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre0).integrableOn (s := Iic b)
    refine h.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact ((continuous_phiG (fun s hs => continuousAt_twistG hGc η hs)).mul
        (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_phiG_twistG]
  have hcont := setIntegral_Iic_radial_eq_of (fun s hs => continuousAt_twistG hGc η hs)
    (fun s hs => hasDerivAt_twistG hGd η hs) (by positivity) hF' hτre0 hτ1 hedge' hb hfint'
  have hs := hasSum_twEdgeTerm hsl hid hGd hG2 η hτre0 hτ1 (B := 2 * b) (by linarith)
  have hoff := norm_tsum_twEdgeTerm_le_of_sep hSa_summ η hτre0 hτ1 hd0 hsep (B := 2 * b)
    (by linarith)
  rw [hδ', ← hSa] at hoff
  -- the top edge
  have h2b : 2 ≤ |2 * b| := by rw [abs_mul, abs_two, abs_of_neg (by linarith : b < 0)]; linarith
  have htop := norm_horizontalEdge_le hFν' hτre0 hτ1 h2b
  rw [hδ'] at htop
  have h2babs : |2 * b| = 2 * |b| := by rw [abs_mul, abs_two]
  have hexpb : Real.exp (-(|2 * b| * δ)) = Real.exp (2 * b * δ) := by
    rw [h2babs, abs_of_neg (by linarith : b < 0)]; congr 1; ring
  rw [hexpb, h2babs] at htop
  -- assemble
  have hedge_eq : (∫ y in Iic (2 * b), edgeIntegrand (twistG η G) τ
      (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) = ∑' n, twEdgeTerm a η τ (2 * b) n := hs.tsum_eq.symm
  rw [hcont, hedge_eq]
  set T : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2),
    edgeIntegrand (twistG η G) τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  rw [norm_mul, hεn, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  have hsum_le : ‖(∑' n, twEdgeTerm a η τ (2 * b) n) + I * T‖ ≤
      Sa * (c₂ * ‖τ‖ ^ (1 / 2 : ℝ) * (4 / d + 4 / Real.pi) * Real.exp (2 * b * δ)) +
        CFν * c₁ * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (2 * b * δ)) := by
    refine (norm_add_le _ _).trans (add_le_add hoff ?_)
    rw [norm_mul, Complex.norm_I, one_mul]; exact htop
  exact twistRadial_assemble hε hε1 hδ0 hM0 hεδ hb hν0 hν1 hτM hSa0 hc₂0.le (by positivity)
    (by positivity) hsum_le hK (norm_nonneg _)


/-! ### The twisted far piece vanishes -/

theorem integrable_phiG_twistG_mul_pairKernel {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable fun t : ℝ => phiG (twistG η G) t * pairKernel (2 * t) τ := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  refine (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτ).norm.mono'
    ((continuous_phiG (fun s hs => continuousAt_twistG hGc η hs)).mul
      (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_mul, norm_phiG_twistG]

/-- The weight `(C(−t) − C(1))‖c F(½+2it) k(2t, τ)‖` is integrable on `t ≤ −1` when `C` is monotone
of at most linear growth and `F` grows polynomially on the line. -/
theorem integrableOn_phase_mul_phiG {G : ℂ → ℂ} {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖phiG G t‖ ≤ CB * (1 + |t|) ^ N)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) {C : ℝ → ℝ} (hC : Monotone C) {K₁ : ℝ}
    (hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K₁ * (x + 1)) {τ : ℂ} (hτre : 0 < τ.re) (c : ℂ) :
    IntegrableOn (fun t => (C (-t) - C 1) * ‖c * (phiG G t * pairKernel (2 * t) τ)‖)
      (Iic (-1)) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := by positivity
  set D := 3 * CB * ‖τ‖ ^ (-(1 / 2 : ℝ)) with hD
  have hD0 : 0 ≤ D := by positivity
  set A := 2 * |K₁| + |C 1| with hA
  have hdom := ((integrable_one_add_abs_pow_mul_exp hδ (N + 1)).const_mul
    (A * (‖c‖ * D))).integrableOn (s := Iic (-1))
  have hmeas : AEStronglyMeasurable
      (fun t => (C (-t) - C 1) * ‖c * (phiG G t * pairKernel (2 * t) τ)‖)
      (volume.restrict (Iic (-1))) :=
    (((hC.measurable.comp measurable_neg).sub_const _).mul
      (continuous_const.mul ((continuous_phiG hGc).mul
        (continuous_pairKernel_two_mul hτ0))).norm.measurable).aestronglyMeasurable
  refine hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Iic).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : t ≤ -1 := ht
  have hC1 : C 1 ≤ C (-t) := hC (by linarith)
  have habs : |t| = -t := abs_of_neg (by linarith)
  have hCt : C (-t) - C 1 ≤ A * (1 + |t|) := by
    have h0 := hK₁ (-t) (by linarith)
    have hk1 : K₁ * (-t + 1) ≤ |K₁| * (2 * (1 + |t|)) := by
      rw [habs]
      calc K₁ * (-t + 1) ≤ |K₁ * (-t + 1)| := le_abs_self _
        _ = |K₁| * (-t + 1) := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < -t + 1 by linarith)]
        _ ≤ |K₁| * (2 * (1 + -t)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    have hc1 := neg_abs_le (C 1)
    nlinarith [abs_nonneg K₁, abs_nonneg (C 1)]
  have hk := norm_pairKernel_two_mul_le t hτre
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _)), norm_mul,
    norm_mul]
  set E := Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc (C (-t) - C 1) * (‖c‖ * (‖phiG G t‖ * ‖pairKernel (2 * t) τ‖))
      ≤ (A * (1 + |t|)) * (‖c‖ * ((CB * (1 + |t|) ^ N) *
          (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * E))) := by
        gcongr
        exact hpoly t
    _ = A * (‖c‖ * D) * ((1 + |t|) ^ (N + 1) * E) := by rw [hD]; ring

/-- **The twisted far piece vanishes without resonance.**  If `m e^{−η/2} ∉ ℕ`, `C` is monotone
with `C(x) ≤ K x^α` (`0 < α < 1`), and `Ψ = Ψ(u) + ∫ψ` with `‖ψ‖ ≤ L`, then
`ε ∫_{t ≤ −1} Ψ(C(−t)) (W_η F)(½+2it) k(2t, ε + im) dt → 0` as `ε → 0⁺`. -/
theorem tendsto_twisted_far_nonres_profile {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {m : ℕ} (hm : 1 ≤ m) (hres : ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(η / 2)))
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
  set ν : ℝ := (1 - α) / 2 with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  have hν1 : ν ≤ 1 := by rw [hν]; linarith
  obtain ⟨Kr, ε₀, hε₀, hKr⟩ :=
    exists_norm_twistRadial_le hsl hΦd hΦre hid hGc hGd hG2 η hm hres hν0 hν1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hpoly' : ∀ t : ℝ, ‖phiG (twistG η G) t‖ ≤ CB * (1 + |t|) ^ N := fun t => by
    rw [norm_phiG_twistG]; exact (hpoly t).1
  have hGc' : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt (twistG η G) s := fun s hs =>
    continuousAt_twistG hGc η hs
  have hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K * (x + 1) := fun x hx => by
    have h1 : x ^ α ≤ x := by
      calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hα1.le
        _ = x := Real.rpow_one x
    nlinarith [hgrowth x hx]
  set A : ℝ := |Kr| * (‖Ψ (C 1)‖ + L * max 0 (-C 1)) with hA
  set B : ℝ := |Kr| * L * (2 * K * ((m : ℝ) + 1) ^ α) with hB
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ min 1 ε₀ →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))‖ ≤
        A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by
    intro ε hε hεm
    have hε1 : ε ≤ 1 := hεm.trans (min_le_left _ _)
    have hεε₀ : ε ≤ ε₀ := hεm.trans (min_le_right _ _)
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_nonneg (by linarith)] at h; linarith
    have hτM : ‖τ‖ ≤ (m : ℝ) + 1 := by
      have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_pos hε] at h
      linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := ε / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hε hτpos
    set d : ℝ → ℂ := fun t => (ε : ℂ) * (phiG (twistG η G) t * pairKernel (2 * t) τ) with hd
    have hdc : Continuous d := continuous_const.mul
      ((continuous_phiG hGc').mul (continuous_pairKernel_two_mul hτ0))
    have hphik := integrable_phiG_twistG_mul_pairKernel hsl hΦre hid hGc hGd hG2 η hτre0
    have hdint : IntegrableOn d (Iic (-1)) := (hphik.const_mul (ε : ℂ)).integrableOn
    have hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)) :=
      integrableOn_phase_mul_phiG hCB hpoly' hGc' hC hK₁ hτre0 _
    have herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ (|Kr| * ε ^ (1 - ν)) * Real.exp (b * δ) := by
      intro b hb
      have h1 : ∫ t in Iic b, d t =
          (ε : ℂ) * ∫ t in Iic b, phiG (twistG η G) t * pairKernel (2 * t) τ := by
        simp only [hd]; rw [integral_const_mul]
      rw [h1]
      refine (hKr ε hε hεε₀ b hb).trans ?_
      gcongr
      exact le_abs_self Kr
    have htw := norm_setIntegral_layer_le_pow hC hL hψm hψL hΨ hδ0 hα0 hα1.le hK
      (by positivity) hgrowth hdc.aestronglyMeasurable hdint hdom herr
    have e1 : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        (phiG (twistG η G) t * pairKernel (2 * t) τ) =
        ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t := by
      rw [← integral_const_mul]; congr 1; funext t; simp only [hd]; ring
    rw [e1]
    refine htw.trans ?_
    have hδα : δ ^ (-α) ≤ ((m : ℝ) + 1) ^ α * ε ^ (-α) := by
      rw [hδ, Real.div_rpow hε.le hτpos.le, Real.rpow_neg hτpos.le, div_inv_eq_mul, mul_comm]
      gcongr
    have hεmul : ε ^ (1 - ν) * ε ^ (-α) = ε ^ (1 - ν - α) := by
      rw [← Real.rpow_add hε]; ring_nf
    have hM0 : 0 ≤ max 0 (-C 1) := le_max_left _ _
    calc |Kr| * ε ^ (1 - ν) * (‖Ψ (C 1)‖ + L * (max 0 (-C 1) + 2 * K * δ ^ (-α)))
        = A * ε ^ (1 - ν) + |Kr| * L * (2 * K) * (ε ^ (1 - ν) * δ ^ (-α)) := by
          rw [hA]; ring
      _ ≤ A * ε ^ (1 - ν) + |Kr| * L * (2 * K) *
            (ε ^ (1 - ν) * (((m : ℝ) + 1) ^ α * ε ^ (-α))) := by gcongr
      _ = A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by rw [hB, ← hεmul]; ring
  have hp : 0 < 1 - ν := by linarith
  have hq : 0 < 1 - ν - α := by rw [hν]; linarith
  have hlim : Tendsto (fun ε : ℝ => A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (1 - ν)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν))) :=
      ((Real.continuous_rpow_const hp.le).tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν - α))) :=
      ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne'] at h1
    rw [Real.zero_rpow hq.ne'] at h2
    simpa using (h1.const_mul A).add (h2.const_mul B)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 ε₀ from lt_min one_pos hε₀)] with ε hε
  exact hbound ε hε.1 hε.2.le

/-- The phase case `Ψ(v) = e^{iβ₀v}` of `tendsto_twisted_far_nonres_profile`. -/
theorem tendsto_twisted_far_nonres {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {m : ℕ} (hm : 1 ≤ m) (hres : ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(η / 2)))
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α) (β₀ : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) :=
  tendsto_twisted_far_nonres_profile hsl hΦd hΦre hid hGc hGd hG2 η hm hres hC hα0 hα1 hK hgrowth
    (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I)) (abs_nonneg β₀)
    (continuous_phaseDensity β₀).measurable (fun x => (norm_phaseDensity β₀ x).le)
    (fun _ _ huv => phase_eq_add_setIntegral β₀ huv)

theorem norm_pairKernel_two_mul_le_three (t : ℝ) {τ : ℂ} (hτ : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) :
    ‖pairKernel (2 * t) τ‖ ≤ 3 := by
  refine (norm_pairKernel_two_mul_le t hτ).trans ?_
  have h1 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
  have h2 : Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (2 * (τ.re / ‖τ‖)) * |t| := by
      have : 0 < ‖τ‖ := by linarith
      positivity
    linarith
  have h0 : 0 ≤ ‖τ‖ ^ (-(1 / 2 : ℝ)) := by positivity
  calc 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|)) ≤ 3 * 1 * 1 := by
        gcongr
    _ = 3 := by ring

theorem tendsto_eps_mul_setIntegral_Ioo {h : ℝ → ℂ} {B : ℝ}
    (hB : ∀ t ∈ Ioo (-1 : ℝ) 0, ‖h t‖ ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0,
      h t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := by
    have := hB (-1 / 2) ⟨by norm_num, by norm_num⟩
    exact (norm_nonneg _).trans this
  refine squeeze_zero_norm' (a := fun ε : ℝ => ε * (B * 3)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : 0 < τ.re := by simp [hτ]; exact hε'
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_nonneg (by linarith)] at h; linarith
    have hint : ‖∫ t in Ioo (-1 : ℝ) 0, h t * pairKernel (2 * t) τ‖ ≤ B * 3 := by
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-1 : ℝ) 0)
        (C := B * 3) (f := fun t => h t * pairKernel (2 * t) τ)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (fun t ht => by
          rw [norm_mul]
          exact mul_le_mul (hB t ht) (norm_pairKernel_two_mul_le_three t hτre hτ1)
            (norm_nonneg _) hB0)
      rw [Measure.real, Real.volume_Ioo, show (0 : ℝ) - -1 = 1 by norm_num, ENNReal.toReal_ofReal
        zero_le_one, mul_one] at h1
      exact h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    exact mul_le_mul_of_nonneg_left hint hε'.le
  · have h : Tendsto (fun ε : ℝ => ε * (B * 3)) (𝓝 0) (𝓝 (0 * (B * 3))) :=
      (continuous_id.mul continuous_const).tendsto (0 : ℝ)
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds

/-! ### The theorem -/

/-- **Linear lock phases are quantized, profile form.**  Let `G` be a Herglotz producer for the
weights `lam`.  Suppose that on the lower critical line
`G(1 − s) = κ₀ e^{iη(−τ)} Ψ(C(−τ)) G(s)`, `s = ½ + 2iτ`, `τ < 0`,
where `C` is monotone with `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`, and `Ψ` is a bounded
continuous profile `Ψ = Ψ(u) + ∫ψ` with `‖ψ‖ ≤ L`.  Then `e^{−η/2}` is a natural number. -/
theorem linear_twist_quantization_profile {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L M : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    (hΨc : Continuous Ψ) (hΨb : ∀ v, ‖Ψ v‖ ≤ M)
    {κ₀ : ℂ} {η : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * Ψ (C (-τ)) * G (lineS τ)) :
    ∃ n : ℕ, (n : ℝ) = Real.exp (-(η / 2)) := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  by_contra hres
  push Not at hres
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  -- the growth exponent in `(0, 1)`
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  set α' : ℝ := max α (1 / 2) with hα'
  set K' : ℝ := |K| + 1 with hK'
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  have hC' : ∀ x : ℝ, 1 ≤ x → C x ≤ K' * x ^ α' := by
    intro x hx
    have h1 : x ^ α ≤ x ^ α' := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    have h0 : 0 ≤ x ^ α := Real.rpow_nonneg (by linarith) _
    have h2 := hCK x hx
    have h3 : K * x ^ α ≤ |K| * x ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
    have h4 : |K| * x ^ α ≤ K' * x ^ α' := by
      rw [hK']; nlinarith [abs_nonneg K]
    linarith
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  have hpoly' : ∀ t : ℝ, ‖phiG (twistG η G) t‖ ≤ CB * (1 + |t|) ^ N := fun t => by
    rw [norm_phiG_twistG]; exact (hpoly t).1
  have hrefl := tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hΨb 0)
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, Ψ (C (-t)) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => Ψ (C (-t)) * phiG (twistG η G) t)
      (B := M * (CB * 2 ^ N)) (fun t ht => ?_) le_rfl).congr fun ε => ?_
    · rw [norm_mul]
      have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have h3 : (1 + |t|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      exact mul_le_mul (hΨb _) ((hpoly' t).trans (by gcongr)) (norm_nonneg _) hM0
    · simp only [mul_assoc]
  have hfar := tendsto_twisted_far_nonres_profile hsl hΦd hΦre hidT hGc hGd hG2 η (m := 1) le_rfl
    (fun n hn => hres n (by rw [hn, Nat.cast_one, one_mul])) hC hα'0 hα'1
    (by positivity) hC' hL hψm hψL hΨ
  -- the reflected integral splits into the far and near twisted pieces
  have hdecomp : ∀ ε : ℝ, 0 < ε →
      ((2 * Real.pi : ℝ) : ℂ) * ((ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
        ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) -
        κ₀ * ((ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
          (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) -
        κ₀ * ((ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, Ψ (C (-t)) *
          (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) = 0 := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hphik := integrable_phiG_twistG_mul_pairKernel hsl hΦre hidT hGc hGd hG2 η hτre0
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have hcongr : ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ =
        ∫ t in Iio (0 : ℝ), κ₀ * (Ψ (C (-t)) *
          (phiG (twistG η G) t * pairKernel (2 * t) τ)) := by
      refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
      have ht0 : t < 0 := ht
      rw [phiG_twistG, linTwist_lineS]
      simp only [phiStar, phiG]
      rw [hlock t ht0]
      ring
    have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
      ext t
      simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h
        by_cases h1 : t ≤ -1
        · exact Or.inl h1
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
      Set.disjoint_left.mpr fun t h1 h2 => by
        simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
    have hΨm : AEStronglyMeasurable (fun t : ℝ => Ψ (C (-t))) volume :=
      (hΨc.measurable.comp (hC.measurable.comp measurable_neg)).aestronglyMeasurable
    have hint := hphik.bdd_mul hΨm (c := M) (Eventually.of_forall fun t => hΨb _)
    have hint1 := hint.integrableOn (s := Iic (-1))
    have hint2 := hint.integrableOn (s := Ioo (-1) 0)
    rw [hcongr, integral_const_mul, hsplit, setIntegral_union hdisj measurableSet_Ioo hint1 hint2]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    linear_combination (↑ε * (κ₀ * ((∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
      (phiG (twistG η G) t * pairKernel (2 * t) τ)) +
        ∫ t in Ioo (-1 : ℝ) 0, Ψ (C (-t)) *
          (phiG (twistG η G) t * pairKernel (2 * t) τ)))) * h2pi
  have hlim := (((hrefl.const_mul ((2 * Real.pi : ℝ) : ℂ)).sub (hfar.const_mul κ₀)).sub
    (hnear.const_mul κ₀))
  have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) - κ₀ * 0 - κ₀ * 0 =
      2 * betaG G := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    push_cast; field_simp; ring
  rw [hval] at hlim
  have hzero : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 (2 * betaG G)) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => hdecomp ε hε)
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hzero tendsto_const_nhds
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)

/-- **Linear lock phases are quantized.**  Let `G` be a Herglotz producer for the weights `lam`.
Suppose that on the lower critical line
`G(1 − s) = κ₀ e^{iη(−τ)} e^{iβ₀C(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`,
where `C` is monotone and `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.  Then `e^{−η/2}` is a
natural number. -/
theorem linear_twist_quantization {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {κ₀ : ℂ} {η β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    ∃ n : ℕ, (n : ℝ) = Real.exp (-(η / 2)) :=
  linear_twist_quantization_profile hsl hΦd hΦre hid hGc hGd hG2 hC hgrowth
    (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I)) (M := 1) (abs_nonneg β₀)
    (continuous_phaseDensity β₀).measurable (fun x => (norm_phaseDensity β₀ x).le)
    (fun _ _ huv => phase_eq_add_setIntegral β₀ huv) (by fun_prop)
    (fun v => (Complex.norm_exp_ofReal_mul_I _).le) hlock

/-- **A linear lock phase of positive slope is impossible.** -/
theorem linear_twist_slope_nonpos {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {κ₀ : ℂ} {η β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    η ≤ 0 := by
  obtain ⟨n, hn⟩ := linear_twist_quantization hsl hΦd hΦre hid hGc hGd hG2 hC hgrowth hlock
  have hpos : (0 : ℝ) < n := by rw [hn]; exact Real.exp_pos _
  have h1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hpos
    exact_mod_cast this
  have h2 : 0 ≤ -(η / 2) := by
    rw [← Real.exp_le_exp, Real.exp_zero, ← hn]; exact h1
  linarith


/-! ### No uniform spectral density -/

/-- **A mixed spectrum carries no uniform density.**  The data of
`mixed_spectrum_power_rigidity` (integer atoms, real atoms, a diffuse part `Φ_d` with
non-integer mass `O(y^α)`, `α < 1`) cannot be completed by a constant `c > 0`:
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = (atoms) + (real atoms) + Φ_d(s) + c` is impossible.
The constant is the Herglotz function of the boundary density `c/π` on the whole line. -/
theorem mixed_spectrum_no_uniform_density {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}
    {Φd : ℂ → ℂ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hΦdd : DifferentiableOn ℂ Φd {s : ℂ | 1 / 2 < s.re})
    (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y →
      phaseSum c u y + (∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re) / Real.pi ≤
        K * y ^ α)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {κ : ℝ} (hκ : 0 < κ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s +
            (κ : ℂ)) :
    False := by
  have hpi := Real.pi_pos
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  have hline_re : ∀ v : ℝ, 0 ≤ (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := fun v =>
    re_nonneg_of_closure hΦdc hΦdre (by simp)
  have hlc : Continuous fun v : ℝ => (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (hΦdc.comp_continuous (by fun_prop) fun v => ?_)
    show 1 / 2 ≤ ((1 / 2 : ℂ) + (v : ℂ) * I).re
    simp
  set D : ℝ → ℝ := fun y => ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re with hD
  have hD0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ D y := fun y hy =>
    intervalIntegral.integral_nonneg (by linarith) fun v _ => hline_re v
  have hcs2 : Summable fun k => c k / u k ^ 2 :=
    summable_div_sq_of_phaseSum_le hc hu1 hut (K := |K|) (K' := 0) fun y hy => by
      have h1 : y ^ α ≤ y := by
        calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy hα1.le
          _ = y := Real.rpow_one y
      have h0 : 0 ≤ y ^ α := Real.rpow_nonneg (by linarith) _
      have h2 : K * y ^ α ≤ |K| * y ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
      have h3 : 0 ≤ D y / Real.pi := div_nonneg (hD0 y (by linarith)) hpi.le
      have h4 := hCK y hy
      simp only [hD] at h3
      nlinarith [abs_nonneg K]
  -- the diffuse part with the constant
  set Φd' : ℂ → ℂ := fun s => Φd s + (κ : ℂ) with hΦd'
  have hid' : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd' s :=
    fun s hs => by rw [hid s hs, hΦd']; ring
  obtain ⟨Φ, G, hΦd, hΦre, hidΦ, hGc, hGd, hG2, hlock₀⟩ :=
    exists_producer_of_mixed_spectrum hone hsum hc hu1 hut hcs2 (hΦdd.add_const _)
      (hΦdc.add continuousOn_const)
      (fun s hs => by simp only [Complex.add_re, Complex.ofReal_re]; linarith [hΦdre s hs])
      hid'
  -- the lock splits into a linear phase and a monotone sublinear phase
  set C : ℝ → ℝ := fun x => phaseSum c u (2 * x) + D (2 * x) / Real.pi with hCdef
  have hDmono : Monotone fun y : ℝ => D (2 * y) := by
    intro a b hab
    simp only [hD]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hlc.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * b)) (-(2 * a)))
      (hlc.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * a)) 0)
    rw [← h]
    have : 0 ≤ ∫ v in -(2 * b)..-(2 * a), (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re :=
      intervalIntegral.integral_nonneg (by linarith) fun v _ => hline_re v
    linarith
  have hCm : Monotone C := fun a b hab => by
    have h1 := phaseSum_mono hc hut (show 2 * a ≤ 2 * b by linarith)
    have h2 := hDmono hab
    simp only [hCdef]
    have : D (2 * a) / Real.pi ≤ D (2 * b) / Real.pi := div_le_div_of_nonneg_right h2 hpi.le
    linarith
  have hCg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α := by
    refine ⟨α, K * 2 ^ α, hα1, fun x hx => ?_⟩
    have h := hCK (2 * x) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h
    simp only [hCdef, hD]; linarith
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((4 * κ) * (-τ) : ℝ) : ℂ) * I) *
        cexp ((((2 * Real.pi) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hint : ∫ v in -(-(2 * τ))..0, (Φd' ((1 / 2 : ℂ) + (v : ℂ) * I)).re =
        D (-(2 * τ)) + κ * (-(2 * τ)) := by
      simp only [hΦd', Complex.add_re, Complex.ofReal_re, hD]
      rw [intervalIntegral.integral_add (hlc.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hCτ : C (-τ) = phaseSum c u (-(2 * τ)) + D (-(2 * τ)) / Real.pi := by
      simp only [hCdef]; ring_nf
    rw [hlock₀ τ hτ0, hint, hCτ, one_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have h := linear_twist_slope_nonpos hsl hΦd hΦre hidΦ hGc hGd hG2 hCm hCg hlock
  linarith

end

end AbelianTwist

end RHTower
