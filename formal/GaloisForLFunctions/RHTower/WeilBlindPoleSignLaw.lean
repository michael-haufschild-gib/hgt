import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift
import GaloisForLFunctions.RHTower.WeilConeDegreePoleSandwich

/-!
# The archimedean part is bounded below by the anomaly: violators are pole-negative

For a Weil test `f` with autocorrelation `k = f ⋆ f̃`, the pole and archimedean part of the Weil
functional is `weilArchRe k = Re P(k) + (1/2π) ∫ |f̂(r)|² γ(r) dr`, where
`P(k) = k̂(i/2) + k̂(−i/2)` is the pole term (`weilPoleTerm`) and
`γ(r) = Re ψ(¼ + ir/2) − log π` is the archimedean symbol (`EF.gammaBracket`).

**Theorem** (`pole_add_anomaly_le_weilArchRe`).
`Re P(k) + γ(0) ‖f‖² ≤ weilArchRe k`.

Proof: `γ(r) ≥ γ(0)` for every real `r` (the Lévy–Khintchine form of `θ'`), and Plancherel
`∫ |f̂|² = 2π ‖f‖²`.

The anomaly `γ(0) = ψ(¼) − log π` is negative. Summing over a nonnegative combination of
autocorrelations:

* **Pole-heavy combinations are positive** (`sum_weilArchRe_nonneg_of_pole_ge`): if the total pole
  term is at least `−γ(0)` times the total mass, the pole and archimedean part is nonnegative. In
  particular prime-blind positivity can fail only on combinations whose pole term is below
  `−γ(0) Σ c_f ‖f‖²`.
* **Strong violators are pole-negative** (`sum_pole_lt_of_sum_weilArchRe_lt`): if the pole and
  archimedean part is below `−K` times the total mass, the total pole term is below
  `−(K + γ(0))` times the total mass.

Neither statement uses blindness or any information about `ζ`.

**Parity** (`weilPoleTerm_even`, `weilPoleTerm_odd`).  The pole term is `+2|∫ f e^{−u/2}|²` for an
even test and `−2|∫ f e^{−u/2}|²` for an odd one.  Hence for even tests the anomaly is the only
negative contribution: `γ(0) ‖f‖² ≤ weilArchRe (f ⋆ f̃)` (`anomaly_le_weilArchRe_of_even`), and
even violations of prime-blind positivity are bounded by `γ(0)`.
-/

open Complex MeasureTheory Set Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower

open WeilOneSided

/-- The archimedean symbol is minimal at the origin. -/
theorem gammaBracket_zero_le (r : ℝ) : EF.gammaBracket 0 ≤ EF.gammaBracket r := by
  rw [WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  linarith [gammaHardyPhaseRate_zero_le_levy r]

/-- **The anomaly bound**: `Re P(k) + γ(0) ‖f‖² ≤ weilArchRe k` for `k = f ⋆ f̃`. -/
theorem pole_add_anomaly_le_weilArchRe {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest f f)).re + EF.gammaBracket 0 * ∫ x, ‖f x‖ ^ 2 ≤
      weilArchRe (EF.weilTest f f) := by
  have hfcont := hf.continuous
  obtain ⟨a, ha⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hsupp : tsupport f ⊆ Icc (-a) a := by
    intro x hx
    have := ha hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hplanch := integral_norm_paperFT_sq hf hsupp
  -- the archimedean integrand is real
  have hint := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [paperFT_weilTest_self_ofReal hfcont hfc r]
    push_cast
    ring
  have hintR : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * EF.gammaBracket r :=
    hint.re.congr (Filter.Eventually.of_forall fun r => by
      simp only
      rw [hreal r]
      exact Complex.ofReal_re _)
  have hsq : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 := by
    by_contra hni
    have h0 : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 = 0 := integral_undef hni
    have hnorm : ∫ x : ℝ, ‖f x‖ ^ 2 = 0 := by
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [h0] at hplanch
      have := hplanch.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpi.ne'
      · exact h
    have hf0 : ∀ x, f x = 0 := by
      have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
      have hi : Integrable fun x => ‖f x‖ ^ 2 :=
        hcont.integrable_of_hasCompactSupport
          (hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      have hz := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).mp hnorm
      have hfun : (fun x => ‖f x‖ ^ 2) = 0 :=
        Continuous.ae_eq_iff_eq volume hcont continuous_const |>.mp hz
      intro x
      have := congrFun hfun x
      simpa using this
    apply hni
    have : (fun r : ℝ => ‖paperFT f r‖ ^ 2) = fun _ => 0 := by
      funext r
      rw [paperFT_def]
      simp [hf0]
    rw [this]
    exact integrable_zero _ _ _
  have hint_eq : ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hreal]
    exact integral_complex_ofReal
  have hlower : EF.gammaBracket 0 * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 ≤
      ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r := by
    rw [← integral_const_mul]
    refine integral_mono (hsq.const_mul _) hintR fun r => ?_
    have := gammaBracket_zero_le r
    have h0 : 0 ≤ ‖paperFT f r‖ ^ 2 := by positivity
    nlinarith
  have hW : weilArchRe (EF.weilTest f f) = (weilPoleTerm (EF.weilTest f f)).re +
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r := by
    unfold weilArchRe weilPoleTerm
    rw [hint_eq, Complex.add_re]
    congr 1
    have hc : (1 / (2 * (Real.pi : ℂ))) *
        ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) =
        (((1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc, Complex.ofReal_re]
  rw [hW]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have key : EF.gammaBracket 0 * ∫ x, ‖f x‖ ^ 2 ≤
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r := by
    rw [hplanch] at hlower
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpi]
    linarith
  linarith

/-- The anomaly bound for a Weil test. -/
theorem pole_add_anomaly_le_weilArchRe' (f : WeilTestFn) :
    (weilPoleTerm (EF.weilTest f.1 f.1)).re + EF.gammaBracket 0 * ∫ x, ‖f.1 x‖ ^ 2 ≤
      weilArchRe (EF.weilTest f.1 f.1) :=
  pole_add_anomaly_le_weilArchRe f.2.1 f.2.2

/-- The anomaly bound summed over a nonnegative combination of autocorrelations. -/
theorem sum_pole_add_anomaly_le (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) +
        EF.gammaBracket 0 * (c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2) ≤
      c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1) := by
  rw [Finsupp.mul_sum, ← Finsupp.sum_add]
  refine Finsupp.sum_le_sum fun f _ => ?_
  have h := pole_add_anomaly_le_weilArchRe' f
  have := hc f
  nlinarith

/-- **Pole-heavy combinations are positive.** -/
theorem sum_weilArchRe_nonneg_of_pole_ge (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (hP : -EF.gammaBracket 0 * (c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2) ≤
      c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) :
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1) := by
  have h := sum_pole_add_anomaly_le c hc
  linarith

/-- **Strong violators are pole-negative.**  If the pole and archimedean part of a nonnegative
combination is below `−K` times its mass, its pole term is below `−(K + γ(0))` times its mass. -/
theorem sum_pole_lt_of_sum_weilArchRe_lt (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) {K : ℝ}
    (hA : (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) <
      -K * c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2) :
    (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) <
      -(K + EF.gammaBracket 0) * c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2 := by
  have h := sum_pole_add_anomaly_le c hc
  linarith

/-! ### Parity of the pole term -/

/-- For an even test the two exponential moments coincide. -/
theorem paperFT_neg_I_div_two_of_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) :
    paperFT f (-I / 2) = paperFT f (I / 2) := by
  rw [paperFT_def, paperFT_def, ← integral_neg_eq_self]
  congr 1; funext u
  rw [heven]; congr 1; push_cast; ring_nf

/-- For an odd test the two exponential moments are opposite. -/
theorem paperFT_neg_I_div_two_of_odd {f : ℝ → ℂ} (hodd : ∀ x, f (-x) = -f x) :
    paperFT f (-I / 2) = -paperFT f (I / 2) := by
  rw [paperFT_def, paperFT_def, ← integral_neg_eq_self, ← integral_neg]
  congr 1; funext u
  rw [hodd]; push_cast; ring_nf

/-- **The pole term of an even test is `2|∫ f e^{−u/2}|² ≥ 0`.** -/
theorem weilPoleTerm_even {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ x, f (-x) = f x) :
    weilPoleTerm (EF.weilTest f f) = ((2 * ‖paperFT f (I / 2)‖ ^ 2 : ℝ) : ℂ) := by
  have hI : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat, neg_div]
  have hI' : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  unfold weilPoleTerm
  rw [EF.paperFT_weilTest hf hf hfc hfc, EF.paperFT_weilTest hf hf hfc hfc, hI, hI',
    paperFT_neg_I_div_two_of_even heven, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- **The pole term of an odd test is `−2|∫ f e^{−u/2}|² ≤ 0`.** -/
theorem weilPoleTerm_odd {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) :
    weilPoleTerm (EF.weilTest f f) = ((-(2 * ‖paperFT f (I / 2)‖ ^ 2) : ℝ) : ℂ) := by
  have hI : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat, neg_div]
  have hI' : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  unfold weilPoleTerm
  rw [EF.paperFT_weilTest hf hf hfc hfc, EF.paperFT_weilTest hf hf hfc hfc, hI, hI',
    paperFT_neg_I_div_two_of_odd hodd, map_neg, mul_neg, neg_mul, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- **Even tests: the anomaly is the only negative contribution.**  For an even test,
`γ(0) ‖f‖² ≤ weilArchRe (f ⋆ f̃)`; so even violations of prime-blind positivity are bounded by the
anomaly `γ(0) = ψ(¼) − log π`. -/
theorem anomaly_le_weilArchRe_of_even {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (heven : ∀ x, f (-x) = f x) :
    EF.gammaBracket 0 * ∫ x, ‖f x‖ ^ 2 ≤ weilArchRe (EF.weilTest f f) := by
  have h := pole_add_anomaly_le_weilArchRe hf hfc
  rw [weilPoleTerm_even hf.continuous hfc heven, Complex.ofReal_re] at h
  have : 0 ≤ 2 * ‖paperFT f (I / 2)‖ ^ 2 := by positivity
  linarith

end RHTower
