import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilForPairsOfFrobeniusGraphs
import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyUnconditionalEnvelope

/-!
# Hasse–Weil at the integer degrees is RH

Over a curve, Hasse–Weil is a statement about the integer powers `Fⁿ` of Frobenius: the plane
`⟨Δ, Γ_{Fⁿ}⟩` for every `n ≥ 1`. The same holds for the smoothed Frobenius graphs of `Spec ℤ`
(`riemannHypothesis_iff_hasseWeil_integerDegrees`): RH holds iff for every integer `n ≥ 1` the plane
`⟨Γ_1, Γ_n⟩` of the cubic-spline graphs passes the Hasse–Weil test, `|c_B(log n)| ≤ c_B(0)`.

No density is available, `log ℕ` is discrete; the proof uses that the gaps shrink faster than the
orbit correlation can move. The orbit correlation is the zero sum `c_B(t) = Re Σ_z F(z) e^{zt}`
(`orbitCorr_eq_re_lagStructure`) with `Σ ‖F(z)‖ ‖z‖ < ∞` (`summable_norm_lagCoeff_mul_norm`: the
transform of a `C²` bump decays like `|Im z|^{−2}` on each side, the zeros are tempered), so it is
Lipschitz with a constant `e^{t/2}` (`norm_lagStructure_sub_le`). Between `log n` and `log(n + 1)`
the gap is at most `2e^{−t}`, so the integer bounds propagate to `|c_B(t)| ≤ c_B(0) + 2L` for all
`t ≥ 0`, and a bounded orbit is RH (`ArithmeticOrientationGeometry.riemannHypothesis_iff_splineOrbit_subexponential`).

Atomic Frobenius graphs fail Hasse–Weil at the integer degrees for every finite genus
(`exists_twoTermDefect_neg`); smoothed ones pass it with genus `c_B(0)/2` exactly under RH.
-/

open Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- The orbit correlation is the real part of the lag structure. -/
theorem orbitCorr_eq_re_lagStructure (x : ScalingCycle) (v : ℝ) :
    zetaScalingDatum.orbitCorr x v = (lagStructure Zeta23.zetaZeroConfig (cx x.2.2) v).re := by
  rw [← configScalingDatum_zeta_orbitCorr, configScalingDatum_orbitCorr_eq,
    lagStructure_eq Zeta23.zetaZeroConfig x.2.2.2]

/-- `normSq γ(½ + z) = normSq z`. -/
theorem normSq_gammaOf_half_add (z : ℂ) : Complex.normSq (gammaOf (1 / 2 + z)) = Complex.normSq z := by
  calc Complex.normSq (gammaOf (1 / 2 + z)) = Complex.normSq (I * gammaOf (1 / 2 + z)) := by
        rw [Complex.normSq_mul, Complex.normSq_I, one_mul]
    _ = Complex.normSq z := by rw [I_mul_gammaOf_half_add]

/-- **Tempered decay with one extra power**: `Σ_z ‖F(z)‖ ‖z‖ < ∞`. -/
theorem summable_norm_lagCoeff_mul_norm {Z : Zeta23.ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun z : ℂ => ‖lagCoeff Z b z‖ * ‖z‖ := by
  set C := Real.exp w * bumpDecayConstant b ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set H : ℂ → ℝ := fun z => Z.carrier.indicator
    (fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) (1 / 2 + z) with hH
  have hHs : Summable H := by
    have h1 : Summable (Z.carrier.indicator
        fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
      summable_subtype_iff_indicator.mp hZ
    have : H = (Z.carrier.indicator fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∘
        Equiv.addLeft (1 / 2 : ℂ) := by
      funext z; simp [hH]
    rw [this]
    exact (Equiv.summable_iff _).mpr h1
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_) (hHs.mul_left (2 * C))
  by_cases hF : lagCoeff Z b z = 0
  · rw [hF, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun ρ _ => div_nonneg (Nat.cast_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf ρ); linarith)) _)
  have hmem : (1 / 2 + z) ∈ Z.carrier := by
    by_contra h; exact hF (by rw [lagCoeff, Set.indicator_of_notMem h])
  have hre := abs_re_le_of_lagCoeff_ne_zero hF
  have hdec := norm_lagCoeff_le_decay Z hb hw hbs z
  rw [Set.indicator_of_mem hmem] at hdec
  simp only [hH, Set.indicator_of_mem hmem]
  rw [normSq_gammaOf_half_add]
  set y := |z.im|
  have hy : 0 ≤ y := abs_nonneg _
  have hm : (0 : ℝ) ≤ Z.mult (1 / 2 + z) := Nat.cast_nonneg _
  have hz : ‖z‖ ≤ 1 + y := by
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith
  have hzsq : Complex.normSq z ≤ (1 + y) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hd1 : 0 < 1 + y := by linarith
  have hd2 : 0 < 1 + Complex.normSq z := by have := Complex.normSq_nonneg z; linarith
  have hy3 : (1 + y) ^ 2 ≤ (1 + y) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hy1 : 1 ≤ (1 + y) ^ 3 := one_le_pow₀ (by linarith)
  have h3 : (1 + Complex.normSq z) / 2 ≤ (1 + y) ^ 3 := by linarith
  calc ‖lagCoeff Z b z‖ * ‖z‖
      ≤ (Z.mult (1 / 2 + z) : ℝ) * C / (1 + y) ^ 4 * (1 + y) :=
        mul_le_mul hdec hz (norm_nonneg _) (by positivity)
    _ = (Z.mult (1 / 2 + z) : ℝ) * C / (1 + y) ^ 3 := by
        field_simp
    _ ≤ 2 * C * ((Z.mult (1 / 2 + z) : ℝ) / (1 + Complex.normSq z)) := by
        rw [div_le_iff₀ (by positivity)]
        have hA : 0 ≤ 2 * C * ((Z.mult (1 / 2 + z) : ℝ) / (1 + Complex.normSq z)) := by positivity
        calc (Z.mult (1 / 2 + z) : ℝ) * C =
              2 * C * ((Z.mult (1 / 2 + z) : ℝ) / (1 + Complex.normSq z)) *
                ((1 + Complex.normSq z) / 2) := by field_simp
          _ ≤ 2 * C * ((Z.mult (1 / 2 + z) : ℝ) / (1 + Complex.normSq z)) * (1 + y) ^ 3 :=
              mul_le_mul_of_nonneg_left h3 hA

/-- `‖e^{zt} − e^{zs}‖ ≤ ‖z‖ (t − s) e^{t/2}` for `|Re z| ≤ ½`, `0 ≤ s ≤ t`. -/
theorem norm_cexp_sub_le {z : ℂ} (hz : |z.re| ≤ 1 / 2) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖cexp (z * t) - cexp (z * s)‖ ≤ ‖z‖ * (t - s) * Real.exp (t / 2) := by
  have hderiv : ∀ τ ∈ Set.Icc s t, HasDerivWithinAt (fun τ : ℝ => cexp (z * τ))
      (z * cexp (z * τ)) (Set.Icc s t) τ := by
    intro τ _
    have h1 : HasDerivAt (fun τ : ℝ => z * (τ : ℂ)) (z * 1) τ :=
      ((hasDerivAt_id τ).ofReal_comp).const_mul z
    have h2 := h1.cexp
    simpa [mul_comm] using h2.hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.Ico s t, ‖z * cexp (z * τ)‖ ≤ ‖z‖ * Real.exp (t / 2) := by
    intro τ hτ
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (z * (τ : ℂ)).re = z.re * τ := by simp
    rw [this]
    have hτ0 : 0 ≤ τ := hs.trans hτ.1
    calc z.re * τ ≤ |z.re| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ0
      _ ≤ 1 / 2 * t := mul_le_mul hz hτ.2.le hτ0 (by norm_num)
      _ = t / 2 := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨hst, le_rfl⟩
  calc ‖cexp (z * t) - cexp (z * s)‖ ≤ ‖z‖ * Real.exp (t / 2) * (t - s) := this
    _ = ‖z‖ * (t - s) * Real.exp (t / 2) := by ring

/-- **The lag structure is Lipschitz with constant `L e^{t/2}`.** -/
theorem norm_lagStructure_sub_le {Z : Zeta23.ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖lagStructure Z b t - lagStructure Z b s‖ ≤
      (∑' z : ℂ, ‖lagCoeff Z b z‖ * ‖z‖) * (t - s) * Real.exp (t / 2) := by
  obtain ⟨hst1, hst2⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs t
  obtain ⟨hss1, hss2⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs s
  have hL := summable_norm_lagCoeff_mul_norm hZ hb hw hbs
  have hterm : ∀ z : ℂ, ‖lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s)‖ ≤
      ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (t / 2)) := by
    intro z
    by_cases hF : lagCoeff Z b z = 0
    · simp [hF]
    rw [← mul_sub, norm_mul]
    have := norm_cexp_sub_le (abs_re_le_of_lagCoeff_ne_zero hF) hs hst
    calc ‖lagCoeff Z b z‖ * ‖cexp (z * t) - cexp (z * s)‖
        ≤ ‖lagCoeff Z b z‖ * (‖z‖ * (t - s) * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hsum : Summable fun z : ℂ => ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (t / 2)) :=
    hL.mul_right _
  rw [hst2, hss2, ← hst1.tsum_sub hss1]
  calc ‖∑' z, (lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s))‖
      ≤ ∑' z, ‖lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)
    _ ≤ ∑' z, ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (t / 2)) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)
          hsum
    _ = _ := by rw [tsum_mul_right]; ring

/-- Between `log n` and `log(n + 1)`, `n = ⌊eᵗ⌋`, the gap is at most `2e^{−t}`. -/
theorem floor_log_gap {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ⌊Real.exp t⌋₊ ∧ Real.log ⌊Real.exp t⌋₊ ≤ t ∧
      t - Real.log ⌊Real.exp t⌋₊ ≤ 2 * Real.exp (-t) := by
  set n := ⌊Real.exp t⌋₊ with hn
  have he1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using he1)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hle : (n : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hlt : Real.exp t < n + 1 := Nat.lt_floor_add_one _
  have hlog : Real.log n ≤ t := by
    rw [← Real.log_exp t]; exact Real.log_le_log (by linarith) hle
  refine ⟨hn1, hlog, ?_⟩
  have hgap : t - Real.log n ≤ 1 / n := by
    have h1 : t - Real.log n = Real.log (Real.exp t / n) := by
      rw [Real.log_div (Real.exp_pos t).ne' (by positivity), Real.log_exp]
    rw [h1]
    have h2 := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos t) (by positivity : (0 : ℝ) < n))
    have h3 : Real.exp t / n - 1 ≤ 1 / n := by
      rw [div_sub_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]; linarith
    linarith
  have h4 : 1 / (n : ℝ) ≤ 2 * Real.exp (-t) := by
    have h5 : Real.exp t ≤ 2 * n := by linarith
    have hmul : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h5 (Real.exp_pos (-t)).le]
  linarith

/-- **Hasse–Weil at the integer degrees is RH.** -/
theorem riemannHypothesis_iff_hasseWeil_integerDegrees :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → zetaScalingDatum.HasseWeilAt splineCycle (Real.log n) := by
  constructor
  · intro hRH n _
    exact (riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH) _
  · intro h
    rw [riemannHypothesis_iff_splineOrbit_subexponential]
    set x := splineCycle
    have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
    obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
      (cx_hasCompactSupport hf.2)
    have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
      by_contra hc; exact hu (hw u (not_le.mp hc))
    set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖ with hLdef
    have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
    set c := zetaScalingDatum.orbitCorr x with hc
    have hc0 : 0 ≤ c 0 := by
      have := h 1 one_pos
      rw [ScalingDatum.HasseWeilAt, Nat.cast_one, Real.log_one] at this
      exact (abs_nonneg _).trans this
    -- the orbit correlation is bounded on `[0, ∞)`
    have hbdd : ∀ t : ℝ, 0 ≤ t → |c t| ≤ c 0 + 2 * L := by
      intro t ht
      obtain ⟨hn1, hlog, hgap⟩ := floor_log_gap ht
      set n := ⌊Real.exp t⌋₊
      have hs0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hHW := h n (by omega)
      rw [ScalingDatum.HasseWeilAt] at hHW
      have hlip := norm_lagStructure_sub_le SquareRootThreshold.temperedConfig_zetaZeroConfig
        (cx_contDiff hf.1) hw0 hbs hs0 hlog
      have hdiff : |c t - c (Real.log n)| ≤ L * (t - Real.log n) * Real.exp (t / 2) := by
        rw [hc, orbitCorr_eq_re_lagStructure, orbitCorr_eq_re_lagStructure, ← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans hlip
      have hexp : (t - Real.log n) * Real.exp (t / 2) ≤ 2 := by
        have h1 : Real.exp (-t) * Real.exp (t / 2) ≤ 1 := by
          rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
        calc (t - Real.log n) * Real.exp (t / 2) ≤ 2 * Real.exp (-t) * Real.exp (t / 2) :=
              mul_le_mul_of_nonneg_right hgap (Real.exp_pos (t / 2)).le
          _ ≤ 2 := by nlinarith
      have hmove : |c t - c (Real.log n)| ≤ 2 * L := by
        calc |c t - c (Real.log n)| ≤ L * ((t - Real.log n) * Real.exp (t / 2)) := by
              rw [← mul_assoc]; exact hdiff
          _ ≤ L * 2 := mul_le_mul_of_nonneg_left hexp hL0
          _ = 2 * L := by ring
      calc |c t| = |c (Real.log n) + (c t - c (Real.log n))| := by rw [add_sub_cancel]
        _ ≤ |c (Real.log n)| + |c t - c (Real.log n)| := abs_add_le _ _
        _ ≤ c 0 + 2 * L := add_le_add hHW hmove
    intro ε hε
    refine ⟨c 0 + 2 * L, fun t ht => ?_⟩
    have hK : 0 ≤ c 0 + 2 * L := by linarith
    calc |c t| ≤ c 0 + 2 * L := hbdd t ht
      _ ≤ (c 0 + 2 * L) * Real.exp (ε * t) :=
        le_mul_of_one_le_right hK (Real.one_le_exp (by positivity))

end GaloisForLFunctions.SurfaceOfSpecZ
