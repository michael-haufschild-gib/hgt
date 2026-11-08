import GaloisForLFunctions.SurfaceOfSpecZ.SparseDegreesDecideRH
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees

/-!
# The Stepanov count at the square degrees

Bombieri's form of Stepanov's method bounds the points of a curve over the extensions of **even**
degree, `N_{2k} ≤ q^{2k} + O(q^k)`, and this alone gives Weil's theorem. Over `ℤ` the degree of a
Frobenius graph is multiplicative: the even powers of Frobenius are the graphs of **square** degree,
`Γ_{n²} = Γ_n ∘ Γ_n`.

* `riemannHypothesis_iff_bddBelow_of_sqrtGaps`: for any set `D` of degrees with gaps `O(√x)`, RH holds
  iff `c_B(log d) ≥ −K` for all `d ∈ D`.
* `riemannHypothesis_iff_bddBelow_squareDegrees`: RH holds iff the traces of the smoothed Frobenius
  graphs of square degree are bounded below — an upper bound on the smoothed point counts over the
  "even extensions" of `𝔽₁`.

The proof joins `SparseDegreesDecideRH` (between a degree `d` with `eᵗ − d ≤ M e^{t/2}` and `t` the
orbit correlation moves by at most `4ML`) to the Landau core of `OneSidedHasseWeilAtTheIntegerDegrees`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **From `√`-gap degrees to every large scale.** -/
theorem exists_orbitCorr_sub_sqrtGap_le {D : Set ℕ} (hD : SqrtGaps D) :
    ∃ C T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∃ d ∈ D,
      |zetaScalingDatum.orbitCorr splineCycle t -
        zetaScalingDatum.orbitCorr splineCycle (Real.log d)| ≤ C := by
  obtain ⟨hpos, M, hM0, hgapD⟩ := hD
  set x := splineCycle
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra hc; exact hu (hw u (not_le.mp hc))
  set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  set c := zetaScalingDatum.orbitCorr x with hc
  refine ⟨4 * M * L, 2 * Real.log (2 * M + 1),
    mul_nonneg two_pos.le (Real.log_nonneg (by linarith)), fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (mul_nonneg two_pos.le (Real.log_nonneg (by linarith))) ht
  -- the gap is at most half the height
  have hhalf : 2 * M * Real.sqrt (Real.exp t) ≤ Real.exp t := by
    have hsq : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    rw [hsq, show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf]
    have : 2 * M + 1 ≤ Real.exp (t / 2) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * M + 1)]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos (t / 2)]
  obtain ⟨d, hdD, hdle, hdgap⟩ := hgapD (Real.exp t) (Real.one_le_exp ht0)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d hdD
  have hdhalf : Real.exp t ≤ 2 * d := by linarith
  have hlogd : Real.log d ≤ t := by
    rw [← Real.log_exp t]; exact Real.log_le_log hd0 hdle
  have hs0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hpos d hdD)
  have hlip := norm_lagStructure_sub_le SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff hf.1) hw0 hbs hs0 hlogd
  have hdiff : |c t - c (Real.log d)| ≤ L * (t - Real.log d) * Real.exp (t / 2) := by
    rw [hc, orbitCorr_eq_re_lagStructure, orbitCorr_eq_re_lagStructure, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hlip
  have hg := log_gap_of_sqrtGap hd0 hdgap
  have hg2 : M * Real.exp t / d ≤ 2 * M := by
    rw [div_le_iff₀ hd0]; nlinarith [mul_le_mul_of_nonneg_left hdhalf hM0]
  refine ⟨d, hdD, ?_⟩
  calc |c t - c (Real.log d)| ≤ L * ((t - Real.log d) * Real.exp (t / 2)) := by
        rw [← mul_assoc]; exact hdiff
    _ ≤ L * (2 * M) := mul_le_mul_of_nonneg_left (hg.trans hg2) hL0
    _ ≤ 4 * M * L := by nlinarith [mul_nonneg hM0 hL0]

/-- **One side at `√`-gap degrees.** -/
theorem riemannHypothesis_iff_bddBelow_of_sqrtGaps {D : Set ℕ} (hD : SqrtGaps D) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ d ∈ D,
      -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log d) := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun d hd => ?_⟩
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) d (hD.1 d hd)
    rw [ScalingDatum.HasseWeilAt] at h
    linarith [neg_abs_le (zetaScalingDatum.orbitCorr splineCycle (Real.log d))]
  · rintro ⟨K, hK⟩
    obtain ⟨C, T, hT0, hCT⟩ := exists_orbitCorr_sub_sqrtGap_le hD
    set c := zetaScalingDatum.orbitCorr splineCycle with hc
    -- `c ≥ −B` on `[0, ∞)`: by the gaps above `T`, by continuity below
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuous_zetaOrbitCorr' splineCycle).continuousOn
    have hall : ∀ u : ℝ, 0 ≤ u →
        -((2 * (|K| + C + |B|)) * Real.exp (0 * u)) ≤
          2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
      intro u hu
      rw [← orbitCorr_eq_re_lagStructure_spline, zero_mul, Real.exp_zero, mul_one]
      rcases le_total u T with huT | hTu
      · have h := hB u ⟨hu, huT⟩
        rw [Real.norm_eq_abs] at h
        have := (abs_le.mp (h.trans (le_abs_self B))).1
        have hC0 : 0 ≤ C := by
          obtain ⟨d, -, hd⟩ := hCT T le_rfl
          exact (abs_nonneg _).trans hd
        linarith [abs_nonneg K]
      · obtain ⟨d, hdD, hd⟩ := hCT u hTu
        have h1 := hK d hdD
        have := (abs_le.mp hd).1
        linarith [le_abs_self K, abs_nonneg B]
    apply riemannHypothesis_of_forall_re_le
    intro ρ hρ
    by_contra hre
    push Not at hre
    exact evenCoeff_spline_sees hρ hre
      (evenCoeff_eq_zero_of_two_re_lagStructure_ge zetaZeroConfig
        SquareRootThreshold.temperedConfig_zetaZeroConfig (contDiff_boxSpline one_pos 2)
        (boxSpline_support one_pos 3) le_rfl (by norm_num)
        (fun x hx him => absurd him (evenCoeff_spline_real hx)) hall
        (by simp; linarith))

/-- **The Stepanov count at the square degrees.** RH holds iff the traces of the smoothed Frobenius
graphs of square degree are bounded below: an upper bound on the smoothed point counts over the even
extensions. -/
theorem riemannHypothesis_iff_bddBelow_squareDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log ((n ^ 2 : ℕ) : ℝ)) := by
  rw [riemannHypothesis_iff_bddBelow_of_sqrtGaps sqrtGaps_squares]
  constructor
  · rintro ⟨K, hK⟩; exact ⟨K, fun n hn => hK _ ⟨n, hn, rfl⟩⟩
  · rintro ⟨K, hK⟩; exact ⟨K, fun d ⟨n, hn, hd⟩ => hd ▸ hK n hn⟩

end GaloisForLFunctions.SurfaceOfSpecZ
