import GaloisForLFunctions.SurfaceOfSpecZ.SparseDegreesDecideRH
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# Hasse–Weil at the prime degrees bounds the zero width by `1/12`

`SparseDegreesDecideRH` decides RH on any set of degrees with gaps `O(√x)`. A set `D` with gaps
`O(x^θ)` at large heights (`PowGaps θ D`) decides the width up to the excess of its gap exponent over
the critical abscissa (`zetaZeroWidth_le_of_hasseWeil_of_powGaps`):

  **Hasse–Weil on the planes `⟨Γ_1, Γ_d⟩`, `d ∈ D`, forces `zetaZeroWidth ≤ θ − ½`.**

Between `log d` and `t` the orbit correlation moves by at most `L (t − log d) e^{t/2} ≤ 2LM e^{(θ−½)t}`,
and the rate law `zeta_splineOrbit_rate_iff_zetaZeroWidth_le` reads the width off this growth. For
the primes, Huxley's theorem (`RHTower.eventually_exists_prime_short_interval_seven_twelfths`) gives
every `θ > 7/12` (`powGaps_primes`), hence (`zetaZeroWidth_le_of_hasseWeil_primeDegrees`)

  **Hasse–Weil on the planes `⟨Γ_1, Γ_p⟩`, `p` prime, puts every zero in `|Re ρ − ½| ≤ 1/12`.**

The converse transfer runs at the same exponent: zeros of width `σ` give primes in intervals of
length `x^{½+σ+ε}`. The two transfers compose to the identity on the exponent, so the prime planes
decide RH by this route exactly when the prime gaps are `x^{½+o(1)}`; the pairs `⟨Γ_p, Γ_q⟩` need no
gap input (`HasseWeilForPairsOfPrimeDegrees`).
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- `D` has gaps `O(x^θ)` at large heights. -/
def PowGaps (θ : ℝ) (D : Set ℕ) : Prop :=
  (∀ d ∈ D, 0 < d) ∧
    ∃ M X : ℝ, 0 ≤ M ∧ ∀ x : ℝ, X ≤ x → ∃ d ∈ D, (d : ℝ) ≤ x ∧ x - d ≤ M * x ^ θ

/-- A degree `d ≥ eᵗ/2` with `eᵗ − d ≤ M e^{θt}` satisfies `(t − log d) e^{t/2} ≤ 2M e^{(θ−½)t}`. -/
theorem log_gap_mul_le {t θ M d : ℝ} (hM : 0 ≤ M) (hd0 : 0 < d)
    (hgap : Real.exp t - d ≤ M * Real.exp (θ * t)) (hhalf : Real.exp t ≤ 2 * d) :
    (t - Real.log d) * Real.exp (t / 2) ≤ 2 * M * Real.exp ((θ - 1 / 2) * t) := by
  have h1 : t - Real.log d ≤ (Real.exp t - d) / d := by
    have := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos t) hd0)
    rw [Real.log_div (Real.exp_pos t).ne' hd0.ne', Real.log_exp, div_sub_one hd0.ne'] at this
    exact this
  have he : Real.exp t * Real.exp ((θ - 1) * t) = Real.exp (θ * t) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (Real.exp t - d) / d ≤ 2 * M * Real.exp ((θ - 1) * t) := by
    rw [div_le_iff₀ hd0]
    have hpos : 0 ≤ M * Real.exp ((θ - 1) * t) := mul_nonneg hM (Real.exp_pos _).le
    have hM' : M * Real.exp (θ * t) = Real.exp t * (M * Real.exp ((θ - 1) * t)) := by
      rw [← he]; ring
    nlinarith [mul_le_mul_of_nonneg_right hhalf hpos]
  have hex : Real.exp ((θ - 1) * t) * Real.exp (t / 2) = Real.exp ((θ - 1 / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  calc (t - Real.log d) * Real.exp (t / 2) ≤ 2 * M * Real.exp ((θ - 1) * t) * Real.exp (t / 2) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = 2 * M * Real.exp ((θ - 1 / 2) * t) := by rw [mul_assoc, hex]

/-- **Degrees with gaps `O(x^θ)` bound the width by `θ − ½`.** -/
theorem zetaZeroWidth_le_of_hasseWeil_of_powGaps {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    {D : Set ℕ} (hD : PowGaps θ D)
    (h : ∀ d ∈ D, zetaScalingDatum.HasseWeilAt splineCycle (Real.log d)) :
    zetaZeroWidth ≤ θ - 1 / 2 := by
  obtain ⟨hpos, M, X, hM0, hgapD⟩ := hD
  rw [← zeta_splineOrbit_rate_iff_zetaZeroWidth_le (by linarith : (0 : ℝ) ≤ θ - 1 / 2)]
  set x := splineCycle
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra hc; exact hu (hw u (not_le.mp hc))
  set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  set c := zetaScalingDatum.orbitCorr x with hc
  -- the threshold height: `eᵗ ≥ X` and `2M e^{θt} ≤ eᵗ`
  set T₀ : ℝ := max (Real.log (max X 1)) (Real.log (2 * M + 1) / (1 - θ)) with hT₀
  have hbig : ∀ t : ℝ, T₀ ≤ t → |c t| ≤ c 0 + 2 * L * M * Real.exp ((θ - 1 / 2) * t) := by
    intro t ht
    have hX : X ≤ Real.exp t := by
      have h1 : Real.log (max X 1) ≤ t := (le_max_left _ _).trans ht
      calc X ≤ max X 1 := le_max_left _ _
        _ = Real.exp (Real.log (max X 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr h1
    have hsmall : 2 * M * Real.exp (θ * t) ≤ Real.exp t := by
      have h1 : Real.log (2 * M + 1) ≤ (1 - θ) * t := by
        have := (le_max_right _ _).trans ht
        rwa [div_le_iff₀ (by linarith), mul_comm] at this
      have h2 : 2 * M + 1 ≤ Real.exp ((1 - θ) * t) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * M + 1)]
        exact Real.exp_le_exp.mpr h1
      have he : Real.exp ((1 - θ) * t) * Real.exp (θ * t) = Real.exp t := by
        rw [← Real.exp_add]; ring_nf
      nlinarith [Real.exp_pos (θ * t)]
    obtain ⟨d, hdD, hdle, hdgap⟩ := hgapD (Real.exp t) hX
    rw [← Real.exp_mul, mul_comm t θ] at hdgap
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d hdD
    have hhalf : Real.exp t ≤ 2 * d := by nlinarith
    have hlogd : Real.log d ≤ t := by
      rw [← Real.log_exp t]; exact Real.log_le_log hd0 hdle
    have hs0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hpos d hdD)
    have hlip := norm_lagStructure_sub_le SquareRootThreshold.temperedConfig_zetaZeroConfig
      (cx_contDiff hf.1) hw0 hbs hs0 hlogd
    have hdiff : |c t - c (Real.log d)| ≤ L * (t - Real.log d) * Real.exp (t / 2) := by
      rw [hc, orbitCorr_eq_re_lagStructure, orbitCorr_eq_re_lagStructure, ← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hlip
    have hg := log_gap_mul_le hM0 hd0 hdgap hhalf
    have hmove : |c t - c (Real.log d)| ≤ 2 * L * M * Real.exp ((θ - 1 / 2) * t) := by
      calc |c t - c (Real.log d)| ≤ L * ((t - Real.log d) * Real.exp (t / 2)) := by
            rw [← mul_assoc]; exact hdiff
        _ ≤ L * (2 * M * Real.exp ((θ - 1 / 2) * t)) := mul_le_mul_of_nonneg_left hg hL0
        _ = 2 * L * M * Real.exp ((θ - 1 / 2) * t) := by ring
    have hHW := h d hdD
    rw [ScalingDatum.HasseWeilAt] at hHW
    calc |c t| = |c (Real.log d) + (c t - c (Real.log d))| := by rw [add_sub_cancel]
      _ ≤ |c (Real.log d)| + |c t - c (Real.log d)| := abs_add_le _ _
      _ ≤ c 0 + 2 * L * M * Real.exp ((θ - 1 / 2) * t) := add_le_add hHW hmove
  -- `c 0 ≥ 0`: Hasse–Weil holds at some degree
  have hc0 : 0 ≤ c 0 := by
    obtain ⟨d, hdD, -, -⟩ := hgapD (max X 0) (le_max_left _ _)
    have hHW := h d hdD
    rw [ScalingDatum.HasseWeilAt] at hHW
    exact (abs_nonneg _).trans hHW
  -- below the threshold the correlation is bounded by continuity
  have hcont := continuous_zetaOrbitCorr' x
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B 0 + (c 0 + 2 * L * M), fun t ht => ?_⟩
  have he1 : 1 ≤ Real.exp ((θ - 1 / 2) * t) := Real.one_le_exp (mul_nonneg (by linarith) ht)
  have hLM : 0 ≤ 2 * L * M := by positivity
  rcases le_total t T₀ with htT | hTt
  · have hb : |c t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ⟨ht, htT⟩
    nlinarith [le_max_left B 0, le_max_right B 0]
  · have := hbig t hTt
    nlinarith [le_max_right B 0]

/-- **The primes have gaps `O(x^α)` for every `α > 7/12`** (Huxley). -/
theorem powGaps_primes {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) :
    PowGaps α {p : ℕ | p.Prime} := by
  refine ⟨fun p hp => hp.pos, ?_⟩
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (RHTower.eventually_exists_prime_short_interval_seven_twelfths hα hα1)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < 1 - α by linarith)).eventually_ge_atTop 2).and
      ((eventually_ge_atTop (2 * max Y 0)).and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨1, X, zero_le_one, fun x hx => ?_⟩
  obtain ⟨hx2, hxY, hx0⟩ := hX x hx
  have hsplit : x = x ^ α * x ^ (1 - α) := by
    rw [← Real.rpow_add hx0, show α + (1 - α) = 1 by ring, Real.rpow_one]
  have hxa0 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hxa : 2 * x ^ α ≤ x := by
    calc 2 * x ^ α ≤ x ^ (1 - α) * x ^ α := mul_le_mul_of_nonneg_right hx2 hxa0.le
      _ = x := by rw [mul_comm, ← hsplit]
  set y := x - x ^ α with hy
  have hyY : Y ≤ y := by linarith [le_max_left Y 0]
  have hy0 : 0 ≤ y := by linarith [le_max_right Y 0]
  obtain ⟨p, hp, hyp, hpy⟩ := hY y hyY
  have hya : y ^ α ≤ x ^ α :=
    Real.rpow_le_rpow hy0 (by linarith) (by linarith)
  exact ⟨p, hp, by linarith, by linarith⟩

/-- **Hasse–Weil at the prime degrees puts every zero within `1/12` of the critical line.** -/
theorem zetaZeroWidth_le_of_hasseWeil_primeDegrees
    (h : ∀ p : ℕ, p.Prime → zetaScalingDatum.HasseWeilAt splineCycle (Real.log p)) :
    zetaZeroWidth ≤ 1 / 12 := by
  by_contra hw
  push Not at hw
  set α : ℝ := min (7 / 12 + (zetaZeroWidth - 1 / 12) / 2) (3 / 4) with hα
  have hα1 : 7 / 12 < α := lt_min (by linarith) (by norm_num)
  have hα2 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hle := zetaZeroWidth_le_of_hasseWeil_of_powGaps (by linarith) hα2 (powGaps_primes hα1 hα2)
    fun p hp => h p hp
  have : α ≤ 7 / 12 + (zetaZeroWidth - 1 / 12) / 2 := min_le_left _ _
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
