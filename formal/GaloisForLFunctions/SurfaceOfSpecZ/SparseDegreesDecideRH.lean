import GaloisForLFunctions.SurfaceOfSpecZ.CrudeHasseWeilAtTheIntegerDegrees

/-!
# Sparse sets of degrees decide RH, and the critical exponent is a gap exponent

`HasseWeilAtTheIntegerDegrees` uses every integer degree. The proof only needs, below every height
`x`, a degree `d` with `x − d = O(√x)`: then `t − log d ≤ M e^{−t/2}`, which is exactly what the
Lipschitz constant `e^{t/2}` of the orbit correlation absorbs.

* `riemannHypothesis_iff_hasseWeil_of_sqrtGaps`: for any set `D` of positive integers whose gaps are
  `O(√x)` (`SqrtGaps D`), Hasse–Weil on the planes `⟨Γ_1, Γ_d⟩`, `d ∈ D`, is RH.
* `sqrtGaps_squares`, `riemannHypothesis_iff_hasseWeil_squareDegrees`: the squares qualify, so the
  degrees `n²` already decide RH.

The exponent `½` of the gap condition is the critical abscissa: a set with gaps `O(x^θ)` for some
`θ > ½` only controls the orbit up to `e^{(θ − ½)t}`. The primes have gaps `O(√p log p)` under RH
and `O(p^{0.525})` unconditionally, both just above `√p`: whether the prime degrees alone decide RH
in this way is a question about prime gaps at the critical exponent.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- `D` has gaps `O(√x)`: below every `x ≥ 1` there is `d ∈ D` with `x − d ≤ M √x`. -/
def SqrtGaps (D : Set ℕ) : Prop :=
  (∀ d ∈ D, 0 < d) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 1 ≤ x → ∃ d ∈ D, (d : ℝ) ≤ x ∧ x - d ≤ M * Real.sqrt x

/-- A degree `d` with `eᵗ − d ≤ M e^{t/2}` satisfies `(t − log d) e^{t/2} ≤ M eᵗ/d`. -/
theorem log_gap_of_sqrtGap {t M : ℝ} {d : ℝ} (hd0 : 0 < d)
    (hgap : Real.exp t - d ≤ M * Real.sqrt (Real.exp t)) :
    (t - Real.log d) * Real.exp (t / 2) ≤ M * Real.exp t / d := by
  have hsq : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have h1 : t - Real.log d = Real.log (Real.exp t / d) := by
    rw [Real.log_div (Real.exp_pos t).ne' hd0.ne', Real.log_exp]
  have h2 : Real.log (Real.exp t / d) ≤ (Real.exp t - d) / d := by
    have := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos t) hd0)
    rw [div_sub_one hd0.ne'] at this; exact this
  rw [h1]
  have he : 0 < Real.exp (t / 2) := Real.exp_pos _
  calc Real.log (Real.exp t / d) * Real.exp (t / 2) ≤ (Real.exp t - d) / d * Real.exp (t / 2) :=
        mul_le_mul_of_nonneg_right h2 he.le
    _ ≤ M * Real.exp (t / 2) / d * Real.exp (t / 2) := by
        rw [hsq] at hgap
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hgap hd0.le) he.le
    _ = M * Real.exp t / d := by
        rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]; ring_nf

/-- **Sparse degrees with `√`-gaps decide RH.** -/
theorem riemannHypothesis_iff_hasseWeil_of_sqrtGaps {D : Set ℕ} (hD : SqrtGaps D) :
    RiemannHypothesis ↔ ∀ d ∈ D, zetaScalingDatum.HasseWeilAt splineCycle (Real.log d) := by
  obtain ⟨hpos, M, hM0, hgapD⟩ := hD
  constructor
  · intro hRH d hd
    exact (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) d (hpos d hd)
  · intro h
    rw [riemannHypothesis_iff_splineOrbit_subexponential]
    set x := splineCycle
    have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
    obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
      (cx_hasCompactSupport hf.2)
    have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
      by_contra hc; exact hu (hw u (not_le.mp hc))
    set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
    have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
    set c := zetaScalingDatum.orbitCorr x with hc
    -- a bound on the orbit correlation where the gap is at most half the height
    have hbig : ∀ t : ℝ, 0 ≤ t → 2 * M * Real.sqrt (Real.exp t) ≤ Real.exp t →
        |c t| ≤ c 0 + 4 * M * L := by
      intro t ht hhalf
      obtain ⟨d, hdD, hdle, hdgap⟩ := hgapD (Real.exp t) (Real.one_le_exp ht)
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
      have hmove : |c t - c (Real.log d)| ≤ 4 * M * L := by
        calc |c t - c (Real.log d)| ≤ L * ((t - Real.log d) * Real.exp (t / 2)) := by
              rw [← mul_assoc]; exact hdiff
          _ ≤ L * (2 * M) := mul_le_mul_of_nonneg_left (hg.trans hg2) hL0
          _ ≤ 4 * M * L := by nlinarith [mul_nonneg hM0 hL0]
      have hHW := h d hdD
      rw [ScalingDatum.HasseWeilAt] at hHW
      calc |c t| = |c (Real.log d) + (c t - c (Real.log d))| := by rw [add_sub_cancel]
        _ ≤ |c (Real.log d)| + |c t - c (Real.log d)| := abs_add_le _ _
        _ ≤ c 0 + 4 * M * L := add_le_add hHW hmove
    -- below the threshold height the correlation is bounded by continuity
    obtain ⟨T, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → 2 * M * Real.sqrt (Real.exp t) ≤ Real.exp t := by
      refine ⟨2 * Real.log (2 * M + 1), mul_nonneg two_pos.le (Real.log_nonneg (by linarith)),
        fun t ht => ?_⟩
      have hsq : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
        rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
        ring_nf
      rw [hsq, show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf]
      have : 2 * M + 1 ≤ Real.exp (t / 2) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * M + 1)]
        exact Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.exp_pos (t / 2)]
    have hcont := continuous_zetaOrbitCorr' x
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (hcont.continuousOn)
    intro ε hε
    refine ⟨max B (c 0 + 4 * M * L), fun t ht => ?_⟩
    have hbound : |c t| ≤ max B (c 0 + 4 * M * L) := by
      rcases le_total t T with htT | hTt
      · exact (by simpa [Real.norm_eq_abs] using hB t ⟨ht, htT⟩ : |c t| ≤ B).trans (le_max_left _ _)
      · exact (hbig t ht (hT.2 t hTt)).trans (le_max_right _ _)
    calc |c t| ≤ max B (c 0 + 4 * M * L) := hbound
      _ ≤ max B (c 0 + 4 * M * L) * Real.exp (ε * t) :=
        le_mul_of_one_le_right ((abs_nonneg _).trans hbound) (Real.one_le_exp (by positivity))

/-- The squares have gaps `O(√x)`. -/
theorem sqrtGaps_squares : SqrtGaps {d : ℕ | ∃ n : ℕ, 0 < n ∧ d = n ^ 2} := by
  refine ⟨fun d ⟨n, hn, hd⟩ => hd ▸ pow_pos hn 2, 3, by norm_num, fun x hx => ?_⟩
  set n := ⌊Real.sqrt x⌋₊
  have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hs1)
  have hnle : (n : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hnlt : Real.sqrt x < n + 1 := Nat.lt_floor_add_one _
  have hx0 : 0 ≤ x := by linarith
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨n ^ 2, ⟨n, by omega, rfl⟩, ?_, ?_⟩
  · push_cast
    nlinarith [mul_le_mul hnle hnle hn0 (Real.sqrt_nonneg x)]
  · push_cast
    have h1 : x < ((n : ℝ) + 1) ^ 2 := by
      nlinarith [mul_lt_mul'' hnlt hnlt (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)]
    nlinarith

/-- **The square degrees decide RH.** -/
theorem riemannHypothesis_iff_hasseWeil_squareDegrees :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n →
      zetaScalingDatum.HasseWeilAt splineCycle (Real.log ((n ^ 2 : ℕ) : ℝ)) := by
  rw [riemannHypothesis_iff_hasseWeil_of_sqrtGaps sqrtGaps_squares]
  constructor
  · intro h n hn; exact h _ ⟨n, hn, rfl⟩
  · rintro h d ⟨n, hn, rfl⟩; exact h n hn

end GaloisForLFunctions.SurfaceOfSpecZ
