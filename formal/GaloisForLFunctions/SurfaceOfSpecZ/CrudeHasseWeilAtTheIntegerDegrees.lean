import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtTheIntegerDegrees

/-!
# Crude Hasse–Weil at the integer degrees reads the zero width

The curve proof has a crude step and a self-improvement: a bound `|a_n| ≤ C q^{nθ}` at every level
puts every Frobenius eigenvalue at modulus `≤ q^θ`, and with `θ = ½` and any constant `C` it is
Hasse–Weil. For the smoothed Frobenius graphs of `Spec ℤ` at the integer degrees:

* `zetaZeroWidth_le_iff_crude_integerDegrees`: for `σ ≥ 0`, `|c_B(log n)| ≤ K n^σ` for some `K` and all
  `n ≥ 1` iff the zero width is at most `σ`;
* `riemannHypothesis_iff_bounded_integerDegrees`: a bound with any constant, `|c_B(log n)| ≤ K`, is RH.

So the self-improvement is free here — any constant improves to the genus `c_B(0)/2` — and the whole
difficulty is the crude bound at every integer degree. The proof is that of
`riemannHypothesis_iff_hasseWeil_integerDegrees`: the orbit correlation moves by at most `2L` between
`log n` and `t`, and the continuous-scale width law
(`ArithmeticOrientationGeometry.zeta_splineOrbit_rate_iff_zetaZeroWidth_le`) applies.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **Propagation from the integer degrees.** A bound `K n^σ` at the integer degrees gives
`(K + 2L) e^{σt}` at every scale `t ≥ 0`. -/
theorem exists_rate_of_integerDegrees {σ K : ℝ} (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (h : ∀ n : ℕ, 0 < n →
      |zetaScalingDatum.orbitCorr splineCycle (Real.log n)| ≤ K * (n : ℝ) ^ σ) :
    ∃ K' : ℝ, ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr splineCycle t| ≤ K' * Real.exp (σ * t) := by
  set x := splineCycle
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra hc; exact hu (hw u (not_le.mp hc))
  set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  set c := zetaScalingDatum.orbitCorr x with hc
  refine ⟨K + 2 * L, fun t ht => ?_⟩
  obtain ⟨hn1, hlog, hgap⟩ := floor_log_gap ht
  set n := ⌊Real.exp t⌋₊
  have hs0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
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
  have hnpow : (n : ℝ) ^ σ ≤ Real.exp (σ * t) := by
    have hnle : (n : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
    calc (n : ℝ) ^ σ ≤ (Real.exp t) ^ σ := Real.rpow_le_rpow (Nat.cast_nonneg n) hnle hσ
      _ = Real.exp (σ * t) := by rw [← Real.exp_mul, mul_comm]
  have hint := h n (by omega)
  have he1 : 1 ≤ Real.exp (σ * t) := Real.one_le_exp (by positivity)
  calc |c t| = |c (Real.log n) + (c t - c (Real.log n))| := by rw [add_sub_cancel]
    _ ≤ |c (Real.log n)| + |c t - c (Real.log n)| := abs_add_le _ _
    _ ≤ K * Real.exp (σ * t) + 2 * L * Real.exp (σ * t) := by
        have := mul_le_mul_of_nonneg_left hnpow hK
        nlinarith
    _ = (K + 2 * L) * Real.exp (σ * t) := by ring

/-- **Crude Hasse–Weil at the integer degrees reads the zero width.** -/
theorem zetaZeroWidth_le_iff_crude_integerDegrees {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ n : ℕ, 0 < n →
      |zetaScalingDatum.orbitCorr splineCycle (Real.log n)| ≤ K * (n : ℝ) ^ σ) ↔
      SquareRootThreshold.zetaZeroWidth ≤ σ := by
  rw [← zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ]
  constructor
  · rintro ⟨K, hK⟩
    have hK0 : 0 ≤ K := by
      have := hK 1 one_pos
      simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
      exact (abs_nonneg _).trans this
    exact exists_rate_of_integerDegrees hσ hK0 hK
  · rintro ⟨K, hK⟩
    refine ⟨K, fun n hn => ?_⟩
    have hs : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have := hK _ hs
    rwa [mul_comm σ, Real.exp_mul, Real.exp_log (by exact_mod_cast hn)] at this

/-- **Crude implies sharp.** A bound with any constant at the integer degrees is RH. -/
theorem riemannHypothesis_iff_bounded_integerDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      |zetaScalingDatum.orbitCorr splineCycle (Real.log n)| ≤ K := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun n hn => ?_⟩
    exact (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) n hn
  · rintro ⟨K, hK⟩
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 1 one_pos)
    rw [riemannHypothesis_iff_splineOrbit_subexponential]
    obtain ⟨K', hK'⟩ := exists_rate_of_integerDegrees (σ := 0) le_rfl hK0
      fun n hn => by rw [Real.rpow_zero, mul_one]; exact hK n hn
    intro ε hε
    refine ⟨max K' 0, fun t ht => ?_⟩
    have h1 := hK' t ht
    rw [zero_mul, Real.exp_zero, mul_one] at h1
    calc _ ≤ K' := h1
      _ ≤ max K' 0 := le_max_left _ _
      _ ≤ max K' 0 * Real.exp (ε * t) :=
        le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by positivity))

end GaloisForLFunctions.SurfaceOfSpecZ
