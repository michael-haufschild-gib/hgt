import GaloisForLFunctions.SurfaceOfSpecZ.PolynomiallySparseDegreesSuffice
import GaloisForLFunctions.SurfaceOfSpecZ.TheEffectiveClassesOfThePrimePlanes

/-!
# The count door at every gap set

`TheEffectiveClassesOfThePrimePlanes`: RH iff every effective prime class `Γ_1 + Γ_p` carries an
`ℕ`-count along its ray with Tate limit `δ_p(1, 1) = 2c_B(0) + 2c_B(log p)`. The Tate limit is
nonnegative exactly when `c_B(log p) ≥ −c_B(0)`, a lower bound on the traces, so by the iterated gap
method (`TheGapMethodIterates`) the planes of any degree set with power-saving gaps suffice:

* `riemannHypothesis_iff_effectiveCounts_of_powGaps`: for every `D ⊂ ℕ` with gaps `O(x^θ)`,
  `θ < 1`, RH holds iff every class `Γ_1 + Γ_d`, `d ∈ D`, carries an `ℕ`-count with Tate limit
  `δ_d(1, 1)`;
* `riemannHypothesis_iff_copositive_of_powGaps`: RH iff the planes `⟨Γ_1, Γ_d⟩`, `d ∈ D`, are
  copositive;
* at the degrees `nᵏ` for any `k ≥ 1` (`riemannHypothesis_iff_effectiveCounts_kthPowers`), which
  are `O(x^{1/k})` up to `x`.

The missing count is needed on one ray per degree of a polynomially sparse set.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography
open SquareRootThreshold Zeta23

/-- A nonnegative `δ_d(1, 1)` at every degree of a gap set is RH. -/
theorem riemannHypothesis_of_planeDefect_nonneg_of_powGaps {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) (h : ∀ d ∈ D, 0 ≤ planeDefect d (1, 1)) : RiemannHypothesis := by
  refine riemannHypothesis_iff_zetaZeroConfig_onLine.mpr
    (onLine_of_bddBelow_of_powGaps _ temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hθ1 hD
      (K := 2 * zetaScalingDatum.orbitCorr splineCycle 0) fun d hd => ?_)
  have := h d hd
  rw [planeDefect_one_one, orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_eq_re_lagStructure_spline] at this
  rw [orbitCorr_eq_re_lagStructure_spline]
  linarith

/-- Under RH every plane `⟨Γ_1, Γ_n⟩`, `n ≥ 1`, is copositive. -/
theorem planeDefect_nonneg_of_RH (hRH : RiemannHypothesis) {n : ℕ} (hn : 0 < n) (x y : ℕ) :
    0 ≤ planeDefect n (x, y) := by
  have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) n hn
  rw [ScalingDatum.HasseWeilAt] at h
  have h2 := (abs_le.mp h).1
  have h1 := (abs_nonneg _).trans h
  simp only [planeDefect]
  push_cast
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  nlinarith [sq_nonneg ((x : ℝ) - y), mul_nonneg hx hy,
    mul_le_mul_of_nonneg_right h2 (mul_nonneg hx hy)]

/-- **The count door at the effective classes of any gap set.** -/
theorem riemannHypothesis_iff_effectiveCounts_of_powGaps {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) :
    RiemannHypothesis ↔ ∀ d ∈ D, ∃ K : ℕ → ℕ,
      Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (planeDefect d (1, 1))) := by
  constructor
  · intro hRH d hd
    have h := planeDefect_nonneg_of_RH hRH (hD.1 d hd) 1 1
    exact ⟨fun m => ⌊(m : ℝ) ^ 2 * planeDefect d (1, 1)⌋₊, tendsto_floor_div_sq h⟩
  · intro h
    refine riemannHypothesis_of_planeDefect_nonneg_of_powGaps hθ1 hD fun d hd => ?_
    obtain ⟨K, hK⟩ := h d hd
    exact ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **Copositivity on the planes of any gap set is RH.** -/
theorem riemannHypothesis_iff_copositive_of_powGaps {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) :
    RiemannHypothesis ↔ ∀ d ∈ D, ∀ x y : ℕ, 0 ≤ planeDefect d (x, y) :=
  ⟨fun hRH d hd x y => planeDefect_nonneg_of_RH hRH (hD.1 d hd) x y,
    fun h => riemannHypothesis_of_planeDefect_nonneg_of_powGaps hθ1 hD fun d hd => h d hd 1 1⟩

/-- **The count door at the degrees `nᵏ`.** -/
theorem riemannHypothesis_iff_effectiveCounts_kthPowers {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → ∃ K : ℕ → ℕ,
      Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (planeDefect (n ^ k) (1, 1))) := by
  rw [riemannHypothesis_iff_effectiveCounts_of_powGaps (one_sub_inv_lt_one hk) (powGaps_kthPowers hk)]
  constructor
  · intro h n hn
    exact h (n ^ k) ⟨n, hn, rfl⟩
  · rintro h d ⟨n, hn, rfl⟩
    exact h n hn

end GaloisForLFunctions.SurfaceOfSpecZ
