import GaloisForLFunctions.SurfaceOfSpecZ.SparseDegreesDecideRH
import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount

/-!
# The count door on the planes of integer degree

The count door of `CountingHolography.TheTateLimitOfACount` asks for an `ℕ`-valued count on every
lattice of integer probes `ℤᴺ`. On the surface of `Spec ℤ` the planes spanned by two smoothed
Frobenius graphs suffice. For `n ≥ 1` the defect of `x Γ_1 + y Γ_n` is the binary form

  `δ_n(x, y) = c_B(0) x² + 2 c_B(log n) x y + c_B(0) y²`   (`planeDefect`),

the genus form of the plane, and (`riemannHypothesis_iff_planeCounts`)

  **RH holds iff for every `n ≥ 1` some `K_n : ℤ² → ℕ` has Tate limit `δ_n` along integer rays.**

`⇒`: under RH every plane passes Hasse–Weil, `δ_n ≥ 0`, and `⌊δ_n⌋₊` is a count. `⇐`: a count with Tate
limit `δ_n` forces `δ_n(1, ±1) ≥ 0` (Tate's principle), which is Hasse–Weil at `log n`, and the integer
degrees decide RH (`riemannHypothesis_iff_hasseWeil_integerDegrees`). By `SparseDegreesDecideRH` the
square degrees `n²` already suffice.

So the quadratic integer count the surface must carry is decided plane by plane, one binary count for
each integer degree, as on `C × C`, where the plane `⟨Δ, Γ_{Fⁿ}⟩` carries the integral genus form.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography

/-- The defect of the plane `⟨Γ_1, Γ_n⟩` of smoothed Frobenius graphs. -/
def planeDefect (n : ℕ) (v : ℤ × ℤ) : ℝ :=
  zetaScalingDatum.orbitCorr splineCycle 0 * (v.1 : ℝ) ^ 2 +
    2 * zetaScalingDatum.orbitCorr splineCycle (Real.log n) * v.1 * v.2 +
      zetaScalingDatum.orbitCorr splineCycle 0 * (v.2 : ℝ) ^ 2

theorem planeDefect_smul (n m : ℕ) (v : ℤ × ℤ) :
    planeDefect n (m • v) = (m : ℝ) ^ 2 * planeDefect n v := by
  obtain ⟨a, b⟩ := v
  simp only [planeDefect, Prod.smul_mk, nsmul_eq_mul]
  push_cast
  ring

/-- **The count door on the planes of integer degree.** -/
theorem riemannHypothesis_iff_planeCounts :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → ∃ K : ℤ × ℤ → ℕ, ∀ v : ℤ × ℤ,
      Tendsto (fun m : ℕ => (K (m • v) : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (planeDefect n v)) := by
  rw [riemannHypothesis_iff_hasseWeil_integerDegrees]
  constructor
  · intro h n hn
    have hpsd := (frobeniusPair_defect_nonneg_iff splineCycle (Real.log n)).mpr (h n hn)
    refine ⟨fun v => ⌊planeDefect n v⌋₊, fun v => ?_⟩
    have hv : 0 ≤ planeDefect n v := by
      have := hpsd v.1 v.2
      unfold planeDefect; linarith
    have hfl := tendsto_floor_div_sq hv
    refine hfl.congr' ?_
    filter_upwards with m
    rw [planeDefect_smul]
  · intro h n hn
    obtain ⟨K, hK⟩ := h n hn
    have hnn : ∀ v : ℤ × ℤ, 0 ≤ planeDefect n v := fun v =>
      nonneg_of_tateLimit (M := ℤ × ℤ) (K := fun w => (K w : ℝ)) (fun _ => Nat.cast_nonneg _)
        (hK v)
    rw [← frobeniusPair_defect_nonneg_iff]
    intro u w
    -- the Hasse–Weil bound follows from the two probes `(1, 1)` and `(1, −1)`
    have h1 := hnn (1, 1)
    have h2 := hnn (1, -1)
    simp only [planeDefect] at h1 h2
    push_cast at h1 h2
    set c0 := zetaScalingDatum.orbitCorr splineCycle 0
    set c := zetaScalingDatum.orbitCorr splineCycle (Real.log n)
    have hc0 : 0 ≤ c0 := by linarith
    nlinarith [sq_nonneg (u + w), sq_nonneg (u - w),
      mul_nonneg (by linarith : 0 ≤ c0 - c) (sq_nonneg (u - w)),
      mul_nonneg (by linarith : 0 ≤ c0 + c) (sq_nonneg (u + w))]

end GaloisForLFunctions.SurfaceOfSpecZ
