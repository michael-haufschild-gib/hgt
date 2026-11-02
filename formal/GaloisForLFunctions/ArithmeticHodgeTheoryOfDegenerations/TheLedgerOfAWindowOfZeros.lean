import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerReadsWeilSummands
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# The ledger of a window of zeros

Summing the per-point ledgers over a finite window of zeros and then letting the window grow:

* **Bulk** (`tendsto_sum_bulkLedger`, `re_sum_mult_div_nonneg`): a finite window `S` of the strip
  contributes `(c_N/log N) κ y_1² Σ_{ρ∈S} m_ρ/(ρ(1 − ρ)) + o(c_N/log N)` to a fixed conductor packet,
  `κ = (∫φ)²/∫φ²`, and the coefficient has nonnegative real part: a finite window of zeros, on the
  line or off it, is a positive rank-one gluing at the pole of the bulk.
* **Horizon** (`tendsto_sum_horizonLedger`): the same window contributes
  `c_N κ Σ_{ρ∈S} W_ρ(H, H) + o(c_N)` to the horizon block of `h`, `H(y) = e^{y/2}h(y)`.
* **Exhaustion** (`horizon_window_exhaustion`): for `ζ` and a `C²` profile `h` supported in
  `[−A, 0]`, the window sums `κ Σ_{ρ∈S} W_ρ(H, H)` converge, as `S` exhausts the zeros, to
  `κ W(H, H)`, whose real part is Weil's quadratic form of `H`.

In the iterated limit (horizon first, then the window of zeros) the horizon layer of the complete
family, divided by the overlap, is `κ` times Weil's form of the synthesized test. The bulk sees no
individual zero beyond a positive pole charge.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-- **Bulk ledger of a finite window.** -/
theorem tendsto_sum_bulkLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1) (E : Finset ℕ) (y : ℕ → ℝ) {c : ℕ → ℝ}
    (hc : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((Real.log N / c N : ℝ) : ℂ) * ∑ ρ ∈ S, bulkLedger Z φ E y (c N) N ρ)
      atTop (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑ ρ ∈ S, (Z.mult ρ : ℂ) / (ρ * (1 - ρ)))) := by
  have h := tendsto_finsetSum S fun ρ hρ =>
    tendsto_bulkLedger Z hφ hφc hφ2 (hS ρ hρ).1 (hS ρ hρ).2 E y hc hcN
  have hval : (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
      ∑ ρ ∈ S, (Z.mult ρ : ℂ) / (ρ * (1 - ρ)) = ∑ ρ ∈ S, (Z.mult ρ : ℂ) *
        (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  rw [hval]
  simpa only [mul_sum] using h

/-- The pole charge of a finite window of the open strip has nonnegative real part. -/
theorem re_sum_mult_div_nonneg (Z : ZeroConfig) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1) :
    0 ≤ (∑ ρ ∈ S, (Z.mult ρ : ℂ) / (ρ * (1 - ρ))).re := by
  rw [Complex.re_sum]
  refine sum_nonneg fun ρ hρ => ?_
  rw [div_eq_mul_one_div, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) (re_inv_mul_one_sub_pos (hS ρ hρ).1 (hS ρ hρ).2).le

/-- **Horizon ledger of a finite window.** -/
theorem tendsto_sum_horizonLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) {h : ℝ → ℝ} {A : ℝ} (hh : Continuous h)
    (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (S : Finset ℂ) {c : ℕ → ℝ}
    (hc : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((c N)⁻¹ : ℂ) * ∑ ρ ∈ S, horizonLedger Z φ h (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        ∑ ρ ∈ S, Z.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ)) := by
  have hl := tendsto_finsetSum S fun ρ _ =>
    tendsto_horizonLedger Z hφ hφc hφ2 hh hsupp hA ρ hc hcN
  simpa only [mul_sum] using hl

theorem contDiff_halfWeight {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 2 (halfWeight h) := by
  unfold halfWeight
  exact (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hh

theorem hasCompactSupport_halfWeight {h : ℝ → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (halfWeight h) := by
  unfold halfWeight
  exact hc.mul_left

/-- **Exhaustion.** For `ζ` and a `C²` profile `h` of compact support, the window sums of the
horizon ledger limits converge to `κ W(H, H)`, and `Re W(H, H)` is Weil's quadratic form of
`H = e^{y/2} h`. -/
theorem horizon_window_exhaustion {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hc : HasCompactSupport h)
    (κ : ℂ) :
    Tendsto (fun S : Finset zetaZeroConfig.carrier =>
        κ * ∑ ρ ∈ S, zetaZeroConfig.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ) atTop
      (𝓝 (κ * zetaZeroConfig.W (cx (halfWeight h)) (cx (halfWeight h)))) ∧
    (zetaZeroConfig.W (cx (halfWeight h)) (cx (halfWeight h))).re = weilQuad (halfWeight h) := by
  have hH := contDiff_halfWeight hh
  have hHc := hasCompactSupport_halfWeight hc
  have hcx : ContDiff ℝ 2 (cx (halfWeight h)) := Complex.ofRealCLM.contDiff.comp hH
  have hcxc : HasCompactSupport (cx (halfWeight h)) := hHc.comp_left Complex.ofReal_zero
  refine ⟨?_, (LogCells.weilQuad_eq_zetaW hH hHc).symm⟩
  have hs := ((RHTower.WeilConditional.summable_Wsummand hcx hcxc).hasSum).mul_left κ
  have ht : Tendsto (fun S : Finset zetaZeroConfig.carrier =>
      ∑ ρ ∈ S, κ * zetaZeroConfig.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ) atTop
      (𝓝 (κ * ∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ)) := hs
  simp only [mul_sum]
  exact ht

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
