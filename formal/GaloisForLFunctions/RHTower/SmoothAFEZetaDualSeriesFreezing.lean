import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightDerivativeBound

/-!
# Absolute freezing of exact dual-series weights

For the `n`-th reflected zeta term the dual smoothing scale is `(n+1)x`.
Reciprocal-scale carrier variation therefore contributes a full extra factor
`(n+1)^{-1}`.  Together with critical-line amplitude `(n+1)^{-1/2}` this
produces an absolutely summable `(n+1)^{-3/2}` freezing error.  The oscillatory
critical-line phases remain untouched.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Critical-line modulus of the reflected Dirichlet monomial. -/
theorem norm_natSucc_cpow_linePt_sub_one (n : ℕ) (tau : ℝ) :
    ‖(n + 1 : ℂ) ^ (linePt tau - 1)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hcast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  simp [linePt]
  ring

/-- Freezing the exact dual weights in the complete reflected Dirichlet series has
an absolutely summable `3/2`-power cost.  No Dirichlet phase is frozen or bounded. -/
theorem exists_norm_smoothAFEZetaDualSeriesWeightError_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {x tau u : ℝ}, 0 < x → 4 ≤ tau → 4 ≤ u →
      ‖∑' n : ℕ, (n + 1 : ℂ) ^ (linePt tau - 1) *
          (smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
            smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x))‖ ≤
        (A / x) * |tau - u| * smoothAFEZetaMajorant (3 / 2) := by
  obtain ⟨A, hA, hweight⟩ :=
    exists_norm_smoothAFEZetaDualWeight_sub_le_invScale_mul_height
  refine ⟨A, hA, ?_⟩
  intro x tau u hx htau hu
  let f : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (linePt tau - 1) *
    (smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
      smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x))
  let q : ℕ → ℝ := fun n =>
    (A / x) * |tau - u| * (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hbase : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hq : Summable q := hbase.mul_left ((A / x) * |tau - u|)
  have hpoint : ∀ n : ℕ, ‖f n‖ ≤ q n := by
    intro n
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hY : 0 < (n + 1 : ℝ) * x := mul_pos hnpos hx
    have hw := hweight hY htau hu
    have hpow := norm_natSucc_cpow_linePt_sub_one n tau
    dsimp only [f, q]
    rw [norm_mul, hpow]
    calc
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
            smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x)‖
        ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((A / ((n + 1 : ℝ) * x)) * |tau - u|) := by gcongr
      _ = (A / x) * |tau - u| *
            (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
          have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
              (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
              Real.rpow_add hnpos, Real.rpow_one]
          rw [Real.rpow_neg hnpos.le, hp]
          field_simp [hnpos.ne', hx.ne']
  have hf : Summable f := Summable.of_norm
    (hq.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint)
  calc
    ‖∑' n : ℕ, (n + 1 : ℂ) ^ (linePt tau - 1) *
          (smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
            smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x))‖
      = ‖∑' n : ℕ, f n‖ := by rfl
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ, q n := hf.norm.tsum_le_tsum hpoint hq
    _ = (A / x) * |tau - u| * smoothAFEZetaMajorant (3 / 2) := by
      rw [tsum_mul_left]
      rfl

/-- The exact dual series remains absolutely summable when phase height and
weight height are separated. -/
theorem smoothAFEZetaDualWeightedSeries_summable
    {x : ℝ} (hx : 0 < x) (phaseHeight weightHeight : ℝ) :
    Summable (fun n : ℕ =>
      (n + 1 : ℂ) ^ (linePt phaseHeight - 1) *
        smoothAFEZetaDualWeight weightHeight ((n + 1 : ℝ) * x)) := by
  obtain ⟨K, hK, hweight⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  let C : ℝ := K * (1 + |weightHeight|) * x⁻¹
  let q : ℕ → ℝ := fun n => C * (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hbase : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hq : Summable q := hbase.mul_left C
  apply Summable.of_norm
  apply hq.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hY : 0 < (n + 1 : ℝ) * x := mul_pos hnpos hx
  have hw := hweight weightHeight hY
  have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
      (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
      Real.rpow_add hnpos, Real.rpow_one]
  dsimp only [q, C]
  rw [norm_mul, norm_natSucc_cpow_linePt_sub_one]
  calc
    (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖smoothAFEZetaDualWeight weightHeight ((n + 1 : ℝ) * x)‖
      ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (K * (1 + |weightHeight|) * (((n + 1 : ℝ) * x)⁻¹)) := by gcongr
    _ = K * (1 + |weightHeight|) * x⁻¹ *
          (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le, hp]
      field_simp [hnpos.ne', hx.ne']

/-- The complete exact dual series can be frozen at a second height with the same
absolutely summable `3/2`-power error. -/
theorem exists_norm_smoothAFEZetaDualSeries_sub_frozen_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {x tau u : ℝ}, 0 < x → 4 ≤ tau → 4 ≤ u →
      ‖(∑' n : ℕ, (n + 1 : ℂ) ^ (linePt tau - 1) *
          smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x)) -
        (∑' n : ℕ, (n + 1 : ℂ) ^ (linePt tau - 1) *
          smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x))‖ ≤
        (A / x) * |tau - u| * smoothAFEZetaMajorant (3 / 2) := by
  obtain ⟨A, hA, herr⟩ := exists_norm_smoothAFEZetaDualSeriesWeightError_le
  refine ⟨A, hA, ?_⟩
  intro x tau u hx htau hu
  have hleft := smoothAFEZetaDualWeightedSeries_summable hx tau tau
  have hright := smoothAFEZetaDualWeightedSeries_summable hx tau u
  rw [← hleft.tsum_sub hright]
  have heq : (fun n : ℕ =>
      (n + 1 : ℂ) ^ (linePt tau - 1) *
          smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
        (n + 1 : ℂ) ^ (linePt tau - 1) *
          smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x)) =
      (fun n : ℕ => (n + 1 : ℂ) ^ (linePt tau - 1) *
        (smoothAFEZetaDualWeight tau ((n + 1 : ℝ) * x) -
          smoothAFEZetaDualWeight u ((n + 1 : ℝ) * x))) := by
    funext n
    ring
  rw [heq]
  exact herr hx htau hu

end RHTower
