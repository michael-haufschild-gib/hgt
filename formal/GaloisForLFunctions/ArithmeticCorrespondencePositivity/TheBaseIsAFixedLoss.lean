import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheGoldenDatumHasNoFixedBudget

/-!
# The base is a fixed loss

Deligne proves Weil's bound for a pure family by bounding the even tensor powers `F^{⊗2k}` over a
base with a loss that does not depend on `k`, then taking `2k`-th roots. On a correspondence surface
the `k`-th tensor power of a cycle `x` has orbit correlation `c_x(t)^k`, whose exponential width is
`k` times that of `c_x`: tensor powers amplify the depth of a seen off-line zero linearly. This file
states what a base must deliver for `ζ`, and what any amplification with linear loss gives.

For the cubic spline `B` with orbit correlation `c(t) = W(B, B(· − t))`:

* **Root extraction** (`zetaZeroWidth_le_of_tensor_bound`). A bound `|c(t)|^k ≤ C e^{Lt}` on
  `t ≥ 0` gives zero width `≤ L/k`.
* **Linear loss is the strip** (`zetaZeroWidth_le_iff_linear_tensor_loss`). Bounds
  `|c(t)|^k ≤ C_k e^{kσt}` for every `k` hold iff the zero width is `≤ σ`: tensor powers with linear
  loss carry exactly the information of the first power.
* **Sublinear loss is RH** (`riemannHypothesis_of_sublinear_tensor_loss`) and **a fixed loss is RH**
  (`riemannHypothesis_iff_fixed_tensor_loss`): RH holds iff one exponent `L` bounds every tensor
  power.
* **Calibration** (`goldenDatum_tensor_loss_ge`). On the golden datum every bound
  `trace(j)^k ≤ C e^{Lj}` has `L ≥ k log φ`: its tensor powers lose linearly, with slope `log φ`.

So a base over `Spec ℤ` is, at the level of receivers, exactly a fixed-loss bound for the tensor
powers of one orbit correlation. Multiplicative amplification cannot produce it (gauge Jensen, ACG);
the loss of a base must come from a structure whose cost does not scale with `k`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

/-- The orbit correlation `c(t) = W(B, B(· − t))` of the cubic spline. -/
def splineCorr (t : ℝ) : ℝ := zetaScalingDatum.orbitCorr splineCycle t

/-- **Root extraction.** A bound `|c(t)|^k ≤ C e^{Lt}` for `t ≥ 0`, `k ≥ 1`, `L ≥ 0`, gives
zero width at most `L/k`. -/
theorem zetaZeroWidth_le_of_tensor_bound {k : ℕ} (hk : 1 ≤ k) {L C : ℝ} (hL : 0 ≤ L)
    (h : ∀ t : ℝ, 0 ≤ t → |splineCorr t| ^ k ≤ C * Real.exp (L * t)) :
    SquareRootThreshold.zetaZeroWidth ≤ L / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hC : 0 ≤ C := by
    have := h 0 le_rfl
    rw [mul_zero, Real.exp_zero, mul_one] at this
    exact (pow_nonneg (abs_nonneg _) k).trans this
  refine (zeta_splineOrbit_rate_iff_zetaZeroWidth_le (div_nonneg hL hk0.le)).mp
    ⟨C ^ ((k : ℝ)⁻¹), fun t ht => ?_⟩
  have h1 : |splineCorr t| = (|splineCorr t| ^ k) ^ ((k : ℝ)⁻¹) := by
    rw [Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega)]
  have h2 : (C * Real.exp (L * t)) ^ ((k : ℝ)⁻¹) = C ^ ((k : ℝ)⁻¹) * Real.exp (L / k * t) := by
    rw [Real.mul_rpow hC (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    field_simp
  calc |zetaScalingDatum.orbitCorr splineCycle t| = |splineCorr t| := rfl
    _ = (|splineCorr t| ^ k) ^ ((k : ℝ)⁻¹) := h1
    _ ≤ (C * Real.exp (L * t)) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (abs_nonneg _) k) (h t ht) (inv_nonneg.mpr hk0.le)
    _ = C ^ ((k : ℝ)⁻¹) * Real.exp (L / k * t) := h2

/-- **Linear loss is the strip.** For `σ ≥ 0`, bounds `|c(t)|^k ≤ C_k e^{kσt}` hold for every
`k ≥ 1` iff the zero width is at most `σ`. -/
theorem zetaZeroWidth_le_iff_linear_tensor_loss {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |splineCorr t| ^ k ≤ C * Real.exp (k * σ * t)) ↔
      SquareRootThreshold.zetaZeroWidth ≤ σ := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h 1 le_rfl
    have := zetaZeroWidth_le_of_tensor_bound le_rfl (by positivity) hC
    simpa using this
  · intro hw k _
    obtain ⟨K, hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mpr hw
    refine ⟨K ^ k, fun t ht => ?_⟩
    have hb := hK t ht
    calc |splineCorr t| ^ k ≤ (K * Real.exp (σ * t)) ^ k :=
          pow_le_pow_left₀ (abs_nonneg _) hb k
      _ = K ^ k * Real.exp (k * σ * t) := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf

/-- **Sublinear loss is RH.** If the `k`-th tensor power is bounded by `C_k e^{L_k t}` with
`L_k/k → 0`, then RH holds. -/
theorem riemannHypothesis_of_sublinear_tensor_loss (L : ℕ → ℝ) (hL0 : ∀ k, 0 ≤ L k)
    (hL : Tendsto (fun k : ℕ => L k / k) atTop (𝓝 0))
    (h : ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |splineCorr t| ^ k ≤ C * Real.exp (L k * t)) :
    RiemannHypothesis := by
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm (ge_of_tendsto hL ?_) SquareRootThreshold.zetaZeroWidth_nonneg
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨C, hC⟩ := h k hk
  exact zetaZeroWidth_le_of_tensor_bound hk (hL0 k) hC

/-- **A fixed loss is RH.** RH holds iff one exponent `L` bounds every tensor power of the spline
orbit correlation. -/
theorem riemannHypothesis_iff_fixed_tensor_loss :
    RiemannHypothesis ↔ ∃ L : ℝ, 0 ≤ L ∧ ∀ k : ℕ, 1 ≤ k →
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |splineCorr t| ^ k ≤ C * Real.exp (L * t) := by
  constructor
  · intro hRH
    refine ⟨0, le_rfl, fun k _ => ⟨|splineCorr 0| ^ k, fun t _ => ?_⟩⟩
    have hw := riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH t
    rw [ScalingDatum.HasseWeilAt] at hw
    rw [zero_mul, Real.exp_zero, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw.trans (le_abs_self _)) k
  · rintro ⟨L, hL, h⟩
    refine riemannHypothesis_of_sublinear_tensor_loss (fun _ => L) (fun _ => hL) ?_ h
    simpa using tendsto_const_div_atTop_nhds_zero_nat L

open Real in
/-- **The golden datum loses linearly under tensor powers.** Any bound `trace(j)^k ≤ C e^{Lj}` for
all `j` forces `L ≥ k log φ`. -/
theorem goldenDatum_tensor_loss_ge {k : ℕ} {L C : ℝ}
    (h : ∀ j : ℕ, goldenDatum.trace j ^ k ≤ C * Real.exp (L * j)) : k * Real.log goldenRatio ≤ L := by
  by_contra hlt
  push_neg at hlt
  set a := k * Real.log goldenRatio - L with ha
  have hapos : 0 < a := by linarith
  -- `φ^{kj} = e^{(k log φ) j} ≤ trace(j)^k ≤ C e^{Lj}`, so `e^{a j} ≤ C` for all `j`
  have hb : ∀ j : ℕ, Real.exp (a * j) ≤ C := by
    intro j
    have h1 : goldenRatio ^ (k * j) ≤ goldenDatum.trace j ^ k := by
      rw [pow_mul']
      exact pow_le_pow_left₀ (pow_nonneg goldenRatio_pos.le _)
        (ArithmeticCorrelationGeometry.goldenRatio_pow_le_goldenDatum_trace j) k
    have h2 : goldenRatio ^ (k * j) = Real.exp (k * Real.log goldenRatio * j) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos goldenRatio_pos]
      push_cast; ring_nf
    have h3 := (h2 ▸ h1).trans (h j)
    have h4 : Real.exp (a * j) * Real.exp (L * j) = Real.exp (k * Real.log goldenRatio * j) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; ring
    have h5 : Real.exp (a * j) * Real.exp (L * j) ≤ C * Real.exp (L * j) := h4 ▸ h3
    exact le_of_mul_le_mul_right h5 (Real.exp_pos _)
  obtain ⟨j, hj⟩ := exists_nat_gt (Real.log (max C 1) / a)
  have := hb j
  have hlog : Real.log (max C 1) < a * j := by
    rw [div_lt_iff₀ hapos] at hj; linarith
  have : Real.exp (a * j) ≤ max C 1 := this.trans (le_max_left _ _)
  have := Real.log_le_log (Real.exp_pos _) this
  rw [Real.log_exp] at this
  linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
