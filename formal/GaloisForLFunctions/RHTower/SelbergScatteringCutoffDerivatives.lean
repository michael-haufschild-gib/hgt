import GaloisForLFunctions.RHTower.SelbergScatteringSourceApproximation

/-!
# Strongly vanishing original cutoff derivative operators

All height-scaled derivatives of the actual expanding cutoff have uniform
bounds. Every positive-order derivative eventually vanishes at each fixed
point. The resulting bounded multipliers therefore converge strongly to zero
on every native Hilbert vector, including the complete source and its admitted
vertical derivative. No bound or convergence premise is supplied.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.SelbergScatteringCutoffDerivatives
open D4BMModularCore SelbergScatteringSourceApproximation
noncomputable section

private theorem heightWeight_iterated_low (j : ℕ) (hj : 0 < j) (n : ℕ) (y : ℝ)
    (hy : y < cutoffHeight n) : iteratedDeriv j (heightWeight n) y = 0 := by
  have he : heightWeight n =ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
    filter_upwards [Iio_mem_nhds hy] with t ht
    exact heightWeight_one n t ht.le
  rw [he.iteratedDeriv_eq j,iteratedDeriv_const,if_neg (ne_of_gt hj)]

private theorem heightWeight_iterated_high (j n : ℕ) (y : ℝ)
    (hy : 2*cutoffHeight n < y) : iteratedDeriv j (heightWeight n) y = 0 := by
  have he : heightWeight n =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact heightWeight_zero n t ht.le
  rw [he.iteratedDeriv_eq j,iteratedDeriv_const]
  simp

/-- The exact height-scaled cutoff derivative appearing in the native graph equation. -/
def cutoffDerivative (j n : ℕ) (z : UpperHalfPlane) : ℂ :=
  ((z.im^j * iteratedDeriv j (heightWeight n) z.im : ℝ) : ℂ)

theorem cutoffDerivative_continuous (j n : ℕ) : Continuous (cutoffDerivative j n) := by
  have hc : Continuous (iteratedDeriv j (heightWeight n)) :=
    ContDiff.continuous_iteratedDeriv j (smoothWeight_contDiff _ _ (n := (j:ℕ∞))) le_rfl
  exact Complex.ofRealCLM.continuous.comp
    ((UpperHalfPlane.continuous_im.pow j).mul (hc.comp UpperHalfPlane.continuous_im))

/-- All expanding cutoff derivatives have one original hyperbolic bound per
derivative order, independent of the cutoff height. -/
theorem cutoffDerivative_uniform_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, ‖cutoffDerivative j n z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform j
  refine ⟨2^j*C,by positivity,?_⟩
  intro n z
  have hn : 0 < cutoffHeight n := by unfold cutoffHeight; positivity
  by_cases hy : z.im ≤ 2*cutoffHeight n
  · unfold cutoffDerivative
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg z.im_pos.le j)]
    calc
      _ ≤ (2*cutoffHeight n)^j * (C / cutoffHeight n^j) :=
        mul_le_mul (pow_le_pow_left₀ z.im_pos.le hy j) (hb _ _ hn _)
          (abs_nonneg _) (by positivity)
      _ = 2^j*C := by
        rw [mul_pow]
        field_simp
  · rw [cutoffDerivative,heightWeight_iterated_high j n z.im (lt_of_not_ge hy),mul_zero]
    simpa using mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) j) hC

private def derivativeBound (j : ℕ) : ℝ := (cutoffDerivative_uniform_bound j).choose

private theorem derivativeBound_nonneg (j : ℕ) : 0 ≤ derivativeBound j :=
  (cutoffDerivative_uniform_bound j).choose_spec.1

private theorem derivativeBound_spec (j : ℕ) (n : ℕ) (z : UpperHalfPlane) :
    ‖cutoffDerivative j n z‖ ≤ derivativeBound j :=
  (cutoffDerivative_uniform_bound j).choose_spec.2 n z

/-- Every positive-order scaled derivative eventually vanishes at each point. -/
theorem cutoffDerivative_eventually_zero (j : ℕ) (hj : 0 < j) (z : UpperHalfPlane) :
    ∀ᶠ n : ℕ in atTop, cutoffDerivative j n z = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt z.im
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hh : z.im < cutoffHeight n := by unfold cutoffHeight; linarith
  rw [cutoffDerivative,heightWeight_iterated_low j hj n z.im hh,mul_zero]
  rfl

/-- Multiplication by the actual scaled cutoff derivative in the original Hilbert space. -/
def cutoffDerivativeOperator (j n : ℕ) : Space →L[ℂ] Space :=
  lpBoundedMulCLM (p := 2) (μ := measure) (cutoffDerivative_continuous j n).measurable
    (derivativeBound_nonneg j) (derivativeBound_spec j n)

theorem cutoffDerivativeOperator_coe (j n : ℕ) (f : Space) :
    (cutoffDerivativeOperator j n f : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => cutoffDerivative j n z * f z) :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := measure) (cutoffDerivative_continuous j n).measurable
    (derivativeBound_nonneg j) (derivativeBound_spec j n) f

/-- The actual cutoff derivative errors vanish strongly on every original native vector. -/
theorem cutoffDerivativeOperator_tendsto_zero (j : ℕ) (hj : 0 < j) (f : Space) :
    Tendsto (fun n => cutoffDerivativeOperator j n f) atTop (𝓝 (0:Space)) := by
  have h0 (z : UpperHalfPlane) : ‖(0:ℂ)‖ ≤ derivativeBound j := by
    simpa using derivativeBound_nonneg j
  have hp (z : UpperHalfPlane) : Tendsto (fun n => cutoffDerivative j n z) atTop (𝓝 (0:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoffDerivative_eventually_zero j hj z] with n hn
    exact hn.symm
  have ht := tendsto_lpBoundedMulCLM_apply (μ := measure)
    (fun n => (cutoffDerivative_continuous j n).measurable) measurable_const
    (derivativeBound_nonneg j) (derivativeBound_spec j) h0 hp f
  have he : lpBoundedMulCLM (p := 2) (μ := measure) measurable_const
      (derivativeBound_nonneg j) h0 f = 0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := measure) measurable_const
      (derivativeBound_nonneg j) h0 f,Lp.coeFn_zero ℂ 2 measure] with z hz hz0
    rw [hz,hz0,zero_mul]
    rfl
  simpa only [cutoffDerivativeOperator,he] using ht

end
end RHTower.SelbergScatteringCutoffDerivatives
