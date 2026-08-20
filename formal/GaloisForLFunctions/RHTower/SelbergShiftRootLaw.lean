/-
# Step 3 of the cusp--spectrum radius law, in every degree

Kaczorowski--Perelli's asymmetric functional equation writes a class member along the shift
lattice as a unimodular phase, a sine factor, an archimedean factor and a reflected Dirichlet
series.  The archimedean factor has `k`-th root exactly the cusp constant; the reflected series
tends to the first coefficient, so its root tends to one; and the sine factor is bounded, so it
can only lower the root -- and it does not, as soon as it is frequently bounded below, which is
the card's "off the exceptional lattice".

Main results:
* `SelbergGammaData.norm_invariantRootNumber` — the invariant phase is unimodular.
* `norm_sin_le_exp_abs_im` — the sine of a fixed height is bounded.
* `SelbergGammaData.exists_bound_norm_asymmetricS_shift` — the sine factor is bounded along the
  lattice, with no hypotheses.
* `ExtendedSelbergClass.tendsto_norm_reflection_shift` — the reflected series tends to `|a_F(1)|`.
* `ExtendedSelbergClass.limsup_norm_shift_rpow_inv` —
  **`limsup_k (‖F(s₀-k/d)‖/k!)^{1/k} = q^{1/d}/(2πd)`**.
-/
import GaloisForLFunctions.RHTower.SelbergCuspArchimedeanRoot
import GaloisForLFunctions.RHTower.SelbergCuspSpectrumRadius
import GaloisForLFunctions.HTGeometry.LimsupPositiveFactor
import GaloisForLFunctions.HTGeometry.LSeriesRightLimit
import GaloisForLFunctions.HTGeometry.OscillatingRootLimsup

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The invariant phase is unimodular -/

theorem SelbergGammaData.norm_invariantRootNumber (G : SelbergGammaData) :
    ‖G.invariantRootNumber‖ = 1 := by
  unfold SelbergGammaData.invariantRootNumber
  rw [norm_mul, G.rootNumber_norm, one_mul, norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (G.lambda_pos j)]
  have hre : ((-(2 : ℂ)) * Complex.I * (((G.mu j).im : ℝ) : ℂ)).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-! ## The sine factor is bounded along the lattice -/

theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h2 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hle1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]
        norm_num
    _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
        have := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
        linarith
    _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by rw [h1, h2]; linarith
    _ = Real.exp |w.im| := by ring

theorem SelbergGammaData.sine_arg_im (G : SelbergGammaData) (s₀ : ℂ)
    (k : ℕ) (j : Fin G.rank) :
    ((Real.pi : ℂ) * ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)).im
      = Real.pi * (G.lambda j * s₀.im + (G.mu j).im) := by
  have hkd : ((k : ℂ) / (G.degree : ℂ)) = ((((k : ℝ) / G.degree : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hkd]
  simp [Complex.mul_im, Complex.mul_re]

/-- **The sine factor is bounded along the shift lattice**, with no hypothesis: shifting the real
part leaves every imaginary part unchanged. -/
theorem SelbergGammaData.exists_bound_norm_asymmetricS_shift (G : SelbergGammaData) (s₀ : ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ,
      ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ ≤ B := by
  refine ⟨(2 : ℝ) ^ G.rank * ∏ j, Real.exp |Real.pi * (G.lambda j * s₀.im + (G.mu j).im)|,
    by positivity, fun k => ?_⟩
  unfold SelbergGammaData.asymmetricS
  rw [norm_mul, norm_pow, norm_prod]
  have hnorm2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [hnorm2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  have := norm_sin_le_exp_abs_im
    ((Real.pi : ℂ) * ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j))
  rwa [G.sine_arg_im s₀ k j] at this

/-! ## The reflected Dirichlet series tends to the first coefficient -/

theorem ExtendedSelbergClass.tendsto_norm_reflection_shift (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    Tendsto (fun k : ℕ =>
        ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖) atTop
      (𝓝 ‖(F.coeff 1 : ℂ)‖) := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((4 : ℝ) : ℂ) n‖) :=
    summable_norm_term_of_rpow_bound hC (by norm_num)
  set w : ℕ → ℂ := fun k => 1 - star (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) with hw
  have hkd : ∀ k : ℕ, ((k : ℂ) / (F.gammaData.degree : ℂ))
      = ((((k : ℝ) / F.gammaData.degree : ℝ)) : ℂ) := by
    intro k
    push_cast
    ring
  have hre : ∀ k : ℕ, (w k).re = 1 - s₀.re + (k : ℝ) / F.gammaData.degree := by
    intro k
    rw [hw]
    simp only [hkd k]
    simp
    ring
  have hatTop : Tendsto (fun k : ℕ => (w k).re) atTop atTop := by
    have hbase : Tendsto (fun k : ℕ => (k : ℝ) / F.gammaData.degree) atTop atTop := by
      refine Filter.Tendsto.atTop_div_const hd ?_
      exact tendsto_natCast_atTop_atTop
    have := Filter.tendsto_atTop_add_const_left atTop (1 - s₀.re) hbase
    refine this.congr fun k => (hre k).symm
  have hLS := tendsto_LSeries_of_re_atTop hsum hatTop
  have heq : ∀ᶠ k : ℕ in atTop,
      ‖LSeries (fun n => (F.coeff n : ℂ)) (w k)‖
        = ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ := by
    filter_upwards [hatTop.eventually_gt_atTop 1] with k hk
    rw [selbergConjugateReflection, norm_star]
    congr 1
    exact F.lSeries_eq_value (w k) hk
  exact (hLS.norm).congr' heq

/-! ## The root law -/

/-- **Step 3 of the cusp--spectrum radius law, in every degree.**  Along the shift lattice the
factorially normalized values of a class member have `k`-th root `limsup` exactly the cusp
constant `q^{1/d}/(2πd)` of the gamma presentation. -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hFE : ∀ᶠ k : ℕ in atTop,
      (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) ∈ F.asymmetricFERegularSet)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfreq : ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  set d : ℝ := F.gammaData.degree with hdef
  set κ : ℝ := F.gammaData.conductor ^ (1 / d) / (2 * Real.pi * d) with hκdef
  have hκ : 0 < κ := by
    have h1 : 0 < F.gammaData.conductor ^ (1 / d) :=
      Real.rpow_pos_of_pos F.gammaData.conductor_pos _
    have h2 : 0 < 2 * Real.pi * d := by positivity
    exact div_pos h1 h2
  -- the archimedean group converges to the cusp constant
  have harch := F.gammaData.tendsto_norm_asymmetricH_shift_rpow_inv hd s₀
  -- the reflected series contributes nothing
  have hrefl : Tendsto (fun k : ℕ =>
      ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hlim := F.tendsto_norm_reflection_shift hd s₀
    have hpos : 0 < ‖(F.coeff 1 : ℂ)‖ := norm_pos_iff.mpr ha1
    refine tendsto_rpow_inv_of_polynomial_bounds (C₁ := ‖(F.coeff 1 : ℂ)‖ / 2)
      (C₂ := 2 * ‖(F.coeff 1 : ℂ)‖) (B := 0) (by positivity) (by positivity) ?_ ?_
    · filter_upwards [hlim.eventually_const_lt
        (by linarith : ‖(F.coeff 1 : ℂ)‖ / 2 < ‖(F.coeff 1 : ℂ)‖)] with k hk
      rw [neg_zero, Real.rpow_zero, mul_one]
      exact hk.le
    · filter_upwards [hlim.eventually_lt_const
        (by linarith : ‖(F.coeff 1 : ℂ)‖ < 2 * ‖(F.coeff 1 : ℂ)‖)] with k hk
      rw [Real.rpow_zero, mul_one]
      exact hk.le
  have hA : Tendsto (fun k : ℕ =>
      (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ))
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ)))
      atTop (𝓝 κ) := by
    have h := harch.mul hrefl
    rwa [mul_one] at h
  -- the sine factor has root limsup one
  obtain ⟨B, hB, hBle⟩ := F.gammaData.exists_bound_norm_asymmetricS_shift s₀
  have hnn : ∀ k : ℕ, 0 ≤ ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ :=
    fun k => norm_nonneg _
  have hBlimsup : limsup (fun k : ℕ =>
      ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ))) atTop = 1 :=
    limsup_rpow_inv_eq_one hB hc₀ hnn hBle hfreq
  have hBbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ =>
      ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ))) :=
    isBoundedUnder_rpow_inv hB hnn hBle
  have hmain := limsup_mul_eq_of_tendsto hκ hA
    (fun k => Real.rpow_nonneg (norm_nonneg _) _) hBbdd hBlimsup
  rw [← hmain]
  refine limsup_congr ?_
  filter_upwards [hFE] with k hmem
  have hFEk := F.asymmetricFunctionalEquation_eq_of_mem_regularSet hmem
  have hnormF : ‖F (s₀ - (k : ℂ) / (d : ℂ))‖
      = ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ := by
    rw [hFEk, norm_mul, norm_mul, norm_mul, F.gammaData.norm_invariantRootNumber, one_mul]
  have hfactnn : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
  rw [hnormF]
  have hrearr : ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)
      = (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)
          * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖)
        * ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ := by
    ring
  rw [hrearr, Real.mul_rpow (by positivity) (norm_nonneg _),
    Real.mul_rpow (by positivity) (norm_nonneg _)]

end

end RHTower
