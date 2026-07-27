import GaloisForLFunctions.RHTower.GammaDampedSquarefreeSeries
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The damped squarefree Dirichlet series and its pole

The Gamma damping `η_d = (1 + d^(-4))^(-1/4)` perturbs the squarefree Dirichlet series by
coefficients of size `O(d^(-4))`, so the correction

```text
H(z) = ∑_d μ(d)² (η_d - 1) d^(-z)
```

has abscissa of absolute convergence at most `-3` and is holomorphic on the half plane
`re z > -3`.  Consequently

```text
F(z) = ∑_d μ(d)² η_d d^(-z) = ζ(z)/ζ(2z) + H(z)        (re z > 1),
```

so the damping does not move the pole: `F` inherits the simple pole of `ζ(z)/ζ(2z)` at `z = 1`
with residue `1/ζ(2) = 6/π²`.
-/

open Filter Topology LSeries

namespace RHTower

noncomputable section

/-! ### The three coefficient families -/

/-- Squarefree indicator coefficients. -/
def squarefreeCoeff (d : ℕ) : ℂ := if Squarefree d then 1 else 0

/-- Gamma-damped squarefree coefficients `μ(d)² η_d`. -/
def gammaDampedCoeff (d : ℕ) : ℂ :=
  if Squarefree d then (gammaDampingFactor d : ℂ) else 0

/-- The damping correction coefficients `μ(d)² (η_d - 1)`. -/
def gammaDampedCorrectionCoeff (d : ℕ) : ℂ :=
  if Squarefree d then ((gammaDampingFactor d - 1 : ℝ) : ℂ) else 0

theorem gammaDampedCoeff_eq (d : ℕ) :
    gammaDampedCoeff d = squarefreeCoeff d + gammaDampedCorrectionCoeff d := by
  rw [gammaDampedCoeff, squarefreeCoeff, gammaDampedCorrectionCoeff]
  split_ifs
  · push_cast
    ring
  · ring

theorem norm_squarefreeCoeff_le (d : ℕ) : ‖squarefreeCoeff d‖ ≤ 1 := by
  rw [squarefreeCoeff]
  split_ifs <;> simp

/-- The correction coefficients are `O(d^(-4))`. -/
theorem norm_gammaDampedCorrectionCoeff_le (d : ℕ) :
    ‖gammaDampedCorrectionCoeff d‖ ≤ 1 / 4 * (d : ℝ) ^ (-4 : ℝ) := by
  have hnn : (0 : ℝ) ≤ 1 / 4 * (d : ℝ) ^ (-4 : ℝ) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg d) (-4 : ℝ)
    linarith
  rw [gammaDampedCorrectionCoeff]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith [gammaDampingFactor_le_one d])]
    exact one_sub_gammaDampingFactor_le d
  · simpa using hnn

/-! ### Abscissae of absolute convergence -/

theorem abscissaOfAbsConv_squarefreeCoeff_le :
    abscissaOfAbsConv squarefreeCoeff ≤ 1 :=
  abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_squarefreeCoeff_le n⟩

theorem abscissaOfAbsConv_gammaDampedCorrectionCoeff_le :
    abscissaOfAbsConv gammaDampedCorrectionCoeff ≤ ((-3 : ℝ) : EReal) := by
  have h := abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := gammaDampedCorrectionCoeff) (x := -4)
    ⟨1 / 4, fun n _ => norm_gammaDampedCorrectionCoeff_le n⟩
  refine h.trans ?_
  rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from rfl, ← EReal.coe_add]
  norm_num

theorem lSeriesSummable_squarefreeCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable squarefreeCoeff s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  refine lt_of_le_of_lt abscissaOfAbsConv_squarefreeCoeff_le ?_
  rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from rfl]
  exact_mod_cast hs

theorem lSeriesSummable_gammaDampedCorrectionCoeff {s : ℂ} (hs : -3 < s.re) :
    LSeriesSummable gammaDampedCorrectionCoeff s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  refine lt_of_le_of_lt abscissaOfAbsConv_gammaDampedCorrectionCoeff_le ?_
  exact_mod_cast hs

/-! ### The correction is holomorphic far to the left -/

/-- The damping correction Dirichlet series. -/
def gammaDampedCorrectionLSeries : ℂ → ℂ := LSeries gammaDampedCorrectionCoeff

/-- **The damping correction is holomorphic on `re z > -3`.** -/
theorem analyticOnNhd_gammaDampedCorrectionLSeries :
    AnalyticOnNhd ℂ gammaDampedCorrectionLSeries {s : ℂ | -3 < s.re} := by
  refine (LSeries_analyticOnNhd gammaDampedCorrectionCoeff).mono fun s hs => ?_
  refine lt_of_le_of_lt abscissaOfAbsConv_gammaDampedCorrectionCoeff_le ?_
  exact_mod_cast hs

theorem analyticAt_gammaDampedCorrectionLSeries_one :
    AnalyticAt ℂ gammaDampedCorrectionLSeries 1 :=
  analyticOnNhd_gammaDampedCorrectionLSeries 1 (by norm_num)

/-! ### The squarefree series and the damped series -/

theorem lSeries_squarefreeCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeries squarefreeCoeff s = riemannZeta s / riemannZeta (2 * s) := by
  rw [← tsum_squarefree_cpow hs]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_squarefree_zero]
  · rw [term_of_ne_zero hn, squarefreeCoeff]
    split_ifs <;> simp

/-- **The Dirichlet reduction.**  `F(z) = ζ(z)/ζ(2z) + H(z)` on `re z > 1`. -/
theorem lSeries_gammaDampedCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeries gammaDampedCoeff s
      = riemannZeta s / riemannZeta (2 * s) + gammaDampedCorrectionLSeries s := by
  have hfun : gammaDampedCoeff = squarefreeCoeff + gammaDampedCorrectionCoeff := by
    funext d
    exact gammaDampedCoeff_eq d
  rw [hfun, LSeries_add (lSeriesSummable_squarefreeCoeff hs)
    (lSeriesSummable_gammaDampedCorrectionCoeff (by linarith)), lSeries_squarefreeCoeff hs]
  rfl

/-! ### The pole of the damped series -/

theorem mem_compl_singleton_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
  intro h
  rw [Set.mem_singleton_iff] at h
  rw [h] at hs
  simp at hs

/-- **The damping does not move the pole.**  `(z-1) F(z) → 1/ζ(2)` as `z → 1` inside the Euler
half plane. -/
theorem tendsto_sub_one_mul_lSeries_gammaDampedCoeff :
    Tendsto (fun s : ℂ => (s - 1) * LSeries gammaDampedCoeff s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds (1 / riemannZeta 2)) := by
  have hsub : {s : ℂ | 1 < s.re} ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := fun _ hs =>
    mem_compl_singleton_of_one_lt_re hs
  have hzeta : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds 1) :=
    riemannZeta_residue_one.mono_left (nhdsWithin_mono 1 hsub)
  have hne : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hcont : ContinuousAt (fun s : ℂ => riemannZeta (2 * s)) 1 := by
    have hne1 : (2 : ℂ) * 1 ≠ 1 := by norm_num
    exact (differentiableAt_riemannZeta hne1).continuousAt.comp (by fun_prop)
  have hinv : Tendsto (fun s : ℂ => (riemannZeta (2 * s))⁻¹)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds (riemannZeta 2)⁻¹) := by
    have h := (hcont.inv₀ (by simpa using hne)).tendsto
    simp only [mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hH : Tendsto (fun s : ℂ => (s - 1) * gammaDampedCorrectionLSeries s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds 0) := by
    have hc := analyticAt_gammaDampedCorrectionLSeries_one.continuousAt
    have h1 : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
      simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
    have := (h1.mul hc).mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {s : ℂ | 1 < s.re}))
    simpa using this
  have hEq : ∀ᶠ s in nhdsWithin 1 {s : ℂ | 1 < s.re},
      ((s - 1) * riemannZeta s) * (riemannZeta (2 * s))⁻¹ +
          (s - 1) * gammaDampedCorrectionLSeries s
        = (s - 1) * LSeries gammaDampedCoeff s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [lSeries_gammaDampedCoeff hs, div_eq_mul_inv]
    ring
  refine Tendsto.congr' hEq ?_
  have := (hzeta.mul hinv).add hH
  simpa [one_div] using this

/-- The complex damped series restricts to the real damped total on the Euler half line. -/
theorem ofReal_gammaDampedTotal_eq {σ : ℝ} (hσ : 1 < σ) :
    (gammaDampedTotal σ : ℂ) = LSeries gammaDampedCoeff (σ : ℂ) := by
  have hmap := Complex.ofRealCLM.map_tsum (summable_gammaDampedMass hσ)
  simp only [Complex.ofRealCLM_apply] at hmap
  rw [gammaDampedTotal, hmap]
  unfold LSeries
  refine tsum_congr fun d => ?_
  rcases eq_or_ne d 0 with rfl | hd
  · simp [gammaDampedMass, not_squarefree_zero]
  · rw [term_of_ne_zero hd, gammaDampedMass, gammaDampedCoeff]
    split_ifs
    · have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hcp : (((d : ℝ) ^ σ : ℝ) : ℂ) = (d : ℂ) ^ (σ : ℂ) := by
        rw [Complex.ofReal_cpow hd0]
        norm_cast
      rw [Complex.ofReal_mul, Real.rpow_neg hd0, Complex.ofReal_inv, hcp, div_eq_mul_inv]
    · simp

/-- The residue in closed real form. -/
theorem tendsto_sub_one_mul_lSeries_gammaDampedCoeff_closed :
    Tendsto (fun s : ℂ => (s - 1) * LSeries gammaDampedCoeff s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds (6 / (Real.pi : ℂ) ^ 2)) := by
  have h := tendsto_sub_one_mul_lSeries_gammaDampedCoeff
  rw [riemannZeta_two] at h
  have hπ : ((Real.pi : ℂ)) ^ 2 ≠ 0 := by
    simp [Real.pi_ne_zero]
  rw [show (1 : ℂ) / ((Real.pi : ℂ) ^ 2 / 6) = 6 / (Real.pi : ℂ) ^ 2 by
    field_simp] at h
  exact h

end

end RHTower
