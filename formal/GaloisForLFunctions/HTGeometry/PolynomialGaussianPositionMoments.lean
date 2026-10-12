import GaloisForLFunctions.HTGeometry.HermitePolynomialDerivativeEnergy
import GaloisForLFunctions.HTGeometry.SchwartzOscillatorL2Bound
import GaloisForLFunctions.HTGeometry.SchwartzSupL2Bound

/-!
# Position moments of polynomial–Gaussians

**Theorem** (`norm_toLp_mulX_polyGauss_le`).  For a real polynomial `P` of degree `d` and
`v = P(x) e^{-πx²}`,

`‖x v‖₂ ≤ (√d + √(d+1)) / (2√π) · ‖v‖₂`.

Proof.  With annihilation `B = 2πx + ∂` and creation `A = 2πx − ∂`, `4πx = A + B`.  The number
operator `N = AB` has norm `≤ 4πd` on the first `d + 1` Hermite modes.  Hence
`‖Bv‖² ≤ ‖v‖ ‖Nv‖ ≤ 4πd ‖v‖²` and `‖Av‖² ≤ ‖v‖ ‖(N + 4π)v‖ ≤ 4π(d + 1) ‖v‖²`.

**Corollary** (`norm_toLp_polyGauss_X_pow_mul_le`).
`‖x^k v‖₂ ≤ ∏_{i<k} (√(d+i) + √(d+i+1))/(2√π) · ‖v‖₂`.  A polynomial–Gaussian of degree `d` lives
in the phase-space disc of radius `≍ √d`; its mass beyond `|x| ≳ √(d + k)` is controlled by the
`k`-th moment.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory Polynomial

namespace GaloisForLFunctions

noncomputable section

theorem mulXCLM_polyGaussSchwartz (P : ℝ[X]) :
    mulXCLM (polyGaussSchwartz P) = polyGaussSchwartz (X * P) := by
  apply SchwartzMap.ext
  intro x
  simp only [mulXCLM_apply, polyGaussSchwartz_apply, eval_mul, eval_X]
  push_cast
  ring

theorem annihilationCLM_add_creationCLM (f : 𝓢(ℝ, ℂ)) :
    annihilationCLM f + creationCLM f = (4 * (π : ℂ)) • mulXCLM f := by
  rw [annihilationCLM_eq, creationCLM_eq, add_add_sub_cancel, ← add_smul]
  congr 1
  ring

theorem schwartz_toLp_add (f g : 𝓢(ℝ, ℂ)) :
    (f + g).toLp 2 (volume : Measure ℝ) = f.toLp 2 volume + g.toLp 2 volume := by
  have h := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_add f g
  simpa only [SchwartzMap.toLpCLM_apply] using h

theorem schwartz_toLp_smul (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    (c • f).toLp 2 (volume : Measure ℝ) = c • f.toLp 2 volume := by
  have h := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_smul c f
  simpa only [SchwartzMap.toLpCLM_apply] using h

/-- **The position bound.**  `‖x v‖₂ ≤ (√d + √(d+1))/(2√π) ‖v‖₂` for `v = P e^{-πx²}`,
`d = deg P`. -/
theorem norm_toLp_mulX_polyGauss_le (P : ℝ[X]) :
    ‖(mulXCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      (Real.sqrt P.natDegree + Real.sqrt (P.natDegree + 1)) / (2 * Real.sqrt π) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  obtain ⟨v, hv⟩ : ∃ v, v = polyGaussSchwartz P := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = P.natDegree := ⟨_, rfl⟩
  rw [← hv, ← hd]
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hN := numberCLM_polyGauss_norm_le P
  rw [← hv, ← hd] at hN
  have hB := norm_toLp_annihilationCLM_sq_le v
  have hA := norm_toLp_creationCLM_sq_le v
  set n := ‖v.toLp 2 (volume : Measure ℝ)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hππ : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hdd : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd0
  have hd1 : Real.sqrt (d + 1) ^ 2 = d + 1 := Real.sq_sqrt (by linarith)
  have hBv : ‖(annihilationCLM v).toLp 2 (volume : Measure ℝ)‖ ≤
      2 * Real.sqrt π * Real.sqrt d * n := by
    have h2 : ‖(annihilationCLM v).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        (2 * Real.sqrt π * Real.sqrt d * n) ^ 2 := by
      calc ‖(annihilationCLM v).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤ n * (4 * π * d * n) :=
            hB.trans (mul_le_mul_of_nonneg_left hN hn0)
        _ = (2 * Real.sqrt π * Real.sqrt d * n) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, hππ, hdd]; ring
    have := abs_le_of_sq_le_sq h2 (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hAv : ‖(creationCLM v).toLp 2 (volume : Measure ℝ)‖ ≤
      2 * Real.sqrt π * Real.sqrt (d + 1) * n := by
    have hsum : ‖(numberCLM v + (4 * (π : ℂ)) • v).toLp 2 (volume : Measure ℝ)‖ ≤
        4 * π * (d + 1) * n := by
      rw [schwartz_toLp_add, schwartz_toLp_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have h4 : ‖(4 * (π : ℂ))‖ = 4 * π := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
      rw [h4, ← hn]
      linarith
    have h2 : ‖(creationCLM v).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        (2 * Real.sqrt π * Real.sqrt (d + 1) * n) ^ 2 := by
      calc ‖(creationCLM v).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤ n * (4 * π * (d + 1) * n) :=
            hA.trans (mul_le_mul_of_nonneg_left hsum hn0)
        _ = (2 * Real.sqrt π * Real.sqrt (d + 1) * n) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, hππ, hd1]; ring
    have := abs_le_of_sq_le_sq h2 (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hx : 4 * π * ‖(mulXCLM v).toLp 2 (volume : Measure ℝ)‖ ≤
      ‖(annihilationCLM v).toLp 2 (volume : Measure ℝ)‖ +
        ‖(creationCLM v).toLp 2 (volume : Measure ℝ)‖ := by
    have h := norm_add_le ((annihilationCLM v).toLp 2 (volume : Measure ℝ))
      ((creationCLM v).toLp 2 (volume : Measure ℝ))
    rw [← schwartz_toLp_add, annihilationCLM_add_creationCLM, schwartz_toLp_smul, norm_smul] at h
    have h4 : ‖(4 * (π : ℂ))‖ = 4 * π := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
    rwa [h4] at h
  have hpi : 4 * π = 2 * Real.sqrt π * (2 * Real.sqrt π) := by nlinarith [hππ]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hfin : 4 * π * ‖(mulXCLM v).toLp 2 (volume : Measure ℝ)‖ ≤
      2 * Real.sqrt π * (Real.sqrt d + Real.sqrt (d + 1)) * n := by linarith
  rw [hpi] at hfin
  have h2π : 0 < 2 * Real.sqrt π := by positivity
  nlinarith

/-- **Iterated position moments.**
`‖x^k v‖₂ ≤ ∏_{i<k} (√(d+i) + √(d+i+1))/(2√π) · ‖v‖₂`. -/
theorem norm_toLp_polyGauss_X_pow_mul_le (P : ℝ[X]) (k : ℕ) :
    ‖(polyGaussSchwartz (X ^ k * P)).toLp 2 (volume : Measure ℝ)‖ ≤
      (∏ i ∈ Finset.range k, (Real.sqrt (P.natDegree + i) + Real.sqrt (P.natDegree + i + 1)) /
        (2 * Real.sqrt π)) * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdeg : ((X ^ k * P).natDegree : ℝ) ≤ P.natDegree + k := by
      have := natDegree_mul_le (p := (X : ℝ[X]) ^ k) (q := P)
      rw [natDegree_X_pow] at this
      exact_mod_cast (by omega : (X ^ k * P).natDegree ≤ P.natDegree + k)
    have hstep := norm_toLp_mulX_polyGauss_le (X ^ k * P)
    rw [mulXCLM_polyGaussSchwartz, ← mul_assoc, ← pow_succ'] at hstep
    have hmono : (Real.sqrt (X ^ k * P).natDegree + Real.sqrt ((X ^ k * P).natDegree + 1)) /
        (2 * Real.sqrt π) ≤
        (Real.sqrt (P.natDegree + k) + Real.sqrt (P.natDegree + k + 1)) / (2 * Real.sqrt π) := by
      gcongr
    rw [Finset.prod_range_succ]
    calc ‖(polyGaussSchwartz (X ^ (k + 1) * P)).toLp 2 (volume : Measure ℝ)‖
        ≤ (Real.sqrt (X ^ k * P).natDegree + Real.sqrt ((X ^ k * P).natDegree + 1)) /
            (2 * Real.sqrt π) * ‖(polyGaussSchwartz (X ^ k * P)).toLp 2 (volume : Measure ℝ)‖ :=
          hstep
      _ ≤ (Real.sqrt (P.natDegree + k) + Real.sqrt (P.natDegree + k + 1)) / (2 * Real.sqrt π) *
            ((∏ i ∈ Finset.range k, (Real.sqrt (P.natDegree + i) +
              Real.sqrt (P.natDegree + i + 1)) / (2 * Real.sqrt π)) *
              ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖) :=
          mul_le_mul hmono ih (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-! ## Tails beyond the turning point -/

theorem norm_polyGaussSchwartz_X_pow_mul (P : ℝ[X]) (k : ℕ) (x : ℝ) :
    ‖polyGaussSchwartz (X ^ k * P) x‖ = |x| ^ k * ‖polyGaussSchwartz P x‖ := by
  simp only [polyGaussSchwartz_apply, eval_mul, eval_pow, eval_X, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_pow]
  ring

/-- **Chebyshev tail bound.**  `∫_{|x| ≥ R} |v|² ≤ R^{−2k} ‖x^k v‖₂²` for `v = P e^{-πx²}`. -/
theorem setIntegral_tail_polyGauss_le (P : ℝ[X]) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : ℝ | R ≤ |x|}, ‖polyGaussSchwartz P x‖ ^ 2 ≤
      ‖(polyGaussSchwartz (X ^ k * P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 / R ^ (2 * k) := by
  have hRk : 0 < R ^ (2 * k) := by positivity
  have hint : Integrable (fun x : ℝ => ‖polyGaussSchwartz (X ^ k * P) x‖ ^ 2) := by
    have := (polyGaussSchwartz (X ^ k * P)).memLp 2 (volume : Measure ℝ)
    exact this.integrable_norm_pow (by norm_num)
  have hpt : ∀ x ∈ {x : ℝ | R ≤ |x|}, ‖polyGaussSchwartz P x‖ ^ 2 ≤
      ‖polyGaussSchwartz (X ^ k * P) x‖ ^ 2 / R ^ (2 * k) := by
    intro x hx
    rw [norm_polyGaussSchwartz_X_pow_mul, mul_pow, le_div_iff₀ hRk]
    have hRx : R ^ (2 * k) ≤ (|x| ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm k 2]
      exact pow_le_pow_left₀ hR.le hx _
    nlinarith [sq_nonneg ‖polyGaussSchwartz P x‖]
  calc ∫ x in {x : ℝ | R ≤ |x|}, ‖polyGaussSchwartz P x‖ ^ 2
      ≤ ∫ x in {x : ℝ | R ≤ |x|}, ‖polyGaussSchwartz (X ^ k * P) x‖ ^ 2 / R ^ (2 * k) :=
        setIntegral_mono_on ((polyGaussSchwartz P).memLp 2 volume |>.integrable_norm_pow
          (by norm_num)).integrableOn (hint.div_const _).integrableOn
          (measurableSet_le measurable_const (continuous_abs.measurable)) hpt
    _ ≤ ∫ x : ℝ, ‖polyGaussSchwartz (X ^ k * P) x‖ ^ 2 / R ^ (2 * k) :=
        setIntegral_le_integral (hint.div_const _) (Filter.Eventually.of_forall fun x => by
          positivity)
    _ = ‖(polyGaussSchwartz (X ^ k * P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 / R ^ (2 * k) := by
        rw [integral_div, ← norm_toLp_sq_eq_integral]

/-- **Phase-space tail.**  For `v = P e^{-πx²}` of degree `d`,
`∫_{|x| ≥ R} |v|² ≤ R^{−2k} ∏_{i<k} c(d+i)² ‖v‖₂²`, `c(m) = (√m + √(m+1))/(2√π)`.  With `k ≍ d` and
`R² ≥ λ d`, `λ` above the turning constant, this is exponentially small in `d`. -/
theorem setIntegral_tail_polyGauss_le_moment (P : ℝ[X]) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : ℝ | R ≤ |x|}, ‖polyGaussSchwartz P x‖ ^ 2 ≤
      (∏ i ∈ Finset.range k, (Real.sqrt (P.natDegree + i) + Real.sqrt (P.natDegree + i + 1)) /
        (2 * Real.sqrt π)) ^ 2 * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 /
        R ^ (2 * k) := by
  refine (setIntegral_tail_polyGauss_le P k hR).trans ?_
  have hm := norm_toLp_polyGauss_X_pow_mul_le P k
  have h0 := norm_nonneg ((polyGaussSchwartz (X ^ k * P)).toLp 2 (volume : Measure ℝ))
  gcongr
  rw [← mul_pow]
  exact pow_le_pow_left₀ h0 hm 2

end

end GaloisForLFunctions
