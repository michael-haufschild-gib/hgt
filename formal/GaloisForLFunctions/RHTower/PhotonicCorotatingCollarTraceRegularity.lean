import GaloisForLFunctions.HTGeometry.DominantEllipticCollarTraceDecay
import GaloisForLFunctions.RHTower.PhotonicFrozenComplexTransmissionConormalNoGo

/-!
# The variable-coefficient rotating-cylinder collar has smooth interface traces

For the TE field `E_z = e^{i q θ - i ω t} U(r, φ')` of the rotating dielectric
cylinder, with co-rotating phase `φ' = 4θ - Ω t`, Maxwell's equation
`ΔE - c⁻² ∂ₜ²(ε E) = 0` becomes, in the Euler radial variable `t = log (r/R)`
and for the angular Fourier modes `u n` of `U` in `φ'`,

  `ü n = 16 (n + α)² u n - 16 e^{2t} (v/c)² (n + β)² (ε̂ ⋆ u) n`,

where `α = q/4`, `β = ω/Ω`, `v = ΩR/4` is the wall speed, and `ε̂` is the Fourier
sequence of the permittivity in `φ'`. Inside the cylinder (`t < 0`) the
dielectric `ε = 25/2 (1 + cos φ'/5) + i/500` gives `ε̂ = (25/2 + i/500; 5/4, 5/4)`.
In exterior air (`t > 0`) `ε̂ = 1`. A nonmagnetic wall makes `u n` and `u̇ n`
continuous across `t = 0`.

At the displayed drive the wall moves well below the light speed. The real
part of the diagonal coefficient therefore dominates the two neighbour
couplings at high grade, uniformly for `|t| < 1/2`. The dominant-collar theorem
then shows that every collar field tempered in `φ'` uniformly in radius has an
interface trace decaying faster than every power of the grade, in both
directions.

A bilateral geometric sequence never decays in both directions. Hence no
nonzero multiple of the prime conormal sideband family `p^{(s-1/2)e}` is the
interface trace of such a field, for any `s`, including the critical line.
This replaces the frozen constant-coefficient collar by the full
variable-coefficient Maxwell collar.
-/

open Set Filter Topology Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Squared ratio of the displayed wall speed `27π/200` to the light speed,
both in units of `10⁸ m/s`. -/
noncomputable def ptrCollarSpeedRatioSq : ℝ :=
  ((27 / 200 * Real.pi) / ((299792458 : ℝ) / 100000000)) ^ 2

/-- Angular mean of the literal lossy rotating dielectric. -/
noncomputable def ptrPaperDielectricMean : ℂ := 25 / 2 + Complex.I * (1 / 500)

/-- The literal dielectric is the three-term Fourier sum with mean
`25/2 + i/500` and first harmonics `5/4` in the co-rotating phase `4φ`. -/
theorem ptrPaperDielectricComplex_eq_fourier (φ : ℝ) :
    ptrPaperDielectricComplex φ =
      ptrPaperDielectricMean + 5 / 4 * Complex.exp (4 * (φ : ℂ) * Complex.I) +
        5 / 4 * Complex.exp (-(4 * (φ : ℂ) * Complex.I)) := by
  have hcos : Complex.cos (4 * (φ : ℂ)) =
      (Complex.exp (4 * (φ : ℂ) * Complex.I) +
        Complex.exp (-(4 * (φ : ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]
    ring_nf
  unfold ptrPaperDielectricComplex ptrPaperDielectricReal ptrPaperDielectricMean
  push_cast
  rw [hcos]
  ring

/-- Mean permittivity across the collar: the dielectric inside, air outside. -/
noncomputable def ptrCollarMeanPermittivity (t : ℝ) : ℂ :=
  if t < 0 then ptrPaperDielectricMean else 1

/-- First-harmonic permittivity across the collar. -/
noncomputable def ptrCollarHarmonicPermittivity (t : ℝ) : ℂ :=
  if t < 0 then 5 / 4 else 0

/-- Common temporal weight `16 e^{2t} (v/c)² (n + β)²` of the material terms. -/
noncomputable def ptrCollarMaterialWeight (β : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  16 * Real.exp (2 * t) * ptrCollarSpeedRatioSq * ((n : ℝ) + β) ^ 2

/-- Diagonal coefficient of the co-rotating collar mode system. -/
noncomputable def ptrCollarDiag (α β : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  ((16 * ((n : ℝ) + α) ^ 2 : ℝ) : ℂ) -
    (ptrCollarMaterialWeight β n t : ℂ) * ptrCollarMeanPermittivity t

/-- Nearest-neighbour coefficient of the co-rotating collar mode system. -/
noncomputable def ptrCollarCoupling (β : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  -((ptrCollarMaterialWeight β n t : ℂ) * ptrCollarHarmonicPermittivity t)

/-- The Euler radial variable turns the radial part `ρ² U'' + ρ U'` of the
polar Laplacian into a plain second derivative. -/
theorem ptr_euler_radial_second_derivative {U U' U'' : ℝ → ℂ} {t : ℝ}
    (hU : HasDerivAt U (U' (Real.exp t)) (Real.exp t))
    (hU'' : HasDerivAt U' (U'' (Real.exp t)) (Real.exp t)) :
    HasDerivAt (fun x => U (Real.exp x)) ((Real.exp t : ℂ) * U' (Real.exp t)) t ∧
      HasDerivAt (fun x => (Real.exp x : ℂ) * U' (Real.exp x))
        ((Real.exp t : ℂ) ^ 2 * U'' (Real.exp t) + (Real.exp t : ℂ) * U' (Real.exp t)) t := by
  have hexp := Real.hasDerivAt_exp t
  constructor
  · have h := hU.scomp t hexp
    rw [Complex.real_smul] at h
    exact h
  · have h1 : HasDerivAt (fun x => (Real.exp x : ℂ)) (Real.exp t : ℂ) t := hexp.ofReal_comp
    have h2 := hU''.scomp t hexp
    rw [Complex.real_smul] at h2
    exact (h1.mul h2).congr_deriv (by simp only [Function.comp_apply]; ring)

/-- The displayed wall is at most one seventh of the light speed. -/
theorem ptrCollarSpeedRatioSq_le : ptrCollarSpeedRatioSq ≤ 1 / 49 := by
  unfold ptrCollarSpeedRatioSq
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hc : (0 : ℝ) < (299792458 : ℝ) / 100000000 := by norm_num
  have h0 : 0 ≤ (27 / 200 * Real.pi) / ((299792458 : ℝ) / 100000000) := by positivity
  have h1 : (27 / 200 * Real.pi) / ((299792458 : ℝ) / 100000000) ≤ 1 / 7 := by
    rw [div_le_iff₀ hc]
    nlinarith
  calc ((27 / 200 * Real.pi) / ((299792458 : ℝ) / 100000000)) ^ 2 ≤ (1 / 7) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = 1 / 49 := by norm_num

theorem ptrCollarSpeedRatioSq_nonneg : 0 ≤ ptrCollarSpeedRatioSq := by
  unfold ptrCollarSpeedRatioSq; positivity

private theorem shifted_sq_bounds {n : ℤ} {α β : ℝ}
    (hα : 10 * |α| ≤ |(n : ℝ)|) (hβ : 10 * |β| ≤ |(n : ℝ)|) :
    81 / 100 * (n : ℝ) ^ 2 ≤ ((n : ℝ) + α) ^ 2 ∧
      ((n : ℝ) + β) ^ 2 ≤ 121 / 100 * (n : ℝ) ^ 2 := by
  have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  constructor
  · have h1 : |(n : ℝ)| - |α| ≤ |(n : ℝ) + α| := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) (-α)
      simpa [sub_neg_eq_add] using this
    have h2 : 9 / 10 * |(n : ℝ)| ≤ |(n : ℝ) + α| := by linarith
    have h3 : (9 / 10 * |(n : ℝ)|) ^ 2 ≤ |(n : ℝ) + α| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [sq_abs, mul_pow, sq_abs] at h3
    linarith
  · have h1 : |(n : ℝ) + β| ≤ |(n : ℝ)| + |β| := abs_add_le _ _
    have h2 : |(n : ℝ) + β| ≤ 11 / 10 * |(n : ℝ)| := by linarith
    have h3 : |(n : ℝ) + β| ^ 2 ≤ (11 / 10 * |(n : ℝ)|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs, mul_pow, sq_abs] at h3
    linarith

private theorem material_weight_le {β δ t : ℝ} {n : ℤ} (hβ : 10 * |β| ≤ |(n : ℝ)|)
    (ht : t ∈ Ioo (-δ) δ) (hδ : δ ≤ 1 / 2) :
    0 ≤ ptrCollarMaterialWeight β n t ∧
      ptrCollarMaterialWeight β n t ≤ 16 * 3 * (1 / 49) * (121 / 100 * (n : ℝ) ^ 2) ∧
      (t < 0 → ptrCollarMaterialWeight β n t ≤ 16 * (1 / 49) * (121 / 100 * (n : ℝ) ^ 2)) := by
  have hρ := ptrCollarSpeedRatioSq_le
  have hρ0 := ptrCollarSpeedRatioSq_nonneg
  have hsq : ((n : ℝ) + β) ^ 2 ≤ 121 / 100 * (n : ℝ) ^ 2 :=
    (shifted_sq_bounds (α := 0) (by simp) hβ).2
  have hsq0 : 0 ≤ ((n : ℝ) + β) ^ 2 := sq_nonneg _
  have hexp0 : 0 < Real.exp (2 * t) := Real.exp_pos _
  have hexp3 : Real.exp (2 * t) ≤ 3 := by
    have : Real.exp (2 * t) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [ht.2])
    linarith [Real.exp_one_lt_d9]
  unfold ptrCollarMaterialWeight
  refine ⟨by positivity, ?_, ?_⟩
  · have h1 : Real.exp (2 * t) * ptrCollarSpeedRatioSq ≤ 3 * (1 / 49) :=
      mul_le_mul hexp3 hρ hρ0 (by norm_num)
    have h2 := mul_le_mul h1 hsq hsq0 (by norm_num)
    nlinarith
  · intro htn
    have hexp1 : Real.exp (2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h1 : Real.exp (2 * t) * ptrCollarSpeedRatioSq ≤ 1 * (1 / 49) :=
      mul_le_mul hexp1 hρ hρ0 (by norm_num)
    have h2 := mul_le_mul h1 hsq hsq0 (by norm_num)
    nlinarith

/-- High-grade strong ellipticity of the literal collar: the real diagonal
coefficient is at least `7 n²` on both sides of the wall. -/
theorem ptrCollarDiag_re_ge {α β δ t : ℝ} {n : ℤ}
    (hα : 10 * |α| ≤ |(n : ℝ)|) (hβ : 10 * |β| ≤ |(n : ℝ)|)
    (ht : t ∈ Ioo (-δ) δ) (hδ : δ ≤ 1 / 2) :
    7 * (n : ℝ) ^ 2 ≤ (ptrCollarDiag α β n t).re := by
  obtain ⟨hW0, hWout, hWin⟩ := material_weight_le hβ ht hδ
  have hsq := (shifted_sq_bounds hα hβ).1
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  unfold ptrCollarDiag ptrCollarMeanPermittivity
  by_cases htn : t < 0
  · rw [if_pos htn]
    have hW := hWin htn
    simp only [ptrPaperDielectricMean, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im]
    norm_num
    nlinarith
  · rw [if_neg htn]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    nlinarith

/-- High-grade neighbour coupling of the literal collar is at most `(1/6) · 7 n²`. -/
theorem ptrCollarCoupling_le {β δ t : ℝ} {n : ℤ}
    (hβ : 10 * |β| ≤ |(n : ℝ)|) (ht : t ∈ Ioo (-δ) δ) (hδ : δ ≤ 1 / 2) :
    ‖ptrCollarCoupling β n t‖ + ‖ptrCollarCoupling β n t‖ ≤ 1 / 6 * 7 * (n : ℝ) ^ 2 := by
  obtain ⟨hW0, -, hWin⟩ := material_weight_le hβ ht hδ
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  unfold ptrCollarCoupling ptrCollarHarmonicPermittivity
  by_cases htn : t < 0
  · rw [if_pos htn, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0]
    have hW := hWin htn
    norm_num
    nlinarith
  · rw [if_neg htn]
    simp only [mul_zero, neg_zero, norm_zero, add_zero]
    positivity

/-- **Smooth interface trace of the literal rotating-cylinder collar.**
Every collar mode family of the co-rotating TE equation, in any helical charge
sector `α` and at any frequency ratio `β`, on any collar `|log(r/R)| ≤ δ ≤ 1/2`,
whose modes are polynomially bounded uniformly in radius, has an interface trace
decaying faster than every power of the grade in both directions. -/
theorem ptr_corotating_collar_trace_rapid_decay
    (α β : ℝ) {δ C : ℝ} {N : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    {u u' u'' : ℤ → ℝ → ℂ}
    (hu : ∀ n, ∀ t ∈ Icc (-δ) δ, HasDerivAt (u n) (u' n t) t)
    (hu'c : ∀ n, ContinuousOn (u' n) (Icc (-δ) δ))
    (hu'' : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 → HasDerivAt (u' n) (u'' n t) t)
    (heq : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      u'' n t = ptrCollarDiag α β n t * u n t +
        (ptrCollarCoupling β n t * u (n - 1) t + ptrCollarCoupling β n t * u (n + 1) t))
    (hpoly : ∀ n, ∀ t ∈ Icc (-δ) δ, ‖u n t‖ ≤ C * (1 + |(n : ℝ)|) ^ N) (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * ‖u n 0‖) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ k * ‖u (-(n : ℤ)) 0‖) atTop (𝓝 0) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (10 * |α| + 10 * |β|)
  have hα' : 0 ≤ 10 * |α| := by positivity
  have hβ' : 0 ≤ 10 * |β| := by positivity
  refine dominantCollar_trace_rapid_decay (κsq := 7) (θ := 1 / 6) (n₀ := n₀)
    hδ0 (by norm_num) (by norm_num) (by norm_num) hu hu'c hu'' heq ?_ ?_ hpoly k
  · intro n hn t ht _
    exact ptrCollarDiag_re_ge (by linarith) (by linarith) ht hδ
  · intro n hn t ht _
    exact ptrCollarCoupling_le (by linarith) ht hδ

/-- **The variable-coefficient Maxwell collar excludes every prime conormal.**
No interface trace of a tempered collar field of the literal rotating cylinder
is a nonzero multiple of the prime conormal sideband family `p^{(s-1/2)e}`,
for any prime `p` and any `s`; in particular not on the critical line. -/
theorem ptr_corotating_collar_prime_conormal_no_go
    (α β : ℝ) {δ C : ℝ} {N : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    {u u' u'' : ℤ → ℝ → ℂ}
    (hu : ∀ n, ∀ t ∈ Icc (-δ) δ, HasDerivAt (u n) (u' n t) t)
    (hu'c : ∀ n, ContinuousOn (u' n) (Icc (-δ) δ))
    (hu'' : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 → HasDerivAt (u' n) (u'' n t) t)
    (heq : ∀ n, ∀ t ∈ Ioo (-δ) δ, t ≠ 0 →
      u'' n t = ptrCollarDiag α β n t * u n t +
        (ptrCollarCoupling β n t * u (n - 1) t + ptrCollarCoupling β n t * u (n + 1) t))
    (hpoly : ∀ n, ∀ t ∈ Icc (-δ) δ, ‖u n t‖ ≤ C * (1 + |(n : ℝ)|) ^ N)
    (p : Nat.Primes) (s z : ℂ) (hz : z ≠ 0) :
    ¬ ∀ e : ℤ, u e 0 = z * photonicPrimePCMConormalSideband p s e := by
  intro htrace
  obtain ⟨hpos, hneg⟩ := ptr_corotating_collar_trace_rapid_decay α β hδ0 hδ hu hu'c hu''
    heq hpoly 0
  simp only [pow_zero, one_mul] at hpos hneg
  have hprod := hpos.mul hneg
  rw [zero_mul] at hprod
  have hconst : ∀ n : ℕ, ‖u n 0‖ * ‖u (-(n : ℤ)) 0‖ = ‖z‖ ^ 2 := by
    intro n
    rw [htrace, htrace, ← norm_mul, photonicPrimePCMConormalSideband,
      photonicPrimePCMConormalSideband]
    have hM : photonicPrimePCMHalfDensityMultiplier p s ≠ 0 := by
      rw [photonicPrimePCMHalfDensityMultiplier_eq_bilateralHalfDensityCharacter]
      exact bilateralHalfDensityCharacter_ne_zero p.property.pos _
    rw [neg_neg, show z * photonicPrimePCMHalfDensityMultiplier p s ^ (-(n : ℤ)) *
        (z * photonicPrimePCMHalfDensityMultiplier p s ^ (n : ℤ)) =
        z ^ 2 * (photonicPrimePCMHalfDensityMultiplier p s ^ (-(n : ℤ)) *
          photonicPrimePCMHalfDensityMultiplier p s ^ (n : ℤ)) by ring,
      zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hM), mul_one, norm_pow]
  simp only [hconst] at hprod
  have : ‖z‖ ^ 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hprod
  exact hz (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this))

end RHTower
