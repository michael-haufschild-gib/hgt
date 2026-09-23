import GaloisForLFunctions.HTGeometry.AbstractSpectralObliqueComovingExponential

/-!
# Critical oblique mass localization on a moving diagonal corona

The open oblique chamber `4σv>1` is exponentially blind.  This module classifies the exact phase
wall `4σv=1`.  Put `A=a-1/2`, and write an original point as `R+iJ` and its mass image as `M+iK`.
The critical real exponent obeys the large-deviation law

`M(-σM+uK) ≤ -σ((A-R)^(2 : ℕ)+A)`.

Thus every point outside the multiplicative corona `A/2 ≤ R ≤ 2A` regains a linear exponential
gap.  The complete mass trace equals the finite corona trace modulo an explicit exponentially
small tail.  Critical information is therefore neither a finite aperture jet nor a fixed compact
window: it is a cofinal finite packet moving along the spectral diagonal.
-/

open Complex
open scoped BigOperators

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- The threshold-corrected aperture and original height have an additional unit-scale joint gap. -/
theorem sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re
    {a : ℝ} (ha : 2 ≤ a) (i : ι) :
    (a - 1 / 2) ^ (2 : ℕ) + (F.pt i).re ^ (2 : ℕ) + (a - 1 / 2) ≤
      ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re ^ (2 : ℕ) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  have hJ := F.abs_im_lt i
  have hJ2 : (F.pt i).im ^ (2 : ℕ) < 1 / 4 := by
    nlinarith [sq_abs (F.pt i).im, abs_nonneg ((F.pt i).im)]
  have hM2raw := re_le_sq_csqrtRe (F.massArg_re_pos haHalf i)
  rw [F.massArg_re] at hM2raw
  have hM2 :
      (F.pt i).re ^ (2 : ℕ) - (F.pt i).im ^ (2 : ℕ) + a ^ (2 : ℕ) ≤
        ((F.mass haHalf).pt i).re ^ (2 : ℕ) := by
    simpa only [F.mass_pt, csqrt_re] using hM2raw
  nlinarith

/-- Finite multiplicative corona around the critical diagonal `Re p = a - 1/2`. -/
def criticalDiagonalCorona (a : ℝ) : Finset ι :=
  ((F.shell_finite (2 * (a - 1 / 2))).toFinset).filter
    (fun i => (a - 1 / 2) / 2 ≤ (F.pt i).re)

theorem mem_criticalDiagonalCorona {a : ℝ} {i : ι} :
    i ∈ F.criticalDiagonalCorona a ↔
      (a - 1 / 2) / 2 ≤ (F.pt i).re ∧
        (F.pt i).re ≤ 2 * (a - 1 / 2) := by
  simp [criticalDiagonalCorona, and_comm]

/-- On the phase wall, the real exponent is controlled by the squared distance from the moving
diagonal, plus the strict strip-width gap. -/
theorem critical_mass_phase_defect
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (_hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) (i : ι) :
    ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re *
        (-σ * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re +
          u * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).im) ≤
      -σ * (((a - 1 / 2) - (F.pt i).re) ^ (2 : ℕ) + (a - 1 / 2)) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (F.pt i).re
  let J : ℝ := (F.pt i).im
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  have hA : 0 < A := by dsimp only [A]; linarith
  have hR : 0 < R := F.re_pos i
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [F.mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg haHalf i
    linarith
  have hsq : A ^ (2 : ℕ) + R ^ (2 : ℕ) + A ≤ M ^ (2 : ℕ) := by
    dsimp only [A, R, M]
    simpa only using F.sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re ha i
  have hprod := F.re_mul_im_mass haHalf i
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    simpa only [M, K, R, J, abs_mul, abs_of_pos hM, abs_of_pos hR] using habs
  have hJ : |J| ≤ 1 / 2 := (F.abs_im_lt i).le
  have hMK : M * |K| ≤ R / 2 := by
    rw [hprodAbs]
    nlinarith [mul_le_mul_of_nonneg_left hJ hR.le]
  have huK : M * (u * K) ≤ |u| * (R / 2) := by
    calc
      M * (u * K) ≤ M * |u * K| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hM.le
      _ = |u| * (M * |K|) := by rw [abs_mul]; ring
      _ ≤ |u| * (R / 2) := mul_le_mul_of_nonneg_left hMK (abs_nonneg u)
  have hconeR : v * |u| * R ≤ A * R := by
    have := mul_le_mul_of_nonneg_right hcone hR.le
    simpa only [A] using this
  have hscaled : 2 * σ * (v * |u| * R) ≤ 2 * σ * (A * R) :=
    mul_le_mul_of_nonneg_left hconeR (by positivity)
  have hucrit : |u| * (R / 2) ≤ 2 * σ * A * R := by
    calc
      |u| * (R / 2) = (4 * σ * v) * (|u| * (R / 2)) := by rw [hcritical]; ring
      _ = 2 * σ * (v * |u| * R) := by ring
      _ ≤ 2 * σ * (A * R) := hscaled
      _ = 2 * σ * A * R := by ring
  have hphase : M * (-σ * M + u * K) ≤ -σ * M ^ (2 : ℕ) + 2 * σ * A * R := by
    nlinarith
  change M * (-σ * M + u * K) ≤ -σ * ((A - R) ^ (2 : ℕ) + A)
  nlinarith

/-- Outside the critical diagonal corona, the phase defect regains a uniform linear spectral
gap. -/
theorem critical_mass_phase_le_outside_corona
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1)
    {i : ι} (hi : i ∉ F.criticalDiagonalCorona a) :
    -σ * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re +
        u * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).im ≤
      -(σ / 12) * ((a - 1 / 2) + (F.pt i).re) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (F.pt i).re
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  have hA : 0 < A := by dsimp only [A]; linarith
  have hR : 0 < R := F.re_pos i
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [F.mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg haHalf i
    linarith
  have hMup : M ≤ A + R + 1 / 2 := by
    dsimp only [M, A, R]
    rw [F.mass_pt, csqrt_re]
    have := F.csqrtRe_massArg_le_add haHalf i
    linarith
  have hMup' : M ≤ (4 / 3 : ℝ) * (A + R) := by
    have hAthree : 3 / 2 ≤ A := by dsimp only [A]; linarith
    nlinarith
  have hout : R < A / 2 ∨ 2 * A < R := by
    have hnot : ¬ (A / 2 ≤ R ∧ R ≤ 2 * A) := by
      intro hmem
      apply hi
      exact F.mem_criticalDiagonalCorona.mpr (by simpa only [A, R] using hmem)
    by_cases hlo : A / 2 ≤ R
    · exact Or.inr (lt_of_not_ge (fun hupper => hnot ⟨hlo, hupper⟩))
    · exact Or.inl (lt_of_not_ge hlo)
  have hsqgap : (A + R) ^ (2 : ℕ) ≤ 9 * (A - R) ^ (2 : ℕ) := by
    rcases hout with hlo | hhi
    · have hlin : A + R ≤ 3 * (A - R) := by linarith
      have hnonneg : 0 ≤ A - R := by linarith
      nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ A + R) hlin]
    · have hlin : A + R ≤ 3 * (R - A) := by linarith
      have hnonneg : 0 ≤ R - A := by linarith
      nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ A + R) hlin]
  have hratio : (A + R) * M ≤ 12 * (A - R) ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hMup' (by positivity : 0 ≤ A + R)
    nlinarith
  have hdefect := F.critical_mass_phase_defect ha hσ hv hcone hcritical i
  have hscaled : -σ * ((A - R) ^ (2 : ℕ) + A) ≤
      M * (-(σ / 12) * (A + R)) := by
    have hσratio := mul_le_mul_of_nonneg_left hratio (show 0 ≤ σ / 12 by positivity)
    nlinarith
  have hmul : M * (-σ * M + u * K) ≤ M * (-(σ / 12) * (A + R)) := by
    have hdefect' : M * (-σ * M + u * K) ≤
        -σ * ((A - R) ^ (2 : ℕ) + A) := by
      simpa only [M, K, A, R] using hdefect
    nlinarith
  have hfinal := le_of_mul_le_mul_left hmul hM
  simpa only [M, K, A, R] using hfinal

/-- Every individual critical-wall term is contractive. -/
theorem norm_mass_term_le_one_of_critical
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) (i : ι) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ ≤ 1 := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  have hA : 0 < A := by dsimp only [A]; linarith
  have hM : 0 < M := by
    have hMR : (F.pt i).re < M := by
      dsimp only [M]
      simpa only [F.mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg haHalf i
    linarith [F.re_pos i]
  have hdefect := F.critical_mass_phase_defect ha hσ hv hcone hcritical i
  have hexponent : -σ * M + u * K ≤ 0 := by
    have hdefect' : M * (-σ * M + u * K) ≤
        -σ * (((A - (F.pt i).re) ^ (2 : ℕ)) + A) := by
      simpa only [M, K, A] using hdefect
    have hright : -σ * (((A - (F.pt i).re) ^ (2 : ℕ)) + A) < 0 := by
      have : 0 < (A - (F.pt i).re) ^ (2 : ℕ) + A := by positivity
      nlinarith
    nlinarith
  rw [(F.mass haHalf).norm_term]
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  dsimp only [M, K] at hexponent ⊢
  linarith

/-- Outside the critical corona, individual terms recover a summable exponential gap. -/
theorem norm_mass_term_le_critical_corona_tail
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1)
    {i : ι} (hi : i ∉ F.criticalDiagonalCorona a) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ ≤
      Real.exp (-(σ / 12) * (a - 1 / 2)) * F.weight (σ / 12) i := by
  let haHalf : 1 / 2 ≤ a := by linarith
  have hphase := F.critical_mass_phase_le_outside_corona
    ha hσ hv hcone hcritical hi
  rw [(F.mass haHalf).norm_term, weight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  linarith

/-- Finite trace carried by the moving critical diagonal corona. -/
def massCriticalDiagonalCoronaTraceC
    (a : ℝ) (ha : 1 / 2 ≤ a) (τ : ℂ) : ℂ :=
  ∑ i ∈ F.criticalDiagonalCorona a, (F.mass ha).term τ i

/-- The finite critical corona has the trivial but sharp cardinality majorant. -/
theorem norm_massCriticalDiagonalCoronaTraceC_le_card
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    ‖F.massCriticalDiagonalCoronaTraceC a
        (show 1 / 2 ≤ a by linarith) ((σ : ℂ) + u * I)‖ ≤
      (F.criticalDiagonalCorona a).card := by
  classical
  unfold massCriticalDiagonalCoronaTraceC
  calc
    ‖∑ i ∈ F.criticalDiagonalCorona a,
        (F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ ≤
      ∑ i ∈ F.criticalDiagonalCorona a,
        ‖(F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _i ∈ F.criticalDiagonalCorona a, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => F.norm_mass_term_le_one_of_critical
        ha hσ hv hcone hcritical i
    _ = (F.criticalDiagonalCorona a).card := by simp

/-- **Critical diagonal-corona localization.**  On the exact phase wall, deleting the finite
moving corona leaves an exponentially small trace tail. -/
theorem norm_mass_traceC_sub_criticalDiagonalCoronaTraceC_le
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I) -
        F.massCriticalDiagonalCoronaTraceC a
          (show 1 / 2 ≤ a by linarith) ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(σ / 12) * (a - 1 / 2)) * F.traceReal (σ / 12) := by
  classical
  let haHalf : 1 / 2 ≤ a := by linarith
  let S : Finset ι := F.criticalDiagonalCorona a
  let T : Set ι := (S : Set ι)ᶜ
  let τ : ℂ := (σ : ℂ) + u * I
  let E : ℝ := Real.exp (-(σ / 12) * (a - 1 / 2))
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ12 : 0 < σ / 12 := by positivity
  have hsum : Summable (fun i : ι => (F.mass haHalf).term τ i) :=
    ((F.mass haHalf).summable_norm_term hτ).of_norm
  have hsumnorm : Summable (fun i : ι => ‖(F.mass haHalf).term τ i‖) :=
    (F.mass haHalf).summable_norm_term hτ
  have hweight : Summable (fun i : ι => F.weight (σ / 12) i) :=
    F.summable_weight hσ12
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hdiff :
      (F.mass haHalf).traceC τ - F.massCriticalDiagonalCoronaTraceC a haHalf τ =
        ∑' i : T, (F.mass haHalf).term τ (i : ι) := by
    rw [traceC, massCriticalDiagonalCoronaTraceC, ← hsplit]
    dsimp only [S, T]
    ring
  rw [hdiff]
  calc
    ‖∑' i : T, (F.mass haHalf).term τ (i : ι)‖ ≤
        ∑' i : T, ‖(F.mass haHalf).term τ (i : ι)‖ :=
      norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ ≤ ∑' i : T, E * F.weight (σ / 12) (i : ι) := by
      refine Summable.tsum_le_tsum (fun i => ?_)
        (hsumnorm.subtype _) ((hweight.subtype _).mul_left E)
      have hi : (i : ι) ∉ F.criticalDiagonalCorona a := by
        simpa only [T, S, Set.mem_compl_iff, Finset.mem_coe] using i.2
      simpa only [τ, E] using
        F.norm_mass_term_le_critical_corona_tail ha hσ hv hcone hcritical hi
    _ = E * ∑' i : T, F.weight (σ / 12) (i : ι) := tsum_mul_left
    _ = E * ∑' i : ι, T.indicator (F.weight (σ / 12)) i := by
      rw [tsum_subtype]
    _ ≤ E * ∑' i : ι, F.weight (σ / 12) i := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Summable.tsum_le_tsum
        (fun i => Set.indicator_le_self' (fun _ _ => (F.weight_pos _ _).le) i)
        (hweight.indicator _) hweight
    _ = Real.exp (-(σ / 12) * (a - 1 / 2)) * F.traceReal (σ / 12) := by
      simp only [E, traceReal]

/-- Complete critical trace bound: exponential tails plus one finite cofinal corona. -/
theorem norm_mass_traceC_le_criticalDiagonalCorona_card_add_tail
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I)‖ ≤
      (F.criticalDiagonalCorona a).card +
        Real.exp (-(σ / 12) * (a - 1 / 2)) * F.traceReal (σ / 12) := by
  let C := F.massCriticalDiagonalCoronaTraceC a
    (show 1 / 2 ≤ a by linarith) ((σ : ℂ) + u * I)
  calc
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I)‖ =
        ‖((F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I) - C) + C‖ := by ring_nf
    _ ≤ ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I) - C‖ + ‖C‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (-(σ / 12) * (a - 1 / 2)) * F.traceReal (σ / 12) +
        (F.criticalDiagonalCorona a).card :=
      add_le_add
        (F.norm_mass_traceC_sub_criticalDiagonalCoronaTraceC_le
          ha hσ hv hcone hcritical)
        (F.norm_massCriticalDiagonalCoronaTraceC_le_card ha hσ hv hcone hcritical)
    _ = (F.criticalDiagonalCorona a).card +
        Real.exp (-(σ / 12) * (a - 1 / 2)) * F.traceReal (σ / 12) := by ring

end AbstractSpectralFamily

end

end HTGeometry
