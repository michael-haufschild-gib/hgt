import GaloisForLFunctions.HTGeometry.RegularizedDeterminantLimit

/-!
# Hilbert--Schmidt continuity of the entire regularized determinant

The disc-local `fredholmDet` is an exponential and never vanishes.  The zero divisor belongs to its
canonical entire continuation `entireDet2`, so a divisor-stability argument needs continuity of that
global object, not only continuity of the local exponential.

This file proves fixed-evaluation continuity of `entireDet2` under Hilbert--Schmidt convergence.  The
proof first obtains coefficient convergence from the local determinant Lipschitz estimate and Cauchy's
coefficient bound.  The global Carleman coefficient bound then supplies a common geometric majorant,
allowing dominated convergence at an arbitrary spectral coordinate.

The final theorem is the operator-valued firewall: a fixed normalized determinant zero cannot persist
along Hilbert--Schmidt kernels converging to a kernel whose determinant is nonzero there.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Taylor coefficients of the canonical regularized determinant are continuous along
Hilbert--Schmidt-convergent kernel sequences. -/
theorem tendsto_detCoeff_of_hsNorm_sub_tendsto_zero
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    (k : ℕ) :
    Tendsto (fun n => detCoeff (K n) k) atTop (nhds (detCoeff K₀ k)) := by
  set M : ℝ := hsNorm K₀ + 1 with hMdef
  have hM0 : 0 < M := by
    have := hsNorm_nonneg K₀
    simp only [hMdef]
    linarith
  have hK₀M : hsNorm K₀ ≤ M := by simp [hMdef]
  have hbounded : ∀ᶠ n : ℕ in atTop, hsNorm (K n) ≤ M := by
    have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsmall] with n hn
    have hsplit : hsNorm (K n) ≤ hsNorm (K n - K₀) + hsNorm K₀ := by
      have heq : K n = (K n - K₀) + K₀ := by
        funext p
        simp
      calc
        hsNorm (K n) = hsNorm ((K n - K₀) + K₀) := congrArg hsNorm heq
        _ ≤ hsNorm (K n - K₀) + hsNorm K₀ :=
          hsNorm_add_le (isHS_sub (hK n) hK₀) hK₀
    rw [hMdef]
    linarith
  set r : ℝ := 1 / (2 * M) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrM : r * M = 1 / 2 := by
    rw [hrdef]
    field_simp
  have hrMlt : r * M < 1 := by rw [hrM]; norm_num
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  set C : ℝ := 2 * Real.exp ((r * M) ^ 2 / (1 - r * M)) with hCdef
  set L : ℝ := r ^ 2 * M / (1 - r * M) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef, hrM]; positivity
  have hK₀diff : DifferentiableOn ℂ (fun z => fredholmDet K₀ z) (ball (0 : ℂ) r) :=
    fredholmDet_differentiableOn hK₀ r
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hK₀M hr0.le) hrMlt)
  have hkey : ∀ n, hsNorm (K n) ≤ M → hsNorm (K n - K₀) * L ≤ 1 →
      ‖detCoeff (K n) k - detCoeff K₀ k‖
        ≤ (C * (hsNorm (K n - K₀) * L)) / ρ ^ k := by
    intro n hKn hsmall
    have hKndiff : DifferentiableOn ℂ (fun z => fredholmDet (K n) z) (ball (0 : ℂ) r) :=
      fredholmDet_differentiableOn (hK n) r
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hKn hr0.le) hrMlt)
    have hsubeq : detCoeff (K n) k - detCoeff K₀ k =
        taylorCoeff ((fun z => fredholmDet (K n) z) - fun z => fredholmDet K₀ z) k := by
      simp only [detCoeff, taylorCoeff]
      rw [iteratedDeriv_sub
        ((hKndiff.analyticAt (isOpen_ball.mem_nhds (by simpa using hr0))).contDiffAt)
        ((hK₀diff.analyticAt (isOpen_ball.mem_nhds (by simpa using hr0))).contDiffAt)]
      ring
    rw [hsubeq]
    refine norm_taylorCoeff_le' hρ0 ?_ ?_ k
    · exact diffContOnCl_of_differentiableOn_ball hρ0 hρr (hKndiff.sub hK₀diff)
    · intro z hz
      have hzr : ‖z‖ ≤ r := by
        rw [hz, hρdef]
        linarith
      have hdet := norm_fredholmDet_sub_le (hK n) hK₀ hr0.le hKn hK₀M hM0.le
        hrMlt hzr (by rw [← hLdef]; exact hsmall)
      simpa [hCdef, hLdef] using hdet
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hmaj : Tendsto (fun n : ℕ =>
      (C * (hsNorm (K n - K₀) * L)) / ρ ^ k) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => C * (hsNorm (K n - K₀) * L)) atTop (nhds 0) := by
      have := (hlim.mul_const L).const_mul C
      simpa using this
    simpa using h1.div_const (ρ ^ k)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
  have hevSmall : ∀ᶠ n : ℕ in atTop, hsNorm (K n - K₀) * L ≤ 1 := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · exact Eventually.of_forall fun n => by rw [← hL]; simp
    · have hnear := hlim.eventually (ge_mem_nhds (show (0 : ℝ) < L⁻¹ by positivity))
      filter_upwards [hnear] with n hn
      rw [← le_div_iff₀ hL]
      simpa [div_eq_mul_inv] using hn
  filter_upwards [hbounded, hevSmall] with n hKn hsmall
  exact hkey n hKn hsmall

/-- The canonical entire Hilbert--Carleman determinant is continuous at every fixed spectral
coordinate under Hilbert--Schmidt convergence of kernels. -/
theorem tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    (z : ℂ) :
    Tendsto (fun n => entireDet2 (K n) z) atTop (nhds (entireDet2 K₀ z)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hn : ∀ n, entireDet2 (K n) 0 = 1 := fun n =>
      (isRegularizedDet_entireDet2 (hK n)).eq_one_at_zero
    have h₀ : entireDet2 K₀ 0 = 1 :=
      (isRegularizedDet_entireDet2 hK₀).eq_one_at_zero
    simp_rw [hn, h₀]
    exact tendsto_const_nhds
  · set M : ℝ := hsNorm K₀ + 1 with hMdef
    have hM0 : 0 < M := by
      have := hsNorm_nonneg K₀
      simp only [hMdef]
      linarith
    have hbounded : ∀ᶠ n : ℕ in atTop, hsNorm (K n) ≤ M := by
      have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      filter_upwards [hsmall] with n hn
      have hsplit : hsNorm (K n) ≤ hsNorm (K n - K₀) + hsNorm K₀ := by
        have heq : K n = (K n - K₀) + K₀ := by
          funext p
          simp
        calc
          hsNorm (K n) = hsNorm ((K n - K₀) + K₀) := congrArg hsNorm heq
          _ ≤ hsNorm (K n - K₀) + hsNorm K₀ :=
            hsNorm_add_le (isHS_sub (hK n) hK₀) hK₀
      rw [hMdef]
      linarith
    have hK₀M : hsNorm K₀ ≤ M := by simp [hMdef]
    have hK₀sq : hsNormSq K₀ ≤ M ^ 2 := by
      have heq : hsNormSq K₀ = hsNorm K₀ ^ 2 := by
        rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg K₀)]
      rw [heq]
      exact pow_le_pow_left₀ (hsNorm_nonneg K₀) hK₀M 2
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set R : ℝ := 2 * ‖z‖ with hRdef
    have hR : 0 < R := by rw [hRdef]; positivity
    set E : ℝ := Real.exp (R ^ 2 * M ^ 2 / 2) with hEdef
    set bnd : ℕ → ℝ := fun k => E * (1 / 2) ^ k with hbnd
    have hsumbnd : Summable bnd := by
      rw [hbnd]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left E
    have hterm_bound : ∀ (A : ι × ι → ℂ), IsHS A → hsNorm A ≤ M → ∀ k,
        ‖detCoeff A k * z ^ k‖ ≤ bnd k := by
      intro A hA hAM k
      have hAsq : hsNormSq A ≤ M ^ 2 := by
        have heq : hsNormSq A = hsNorm A ^ 2 := by
          rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg A)]
        rw [heq]
        exact pow_le_pow_left₀ (hsNorm_nonneg A) hAM 2
      have hcoeff : ‖detCoeff A k‖ ≤ E / R ^ k := by
        refine le_trans (norm_detCoeff_le hA hR k) ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [hEdef]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg R])
      rw [norm_mul, norm_pow, hbnd]
      have hzk : ‖z‖ ^ k ≠ 0 := by positivity
      have hkey : (E / R ^ k) * ‖z‖ ^ k = E * (1 / 2) ^ k := by
        have hRk : R ^ k = 2 ^ k * ‖z‖ ^ k := by rw [hRdef, mul_pow]
        rw [hRk, div_pow, one_pow]
        field_simp
      calc
        ‖detCoeff A k‖ * ‖z‖ ^ k ≤ (E / R ^ k) * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = E * (1 / 2) ^ k := hkey
    have hpoint : ∀ k : ℕ, Tendsto
        (fun n => detCoeff (K n) k * z ^ k) atTop
        (nhds (detCoeff K₀ k * z ^ k)) := by
      intro k
      exact (tendsto_detCoeff_of_hsNorm_sub_tendsto_zero K K₀ hK hK₀ hlim k).mul_const _
    have hdom : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
        ‖detCoeff (K n) k * z ^ k‖ ≤ bnd k := by
      filter_upwards [hbounded] with n hn
      exact hterm_bound (K n) (hK n) hn
    have hconv := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
      (f := fun n k => detCoeff (K n) k * z ^ k)
      (g := fun k => detCoeff K₀ k * z ^ k) hsumbnd hpoint hdom
    simpa only [entireDet2, entireOfCoeffs] using hconv

/-- **Operator-valued firewall.** A determinant zero at one fixed normalized spectral coordinate
cannot persist along Hilbert--Schmidt kernels converging to a base kernel whose determinant is
nonzero at that coordinate. -/
theorem not_persistent_entireDet2_zero_of_hsNorm_tendsto
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    (z : ℂ) (hbase : entireDet2 K₀ z ≠ 0) :
    ¬ ∀ n, entireDet2 (K n) z = 0 := by
  intro hzero
  have htoZero : Tendsto (fun n => entireDet2 (K n) z) atTop (nhds 0) := by
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  have htoBase := tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
    K K₀ hK hK₀ hlim z
  exact hbase (tendsto_nhds_unique htoBase htoZero)

end GaloisForLFunctions.HTGeometry
