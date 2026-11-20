import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TaylorCoefficientsOfLaplaceTransforms
import GaloisForLFunctions.WindowedLandauTheory.TaylorCoefficientsNearASimplePole

/-!
# Landau's theorem on windows

Let `g` be a real function of at most exponential growth with Laplace transform `Φ`. Suppose `Φ`
continues to `Re s > θ` except for simple poles, with positive residue at every real pole, and
suppose the one-sided bound `g(u) ≤ C e^{θu}` holds on windows `[U, (1+δ)U]` for arbitrarily large
`U`. Then `Φ` has no pole in `Re s > θ` (`re_le_of_window_bound`).

At a far-right centre `σ` the Taylor coefficients `A_k(s) = ∫ g(u) u^k e^{-su}/k! du` satisfy, for
every `|ω| ≤ 1`,

```text
Re A_k(σ) + Re(ω A_k(σ+iγ)) = ∫ g(u) (u^k e^{-σu}/k!) (1 + Re(ω e^{-iγu})) du,
```

with a nonnegative kernel. For `k ≍ U` the kernel concentrates on the window, so the right side is
`O((σ-θ)^{-k})` (`exists_window_coeff_bound`). A pole at distance `d < σ - θ` from `σ + iγ` forces
`|A_k(σ+iγ)| ≍ d^{-k-1}`. Either some pole is horizontally closer to the line `Re s = σ` than every
pole is to `σ`, and from a generic height `γ` one pole is strictly nearest; or the pole nearest to
`σ` is real with positive residue, and then `Re A_k(σ)` itself is too large.
-/

open MeasureTheory Set Complex Filter Topology Metric

namespace WindowedLandauTheory

noncomputable section

/-! ## The positive kernel -/

/-- Multiplying by `e^{cu}` shifts the Taylor kernel's decay rate. -/
theorem taylorKernel_sub (k : ℕ) (a c u : ℝ) :
    taylorKernel k (a - c) u = Real.exp (c * u) * taylorKernel k a u := by
  unfold taylorKernel
  rw [show -(a - c) * u = c * u + -a * u by ring, Real.exp_add]
  ring

/-- A growth bound `|g u| ≤ C₀ e^{bu}` forces `C₀ ≥ 0`. -/
theorem nonneg_of_growth {g : ℝ → ℝ} {C₀ b : ℝ}
    (hgC : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (b * u)) : 0 ≤ C₀ := by
  have h := (abs_nonneg (g 1)).trans (hgC 1 one_pos)
  by_contra hneg
  push Not at hneg
  have := mul_neg_of_neg_of_pos hneg (Real.exp_pos (b * 1))
  linarith

theorem norm_laplaceCoeff_integrand_le {g : ℝ → ℂ} {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖g u * ((u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ))‖ ≤
      C * taylorKernel k (s.re - b) u := by
  have h1 : ‖(u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ)‖ = taylorKernel k s.re u := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hu.le, taylorKernel, show (-s * (u : ℂ)).re = -s.re * u by simp]
  rw [norm_mul, h1, taylorKernel_sub, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hgC u hu) (taylorKernel_nonneg k _ hu.le)

theorem integrableOn_laplaceCoeff_integrand {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) {s : ℂ} (hs : b < s.re) :
    IntegrableOn (fun u : ℝ => g u * ((u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ)))
      (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_taylorKernel k (sub_pos.mpr hs)).const_mul C)
    (hg.mul (by fun_prop : Continuous fun u : ℝ =>
      (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ)).aestronglyMeasurable) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact norm_laplaceCoeff_integrand_le hgC k s hu

/-- The weight `Re(ω e^{-iγu})` of the kernel `1 + Re(ω e^{-iγu})`. -/
def phaseWeight (ω : ℂ) (γ u : ℝ) : ℝ := (ω * cexp (((-(γ * u) : ℝ) : ℂ) * I)).re

theorem abs_phaseWeight_le {ω : ℂ} (hω : ‖ω‖ ≤ 1) (γ u : ℝ) : |phaseWeight ω γ u| ≤ 1 :=
  calc |phaseWeight ω γ u| ≤ ‖ω * cexp (((-(γ * u) : ℝ) : ℂ) * I)‖ := Complex.abs_re_le_norm _
    _ = ‖ω‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ 1 := hω

/-- Pointwise form of the kernel bound: `x T (1 + w) ≤ 2 C e T` when `x ≤ C e`, `T ≥ 0`, `|w| ≤ 1`. -/
theorem kernel_pointwise_le {x T w C e : ℝ} (hx : x ≤ C * e) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hT : 0 ≤ T) (hw : |w| ≤ 1) : x * T * (1 + w) ≤ 2 * C * (e * T) := by
  have h1 := abs_le.mp hw
  have h2 : x * T ≤ C * e * T := mul_le_mul_of_nonneg_right hx hT
  have h3 : 0 ≤ C * e * T := mul_nonneg (mul_nonneg hC he) hT
  calc x * T * (1 + w) ≤ C * e * T * (1 + w) := mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ C * e * T * 2 := mul_le_mul_of_nonneg_left (by linarith) h3
    _ = 2 * C * (e * T) := by ring

theorem vertical_re (σ γ : ℝ) : ((σ : ℂ) + γ * I).re = σ := by simp

theorem vertical_im (σ γ : ℝ) : ((σ : ℂ) + γ * I).im = γ := by simp

/-- **The window inequality.** For `|ω| ≤ 1`, `Re A_k(σ) + Re(ω A_k(σ+iγ))` is at most
`2C/(σ-θ)^{k+1}` plus twice the growth constant times the kernel mass off the window. -/
theorem re_laplaceCoeff_add_re_mul_le {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C₀ b : ℝ}
    (hgC : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (b * u)) {θ C U V : ℝ} (hC : 0 ≤ C)
    (hwin : ∀ u ∈ Icc U V, g u ≤ C * Real.exp (θ * u)) (k : ℕ) {σ : ℝ} (hσb : b < σ)
    (hσθ : θ < σ) (γ : ℝ) {ω : ℂ} (hω : ‖ω‖ ≤ 1) :
    (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ)).re +
        (ω * laplaceCoeff (fun u => (g u : ℂ)) k ((σ : ℂ) + γ * I)).re ≤
      2 * C * ((σ - θ) ^ (k + 1))⁻¹ +
        2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, taylorKernel k (σ - b) u := by
  have hC₀ := nonneg_of_growth hgC
  have hG : AEStronglyMeasurable (fun u => (g u : ℂ)) (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg
  have hGC : ∀ u, 0 < u → ‖(g u : ℂ)‖ ≤ C₀ * Real.exp (b * u) := fun u hu => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu
  have hF₀ := integrableOn_laplaceCoeff_integrand hG hGC k (s := (σ : ℂ))
    (by rw [Complex.ofReal_re]; exact hσb)
  have hF₁ := integrableOn_laplaceCoeff_integrand hG hGC k (s := (σ : ℂ) + γ * I)
    (by rw [vertical_re]; exact hσb)
  have hint : IntegrableOn (fun u : ℝ =>
      (g u : ℂ) * ((u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)) +
        ω * ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ))))
      (Ioi 0) := hF₀.add (hF₁.const_mul ω)
  -- the combined integrand is real: `g T (1 + w)`
  have hpt : ∀ u : ℝ,
      ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)) +
        ω * ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) /
          (k.factorial : ℂ)))).re = g u * taylorKernel k σ u * (1 + phaseWeight ω γ u) := by
    intro u
    have e : -((σ : ℂ) + γ * I) * u = -(σ : ℂ) * u + ((-(γ * u) : ℝ) : ℂ) * I := by
      push_cast
      ring
    have e2 : (g u : ℂ) * ((u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)) +
        ω * ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ))) =
        ((g u * taylorKernel k σ u : ℝ) : ℂ) * (1 + ω * cexp (((-(γ * u) : ℝ) : ℂ) * I)) := by
      rw [e, Complex.exp_add, taylorKernel]
      push_cast
      ring
    rw [phaseWeight, e2, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
  have hre : (∫ u in Ioi (0 : ℝ), ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-(σ : ℂ) * u) /
        (k.factorial : ℂ)) + ω * ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) /
        (k.factorial : ℂ))))).re =
      ∫ u in Ioi (0 : ℝ), g u * taylorKernel k σ u * (1 + phaseWeight ω γ u) := by
    have h := reCLM.integral_comp_comm hint
    simp only [reCLM_apply] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u)
  have hsplit : laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ) +
      ω * laplaceCoeff (fun u => (g u : ℂ)) k ((σ : ℂ) + γ * I) =
      ∫ u in Ioi (0 : ℝ), ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-(σ : ℂ) * u) /
        (k.factorial : ℂ)) + ω * ((g u : ℂ) * ((u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) /
        (k.factorial : ℂ)))) := by
    rw [integral_add hF₀ (hF₁.const_mul ω), integral_const_mul]
    rfl
  have hhint : IntegrableOn (fun u => g u * taylorKernel k σ u * (1 + phaseWeight ω γ u))
      (Ioi 0) := by
    refine (reCLM.integrable_comp hint).congr ?_
    filter_upwards with u
    simp only [reCLM_apply]
    exact hpt u
  rw [← Complex.add_re, hsplit, hre, ← integral_inter_add_sdiff measurableSet_Icc hhint]
  refine add_le_add ?_ ?_
  · -- on the window, `g ≤ C e^{θu}`
    calc ∫ u in Ioi (0 : ℝ) ∩ Icc U V, g u * taylorKernel k σ u * (1 + phaseWeight ω γ u)
        ≤ ∫ u in Ioi (0 : ℝ) ∩ Icc U V, 2 * C * taylorKernel k (σ - θ) u := by
          refine setIntegral_mono_on (hhint.mono_set inter_subset_left)
            (IntegrableOn.mono_set
              ((integrableOn_taylorKernel k (sub_pos.mpr hσθ)).const_mul (2 * C)) inter_subset_left) (measurableSet_Ioi.inter measurableSet_Icc) (fun u hu => ?_)
          have hu0 : (0 : ℝ) < u := hu.1
          rw [taylorKernel_sub]
          exact kernel_pointwise_le (hwin u hu.2) hC (Real.exp_pos _).le
            (taylorKernel_nonneg k σ hu0.le) (abs_phaseWeight_le hω γ u)
      _ ≤ ∫ u in Ioi (0 : ℝ), 2 * C * taylorKernel k (σ - θ) u := by
          refine setIntegral_mono_set
            ((integrableOn_taylorKernel k (sub_pos.mpr hσθ)).const_mul (2 * C)) ?_
            (Eventually.of_forall fun u hu => hu.1)
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
          exact mul_nonneg (mul_nonneg zero_le_two hC) (taylorKernel_nonneg k _ (le_of_lt hu))
      _ = 2 * C * ((σ - θ) ^ (k + 1))⁻¹ := by
          rw [integral_const_mul, integral_taylorKernel k (sub_pos.mpr hσθ)]
  · -- off the window, the growth bound
    calc ∫ u in Ioi (0 : ℝ) \ Icc U V, g u * taylorKernel k σ u * (1 + phaseWeight ω γ u)
        ≤ ∫ u in Ioi (0 : ℝ) \ Icc U V, 2 * C₀ * taylorKernel k (σ - b) u := by
          refine setIntegral_mono_on (hhint.mono_set fun _ h => h.1)
            (IntegrableOn.mono_set
              ((integrableOn_taylorKernel k (sub_pos.mpr hσb)).const_mul (2 * C₀)) fun _ h => h.1) (measurableSet_Ioi.diff measurableSet_Icc) (fun u hu => ?_)
          have hu0 : (0 : ℝ) < u := hu.1
          rw [taylorKernel_sub]
          exact kernel_pointwise_le ((le_abs_self _).trans (hgC u hu0)) hC₀ (Real.exp_pos _).le
            (taylorKernel_nonneg k σ hu0.le) (abs_phaseWeight_le hω γ u)
      _ = 2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, taylorKernel k (σ - b) u :=
          integral_const_mul _ _

/-- Every complex number is rotated onto its modulus by some `ω` with `|ω| ≤ 1`. -/
theorem exists_norm_le_one_mul_re_eq_norm (A : ℂ) : ∃ ω : ℂ, ‖ω‖ ≤ 1 ∧ (ω * A).re = ‖A‖ := by
  rcases eq_or_ne A 0 with rfl | hA
  · exact ⟨0, by simp, by simp⟩
  · have hn : (‖A‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hA)
    refine ⟨starRingEnd ℂ A / ‖A‖, le_of_eq ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
        div_self (norm_ne_zero_iff.mpr hA)]
    · rw [div_mul_eq_mul_div, Complex.conj_mul', pow_two, mul_div_assoc, div_self hn, mul_one,
        Complex.ofReal_re]

/-- **Coefficients on windows.** There is a centre `σ > b` and a constant `K` such that for
infinitely many `k`, uniformly in the height `γ`,
`Re A_k(σ) + |A_k(σ+iγ)| ≤ K/(σ-θ)^k`. -/
theorem exists_window_coeff_bound {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C₀ b : ℝ}
    (hgC : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (b * u)) {θ δ C : ℝ} (hθb : θ ≤ b) (hδ : 0 < δ)
    (hC : 0 ≤ C)
    (hwin : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u)) :
    ∃ σ : ℝ, b < σ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∃ k ≥ N, ∀ γ : ℝ,
      (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ)).re +
        ‖laplaceCoeff (fun u => (g u : ℂ)) k ((σ : ℂ) + γ * I)‖ ≤ K / (σ - θ) ^ k := by
  have hC₀ := nonneg_of_growth hgC
  obtain ⟨a, ha, C', hC'⟩ := exists_taylorKernel_tail_le hδ (sub_nonneg.mpr hθb)
  have hpos : 0 < a + b - θ := by linarith
  refine ⟨a + b, by linarith, 2 * C / (a + b - θ) + 2 * C₀ * max C' 0,
    add_nonneg (div_nonneg (mul_nonneg zero_le_two hC) hpos.le)
      (mul_nonneg (mul_nonneg zero_le_two hC₀) (le_max_right _ _)), fun N => ?_⟩
  obtain ⟨U, hU, hUw⟩ := hwin (max N 1)
  obtain ⟨k, hk, htail⟩ := hC' U ((le_max_right _ _).trans hU)
  refine ⟨k, ?_, fun γ => ?_⟩
  · exact_mod_cast ((le_max_left (N : ℝ) 1).trans hU).trans hk
  · obtain ⟨ω, hω, hωA⟩ := exists_norm_le_one_mul_re_eq_norm
      (laplaceCoeff (fun u => (g u : ℂ)) k (((a + b : ℝ) : ℂ) + γ * I))
    have h1 := re_laplaceCoeff_add_re_mul_le hg hgC hC hUw k (σ := a + b) (by linarith)
      (by linarith) γ hω
    rw [hωA, add_sub_cancel_right] at h1
    have h2 : C' / (a + (b - θ)) ^ k ≤ max C' 0 / (a + b - θ) ^ k := by
      rw [show a + (b - θ) = a + b - θ by ring]
      exact div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hpos.le _)
    calc _ ≤ 2 * C * ((a + b - θ) ^ (k + 1))⁻¹ +
          2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), taylorKernel k a u := h1
      _ ≤ 2 * C * ((a + b - θ) ^ (k + 1))⁻¹ + 2 * C₀ * (max C' 0 / (a + b - θ) ^ k) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (htail.trans h2)
            (mul_nonneg zero_le_two hC₀))
      _ = (2 * C / (a + b - θ) + 2 * C₀ * max C' 0) / (a + b - θ) ^ k := by
          have e : ∀ y : ℝ, 2 * C * (y ^ (k + 1))⁻¹ + 2 * C₀ * (max C' 0 / y ^ k) =
              (2 * C / y + 2 * C₀ * max C' 0) / y ^ k := fun y => by ring
          exact e _

/-! ## Geometry of the poles -/

theorem dist_sq_eq (a z : ℂ) : dist a z ^ 2 = (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem sub_re_le_dist (a z : ℂ) : z.re - a.re ≤ dist a z := by
  have h := Complex.abs_re_le_norm (a - z)
  rw [Complex.sub_re] at h
  rw [Complex.dist_eq]
  linarith [neg_abs_le (a.re - z.re)]

/-- A disc of radius at most `Re z - θ` lies in the half-plane `Re s > θ`. -/
theorem ball_subset_re_gt {z : ℂ} {θ r : ℝ} (hr : r ≤ z.re - θ) :
    ball z r ⊆ {s : ℂ | θ < s.re} := fun s hs => by
  have h := sub_re_le_dist s z
  have hs' : dist s z < r := hs
  show θ < s.re
  linarith

theorem closedBall_subset_re_gt {z : ℂ} {θ r : ℝ} (hr : r < z.re - θ) :
    closedBall z r ⊆ {s : ℂ | θ < s.re} := fun s hs => by
  have h := sub_re_le_dist s z
  have hs' : dist s z ≤ r := hs
  show θ < s.re
  linarith

/-- Inside a finite set, the points outside `S` that are farther than `t` from `z` stay outside a
slightly larger disc. -/
theorem exists_radius_gap {F S : Set ℂ} (hF : F.Finite) (z : ℂ) {t R : ℝ} (htR : t < R)
    (hS : ∀ ρ ∈ F, ρ ∉ S → t < dist ρ z) :
    ∃ r : ℝ, t < r ∧ r ≤ R ∧ ∀ ρ ∈ F, dist ρ z < r → ρ ∈ S := by
  rcases (F \ S).eq_empty_or_nonempty with h | h
  · refine ⟨R, htR, le_rfl, fun ρ hρ _ => ?_⟩
    by_contra hρS
    have hmem : ρ ∈ F \ S := ⟨hρ, hρS⟩
    rw [h] at hmem
    exact hmem
  · obtain ⟨ρ₀, hρ₀, hmin⟩ :=
      Set.exists_min_image (F \ S) (fun ρ => dist ρ z) (hF.subset fun _ h => h.1) h
    refine ⟨min R (dist ρ₀ z), lt_min htR (hS ρ₀ hρ₀.1 hρ₀.2), min_le_left _ _,
      fun ρ hρ hd => ?_⟩
    by_contra hρS
    have h1 : dist ρ₀ z ≤ dist ρ z := hmin ρ ⟨hρ, hρS⟩
    have h2 := min_le_right R (dist ρ₀ z)
    linarith

/-- **Generic heights.** Off finitely many heights, a point `σ + iγ` has pairwise distinct
distances to the points of a finite set lying left of the line `Re s = σ`: equal distances to
`a ≠ b` pin `γ` down when `Im a ≠ Im b` and are impossible when `Im a = Im b`. -/
theorem exists_generic_height {F : Set ℂ} (hF : F.Finite) {σ : ℝ} (hσ : ∀ ρ ∈ F, ρ.re < σ)
    (γ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, |γ - γ₀| < ε ∧ ∀ a ∈ F, ∀ b ∈ F,
      dist a ((σ : ℂ) + γ * I) = dist b ((σ : ℂ) + γ * I) → a = b := by
  have hB : (image2 (fun a b : ℂ => ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) /
      (2 * (a.im - b.im))) F F).Finite := hF.image2 _ hF
  obtain ⟨γ, hγ, hγB⟩ := ((Ioo_infinite (show γ₀ - ε < γ₀ + ε by linarith)).sdiff hB).nonempty
  refine ⟨γ, abs_lt.mpr ⟨by linarith [hγ.1], by linarith [hγ.2]⟩, fun a ha b hb hab => ?_⟩
  have hsq : (σ - a.re) ^ 2 + (γ - a.im) ^ 2 = (σ - b.re) ^ 2 + (γ - b.im) ^ 2 := by
    have h1 := dist_sq_eq a ((σ : ℂ) + γ * I)
    have h2 := dist_sq_eq b ((σ : ℂ) + γ * I)
    rw [vertical_re, vertical_im] at h1 h2
    rw [← h1, ← h2, hab]
  by_cases him : a.im = b.im
  · have hre : (σ - a.re) ^ 2 = (σ - b.re) ^ 2 := by
      rw [him] at hsq
      linarith
    have := (sq_eq_sq₀ (sub_pos.mpr (hσ a ha)).le (sub_pos.mpr (hσ b hb)).le).mp hre
    exact Complex.ext (by linarith) him
  · exfalso
    apply hγB
    refine ⟨a, ha, b, hb, ?_⟩
    show ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) / (2 * (a.im - b.im)) = γ
    have h2 : 2 * (a.im - b.im) ≠ 0 := fun h => him (by linarith)
    rw [div_eq_iff h2]
    linear_combination hsq

/-- Geometric growth beats a fixed exponential rate: `c/d^{k+1} ≤ K/q^k` cannot hold for infinitely
many `k` when `0 < d < q` and `c > 0`. -/
theorem false_of_frequently_le {c d q K : ℝ} (hc : 0 < c) (hd : 0 < d) (hdq : d < q)
    (h : ∀ N : ℕ, ∃ k ≥ N, c / d ^ (k + 1) ≤ K / q ^ k) : False := by
  have hq : 0 < q := hd.trans hdq
  have ht : Tendsto (fun k : ℕ => (q / d) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hd).mpr hdq)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop (K * d / c))
  obtain ⟨k, hk, hle⟩ := h N
  have h1 := hN k hk
  rw [div_pow, div_lt_div_iff₀ hc (pow_pos hd _)] at h1
  rw [div_le_div_iff₀ (pow_pos hd _) (pow_pos hq _), pow_succ] at hle
  have e1 : K * (d ^ k * d) = K * d * d ^ k := by ring
  have e2 : q ^ k * c = c * q ^ k := by ring
  rw [e1] at hle
  rw [e2] at h1
  linarith

/-- In the half-plane where the Laplace integral converges, `Φ` is holomorphic, so it has no
simple pole there. -/
theorem re_le_of_simple_pole {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℂ, b < z.re → Φ z = ∫ u in Ioi (0 : ℝ), g u * cexp (-z * u)) {ρ c : ℂ}
    (hc : c ≠ 0) (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) :
    ρ.re ≤ b := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h, hh, hp⟩ := hp
  apply not_continuousAt_of_simple_pole hc hh.continuousAt hp
  have heq : (fun z : ℂ => ∫ u in Ioi (0 : ℝ), g u * (-(u : ℂ)) ^ 0 * cexp (-z * u)) =ᶠ[𝓝 ρ] Φ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlt] with z hz
    rw [hΦ z hz]
    simp only [pow_zero, mul_one]
  exact (hasDerivAt_laplaceTerm hg hgC 0 hlt).continuousAt.congr heq

/-! ## Landau's theorem on windows -/

/-- **Landau on windows**, normalized form: no poles at all in `Re s > θ`. -/
theorem eq_empty_of_window_bound_of_nonneg {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C₀ b : ℝ}
    (hgC : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (b * u)) {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℂ, b < z.re → Φ z = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
    {θ δ C : ℝ} (hθb : θ ≤ b) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hwin : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u))
    {Z : Set ℂ} (hZθ : ∀ ρ ∈ Z, θ < ρ.re)
    (hZfin : ∀ K : Set ℂ, IsCompact K → K ⊆ {s | θ < s.re} → (Z ∩ K).Finite)
    (hdiff : DifferentiableOn ℂ Φ ({s | θ < s.re} \ Z))
    (hpole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) :
    Z = ∅ := by
  have hG : AEStronglyMeasurable (fun u => (g u : ℂ)) (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg
  have hGC : ∀ u, 0 < u → ‖(g u : ℂ)‖ ≤ C₀ * Real.exp (b * u) := fun u hu => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu
  obtain ⟨σ, hσb, K, hK, hkey⟩ := exists_window_coeff_bound hg hgC hθb hδ hC hwin
  have hσθ : θ < σ := lt_of_le_of_lt hθb hσb
  -- coefficients of the Laplace transform are the Taylor coefficients of `Φ`
  have hcoef : ∀ (k : ℕ) (s : ℂ), s.re = σ →
      laplaceCoeff (fun u => (g u : ℂ)) k s =
        (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) := fun k s hs =>
    (taylorCoeff_eq_laplaceCoeff hG hGC hΦ k (by rw [hs]; exact hσb)).symm
  have hnorm : ∀ (k : ℕ) (s : ℂ), ‖(-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ)‖ =
      ‖iteratedDeriv k Φ s / (k.factorial : ℂ)‖ := fun k s => by
    rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  -- poles lie left of the line `Re s = σ`
  have hZσ : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => by
    obtain ⟨c, hc, -, hp⟩ := hpole ρ hρ
    exact lt_of_le_of_lt (re_le_of_simple_pole hG hGC hΦ hc hp) hσb
  -- `Φ` is holomorphic on discs of the half-plane away from the remaining poles
  have hdiffOn : ∀ (z : ℂ) (r : ℝ) (S : Set ℂ), r ≤ z.re - θ →
      (∀ s ∈ Z, dist s z < r → s ∈ S) → DifferentiableOn ℂ Φ (ball z r \ S) :=
    fun z r S hr hS =>
      hdiff.mono fun s hs => ⟨ball_subset_re_gt hr hs.1, fun hsZ => hs.2 (hS s hsZ hs.1)⟩
  have hpowle : ∀ {r : ℝ}, 0 < r → r ≤ σ - θ → ∀ k : ℕ, K / (σ - θ) ^ k ≤ K / r ^ k :=
    fun hr0 hr k => div_le_div_of_nonneg_left hK (pow_pos hr0 k) (pow_le_pow_left₀ hr0.le hr k)
  by_contra hne
  obtain ⟨ρ₁, hρ₁⟩ := Set.nonempty_iff_ne_empty.mpr hne
  by_cases hcase : ∃ ρ ∈ Z, ∃ q, σ - ρ.re < q ∧ ∀ ρ' ∈ Z, q ≤ dist ρ' (σ : ℂ)
  · -- some pole is horizontally closer than every pole is to `σ`: look from a generic height
    obtain ⟨ρ₀, hρ₀Z, q₀, hq₀, hq₀Z⟩ := hcase
    have hρ₀σ := hZσ ρ₀ hρ₀Z
    have hρ₀θ := hZθ ρ₀ hρ₀Z
    obtain ⟨q, hxq, hqθ, hqZ⟩ : ∃ q : ℝ, σ - ρ₀.re < q ∧ q < σ - θ ∧
        ∀ ρ' ∈ Z, q ≤ dist ρ' (σ : ℂ) :=
      ⟨min q₀ ((σ - ρ₀.re + (σ - θ)) / 2), lt_min hq₀ (by linarith),
        lt_of_le_of_lt (min_le_right _ _) (by linarith),
        fun ρ' h => (min_le_left _ _).trans (hq₀Z ρ' h)⟩
    obtain ⟨ε, hε0, hεx, hεθ⟩ : ∃ ε : ℝ, 0 < ε ∧ σ - ρ₀.re + ε < q ∧ q + ε < σ - θ := by
      have h1 := min_le_left (q - (σ - ρ₀.re)) (σ - θ - q)
      have h2 := min_le_right (q - (σ - ρ₀.re)) (σ - θ - q)
      have h3 : 0 < min (q - (σ - ρ₀.re)) (σ - θ - q) := lt_min (by linarith) (by linarith)
      exact ⟨min (q - (σ - ρ₀.re)) (σ - θ - q) / 2, by linarith, by linarith, by linarith⟩
    have hF₁ : (Z ∩ closedBall ((σ : ℂ) + ρ₀.im * I) (q + ε)).Finite :=
      hZfin _ (isCompact_closedBall _ _)
        (closedBall_subset_re_gt (by rw [vertical_re]; linarith))
    obtain ⟨γ, hγ, hgen⟩ := exists_generic_height hF₁ (fun ρ hρ => hZσ ρ hρ.1) ρ₀.im hε0
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (σ : ℂ) + γ * I := ⟨_, rfl⟩
    have hzre : z.re = σ := by rw [hz, vertical_re]
    have hzz₀ : dist z ((σ : ℂ) + ρ₀.im * I) < ε := by
      rw [Complex.dist_eq, show z - ((σ : ℂ) + ρ₀.im * I) = ((γ - ρ₀.im : ℝ) : ℂ) * I by
        rw [hz]; push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact hγ
    have hρ₀z₀ : dist ρ₀ ((σ : ℂ) + ρ₀.im * I) = σ - ρ₀.re := by
      rw [Complex.dist_eq, show ρ₀ - ((σ : ℂ) + ρ₀.im * I) = ((ρ₀.re - σ : ℝ) : ℂ) from
        Complex.ext (by simp) (by simp), Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      ring
    have hρ₀zq : dist ρ₀ z < q := by
      have h1 := dist_triangle ρ₀ ((σ : ℂ) + ρ₀.im * I) z
      rw [dist_comm ((σ : ℂ) + ρ₀.im * I) z] at h1
      linarith
    have hFsub : Z ∩ closedBall z q ⊆ Z ∩ closedBall ((σ : ℂ) + ρ₀.im * I) (q + ε) :=
      fun s hs => ⟨hs.1, mem_closedBall.mpr ((dist_triangle _ _ _).trans
        (add_le_add (mem_closedBall.mp hs.2) hzz₀.le))⟩
    have hF : (Z ∩ closedBall z q).Finite := hF₁.subset hFsub
    have hρ₀F : ρ₀ ∈ Z ∩ closedBall z q := ⟨hρ₀Z, mem_closedBall.mpr hρ₀zq.le⟩
    -- the nearest pole to `z` is unique
    obtain ⟨ρ, hρF, hρmin⟩ := Set.exists_min_image _ (fun s => dist s z) hF ⟨ρ₀, hρ₀F⟩
    have hρz : ρ ≠ z := fun h => by
      have := hZσ ρ hρF.1
      rw [h, hzre] at this
      exact lt_irrefl _ this
    have hd0 : 0 < dist ρ z := dist_pos.mpr hρz
    have hdq : dist ρ z < q := lt_of_le_of_lt (hρmin ρ₀ hρ₀F) hρ₀zq
    have hS : ∀ s ∈ Z ∩ closedBall z q, s ∉ ({ρ} : Set ℂ) → dist ρ z < dist s z :=
      fun s hs hsρ => lt_of_le_of_ne (hρmin s hs) (fun h => hsρ
        (hgen s (hFsub hs) ρ (hFsub hρF) (by rw [← hz]; exact h.symm)))
    obtain ⟨r, hdr, hrq, hgap⟩ := exists_radius_gap hF z hdq hS
    have hZr : ∀ s ∈ Z, dist s z < r → s ∈ ({ρ} : Set ℂ) := fun s hs hsd =>
      hgap s ⟨hs, mem_closedBall.mpr (hsd.le.trans hrq)⟩ hsd
    have hdz : DifferentiableOn ℂ Φ (ball z r \ {ρ}) :=
      hdiffOn z r {ρ} (by rw [hzre]; linarith) hZr
    obtain ⟨c, hc, -, hp⟩ := hpole ρ hρF.1
    obtain ⟨M, hM⟩ := exists_taylorCoeff_sub_pole_le hρz hdz hp (r' := (dist ρ z + r) / 2)
      (by linarith) (by linarith)
    -- no pole at all within distance `q` of `σ`
    have hdσ : DifferentiableOn ℂ Φ (ball (σ : ℂ) q) := by
      have := hdiffOn (σ : ℂ) q ∅ (by rw [Complex.ofReal_re]; linarith)
        (fun s hs hsd => absurd (hqZ s hs) (not_le.mpr hsd))
      exact this.mono fun s hs => ⟨hs, id⟩
    obtain ⟨M₀, hM₀⟩ := exists_taylorCoeff_le hdσ (r' := (dist ρ z + r) / 2) (by linarith)
      (by linarith)
    refine false_of_frequently_le (norm_pos_iff.mpr hc) hd0 (q := (dist ρ z + r) / 2)
      (K := K + M + M₀) (by linarith) (fun N => ?_)
    obtain ⟨k, hkN, hk⟩ := hkey N
    refine ⟨k, hkN, ?_⟩
    have h1 := hk γ
    rw [← hz] at h1
    have hA := hM k
    rw [← hcoef k z hzre] at hA
    have hB := hM₀ k
    rw [← hnorm, ← hcoef k (σ : ℂ) (Complex.ofReal_re σ)] at hB
    have e1 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / dist ρ z ^ (k + 1) := by
      rw [norm_div, norm_pow, ← Complex.dist_eq, dist_comm]
    have e2 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1)) (laplaceCoeff (fun u => (g u : ℂ)) k z)
    rw [norm_sub_rev] at e2
    have e3 := neg_abs_le (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ)).re
    have e4 := Complex.abs_re_le_norm (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ))
    have e5 := hpowle (r := (dist ρ z + r) / 2) (by linarith) (by linarith) k
    rw [add_div, add_div]
    linarith
  · -- otherwise the pole nearest to `σ` is real, with positive residue
    push Not at hcase
    have hρ₁σ := hZσ ρ₁ hρ₁
    have hρ₁θ := hZθ ρ₁ hρ₁
    obtain ⟨R, hR1, hRθ⟩ : ∃ R : ℝ, σ - ρ₁.re < R ∧ R < σ - θ :=
      ⟨(σ - ρ₁.re + (σ - θ)) / 2, by linarith, by linarith⟩
    have hσre : (σ : ℂ).re = σ := Complex.ofReal_re σ
    have hσim : (σ : ℂ).im = 0 := Complex.ofReal_im σ
    have hF : (Z ∩ closedBall (σ : ℂ) R).Finite :=
      hZfin _ (isCompact_closedBall _ _) (closedBall_subset_re_gt (by rw [hσre]; linarith))
    obtain ⟨ρ', hρ'Z, hρ'd⟩ := hcase ρ₁ hρ₁ R hR1
    have hρ'F : ρ' ∈ Z ∩ closedBall (σ : ℂ) R := ⟨hρ'Z, mem_closedBall.mpr hρ'd.le⟩
    obtain ⟨β, hβF, hβmin⟩ := Set.exists_min_image _ (fun s => dist s (σ : ℂ)) hF ⟨ρ', hρ'F⟩
    -- every nearby pole lies at least `dist β σ` to the left of the line
    have hleft : ∀ ρ ∈ Z ∩ closedBall (σ : ℂ) R, dist β (σ : ℂ) ≤ σ - ρ.re := fun ρ hρ => by
      by_contra hlt
      push Not at hlt
      obtain ⟨ρ'', hρ''Z, hρ''d⟩ := hcase ρ hρ.1 _ hlt
      have hmem : ρ'' ∈ Z ∩ closedBall (σ : ℂ) R :=
        ⟨hρ''Z, mem_closedBall.mpr (hρ''d.le.trans (mem_closedBall.mp hβF.2))⟩
      exact absurd (hβmin ρ'' hmem) (not_le.mpr hρ''d)
    -- so the nearest poles are real
    have hreal : ∀ ρ ∈ Z ∩ closedBall (σ : ℂ) R, dist ρ (σ : ℂ) = dist β (σ : ℂ) →
        ρ = ((σ - dist β (σ : ℂ) : ℝ) : ℂ) := fun ρ hρ hd => by
      have h1 := hleft ρ hρ
      have h2 := sub_re_le_dist ρ (σ : ℂ)
      have h3 := dist_sq_eq ρ (σ : ℂ)
      rw [hσre] at h2
      rw [hσre, hσim, hd] at h3
      have h4 : dist β (σ : ℂ) = σ - ρ.re := le_antisymm h1 (by rw [← hd]; exact h2)
      have h5 : (0 - ρ.im) ^ 2 = 0 := by
        rw [h4] at h3
        linarith
      have h6 : ρ.im = 0 := by
        have := (pow_eq_zero_iff two_ne_zero).mp h5
        linarith
      apply Complex.ext
      · rw [Complex.ofReal_re]
        linarith
      · rw [Complex.ofReal_im]
        exact h6
    obtain ⟨d₀, hd₀⟩ : ∃ d : ℝ, dist β (σ : ℂ) = d := ⟨_, rfl⟩
    have hβ : β = ((σ - d₀ : ℝ) : ℂ) := by
      have := hreal β hβF rfl
      rwa [hd₀] at this
    have hd₀pos : 0 < d₀ := by
      have := hZσ β hβF.1
      rw [hβ, Complex.ofReal_re] at this
      linarith
    have hd₀R : d₀ < R := by
      rw [← hd₀]
      exact lt_of_le_of_lt (hβmin ρ' hρ'F) hρ'd
    have hS : ∀ s ∈ Z ∩ closedBall (σ : ℂ) R, s ∉ ({β} : Set ℂ) → d₀ < dist s (σ : ℂ) :=
      fun s hs hsβ => by
        rw [← hd₀]
        refine lt_of_le_of_ne (hβmin s hs) (fun h => hsβ ?_)
        have := hreal s hs h.symm
        rw [hd₀, ← hβ] at this
        exact this
    obtain ⟨r, hdr, hrR, hgap⟩ := exists_radius_gap hF (σ : ℂ) hd₀R hS
    have hZr : ∀ s ∈ Z, dist s (σ : ℂ) < r → s ∈ ({β} : Set ℂ) := fun s hs hsd =>
      hgap s ⟨hs, mem_closedBall.mpr (hsd.le.trans hrR)⟩ hsd
    have hdβ : DifferentiableOn ℂ Φ (ball (σ : ℂ) r \ {β}) :=
      hdiffOn (σ : ℂ) r {β} (by rw [hσre]; linarith) hZr
    have hβσ : β ≠ (σ : ℂ) := fun h => by
      have := hZσ β hβF.1
      rw [h, hσre] at this
      exact lt_irrefl _ this
    obtain ⟨c, hc, hcpos, hp⟩ := hpole β hβF.1
    obtain ⟨hcre, -⟩ := hcpos (by rw [hβ, Complex.ofReal_im])
    obtain ⟨M, hM⟩ := exists_taylorCoeff_sub_pole_le hβσ hdβ hp (r' := (d₀ + r) / 2)
      (by linarith) (by linarith)
    have hX : ∀ k : ℕ, (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / d₀ ^ (k + 1) := fun k => by
      rw [hβ, show (σ : ℂ) - ((σ - d₀ : ℝ) : ℂ) = ((d₀ : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_pow, Complex.div_ofReal_re]
    refine false_of_frequently_le hcre hd₀pos (q := (d₀ + r) / 2) (K := K + M) (by linarith)
      (fun N => ?_)
    obtain ⟨k, hkN, hk⟩ := hkey N
    refine ⟨k, hkN, ?_⟩
    have h1 : (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ)).re ≤ K / (σ - θ) ^ k :=
      le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hk 0)
    have hA := hM k
    rw [← hcoef k (σ : ℂ) hσre] at hA
    have e1 := Complex.abs_re_le_norm
      (laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1))
    rw [Complex.sub_re, hX k] at e1
    have e2 := neg_abs_le
      ((laplaceCoeff (fun u => (g u : ℂ)) k (σ : ℂ)).re - c.re / d₀ ^ (k + 1))
    have e4 := hpowle (r := (d₀ + r) / 2) (by linarith) (by linarith) k
    rw [add_div]
    linarith

/-- **Landau's theorem on windows.** Let `g` be real, measurable, with `|g u| ≤ C₀ e^{bu}`, and let
`Φ` agree with its Laplace transform on `Re s > b`. Suppose `g u ≤ C e^{θu}` on windows
`[U, (1+δ)U]` for arbitrarily large `U`, and that on `Re s > θ` the function `Φ` is holomorphic off
a locally finite set `Z` of simple poles whose residues are positive at real poles. Then `Z` has no
point in `Re s > θ`. -/
theorem re_le_of_window_bound {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C₀ b : ℝ}
    (hgC : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (b * u)) {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℂ, b < z.re → Φ z = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
    {θ δ C : ℝ} (hδ : 0 < δ)
    (hwin : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u))
    {Z : Set ℂ} (hZfin : ∀ K : Set ℂ, IsCompact K → K ⊆ {s | θ < s.re} → (Z ∩ K).Finite)
    (hdiff : DifferentiableOn ℂ Φ ({s | θ < s.re} \ Z))
    (hpole : ∀ ρ ∈ Z, θ < ρ.re → ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) :
    ∀ ρ ∈ Z, ρ.re ≤ θ := by
  have hC₀ := nonneg_of_growth hgC
  have hgC' : ∀ u, 0 < u → |g u| ≤ C₀ * Real.exp (max b θ * u) := fun u hu =>
    (hgC u hu).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.le)) hC₀)
  have hΦ' : ∀ z : ℂ, max b θ < z.re →
      Φ z = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u) :=
    fun z hz => hΦ z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hwin' : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      g u ≤ max C 0 * Real.exp (θ * u) := fun U₀ => by
    obtain ⟨U, hU, h⟩ := hwin U₀
    exact ⟨U, hU, fun u hu =>
      (h u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  have hempty := eq_empty_of_window_bound_of_nonneg hg hgC' hΦ' (le_max_right b θ) hδ
    (le_max_right C 0) hwin' (Z := Z ∩ {s | θ < s.re}) (fun ρ hρ => hρ.2)
    (fun K hK hKθ => (hZfin K hK hKθ).subset fun s hs => ⟨hs.1.1, hs.2⟩)
    (hdiff.mono fun s hs => ⟨hs.1, fun hsZ => hs.2 ⟨hsZ, hs.1⟩⟩)
    (fun ρ hρ => hpole ρ hρ.1 hρ.2)
  intro ρ hρ
  by_contra hlt
  push Not at hlt
  have hmem : ρ ∈ Z ∩ {s | θ < s.re} := ⟨hρ, hlt⟩
  rw [hempty] at hmem
  exact hmem

end

end WindowedLandauTheory
