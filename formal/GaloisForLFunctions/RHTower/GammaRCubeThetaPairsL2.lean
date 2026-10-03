import GaloisForLFunctions.RHTower.GammaRCubeVoronoiL2
import GaloisForLFunctions.RHTower.GammaRealPowerKernel

/-!
# Theta pairs of the `Γℝ³` Voronoi transform

Let `K₂` be the inverse Mellin transform of `Γℝ(s)³` (the triple multiplicative convolution of
`2e^{-πx²}`). For every `y > 0`, the scaled kernel `K₂(y·)` lies in `L²((0,∞))`, and the unitary
Voronoi involution of `ζ(s)³`'s functional equation maps it to `y⁻¹ K₂(·/y)`
(`gammaRCubeVoronoi_cubeKernel`). In Mellin terms this is
`G(s) · y^{-(1-s)} Γℝ(1-s)³ = y^{s-1} Γℝ(s)³` with `G(s) = Γℝ(s)³/Γℝ(1-s)³`, on the unitary line.

These are the test functions whose theta relation `Σ e_n K₂(n y) = y⁻¹ Σ e_n K₂(n/y)` turns a
self-dual relation on the integer nodes into a Dirichlet series with the functional equation of
`ζ(s)³`.
-/

open MeasureTheory Set Filter Complex
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Absolute Mellin convergence at `1/2` makes the half-density pullback integrable. -/
theorem integrable_halfDensityPullback_of_mellinConvergent {g : ℝ → ℂ}
    (hg : MellinConvergent g ((1 / 2 : ℝ) : ℂ)) : Integrable (halfDensityPullback g) := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-x)) univ x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    rw [mul_neg_one] at h1
    exact h1.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ h
    simpa using Real.exp_injective h
  have himage : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
    rw [Set.image_univ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩; exact Real.exp_pos _
    · intro hx; exact ⟨-Real.log x, by simp [Real.exp_log hx]⟩
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun t : ℝ => (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) • g t)).mp (by rw [himage]; exact hg)
  rw [integrableOn_univ] at h
  have h2 := h.comp_neg
  refine h2.congr (Eventually.of_forall fun u => ?_)
  simp only [halfDensityPullback, neg_neg, smul_eq_mul]
  have hpos : 0 < Real.exp u := Real.exp_pos u
  rw [abs_neg, abs_of_pos hpos]
  have hcp : ((Real.exp u : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) = ((Real.exp u)⁻¹ * Real.sqrt (Real.exp u) : ℝ) := by
    rw [show (((1 / 2 : ℝ) : ℂ) - 1) = (((-1 / 2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hpos]
    norm_num
  rw [hcp, Complex.real_smul]
  push_cast
  field_simp

/-- `x ↦ K_d(y x)` lies in `L²((0,∞))`. -/
theorem memLp_gammaRPowKernel_scaled (d : ℕ) {y : ℝ} (hy : 0 < y) :
    MemLp (fun x : ℝ => gammaRPowKernel d (y * x)) 2 (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (fun x : ℝ => gammaRPowKernel d (y * x)) (Ioi 0) :=
    (continuousOn_gammaRPowKernel d).comp (continuousOn_const.mul continuousOn_id)
      (fun x hx => mul_pos hy hx)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => gammaRPowKernel d (y * x))
      (volume.restrict (Ioi 0)) := hcont.aestronglyMeasurable measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  obtain ⟨C1, hC1⟩ := exists_norm_gammaRPowKernel_le d (c := 1 / 4) (by norm_num)
  obtain ⟨C2, hC2⟩ := exists_norm_gammaRPowKernel_le d (c := 1) one_pos
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  change IntegrableOn (fun x : ℝ => ‖gammaRPowKernel d (y * x)‖ ^ 2) (Ioi 0)
  rw [hsplit]
  have hsq : ∀ x : ℝ, 0 < x → ∀ (C c : ℝ), (∀ z : ℝ, 0 < z → ‖gammaRPowKernel d z‖ ≤ C * z ^ (-c)) →
      ‖gammaRPowKernel d (y * x)‖ ^ 2 ≤ C ^ 2 * y ^ (-2 * c) * x ^ (-2 * c) := by
    intro x hx C c hC
    have h := hC (y * x) (mul_pos hy hx)
    have h0 := norm_nonneg (gammaRPowKernel d (y * x))
    have hp : 0 ≤ C * (y * x) ^ (-c) := le_trans h0 h
    calc ‖gammaRPowKernel d (y * x)‖ ^ 2 ≤ (C * (y * x) ^ (-c)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = C ^ 2 * y ^ (-2 * c) * x ^ (-2 * c) := by
        have e : ((y * x) ^ (-c)) ^ 2 = y ^ (-2 * c) * x ^ (-2 * c) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_pos hy hx).le, Real.mul_rpow hy.le hx.le]
          push_cast; ring_nf
        rw [mul_pow, e]; ring
  refine IntegrableOn.union ?_ ?_
  · have hb : IntegrableOn (fun x : ℝ => C1 ^ 2 * y ^ (-2 * (1 / 4 : ℝ)) * x ^ (-2 * (1 / 4 : ℝ)))
        (Ioc 0 1) := by
      have h0 : IntegrableOn (fun x : ℝ => x ^ (-2 * (1 / 4 : ℝ))) (Ioc 0 1) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by norm_num)
      exact Integrable.const_mul h0 _
    refine hb.mono' ((hcont.mono Ioc_subset_Ioi_self).norm.pow 2 |>.aestronglyMeasurable
      measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq x hx.1 C1 (1 / 4) hC1
  · have hb : IntegrableOn (fun x : ℝ => C2 ^ 2 * y ^ (-2 * (1 : ℝ)) * x ^ (-2 * (1 : ℝ))) (Ioi 1) := by
      have h0 : IntegrableOn (fun x : ℝ => x ^ (-2 * (1 : ℝ))) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
      exact Integrable.const_mul h0 _
    refine hb.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).norm.pow 2 |>.aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq x (lt_trans one_pos hx) C2 1 hC2

/-- The `L²` class of `x ↦ K₂(y x)`, where `K₂` is the inverse Mellin transform of `Γℝ³`. -/
def cubeKernelL2 {y : ℝ} (hy : 0 < y) : HalfLineL2 :=
  (memLp_gammaRPowKernel_scaled 2 hy).toLp _

/-- The `L²` class of `x ↦ y⁻¹ K₂(x / y)`. -/
def cubeKernelDualL2 {y : ℝ} (hy : 0 < y) : HalfLineL2 :=
  ((memLp_gammaRPowKernel_scaled 2 (inv_pos.mpr hy)).const_mul ((y⁻¹ : ℝ) : ℂ)).toLp _

private theorem mellin_scaled_kernel {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => gammaRPowKernel 2 (y * x)) s = (y : ℂ) ^ (-s) * Gammaℝ s ^ 3 := by
  rw [mellin_comp_mul_left _ _ hy, (hasMellin_gammaRPowKernel 2 hs).2, smul_eq_mul]

private theorem mellinConvergent_scaled_kernel {y : ℝ} (hy : 0 < y) :
    MellinConvergent (fun x : ℝ => gammaRPowKernel 2 (y * x)) ((1 / 2 : ℝ) : ℂ) :=
  (MellinConvergent.comp_mul_left hy).mpr
    (hasMellin_gammaRPowKernel 2 (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)).1

private theorem mellin_cubeKernelL2 {y : ℝ} (hy : 0 < y) :
    (halfLineMellinUnitary (cubeKernelL2 hy) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (y : ℂ) ^ (-(1 / 2 - 2 * Real.pi * ξ * I)) *
        Gammaℝ (1 / 2 - 2 * Real.pi * ξ * I) ^ 3 := by
  have h := halfLineMellinUnitary_ae_eq_mellin (cubeKernelL2 hy)
    (fun x : ℝ => gammaRPowKernel 2 (y * x))
    (MemLp.coeFn_toLp _)
    (integrable_halfDensityPullback_of_mellinConvergent (mellinConvergent_scaled_kernel hy))
  filter_upwards [h] with ξ hξ
  rw [hξ, mellin_scaled_kernel hy (by simp)]

private theorem mellin_cubeKernelDualL2 {y : ℝ} (hy : 0 < y) :
    (halfLineMellinUnitary (cubeKernelDualL2 hy) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((y⁻¹ : ℝ) : ℂ) * (((y⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 - 2 * Real.pi * ξ * I)) *
        Gammaℝ (1 / 2 - 2 * Real.pi * ξ * I) ^ 3) := by
  have hconv : MellinConvergent (fun x : ℝ => ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel 2 (y⁻¹ * x))
      ((1 / 2 : ℝ) : ℂ) := by
    have := (mellinConvergent_scaled_kernel (inv_pos.mpr hy)).const_smul ((y⁻¹ : ℝ) : ℂ)
    simpa [smul_eq_mul] using this
  have h := halfLineMellinUnitary_ae_eq_mellin (cubeKernelDualL2 hy)
    (fun x : ℝ => ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel 2 (y⁻¹ * x))
    (MemLp.coeFn_toLp _)
    (integrable_halfDensityPullback_of_mellinConvergent hconv)
  filter_upwards [h] with ξ hξ
  have hm := mellin_const_smul (fun x : ℝ => gammaRPowKernel 2 (y⁻¹ * x))
    (1 / 2 - 2 * Real.pi * ξ * I) ((y⁻¹ : ℝ) : ℂ)
  simp only [smul_eq_mul] at hm
  rw [hξ, hm, mellin_scaled_kernel (inv_pos.mpr hy) (by simp)]

/-- **Theta pairs.** The `Γℝ³` Voronoi transform maps `K₂(y·)` to `y⁻¹ K₂(·/y)`. -/
theorem gammaRCubeVoronoi_cubeKernel {y : ℝ} (hy : 0 < y) :
    gammaRCubeVoronoi (cubeKernelL2 hy) = cubeKernelDualL2 hy := by
  apply halfLineMellinUnitary.injective
  rw [gammaRCubeVoronoi, mellin_voronoiL2]
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have h1 := continuousUnimodularMulAux_ae gammaRCubeSymbol continuous_gammaRCubeSymbol norm_gammaRCubeSymbol
    (l2Reflection (halfLineMellinUnitary (cubeKernelL2 hy)))
  have h2 := l2Reflection_ae' (halfLineMellinUnitary (cubeKernelL2 hy))
  have h3 := (mellin_cubeKernelL2 hy).comp_tendsto hneg.tendsto_ae
  have h4 := mellin_cubeKernelDualL2 hy
  filter_upwards [h1, h2, h3, h4] with ξ hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx4]
  simp only [Function.comp] at hx3
  rw [hx3]
  have hb : (1 : ℂ) / 2 - 2 * Real.pi * ((-ξ : ℝ) : ℂ) * I = 1 / 2 + 2 * Real.pi * ξ * I := by
    push_cast; ring
  rw [hb]
  unfold gammaRCubeSymbol
  have hB := pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (s := 1 / 2 + 2 * Real.pi * ξ * I) (by simp))
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hyarg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ hyarg, ← Complex.cpow_neg, neg_neg]
  have hcp : (y : ℂ) ^ (-(1 / 2 + 2 * Real.pi * ξ * I)) =
      (y : ℂ)⁻¹ * (y : ℂ) ^ (1 / 2 - 2 * Real.pi * ξ * I) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hy0]
    congr 1; ring
  rw [hcp]
  calc _ = Gammaℝ (1 / 2 - 2 * Real.pi * ξ * I) ^ 3 *
        ((y : ℂ)⁻¹ * (y : ℂ) ^ (1 / 2 - 2 * Real.pi * ξ * I)) *
        (Gammaℝ (1 / 2 + 2 * Real.pi * ξ * I) ^ 3 / Gammaℝ (1 / 2 + 2 * Real.pi * ξ * I) ^ 3) := by
          ring
    _ = _ := by rw [div_self hB]; ring

end RHTower
