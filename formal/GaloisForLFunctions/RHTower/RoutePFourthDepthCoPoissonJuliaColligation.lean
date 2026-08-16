import GaloisForLFunctions.RHTower.RouteEPCubicSourceNormalizationJuliaDefectCompletion
import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceDilation
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

open Complex MeasureTheory Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Route P's fourth-depth physical contraction as one eighth of Burnol's unitary fourfold
dilation on the even `L²` carrier. -/
def routePPrimitiveFourthDepthCoPoissonContraction :
    evenSubspace →L[ℂ] evenSubspace :=
  (routeEPCubicFourthDepthNormalizedContraction : ℂ) •
    evenDilationCLM 4 (by norm_num)

/-- Defect operator of the scaled unitary fourth-depth contraction. -/
def routePPrimitiveFourthDepthCoPoissonJuliaDefect :
    evenSubspace →L[ℂ] evenSubspace :=
  (routeEPCubicFourthDepthJuliaDefect : ℂ) • 1

theorem norm_routePPrimitiveFourthDepthCoPoissonContraction
    (f : evenSubspace) :
    ‖routePPrimitiveFourthDepthCoPoissonContraction f‖ =
      routeEPCubicFourthDepthNormalizedContraction * ‖f‖ := by
  rw [routePPrimitiveFourthDepthCoPoissonContraction,
    smul_apply, norm_smul,
    norm_evenDilationCLM_apply]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num [routeEPCubicFourthDepthNormalizedContraction])]

theorem norm_routePPrimitiveFourthDepthCoPoissonJuliaDefect
    (f : evenSubspace) :
    ‖routePPrimitiveFourthDepthCoPoissonJuliaDefect f‖ =
      routeEPCubicFourthDepthJuliaDefect * ‖f‖ := by
  have hd0 : 0 ≤ routeEPCubicFourthDepthJuliaDefect := Real.sqrt_nonneg _
  rw [routePPrimitiveFourthDepthCoPoissonJuliaDefect,
    smul_apply, one_apply_eq_self, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hd0]

/-- The abstract scaled unitary is literally P-G104's quarter-amplitude fourfold dilation almost
everywhere. -/
theorem routePPrimitiveFourthDepthCoPoissonContraction_ae (f : evenSubspace) :
    (((routePPrimitiveFourthDepthCoPoissonContraction f : evenSubspace) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume]
    fun x : ℝ => routePPrimitiveFourthDepthPhysicalDilation
      ((((f : evenSubspace) : SoninL2) : ℝ → ℂ)) x := by
  have hU := dilation_ae 4 (by norm_num : (0 : ℝ) < 4)
    (((f : evenSubspace) : SoninL2))
  have hsmul := MeasureTheory.Lp.coeFn_smul
    (routeEPCubicFourthDepthNormalizedContraction : ℂ)
    (dilation 4 (by norm_num : (0 : ℝ) < 4) (((f : evenSubspace) : SoninL2)))
  change (((routeEPCubicFourthDepthNormalizedContraction : ℂ) •
      dilation 4 (by norm_num : (0 : ℝ) < 4) (((f : evenSubspace) : SoninL2)) :
        SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [hU, hsmul] with x hxU hxsmul
  rw [hxsmul]
  change (routeEPCubicFourthDepthNormalizedContraction : ℂ) *
      (((dilation 4 (by norm_num : (0 : ℝ) < 4)
        (((f : evenSubspace) : SoninL2))) : SoninL2) : ℝ → ℂ) x = _
  rw [hxU]
  unfold routePPrimitiveFourthDepthPhysicalDilation
    routeEPCubicFourthDepthNormalizedContraction
  norm_num
  ring

/-- The contracted child is an actual co-Poisson source at the aperture divided by four. -/
theorem routePPrimitiveFourthDepthCoPoissonContraction_mem_sourceSpace
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    routePPrimitiveFourthDepthCoPoissonContraction f ∈
      burnolCoPoissonSourceSpace ((4 : ℝ)⁻¹ * b) := by
  rw [routePPrimitiveFourthDepthCoPoissonContraction,
    smul_apply]
  exact Submodule.smul_mem _ _
    (evenDilation_mem_coPoissonSourceSpace hb (by norm_num : (1 : ℝ) ≤ 4) hf)

/-- The Julia environment is the original co-Poisson source coordinate, scaled by its canonical
defect. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaDefect_mem_sourceSpace
    {b : ℝ} {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    routePPrimitiveFourthDepthCoPoissonJuliaDefect f ∈
      burnolCoPoissonSourceSpace b := by
  rw [routePPrimitiveFourthDepthCoPoissonJuliaDefect,
    smul_apply, one_apply_eq_self]
  exact Submodule.smul_mem _ _ hf

/-- Exact source-axis Julia conservation law on Burnol's actual even `L²` carrier. -/
theorem routePPrimitiveFourthDepthCoPoisson_JuliaEnergy
    (f : evenSubspace) :
    ‖routePPrimitiveFourthDepthCoPoissonContraction f‖ ^ 2 +
        ‖routePPrimitiveFourthDepthCoPoissonJuliaDefect f‖ ^ 2 =
      ‖f‖ ^ 2 := by
  rw [norm_routePPrimitiveFourthDepthCoPoissonContraction,
    norm_routePPrimitiveFourthDepthCoPoissonJuliaDefect]
  have h := routeEPCubicFourthDepthJulia_pythagoras
  nlinarith [sq_nonneg ‖f‖]

/-- The parent--environment Hilbert pairing has P-G103's exact cross coefficient. -/
theorem inner_routePPrimitiveFourthDepthCoPoissonJuliaDefect
    (f : evenSubspace) :
    ⟪f, routePPrimitiveFourthDepthCoPoissonJuliaDefect f⟫_ℂ =
      (routeEPCubicFourthDepthJuliaDefect : ℂ) * (‖f‖ : ℂ) ^ 2 := by
  rw [routePPrimitiveFourthDepthCoPoissonJuliaDefect,
    smul_apply, one_apply_eq_self,
    inner_smul_right, inner_self_eq_norm_sq_to_K]
  rfl

theorem inner_routePPrimitiveFourthDepthCoPoissonJuliaDefect_eq_quantizedPolarCross
    (f : evenSubspace) :
    ⟪f, routePPrimitiveFourthDepthCoPoissonJuliaDefect f⟫_ℂ =
      (routeEPCubicFourthDepthQuantizedPolarCross (‖f‖ ^ 2) : ℂ) := by
  rw [inner_routePPrimitiveFourthDepthCoPoissonJuliaDefect,
    routeEPCubicFourthDepthQuantizedPolarCross,
    routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  norm_cast

/-- Full two-channel Julia colligation of the scaled Burnol fourfold dilation. -/
def routePPrimitiveFourthDepthCoPoissonJuliaTransportV
    (v : evenSubspace × evenSubspace) : evenSubspace × evenSubspace :=
  let c : ℂ := routeEPCubicFourthDepthNormalizedContraction
  let d : ℂ := routeEPCubicFourthDepthJuliaDefect
  (evenDilationCLM 4 (by norm_num) (c • v.1 - d • v.2),
    d • v.1 + c • v.2)

theorem routePPrimitiveFourthDepthCoPoissonJuliaTransportV_sourceAxis
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonJuliaTransportV (f, 0) =
      (routePPrimitiveFourthDepthCoPoissonContraction f,
        routePPrimitiveFourthDepthCoPoissonJuliaDefect f) := by
  apply Prod.ext
  · simp only [routePPrimitiveFourthDepthCoPoissonJuliaTransportV, smul_zero, sub_zero,
      routePPrimitiveFourthDepthCoPoissonContraction, smul_apply]
    exact map_smul (evenDilationCLM 4 (by norm_num)) _ f
  · simp [routePPrimitiveFourthDepthCoPoissonJuliaTransportV,
      routePPrimitiveFourthDepthCoPoissonJuliaDefect]

theorem routePPrimitiveFourthDepthCoPoissonJuliaTransportV_normSq
    (v : evenSubspace × evenSubspace) :
    ‖(routePPrimitiveFourthDepthCoPoissonJuliaTransportV v).1‖ ^ 2 +
        ‖(routePPrimitiveFourthDepthCoPoissonJuliaTransportV v).2‖ ^ 2 =
      ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
  have hc0 : 0 ≤ routeEPCubicFourthDepthNormalizedContraction := by
    norm_num [routeEPCubicFourthDepthNormalizedContraction]
  have hd0 : 0 ≤ routeEPCubicFourthDepthJuliaDefect := Real.sqrt_nonneg _
  have hcross :
      RCLike.re ⟪(routeEPCubicFourthDepthNormalizedContraction : ℂ) • v.1,
          (routeEPCubicFourthDepthJuliaDefect : ℂ) • v.2⟫_ℂ =
      RCLike.re ⟪(routeEPCubicFourthDepthJuliaDefect : ℂ) • v.1,
          (routeEPCubicFourthDepthNormalizedContraction : ℂ) • v.2⟫_ℂ := by
    change RCLike.re ⟪(routeEPCubicFourthDepthNormalizedContraction : ℂ) •
        (v.1 : SoninL2), (routeEPCubicFourthDepthJuliaDefect : ℂ) •
        (v.2 : SoninL2)⟫_ℂ =
      RCLike.re ⟪(routeEPCubicFourthDepthJuliaDefect : ℂ) •
        (v.1 : SoninL2), (routeEPCubicFourthDepthNormalizedContraction : ℂ) •
        (v.2 : SoninL2)⟫_ℂ
    have hcd :
        ⟪(routeEPCubicFourthDepthNormalizedContraction : ℂ) • (v.1 : SoninL2),
            (routeEPCubicFourthDepthJuliaDefect : ℂ) • (v.2 : SoninL2)⟫_ℂ =
          (routeEPCubicFourthDepthNormalizedContraction : ℂ) *
            (routeEPCubicFourthDepthJuliaDefect : ℂ) *
              ⟪(v.1 : SoninL2), (v.2 : SoninL2)⟫_ℂ := by
      calc
        _ = (routeEPCubicFourthDepthJuliaDefect : ℂ) *
            ⟪(routeEPCubicFourthDepthNormalizedContraction : ℂ) •
              (v.1 : SoninL2), (v.2 : SoninL2)⟫_ℂ := inner_smul_right _ _ _
        _ = _ := by rw [inner_smul_left, Complex.conj_ofReal]; ring
    have hdc :
        ⟪(routeEPCubicFourthDepthJuliaDefect : ℂ) • (v.1 : SoninL2),
            (routeEPCubicFourthDepthNormalizedContraction : ℂ) • (v.2 : SoninL2)⟫_ℂ =
          (routeEPCubicFourthDepthJuliaDefect : ℂ) *
            (routeEPCubicFourthDepthNormalizedContraction : ℂ) *
              ⟪(v.1 : SoninL2), (v.2 : SoninL2)⟫_ℂ := by
      calc
        _ = (routeEPCubicFourthDepthNormalizedContraction : ℂ) *
            ⟪(routeEPCubicFourthDepthJuliaDefect : ℂ) •
              (v.1 : SoninL2), (v.2 : SoninL2)⟫_ℂ := inner_smul_right _ _ _
        _ = _ := by rw [inner_smul_left, Complex.conj_ofReal]; ring
    rw [hcd, hdc]
    apply congrArg RCLike.re
    ring
  rw [routePPrimitiveFourthDepthCoPoissonJuliaTransportV]
  dsimp only
  rw [norm_evenDilationCLM_apply]
  rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ)]
  rw [hcross]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc0, abs_of_nonneg hd0]
  have h := routeEPCubicFourthDepthJulia_pythagoras
  ring_nf at h ⊢
  nlinarith

/-- The full Julia colligation respects the two-level co-Poisson aperture ladder. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaTransportV_mem_sourceSpaces
    {b : ℝ} (hb : 0 < b) {v : evenSubspace × evenSubspace}
    (hv1 : v.1 ∈ burnolCoPoissonSourceSpace b)
    (hv2 : v.2 ∈ burnolCoPoissonSourceSpace b) :
    (routePPrimitiveFourthDepthCoPoissonJuliaTransportV v).1 ∈
        burnolCoPoissonSourceSpace ((4 : ℝ)⁻¹ * b) ∧
      (routePPrimitiveFourthDepthCoPoissonJuliaTransportV v).2 ∈
        burnolCoPoissonSourceSpace b := by
  rw [routePPrimitiveFourthDepthCoPoissonJuliaTransportV]
  dsimp only
  constructor
  · apply evenDilation_mem_coPoissonSourceSpace hb (by norm_num : (1 : ℝ) ≤ 4)
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hv1) (Submodule.smul_mem _ _ hv2)
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv1) (Submodule.smul_mem _ _ hv2)

/-- **P-G105 source-pair capstone.** Every genuine co-Poisson source produces the exact Route-P
fourth-depth child and canonical defect channel, both remaining inside the co-Poisson aperture
ladder, with conserved energy and P-G103's rigid parent--defect pairing. -/
theorem routePPrimitiveFourthDepthCoPoisson_JuliaSourcePair
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    routePPrimitiveFourthDepthCoPoissonContraction f ∈
        burnolCoPoissonSourceSpace ((4 : ℝ)⁻¹ * b) ∧
      routePPrimitiveFourthDepthCoPoissonJuliaDefect f ∈
        burnolCoPoissonSourceSpace b ∧
      ‖routePPrimitiveFourthDepthCoPoissonContraction f‖ ^ 2 +
          ‖routePPrimitiveFourthDepthCoPoissonJuliaDefect f‖ ^ 2 = ‖f‖ ^ 2 ∧
      ⟪f, routePPrimitiveFourthDepthCoPoissonJuliaDefect f⟫_ℂ =
        (routeEPCubicFourthDepthQuantizedPolarCross (‖f‖ ^ 2) : ℂ) := by
  exact ⟨routePPrimitiveFourthDepthCoPoissonContraction_mem_sourceSpace hb hf,
    routePPrimitiveFourthDepthCoPoissonJuliaDefect_mem_sourceSpace hf,
    routePPrimitiveFourthDepthCoPoisson_JuliaEnergy f,
    inner_routePPrimitiveFourthDepthCoPoissonJuliaDefect_eq_quantizedPolarCross f⟩

end

end RHTower
