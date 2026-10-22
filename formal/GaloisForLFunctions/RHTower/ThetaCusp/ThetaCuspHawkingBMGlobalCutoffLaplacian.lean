import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalPlanarEquation
import GaloisForLFunctions.HTGeometry.PlanarSobolevLaplacianGain

/-!
The full localization commutator is derived from the scalar distribution equation, without scalarizing the completed frame gradients.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- The actual planar L² vector obtained by localizing the globally modular lift. -/
def PlanarChartTest.localVector (g : PlanarChartTest) (u : Space) : Lp ℂ 2 (volume : Measure ℂ) :=
  (g.localValue_memLp u).toLp (g.localValue u)

/-- The distribution of the actual lifted and localized scalar vector. -/
def PlanarChartTest.localDistribution (g : PlanarChartTest) (u : Space) : 𝓢'(ℂ,ℂ) :=
  g.localVector u

/-- A localized distribution pairs with the original constructed chart lift. -/
theorem PlanarChartTest.localDistribution_apply (g : PlanarChartTest) (u : Space) (ψ : 𝓢(ℂ,ℂ)) :
    g.localDistribution u ψ = ∫ z : ℂ, ψ z*g.localValue u z := by
  rw [PlanarChartTest.localDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(g.localValue_memLp u).coeFn_toLp] with z hz
  change g.localVector u z = g.localValue u z at hz
  rw [hz]
  rfl

private theorem lift_local_pair_integrable (g : PlanarChartTest) (u : Space) (ψ : 𝓢(ℂ,ℂ)) :
    Integrable (fun z : ℂ => ψ z*g.localValue u z) :=
  (ψ.memLp 2).integrable_mul (g.localValue_memLp u)

private theorem lifted_product_derivative (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field z =
      (g.derivative v).field z*ψ z+g.field z*(∂_{v} ψ) z := by
  change fderiv ℝ (fun w => ψ w*g.field w) z v = _
  rw [fderiv_fun_mul ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,PlanarChartTest.derivative]
  ring

private theorem lifted_product_second (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).derivative v).field z =
      ((g.derivative v).derivative v).field z*ψ z +
      2*(g.derivative v).field z*(∂_{v} ψ) z + g.field z*(∂_{v} (∂_{v} ψ)) z := by
  have he : ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field =
      (fun w => (g.derivative v).field w*ψ w+g.field w*(∂_{v} ψ) w) :=
    funext (lifted_product_derivative g ψ v)
  change fderiv ℝ ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field z v = _
  rw [he]
  have hg := (g.smooth.differentiable (by simp)).differentiableAt (x := z)
  have hgd := ((g.derivative v).smooth.differentiable (by simp)).differentiableAt (x := z)
  have hp := ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt (x := z)
  have hpd := (((∂_{v} ψ).smooth ⊤).differentiable (by simp)).differentiableAt (x := z)
  rw [fderiv_fun_add (hgd.fun_mul hp) (hg.fun_mul hpd),
    fderiv_fun_mul hgd hp,fderiv_fun_mul hg hpd]
  simp only [add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,PlanarChartTest.derivative]
  ring

private theorem lifted_product_laplacian (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (z : ℂ) :
    (g.mulSmooth ψ (ψ.smooth ⊤)).laplacianTest.field z =
      ψ z*g.laplacianTest.field z +
      2*(∑ i : Fin 2, (∂_{direction i} ψ) z*(g.derivative (direction i)).field z) +
      (Δ ψ) z*g.field z := by
  have hb (i : Fin 2) : Complex.orthonormalBasisOneI i = direction i := by
    rw [Complex.coe_orthonormalBasisOneI]
    rfl
  have hΔ : (Δ ψ) z = ∑ i : Fin 2, (∂_{direction i} (∂_{direction i} ψ)) z := by
    rw [SchwartzMap.laplacian_eq_sum Complex.orthonormalBasisOneI]
    simp only [sum_apply,hb]
  change (∑ i : Fin 2,
    (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative (direction i)).derivative (direction i)).field z) = _
  simp_rw [lifted_product_second]
  simp only [hΔ,PlanarChartTest.laplacianTest,PlanarChartTest.planarLaplacian,
    PlanarChartTest.derivative,Fin.sum_univ_two]
  ring

private theorem lifted_product_laplacian_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) :
    (∫ z : ℂ, (g.mulSmooth ψ (ψ.smooth ⊤)).laplacianTest.localValue u z) =
      g.laplacianTest.localDistribution u ψ +
      2*(∑ i : Fin 2, (g.derivative (direction i)).localDistribution u (∂_{direction i} ψ)) +
      g.localDistribution u (Δ ψ) := by
  simp only [PlanarChartTest.localDistribution_apply]
  rw [← integral_finsetSum _ (fun i _ => lift_local_pair_integrable _ _ _),← integral_const_mul]
  have h0 := lift_local_pair_integrable g.laplacianTest u ψ
  have h1 : Integrable (fun z : ℂ => 2*(∑ i : Fin 2,
      (∂_{direction i} ψ) z*(g.derivative (direction i)).localValue u z)) :=
    (integrable_finsetSum Finset.univ (fun (i : Fin 2) _ =>
      lift_local_pair_integrable (g.derivative (direction i)) u (∂_{direction i} ψ))).const_mul 2
  have h2 := lift_local_pair_integrable g u (Δ ψ)
  rw [← integral_add h0 h1,← integral_add (h0.fun_add h1) h2]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue,lifted_product_laplacian,Fin.sum_univ_two]
  ring

private theorem lifted_product_divHeight_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (n : ℕ) :
    (∫ z : ℂ, ((g.mulSmooth ψ (ψ.smooth ⊤)).divHeight n).localValue u z) =
      (g.divHeight n).localDistribution u ψ := by
  rw [PlanarChartTest.localDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue,PlanarChartTest.divHeight,PlanarChartTest.mulSmooth]
  ring

/-- The complete cutoff Laplacian is derived from the actual scalar equation.
Derivatives of localized scalars retain all cutoff terms, without asserting that
individual hyperbolic frame components are modular scalar functions. -/
theorem full_response_global_cutoff_laplacian (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    Δ (g.localDistribution (embedding (weakResponse q minusBranch))) =
      (2:ℂ) • (∑ i : Fin 2, ∂_{direction i}
        ((g.derivative (direction i)).localDistribution (embedding (weakResponse q minusBranch)))) -
      g.laplacianTest.localDistribution (embedding (weakResponse q minusBranch)) +
      parameter q minusBranch • (g.divHeight 2).localDistribution
        (embedding (weakResponse q minusBranch)) +
      (g.divHeight 2).localDistribution (forcingVector q minusBranch) := by
  ext ψ
  have he := full_response_global_planar_equation q minusBranch (g.mulSmooth ψ (ψ.smooth ⊤))
  rw [lifted_product_laplacian_integral,lifted_product_divHeight_integral,
    lifted_product_divHeight_integral] at he
  rw [TemperedDistribution.laplacian_apply_apply]
  simp only [Fin.sum_univ_two] at he ⊢
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,
    TemperedDistribution.lineDerivOp_apply_apply,map_neg]
  linear_combination he

end
end RHTower.D4BMModularCore
