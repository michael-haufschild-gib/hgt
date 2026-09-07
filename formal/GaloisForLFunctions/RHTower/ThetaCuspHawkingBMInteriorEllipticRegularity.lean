import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlanarLocalDomain
import GaloisForLFunctions.HTGeometry.PlanarSobolevLaplacianGain

/-!
The original completed modular gradients determine the full cutoff commutator. Every compact interior localization of the actual forced Xi response has Sobolev order two and an integrable Fourier transform.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open scoped ContDiff ComplexConjugate ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- The actual localized planar L² vector. -/
def InteriorTest.localVector (g : InteriorTest) (u : Space) : Lp ℂ 2 (volume : Measure ℂ) :=
  (g.localValue_memLp u).toLp (g.localValue u)

/-- The distribution represented by the actual localized planar L² value. -/
def InteriorTest.localDistribution (g : InteriorTest) (u : Space) : 𝓢'(ℂ,ℂ) :=
  g.localVector u

/-- The localized distribution pairs with the original angular representative. -/
theorem InteriorTest.localDistribution_apply (g : InteriorTest) (u : Space) (ψ : 𝓢(ℂ,ℂ)) :
    g.localDistribution u ψ = ∫ z : ℂ, ψ z*g.localValue u z := by
  rw [InteriorTest.localDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(g.localValue_memLp u).coeFn_toLp] with z hz
  change g.localVector u z = g.localValue u z at hz
  rw [hz]
  rfl

private theorem local_pair_integrable (g : InteriorTest) (u : Space) (ψ : 𝓢(ℂ,ℂ)) :
    Integrable (fun z : ℂ => ψ z*g.localValue u z) :=
  (ψ.memLp 2).integrable_mul (g.localValue_memLp u)

/-- The mass test is exactly the local inverse-height planar gradient pairing. -/
theorem InteriorTest.mass_planar (g : InteriorTest) (u : Space) :
    inner ℂ (massTest g) u = ∫ z : ℂ, (g.divHeight 1).localValue u z := by
  rw [massTest_inner,← (g.divHeight 1).height_sq_planar]
  apply integral_congr_ae
  filter_upwards with z
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  simp only [InteriorTest.divHeight,coe_im,pow_one]
  field_simp

/-- The flux test pairs with the actual first derivative under planar measure. -/
theorem InteriorTest.flux_planar (g : InteriorTest) (v : ℂ) (u : Space) :
    inner ℂ (fluxTest g v) u = ∫ z : ℂ, (g.derivative v).localValue u z := by
  rw [fluxTest_inner,← (g.derivative v).height_sq_planar]
  rfl

/-- Every completed modular derivative satisfies the original planar weak derivative identity. -/
theorem energyDomain_planar_derivative (g : InteriorTest) (i : Fin 2) (h : energyDomain) :
    (∫ z : ℂ, (g.divHeight 1).localValue ((h : EnergySpace) i.succ) z) +
      (∫ z : ℂ, (g.derivative (direction i)).localValue (embedding h) z) = 0 := by
  have he := energyDomain_testConstraint g i h
  change inner ℂ (massTest g) ((h : EnergySpace) i.succ) +
    inner ℂ (fluxTest g (direction i)) (embedding h) = 0 at he
  rwa [g.mass_planar,g.flux_planar] at he

private theorem test_product_derivative (g : InteriorTest) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field z =
      (g.derivative v).field z*ψ z+g.field z*(∂_{v} ψ) z := by
  change fderiv ℝ (fun w => g.field w*ψ w) z v = _
  rw [fderiv_fun_mul (g.smooth.differentiable (by simp)).differentiableAt
    ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,InteriorTest.derivative]
  ring

private theorem product_derivative_integral (g : InteriorTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (v : ℂ) :
    (∫ z : ℂ, ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).localValue u z) =
      (g.derivative v).localDistribution u ψ + g.localDistribution u (∂_{v} ψ) := by
  rw [InteriorTest.localDistribution_apply,InteriorTest.localDistribution_apply,
    ← integral_add (local_pair_integrable _ _ _) (local_pair_integrable _ _ _)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [InteriorTest.localValue,test_product_derivative]
  ring

private theorem product_divHeight_integral (g : InteriorTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (n : ℕ) :
    (∫ z : ℂ, ((g.mulSmooth ψ (ψ.smooth ⊤)).divHeight n).localValue u z) =
      (g.divHeight n).localDistribution u ψ := by
  rw [InteriorTest.localDistribution_apply]
  apply integral_congr_ae
  filter_upwards with z
  simp only [InteriorTest.localValue,InteriorTest.divHeight,InteriorTest.mulSmooth]
  ring

/-- The actual first derivative of a localized completed response retains both the
cutoff derivative and the original completed frame derivative divided by height. -/
theorem localDistribution_derivative (g : InteriorTest) (i : Fin 2) (h : energyDomain) :
    ∂_{direction i} (g.localDistribution (embedding h)) =
      (g.derivative (direction i)).localDistribution (embedding h) +
        (g.divHeight 1).localDistribution ((h : EnergySpace) i.succ) := by
  ext ψ
  rw [TemperedDistribution.lineDerivOp_apply_apply,map_neg]
  have he := energyDomain_planar_derivative (g.mulSmooth ψ (ψ.smooth ⊤)) i h
  rw [product_divHeight_integral,product_derivative_integral] at he
  change -g.localDistribution (embedding h) (∂_{direction i} ψ) = _
  change -g.localDistribution (embedding h) (∂_{direction i} ψ) =
    (g.derivative (direction i)).localDistribution (embedding h) ψ +
      (g.divHeight 1).localDistribution ((h : EnergySpace) i.succ) ψ
  linear_combination -he

/-- The complete forced equation in planar first-derivative form. -/
theorem full_response_planar_gradient (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    (∑ i : Fin 2, ∫ z : ℂ, ((g.derivative (direction i)).divHeight 1).localValue
      ((weakResponse q minusBranch : EnergySpace) i.succ) z) +
      parameter q minusBranch*(∫ z : ℂ, (g.divHeight 2).localValue
        (embedding (weakResponse q minusBranch)) z) =
      -(∫ z : ℂ, (g.divHeight 2).localValue (forcingVector q minusBranch) z) := by
  have he := (weakSolution_iff_gradient q minusBranch _).mp
    (weakResponse_spec q minusBranch) g.energyTest
  simp_rw [g.energyTest_gradient,InteriorTest.mass_planar] at he
  rw [g.scalar_pairing,g.scalar_pairing,g.scalar_planar,g.scalar_planar] at he
  exact he

private theorem product_derivative_divHeight_integral (g : InteriorTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (v : ℂ) :
    (∫ z : ℂ, (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).divHeight 1).localValue u z) =
      ((g.derivative v).divHeight 1).localDistribution u ψ +
        (g.divHeight 1).localDistribution u (∂_{v} ψ) := by
  rw [InteriorTest.localDistribution_apply,InteriorTest.localDistribution_apply,
    ← integral_add (local_pair_integrable _ _ _) (local_pair_integrable _ _ _)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [InteriorTest.localValue,InteriorTest.divHeight,test_product_derivative]
  ring

/-- The full forcing determines the divergence of the localized original gradient current,
including the cutoff-gradient term. -/
theorem full_response_local_current_divergence (q : XiZeroCopy) (minusBranch : Bool)
    (g : InteriorTest) :
    (∑ i : Fin 2, ∂_{direction i} ((g.divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) i.succ))) =
    (∑ i : Fin 2, ((g.derivative (direction i)).divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) i.succ)) +
      parameter q minusBranch • (g.divHeight 2).localDistribution
        (embedding (weakResponse q minusBranch)) +
      (g.divHeight 2).localDistribution (forcingVector q minusBranch) := by
  ext ψ
  have he := full_response_planar_gradient q minusBranch (g.mulSmooth ψ (ψ.smooth ⊤))
  simp_rw [product_derivative_divHeight_integral] at he
  rw [product_divHeight_integral,product_divHeight_integral] at he
  simp only [Fin.sum_univ_two] at he ⊢
  change
    (∂_{direction 0} ((g.divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) (0:Fin 2).succ))) ψ +
    (∂_{direction 1} ((g.divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) (1:Fin 2).succ))) ψ = _
  simp only [TemperedDistribution.lineDerivOp_apply_apply,map_neg]
  change _ =
    (((g.derivative (direction 0)).divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) (0:Fin 2).succ)) ψ +
    (((g.derivative (direction 1)).divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) (1:Fin 2).succ)) ψ +
    parameter q minusBranch*((g.divHeight 2).localDistribution
      (embedding (weakResponse q minusBranch))) ψ +
    ((g.divHeight 2).localDistribution (forcingVector q minusBranch)) ψ
  linear_combination -he

/-- The actual localized Laplacian contains the complete cutoff commutator,
the original spectral potential, and the original full forcing. -/
theorem full_response_local_laplacian (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    Δ (g.localDistribution (embedding (weakResponse q minusBranch))) =
    (∑ i : Fin 2, ((g.derivative (direction i)).derivative (direction i)).localDistribution
      (embedding (weakResponse q minusBranch))) +
    (2:ℂ) • (∑ i : Fin 2, ((g.derivative (direction i)).divHeight 1).localDistribution
      ((weakResponse q minusBranch : EnergySpace) i.succ)) +
    parameter q minusBranch • (g.divHeight 2).localDistribution
      (embedding (weakResponse q minusBranch)) +
    (g.divHeight 2).localDistribution (forcingVector q minusBranch) := by
  rw [TemperedDistribution.laplacian_eq_sum Complex.orthonormalBasisOneI]
  have hb (i : Fin 2) : Complex.orthonormalBasisOneI i = direction i := by
    rw [Complex.coe_orthonormalBasisOneI]
    rfl
  simp_rw [hb,localDistribution_derivative,LineDeriv.lineDerivOp_add,localDistribution_derivative]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    full_response_local_current_divergence]
  module

end
end RHTower.D4BMModularCore

open MeasureTheory TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

private theorem localDistribution_sobolev_zero (g : InteriorTest) (u : Space) :
    MemSobolev 0 2 (g.localDistribution u) :=
  memSobolev_zero_iff.mpr ⟨g.localVector u,rfl⟩

private theorem sum_sobolev_zero {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev 0 2 (f i)) : MemSobolev 0 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

/-- The actual localized response has a planar L² Laplacian, with every cutoff and source
term obtained from its proved distributional equation. -/
theorem full_response_local_laplacian_L2 (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    ∃ v : Lp ℂ 2 (volume : Measure ℂ),
      Δ (g.localDistribution (embedding (weakResponse q minusBranch))) = (v : 𝓢'(ℂ,ℂ)) := by
  apply memSobolev_zero_iff.mp
  rw [full_response_local_laplacian]
  exact (((sum_sobolev_zero (fun _ => localDistribution_sobolev_zero _ _)).add
    ((sum_sobolev_zero (fun _ => localDistribution_sobolev_zero _ _)).smul (2:ℂ))).add
    ((localDistribution_sobolev_zero _ _).smul (parameter q minusBranch))).add
    (localDistribution_sobolev_zero _ _)

/-- Every compact interior localization of the actual full-forcing Xi response has
Sobolev order two. This regularity is proved from the original modular energy domain. -/
theorem full_response_local_H2 (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    MemSobolev 2 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  have h := planar_sobolev_gain_two (localDistribution_sobolev_zero g
    (embedding (weakResponse q minusBranch)))
    (memSobolev_zero_iff.mpr (full_response_local_laplacian_L2 q minusBranch g))
  simpa only [zero_add] using h

/-- The localized actual response has an absolutely integrable Fourier transform. -/
theorem full_response_local_fourier_L1 (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ), FourierTransform.fourier
      (g.localDistribution (embedding (weakResponse q minusBranch))) = (v : 𝓢'(ℂ,ℂ)) :=
  (full_response_local_H2 q minusBranch g).fourier_memL1 (by norm_num)

end
end RHTower.D4BMModularCore
