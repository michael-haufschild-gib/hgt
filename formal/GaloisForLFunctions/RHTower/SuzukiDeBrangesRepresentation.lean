import GaloisForLFunctions.RHTower.SuzukiDeBrangesEntire
import GaloisForLFunctions.RHTower.SuzukiPHatBasisCoefficient

noncomputable section

/-!
# `H(E) = E K(Θ)`

Every element of the model space has an entire `E`-multiple, and that multiple lies in the de
Branges space.

The entire candidate is the de Branges series with the element's basis coefficients.  Off the
spectrum and off the zeros of `E`, dividing it by `E` gives the pointwise basis expansion; the
partial sums of that expansion converge in `L²` to the element itself, and an `L²`-convergent
sequence has an almost-everywhere convergent subsequence, so the two agree almost everywhere.

The conjugate quotient is then the second model-space component `Θ conj(F)`, so both Hardy
conditions of `H(E)` hold.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Termwise summability of the de Branges series at a point. -/
theorem summable_deBrangesSeries_at (hRH : RiemannHypothesis)
    {c : XiDivisorSupport → ℂ} (hc : Summable fun ρ : XiDivisorSupport => ‖c ρ‖ ^ 2) (z : ℂ) :
    Summable (fun ρ : XiDivisorSupport =>
      c ρ * suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) z) := by
  have hpi := Real.pi_pos
  have hspec := summable_xiSupportMult_inv_one_add_sq hRH
  set R : ℝ := ‖z‖ + 1 with hRdef
  have hR : 0 < R := by
    have := norm_nonneg z
    linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    XiC_differentiable.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (XiC 0)) (hM 0 (by simpa using hR.le))
  set u : XiDivisorSupport → ℝ := fun ρ =>
    ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
      * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R with hu
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) R := by
    simp [hRdef]
  have hsummable : Summable u := summable_deBrangesBound hRH hc hR hM0 hM
  refine Summable.of_norm_bounded hsummable fun ρ => ?_
  rw [norm_mul, hu]
  have h1 := norm_suzukiDeBrangesVector_le (γ := xiRealSpectralPointSupport ρ)
    (m := xiSupportMult ρ) hzmem
  calc ‖c ρ‖ * ‖suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) z‖
      ≤ ‖c ρ‖ * (Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
          * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
          * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R := by ring

/-! ## The series represents the model-space element -/

theorem suzukiCauchyWeight_mul (ρ : XiDivisorSupport) :
    ‖suzukiEnergyScale ρ‖ ^ 2 * suzukiCauchyWeight ρ = 1 := by
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast xiSupportMult_pos ρ
  rw [suzukiEnergyScale, suzukiCauchyWeight, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]
  field_simp

theorem hasSum_smul_suzukiFGammaFamily (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    HasSum (fun ρ : XiDivisorSupport =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) • suzukiFGammaFamily hRH ρ) F := by
  set Y : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) := ⟨F, hF⟩ with hY
  have hb := (suzukiFGammaHilbertBasis hRH).hasSum_repr Y
  have hcoe := coe_suzukiFGammaHilbertBasis hRH
  have hb' : HasSum (fun ρ : XiDivisorSupport =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) • suzukiFGammaVec hRH ρ) Y := by
    refine hb.congr_fun ?_
    intro ρ
    rw [hcoe, (suzukiFGammaHilbertBasis hRH).repr_apply_apply, hcoe]
    rfl
  exact hb'.map
    (suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))).subtypeL
    (suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))).subtypeL.continuous

theorem ae_not_xiRealSpectralPointSupport :
    ∀ᵐ x : ℝ, ∀ ρ : XiDivisorSupport, ((x : ℝ) : ℂ) ≠ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
  have h : (Set.range xiRealSpectralPointSupport).Countable := Set.countable_range _
  have h0 : volume (Set.range xiRealSpectralPointSupport) = 0 := h.measure_zero _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr h0] with x hx ρ hc
  exact hx ⟨ρ, by exact_mod_cast hc.symm⟩

theorem suzukiFGammaFun_eq_scale_energyKernel (hRH : RiemannHypothesis) {x : ℝ}
    (ρ : XiDivisorSupport)
    (hne : ((x : ℝ) : ℂ) ≠ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) :
    suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) ((x : ℝ) : ℂ)
      = suzukiEnergyScale ρ * suzukiEnergyKernelFun ρ x := by
  rw [suzukiFGammaFun, dslope_suzukiHalfInner_apply (XiC_xiRealSpectralPointSupport hRH ρ) hne,
    suzukiEnergyScale, suzukiEnergyKernelFun, suzukiCauchyKernel, div_eq_mul_inv]
  ring

/-- **The de Branges series divided by `E` is the model-space element.**  So `E F` has an entire
representative for every `F ∈ K(Θ)`, which is the statement that `H(E) = E K(Θ)`. -/
theorem suzukiDeBrangesSeries_div_ae (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    (fun x : ℝ => suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))
        ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      =ᵐ[volume] (F : ℝ → ℂ) := by
  set c : XiDivisorSupport → ℂ := fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) with hcdef
  have hc : Summable fun ρ : XiDivisorSupport => ‖c ρ‖ ^ 2 :=
    (hasSum_normSq_inner_suzukiFGammaFamily hRH hF).summable
  set a : XiDivisorSupport → ℂ := fun ρ => c ρ * suzukiEnergyScale ρ with hadef
  set g : ℝ → ℂ := fun x =>
    suzukiDeBrangesSeries c ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) with hgdef
  have hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ := by
    refine hc.congr fun ρ => ?_
    rw [hadef, norm_mul, mul_pow, mul_assoc, suzukiCauchyWeight_mul, mul_one]
  have hg : ∀ᵐ x : ℝ, HasSum (fun ρ : XiDivisorSupport =>
      a ρ * suzukiEnergyKernelFun ρ x) (g x) := by
    filter_upwards [ae_xiHedenmalmDeBrangesE_ofReal_ne_zero,
      ae_not_xiRealSpectralPointSupport] with x hE hne
    have hbase := (summable_deBrangesSeries_at hRH hc ((x : ℝ) : ℂ)).hasSum
    have hdiv := hbase.div_const (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
    refine hdiv.congr_fun ?_
    intro ρ
    have hDB := suzukiDeBrangesVector_eq (m := xiSupportMult ρ)
      (XiC_xiRealSpectralPointSupport hRH ρ) hE
    rw [hDB, suzukiFGammaFun_eq_scale_energyKernel hRH ρ (hne ρ), hadef]
    field_simp
  obtain ⟨S, hStend, hSae⟩ := exists_lp_of_hasSum hRH a hsa g hg
  have hpartial : ∀ N : ℕ, suzukiCauchyPartial hRH a N
      = ∑ n ∈ Finset.range N, c (xiSupportEnum n) • suzukiFGammaFamily hRH (xiSupportEnum n) := by
    intro N
    rw [suzukiCauchyPartial]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [suzukiFGammaFamily_eq_smul_energyKernel hRH (xiSupportEnum n), smul_smul, hadef]
    rfl
  have htendF : Tendsto (suzukiCauchyPartial hRH a) atTop (𝓝 F) := by
    have hsum := hasSum_smul_suzukiFGammaFamily hRH hF
    have hnat : HasSum (fun n : ℕ =>
        c (xiSupportEnum n) • suzukiFGammaFamily hRH (xiSupportEnum n)) F :=
      (xiSupportEnum.hasSum_iff (f := fun ρ : XiDivisorSupport =>
        c ρ • suzukiFGammaFamily hRH ρ)).mpr hsum
    refine (hnat.tendsto_sum_nat).congr fun N => ?_
    exact (hpartial N).symm
  have hSF : S = F := tendsto_nhds_unique hStend htendF
  rw [hSF] at hSae
  exact hSae.symm


/-- The conjugate quotient of the de Branges series is the second model-space component. -/
theorem suzukiDeBrangesSeries_conj_div_ae (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    (fun x : ℝ => (starRingEnd ℂ)
        (suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))
          ((x : ℝ) : ℂ)) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      =ᵐ[volume] ((thetaMul (star F) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  filter_upwards [suzukiDeBrangesSeries_div_ae hRH hF,
    ae_xiHedenmalmDeBrangesE_ofReal_ne_zero,
    thetaMul_coeFn (star F), MeasureTheory.Lp.coeFn_star F] with x hval hE k1 k2
  have hEs : xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
      = (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) :=
    xiHedenmalmDeBrangesESharp_ofReal_eq_conj x
  have hseries : suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))
      ((x : ℝ) : ℂ) = xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) * (F : ℝ → ℂ) x := by
    rw [← hval]
    field_simp
  rw [hseries, map_mul, k1, k2, Pi.star_apply, suzukiThetaSymbol, if_neg hE, hEs]
  show (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) * (starRingEnd ℂ) ((F : ℝ → ℂ) x)
      / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)
    = (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) * (starRingEnd ℂ) ((F : ℝ → ℂ) x)
  field_simp

/-- **`E K(Θ) ⊆ H(E)`.**  The entire representative of `E F` lies in the de Branges space. -/
theorem memDeBranges_suzukiDeBrangesSeries (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    MemDeBranges (suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))) := by
  have hc : Summable fun ρ : XiDivisorSupport =>
      ‖(inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)‖ ^ 2 :=
    (hasSum_normSq_inner_suzukiFGammaFamily hRH hF).summable
  have h1 : MemLp (fun x : ℝ =>
      suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))
        ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
    (memLp_congr_ae (suzukiDeBrangesSeries_div_ae hRH hF)).mpr (MeasureTheory.Lp.memLp F)
  have h2 : MemLp (fun x : ℝ => (starRingEnd ℂ)
      (suzukiDeBrangesSeries (fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ))
        ((x : ℝ) : ℂ)) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
    (memLp_congr_ae (suzukiDeBrangesSeries_conj_div_ae hRH hF)).mpr
      (MeasureTheory.Lp.memLp (thetaMul (star F)))
  refine (memDeBranges_iff_mem_suzukiModelSpace
    (differentiable_suzukiDeBrangesSeries hRH hc) h1 h2).mpr ?_
  have heq : h1.toLp _ = F := by
    refine MeasureTheory.Lp.ext ?_
    exact (h1.coeFn_toLp).trans (suzukiDeBrangesSeries_div_ae hRH hF)
  rw [heq]
  exact hF


end RHTower
