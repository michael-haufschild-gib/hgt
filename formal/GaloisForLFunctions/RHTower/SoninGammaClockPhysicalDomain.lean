import GaloisForLFunctions.RHTower.SoninGammaClockEvenDomain
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Full physical Gamma domain and Fourier invariance

The actual half-line parity switch identifies the odd sector with the even
sector. Both maximal Gamma domains are retained in the orthogonal Hilbert
product. The original strong cutoff integrals converge precisely on this
full self-adjoint domain, and their Fourier symmetry survives the limit.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace RHTower

private theorem paritySwitch_ae (f : SoninL2) :
    (soninParityMultiplier 1 f : ℝ → ℂ) =ᵐ[volume]
      fun x => (if 0 < x then (1:ℂ) else -1) * f x := by
  let P := indicatorCutoff (Ioi 0) measurableSet_Ioi
  change ((P f + (-1 : ℂ)^1 • (f-P f) : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add (P f) ((-1 : ℂ)^1 • (f-P f)),
    Lp.coeFn_smul ((-1 : ℂ)^1) (f-P f), Lp.coeFn_sub f (P f),
    indicatorCutoff_ae (Ioi 0) measurableSet_Ioi f] with x hadd hsmul hsub hcut
  change _ = (-1 : ℂ)^1 * (f-P f) x at hsmul
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hadd, hsmul, hsub, hcut]
  by_cases hx : 0 < x <;> simp [hx]

/-- The literal half-line parity switch is an involution on full physical L2. -/
theorem soninParitySwitch_involutive (f : SoninL2) :
    soninParityMultiplier 1 (soninParityMultiplier 1 f) = f := by
  apply Lp.ext
  filter_upwards [paritySwitch_ae (soninParityMultiplier 1 f), paritySwitch_ae f] with x h₁ h₂
  rw [h₁,h₂]
  split_ifs <;> simp

/-- Reflection reverses the literal parity switch; the clock origin is null. -/
theorem l2Reflection_paritySwitch (f : SoninL2) :
    l2Reflection (soninParityMultiplier 1 f) = -soninParityMultiplier 1 (l2Reflection f) := by
  apply Lp.ext
  have hj := (paritySwitch_ae f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (soninParityMultiplier 1 f), hj,
    paritySwitch_ae (l2Reflection f), l2Reflection_ae f,
    Lp.coeFn_neg (soninParityMultiplier 1 (l2Reflection f)), volume.ae_ne (0:ℝ)]
    with x hr hj hp hf hn hx
  simp only [Function.comp_apply] at hj
  rw [hr, hj, hn]
  change _ = -(soninParityMultiplier 1 (l2Reflection f) x)
  rw [hp,hf]
  by_cases hx0 : 0 < x
  · simp [hx0, show ¬0 < -x by linarith]
  · simp [hx0, show 0 < -x by rcases lt_or_gt_of_ne hx with h|h <;> linarith]

/-- The second physical sector is precisely the reflection-odd sector. -/
theorem mem_evenOrthogonal_iff (f : SoninL2) :
    f ∈ evenSubspaceᗮ ↔ l2Reflection f = -f := by
  constructor
  · intro hf
    have hp := (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := evenSubspace)).mpr hf
    have he : evenProjection f = 0 := by
      rw [evenProjection_eq_starProjection]
      exact congrArg (fun z : evenSubspace => (z:SoninL2)) hp
    rw [evenProjection_apply] at he
    have hs := congrArg (fun z : SoninL2 => (2:ℂ) • z) he
    simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul, smul_zero] at hs
    calc
      l2Reflection f = (f+l2Reflection f)-f := by abel
      _ = -f := by rw [hs]; simp
  · intro hf
    apply (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := evenSubspace)).mp
    apply Subtype.ext
    change evenSubspace.starProjection f = 0
    rw [← evenProjection_eq_starProjection, evenProjection_apply, hf]
    simp

/-- Odd-to-even transport is the actual sign multiplier, with no discarded sector. -/
def soninOddEvenUnitary : evenSubspaceᗮ ≃ₗᵢ[ℂ] evenSubspace where
  toFun f := ⟨soninParityMultiplier 1 (f:SoninL2), by
    apply (mem_evenSubspace_iff _).mpr
    rw [l2Reflection_paritySwitch, (mem_evenOrthogonal_iff _).mp f.property, map_neg, neg_neg]⟩
  invFun f := ⟨soninParityMultiplier 1 (f:SoninL2), by
    apply (mem_evenOrthogonal_iff _).mpr
    rw [l2Reflection_paritySwitch, (mem_evenSubspace_iff _).mp f.property]⟩
  left_inv f := by apply Subtype.ext; exact soninParitySwitch_involutive f
  right_inv f := by apply Subtype.ext; exact soninParitySwitch_involutive f
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _
  norm_map' f := norm_soninParityMultiplier 1 f

/-- Exact two-sector physical Hilbert decomposition into identical even carriers. -/
def soninParityDecomposition : SoninL2 ≃ₗᵢ[ℂ] WithLp 2 (evenSubspace × evenSubspace) :=
  evenSubspace.orthogonalDecomposition.trans
    ((LinearIsometryEquiv.refl ℂ evenSubspace).withLpProdCongr 2 soninOddEvenUnitary)


open scoped LinearPMap
open GaloisForLFunctions.HTGeometry
local notation "GammaPair" => WithLp 2 (evenSubspace × evenSubspace)

private def doublePhysicalOperator (T : evenSubspace →ₗ.[ℂ] evenSubspace) :
    GammaPair →ₗ.[ℂ] GammaPair where
  domain := (T.domain.prod T.domain).comap
    (WithLp.linearEquiv 2 ℂ (evenSubspace × evenSubspace)).toLinearMap
  toFun :=
    { toFun := fun z => WithLp.toLp 2
        (T ⟨z.val.fst,z.property.1⟩,
         T ⟨z.val.snd,z.property.2⟩)
      map_add' := by
        intro x y
        apply (WithLp.linearEquiv 2 ℂ (evenSubspace × evenSubspace)).injective
        refine Prod.ext ?_ ?_
        · simpa using! (T.map_add ⟨x.val.fst,x.property.1⟩ ⟨y.val.fst,y.property.1⟩)
        · simpa using! (T.map_add ⟨x.val.snd,x.property.2⟩ ⟨y.val.snd,y.property.2⟩)
      map_smul' := by
        intro c x
        apply (WithLp.linearEquiv 2 ℂ (evenSubspace × evenSubspace)).injective
        refine Prod.ext ?_ ?_
        · simpa using! (T.map_smul c ⟨x.val.fst,x.property.1⟩)
        · simpa using! (T.map_smul c ⟨x.val.snd,x.property.2⟩) }

/-- The exact maximal Gamma domain on both physical parity sectors. -/
def gammaClockTwoSectorOperator : GammaPair →ₗ.[ℂ] GammaPair :=
  doublePhysicalOperator gammaClockEvenOperator

private theorem twoSector_dense :
    Dense (gammaClockTwoSectorOperator.domain : Set GammaPair) := by
  exact (gammaClockEvenOperator_isSelfAdjoint.dense_domain.prod
    gammaClockEvenOperator_isSelfAdjoint.dense_domain).preimage
      (WithLp.prodContinuousLinearEquiv 2 ℂ evenSubspace evenSubspace).toHomeomorph.isOpenMap

private theorem even_formal : gammaClockEvenOperator.IsFormalAdjoint gammaClockEvenOperator := by
  have h := LinearPMap.adjoint_isFormalAdjoint gammaClockEvenOperator_isSelfAdjoint.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp gammaClockEvenOperator_isSelfAdjoint] at h

private theorem twoSector_formal :
    gammaClockTwoSectorOperator.IsFormalAdjoint gammaClockTwoSectorOperator := by
  intro x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  exact congrArg₂ (fun a b : ℂ => a+b)
    (even_formal ⟨x.val.fst,x.property.1⟩ ⟨y.val.fst,y.property.1⟩)
    (even_formal ⟨x.val.snd,x.property.2⟩ ⟨y.val.snd,y.property.2⟩)

/-- Both sectors have their full maximal domain; testing each adjoint coordinate
rules out any hidden domain extension. -/
theorem gammaClockTwoSectorOperator_isSelfAdjoint : IsSelfAdjoint gammaClockTwoSectorOperator := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_,?_⟩
    · intro y hy
      let yA : gammaClockTwoSectorOperator†.domain := ⟨y,hy⟩
      have hf : y.fst ∈ gammaClockEvenOperator†.domain := by
        apply LinearPMap.mem_adjoint_domain_of_exists
        refine ⟨(gammaClockTwoSectorOperator† yA).fst,?_⟩
        intro z
        let zA : gammaClockTwoSectorOperator.domain :=
          ⟨WithLp.toLp 2 (z.val,0),⟨z.property,gammaClockEvenOperator.domain.zero_mem⟩⟩
        have h := LinearPMap.adjoint_isFormalAdjoint twoSector_dense yA zA
        rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply] at h
        change inner ℂ (gammaClockTwoSectorOperator† yA).fst z.val +
          inner ℂ (gammaClockTwoSectorOperator† yA).snd 0 =
          inner ℂ y.fst (gammaClockEvenOperator z) +
          inner ℂ y.snd (gammaClockEvenOperator 0) at h
        simpa only [inner_zero_right, LinearPMap.map_zero, add_zero] using h
      have hs : y.snd ∈ gammaClockEvenOperator†.domain := by
        apply LinearPMap.mem_adjoint_domain_of_exists
        refine ⟨(gammaClockTwoSectorOperator† yA).snd,?_⟩
        intro z
        let zA : gammaClockTwoSectorOperator.domain :=
          ⟨WithLp.toLp 2 (0,z.val),⟨gammaClockEvenOperator.domain.zero_mem,z.property⟩⟩
        have h := LinearPMap.adjoint_isFormalAdjoint twoSector_dense yA zA
        rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply] at h
        change inner ℂ (gammaClockTwoSectorOperator† yA).fst 0 +
          inner ℂ (gammaClockTwoSectorOperator† yA).snd z.val =
          inner ℂ y.fst (gammaClockEvenOperator 0) +
          inner ℂ y.snd (gammaClockEvenOperator z) at h
        simpa only [inner_zero_right, LinearPMap.map_zero, zero_add] using h
      rw [LinearPMap.isSelfAdjoint_def.mp gammaClockEvenOperator_isSelfAdjoint] at hf hs
      exact ⟨hf,hs⟩
    · intro x y hxy
      exact LinearPMap.adjoint_apply_eq twoSector_dense x (fun v => by
        rw [twoSector_formal y v,hxy])
  · exact twoSector_formal.le_adjoint twoSector_dense

/-- Full physical Gamma operator, retaining both parity sectors on their exact domain. -/
def gammaClockPhysicalOperator : SoninL2 →ₗ.[ℂ] SoninL2 :=
  unitaryConjugateLinearPMap soninParityDecomposition gammaClockTwoSectorOperator

theorem gammaClockPhysicalOperator_isSelfAdjoint : IsSelfAdjoint gammaClockPhysicalOperator :=
  IsSelfAdjoint.unitaryConjugate soninParityDecomposition gammaClockTwoSectorOperator_isSelfAdjoint


private theorem parityDecomposition_symm_apply (z : GammaPair) :
    soninParityDecomposition.symm z = (z.fst:SoninL2)+soninParityMultiplier 1 (z.snd:SoninL2) := rfl

private def gammaTwoSectorCutoff (ε R : ℝ) (hε : 0 < ε) : GammaPair →L[ℂ] GammaPair :=
  let V := WithLp.prodContinuousLinearEquiv 2 ℂ evenSubspace evenSubspace
  V.symm.toContinuousLinearMap ∘L
    (gammaClockCutoffEvenOperator ε R hε).prodMap (gammaClockCutoffEvenOperator ε R hε) ∘L
      V.toContinuousLinearMap

/-- Original finite Gamma family on the entire physical carrier. -/
def gammaClockCutoffPhysicalOperator (ε R : ℝ) (hε : 0 < ε) : SoninL2 →L[ℂ] SoninL2 :=
  soninParityDecomposition.symm.toLinearIsometry.toContinuousLinearMap ∘L gammaTwoSectorCutoff ε R hε ∘L
    soninParityDecomposition.toLinearIsometry.toContinuousLinearMap

private theorem physicalCutoff_apply (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    gammaClockCutoffPhysicalOperator ε R hε f =
      (gammaClockCutoffEvenOperator ε R hε (soninParityDecomposition f).fst:SoninL2)+
      soninParityMultiplier 1
        (gammaClockCutoffEvenOperator ε R hε (soninParityDecomposition f).snd:SoninL2) := rfl

private theorem physical_difference (u : ℝ) (f : SoninL2) :
    gammaClockDifferenceOperator u f =
      dilation (Real.exp u) (Real.exp_pos u) f+
      dilation (Real.exp (-u)) (Real.exp_pos (-u)) f-(2:ℂ) • f := rfl

private theorem physical_integrable (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    Integrable (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
      gammaClockDifferenceOperator u f) (volume.restrict (Icc ε R)) := by
  have hd : ContinuousOn (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ)) (Icc ε R) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro u hu
    have hu0 : 0 < u := hε.trans_le hu.1
    have hden : Real.exp u-Real.exp (-u) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
    unfold ccmPublishedArchimedeanDensity
    apply ContinuousAt.continuousWithinAt
    exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u).div
      (by fun_prop) hden).div continuousAt_id hu0.ne'
  have hc : Continuous (fun u => gammaClockDifferenceOperator u f) := by
    simp only [physical_difference, ← rayDilate_of_pos (Real.exp_pos _)]
    exact ((continuous_dilationOrbit f).add
      ((continuous_dilationOrbit f).comp continuous_neg)).sub continuous_const
  exact (hd.smul hc.continuousOn).integrableOn_Icc

private theorem parity_difference (u : ℝ) (f : SoninL2) :
    soninParityMultiplier 1 (gammaClockDifferenceOperator u f) =
      gammaClockDifferenceOperator u (soninParityMultiplier 1 f) := by
  simp only [physical_difference, map_sub, map_add, map_smul, soninParityMultiplier_dilation]

/-- Literal strong action of the finite full-carrier operator, including both
parity sectors, both dilation directions and the exact -2I counterterm. -/
theorem gammaClockCutoffPhysicalOperator_apply (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    gammaClockCutoffPhysicalOperator ε R hε f =
      ∫ u in Icc ε R, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
        gammaClockDifferenceOperator u f := by
  let x := (soninParityDecomposition f).fst
  let y := (soninParityDecomposition f).snd
  have hrec : (x:SoninL2)+soninParityMultiplier 1 (y:SoninL2) = f := by
    rw [← parityDecomposition_symm_apply, soninParityDecomposition.symm_apply_apply]
  rw [physicalCutoff_apply, gammaClockCutoffEvenOperator_apply, gammaClockCutoffEvenOperator_apply,
    ← (soninParityMultiplier 1).integral_comp_comm (physical_integrable ε R hε (y:SoninL2))]
  rw [← integral_add (physical_integrable ε R hε (x:SoninL2))
    ((soninParityMultiplier 1).integrable_comp (physical_integrable ε R hε (y:SoninL2)))]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul, parity_difference, ← smul_add, ← map_add, hrec]

private theorem twoSectorCutoff_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop)
    (f : gammaClockTwoSectorOperator.domain) :
    Tendsto (fun i => gammaTwoSectorCutoff (ε i) (R i) (hpos i) f.val) l
      (𝓝 (gammaClockTwoSectorOperator f)) := by
  let fx : gammaClockEvenOperator.domain := ⟨f.val.fst,f.property.1⟩
  let fy : gammaClockEvenOperator.domain := ⟨f.val.snd,f.property.2⟩
  have ht (z : gammaClockEvenOperator.domain) :
      Tendsto (fun i => gammaClockCutoffEvenOperator (ε i) (R i) (hpos i) z.val) l
        (𝓝 (gammaClockEvenOperator z)) := by
    let zU : gammaClockSpectralOperator.domain := ⟨archimedeanMellinUnitary z.val,z.property⟩
    have h := archimedeanMellinUnitary.symm.continuous.continuousAt.tendsto.comp
      (gammaClockCutoffSpectralOperator_tendsto ε R hpos hε hR zU)
    apply h.congr
    intro i
    apply archimedeanMellinUnitary.injective
    simp only [Function.comp_apply, archimedeanMellinUnitary.apply_symm_apply,
      archimedeanMellinUnitary_gammaClockCutoff]
    rfl
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ evenSubspace evenSubspace).symm.continuous.continuousAt.tendsto.comp
    ((ht fx).prodMk_nhds (ht fy))

/-- Every original cofinal full-carrier cutoff family converges exactly on the
maximal physical Gamma domain, and has precisely the maximal operator's action. -/
theorem gammaClockCutoffPhysicalOperator_limit_iff
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (f g : SoninL2) :
    Tendsto (fun i => gammaClockCutoffPhysicalOperator (ε i) (R i) (hpos i) f) l (𝓝 g) ↔
      ∃ hf : f ∈ gammaClockPhysicalOperator.domain, gammaClockPhysicalOperator ⟨f,hf⟩ = g := by
  have hinter (i : ι) : soninParityDecomposition
      (gammaClockCutoffPhysicalOperator (ε i) (R i) (hpos i) f) =
      gammaTwoSectorCutoff (ε i) (R i) (hpos i) (soninParityDecomposition f) :=
    soninParityDecomposition.apply_symm_apply _
  constructor
  · intro ht
    have hp := (soninParityDecomposition.continuous.continuousAt.tendsto.comp ht).congr hinter
    have hx := (WithLp.fstL 2 ℂ evenSubspace evenSubspace).continuous.continuousAt.tendsto.comp hp
    have hy := (WithLp.sndL 2 ℂ evenSubspace evenSubspace).continuous.continuousAt.tendsto.comp hp
    obtain ⟨hfx,hex⟩ := (gammaClockCutoffEvenOperator_limit_iff ε R hpos hε hR
      (soninParityDecomposition f).fst (soninParityDecomposition g).fst).mp hx
    obtain ⟨hfy,hey⟩ := (gammaClockCutoffEvenOperator_limit_iff ε R hpos hε hR
      (soninParityDecomposition f).snd (soninParityDecomposition g).snd).mp hy
    refine ⟨⟨hfx,hfy⟩,?_⟩
    apply soninParityDecomposition.injective
    change soninParityDecomposition (soninParityDecomposition.symm _) = _
    rw [soninParityDecomposition.apply_symm_apply]
    apply (WithLp.linearEquiv 2 ℂ (evenSubspace × evenSubspace)).injective
    exact Prod.ext hex hey
  · rintro ⟨hf,heq⟩
    let fU : gammaClockTwoSectorOperator.domain := ⟨soninParityDecomposition f,hf⟩
    have h := soninParityDecomposition.symm.continuous.continuousAt.tendsto.comp
      (twoSectorCutoff_tendsto ε R hpos hε hR fU)
    have hg : soninParityDecomposition.symm (gammaClockTwoSectorOperator fU) = g := heq
    rw [hg] at h
    exact h


/-- The full literal finite Gamma source commutes with the physical Fourier unitary. -/
theorem fourier_gammaClockCutoffPhysicalOperator (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    fourierUnitary (gammaClockCutoffPhysicalOperator ε R hε f) =
      gammaClockCutoffPhysicalOperator ε R hε (fourierUnitary f) := by
  let L := fourierUnitary.toLinearIsometry.toContinuousLinearMap
  change L (gammaClockCutoffPhysicalOperator ε R hε f) = _
  rw [gammaClockCutoffPhysicalOperator_apply, gammaClockCutoffPhysicalOperator_apply,
    ← L.integral_comp_comm (physical_integrable ε R hε f)]
  apply integral_congr_ae
  filter_upwards [] with u
  change fourierUnitary (((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
    gammaClockDifferenceOperator u f) = _
  rw [map_smul, physical_difference, physical_difference, map_sub, map_add, map_smul,
    fourierUnitary_dilation, fourierUnitary_dilation]
  simp only [Real.exp_neg, inv_inv]
  congr 1
  abel

private theorem physical_domain_unitary (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2)
    (hU : ∀ (ε R : ℝ) (hε : 0 < ε) (f : SoninL2),
      U (gammaClockCutoffPhysicalOperator ε R hε f) =
        gammaClockCutoffPhysicalOperator ε R hε (U f))
    (f : gammaClockPhysicalOperator.domain) :
    ∃ hf : U f.val ∈ gammaClockPhysicalOperator.domain,
      gammaClockPhysicalOperator ⟨U f.val,hf⟩ = U (gammaClockPhysicalOperator f) := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have heps : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  have ht := (gammaClockCutoffPhysicalOperator_limit_iff ε (fun n : ℕ => (n:ℝ)) hpos
    heps tendsto_natCast_atTop_atTop f.val (gammaClockPhysicalOperator f)).mpr ⟨f.property,rfl⟩
  have hu := (U.continuous.continuousAt.tendsto.comp ht).congr
    (fun n => hU (ε n) n (hpos n) f.val)
  exact (gammaClockCutoffPhysicalOperator_limit_iff ε (fun n : ℕ => (n:ℝ)) hpos
    heps tendsto_natCast_atTop_atTop (U f.val) (U (gammaClockPhysicalOperator f))).mp hu

/-- The full unbounded Gamma action and its exact domain are Fourier compatible. -/
theorem gammaClockPhysicalOperator_fourier (f : gammaClockPhysicalOperator.domain) :
    ∃ hf : fourierUnitary f.val ∈ gammaClockPhysicalOperator.domain,
      gammaClockPhysicalOperator ⟨fourierUnitary f.val,hf⟩ =
        fourierUnitary (gammaClockPhysicalOperator f) :=
  physical_domain_unitary fourierUnitary fourier_gammaClockCutoffPhysicalOperator f

/-- Fourier preserves the maximal full physical domain in both directions. -/
theorem gammaClockPhysicalOperator_fourier_domain_iff (f : SoninL2) :
    fourierUnitary f ∈ gammaClockPhysicalOperator.domain ↔ f ∈ gammaClockPhysicalOperator.domain := by
  constructor
  · intro hf
    have hcomm (ε R : ℝ) (hε : 0 < ε) (g : SoninL2) :
        fourierUnitary.symm (gammaClockCutoffPhysicalOperator ε R hε g) =
          gammaClockCutoffPhysicalOperator ε R hε (fourierUnitary.symm g) := by
      apply fourierUnitary.injective
      rw [fourierUnitary.apply_symm_apply, fourier_gammaClockCutoffPhysicalOperator,
        fourierUnitary.apply_symm_apply]
    obtain ⟨h,_⟩ := physical_domain_unitary fourierUnitary.symm hcomm ⟨fourierUnitary f,hf⟩
    simpa only [fourierUnitary.symm_apply_apply] using h
  · intro hf
    exact (gammaClockPhysicalOperator_fourier ⟨f,hf⟩).1


end RHTower
