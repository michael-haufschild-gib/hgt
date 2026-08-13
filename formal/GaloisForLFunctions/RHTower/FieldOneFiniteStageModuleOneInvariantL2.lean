import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassHaarSplitting
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Module-one invariant `L²` vectors are exactly radial vectors

For the normalized Haar splitting `C_S ≃ K_S × ℝ₊ˣ`, this file proves
the non-formal half of the source carrier identification:

`L²(K_S × ℝ₊ˣ)^{K_S} = {f ∘ Prod.snd | f ∈ L²(ℝ₊ˣ)}`.

The converse to obvious radial invariance uses a countable dense family of
left translations.  Fubini transfers their simultaneous invariance to almost
every compact-group fiber; ergodicity of the regular Haar action makes that
fiber essentially constant.  Haar averaging chooses the constants measurably,
and the resulting radial function is proved square integrable.  Thus the final
unitary is onto the literal fixed-point subspace, not an abstract proxy.
-/

open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set Filter Topology TopologicalSpace

theorem ae_eq_const_of_dense_left_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [R1Space G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    {g : G → ℂ} (hgm : AEStronglyMeasurable g μ)
    (hd : Dense {a : G | (fun x => g (a * x)) =ᵐ[μ] g}) :
    ∃ c : ℂ, g =ᵐ[μ] fun _ => c := by
  borelize ℂ
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  letI := ht.secondCountableTopology
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating
    MeasurableSet hgt ?_
  intro U hU
  have hdinv : Dense {a : G |
      (a • ·) ⁻¹' (g ⁻¹' U) =ᵐ[μ] g ⁻¹' U} := by
    apply hd.mono
    intro a ha
    rw [mem_setOf_eq] at ha ⊢
    exact (ha.mono fun x hx => by
      simp only [mem_preimage]
      change g (a * x) ∈ U ↔ g x ∈ U
      change g (a * x) = g x at hx
      rw [hx]).set_eq
  have hc := aeconst_of_dense_setOf_preimage_smul_ae
    (M := G) (X := G) (μ := μ)
    (hgm.aemeasurable.nullMeasurable hU) hdinv
  simpa only [eventuallyConst_set, mem_preimage] using hc

theorem fieldOneFiniteStageInvariant_mem_radialSubmodule
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageSplitProductL2 S)
    (hf : f ∈ fieldOneFiniteStageProductModuleOneInvariantSubmodule S) :
    f ∈ fieldOneFiniteStageRadialSubmodule S := by
  let K := FieldOneFiniteStageModuleOneClass S
  let μK := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S
  let ν := fieldOnePositiveUnitsHaarMeasure
  let μP := fieldOneFiniteStageSplitProductHaarMeasure S
  let F : K × ℝ≥0ˣ → ℂ := (Lp.memLp f).1.mk f
  have hFstrong : StronglyMeasurable F := (Lp.memLp f).1.stronglyMeasurable_mk
  have hFae : F =ᵐ[μP] f := (Lp.memLp f).1.ae_eq_mk.symm
  let g : ℝ≥0ˣ → ℂ := fun r => ∫ k, F (k, r) ∂μK
  have hgstrong : StronglyMeasurable g := by
    exact hFstrong.integral_prod_left'
  have htranslate (a : K) :
      (fun x : K × ℝ≥0ˣ => F ((a, 1) * x)) =ᵐ[μP] F := by
    have hfix := hf a⁻¹
    change Lp.compMeasurePreserving (((a⁻¹)⁻¹, 1) * ·)
        (measurePreserving_mul_left μP ((a⁻¹)⁻¹, 1)) f = f at hfix
    have hfix' : Lp.compMeasurePreserving ((a, 1) * ·)
        (measurePreserving_mul_left μP (a, 1)) f = f := by
      simpa using hfix
    have hcomp := Lp.coeFn_compMeasurePreserving f
      (measurePreserving_mul_left μP (a, 1))
    rw [hfix'] at hcomp
    have hraw : (fun x : K × ℝ≥0ˣ => f ((a, 1) * x)) =ᵐ[μP] f :=
      hcomp.symm
    have hFact := (measurePreserving_mul_left μP (a, 1)).quasiMeasurePreserving
      |>.ae_eq_comp hFae
    filter_upwards [hFact, hraw, hFae] with x hx hrawx hFx
    calc
      F ((a, 1) * x) = f ((a, 1) * x) := hx
      _ = f x := hrawx
      _ = F x := hFx.symm
  have hdenseFiber : ∀ᵐ r ∂ν,
      Dense {a : K |
        (fun k : K => F (a * k, r)) =ᵐ[μK] fun k => F (k, r)} := by
    have hn (n : ℕ) : ∀ᵐ r ∂ν,
        (fun k : K => F (TopologicalSpace.denseSeq K n * k, r)) =ᵐ[μK]
          fun k => F (k, r) := by
      have hprod := htranslate (TopologicalSpace.denseSeq K n)
      have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := μK)).quasiMeasurePreserving
        |>.ae_eq_comp hprod
      have hiter := Measure.ae_ae_of_ae_prod hswap
      filter_upwards [hiter] with r hr
      filter_upwards [hr] with k hk
      have hpair :
          ((TopologicalSpace.denseSeq K n, 1) * (k, r)) =
            (TopologicalSpace.denseSeq K n * k, r) := by
        apply Prod.ext <;> simp
      change F ((TopologicalSpace.denseSeq K n, 1) * (k, r)) =
        F (k, r) at hk
      rw [hpair] at hk
      exact hk
    filter_upwards [eventually_countable_forall.2 hn] with r hr
    apply (TopologicalSpace.denseRange_denseSeq K).mono
    rintro a ⟨n, rfl⟩
    exact hr n
  have hFiberMeas : ∀ᵐ r ∂ν,
      AEStronglyMeasurable (fun k : K => F (k, r)) μK := by
    exact hFstrong.aestronglyMeasurable.prodMk_right
  have hFiberConst : ∀ᵐ r ∂ν,
      ∃ c : ℂ, (fun k : K => F (k, r)) =ᵐ[μK] fun _ => c := by
    filter_upwards [hFiberMeas, hdenseFiber] with r hmeas hdense
    exact ae_eq_const_of_dense_left_mul hmeas hdense
  have hFiberRadial : ∀ᵐ r ∂ν,
      (fun k : K => F (k, r)) =ᵐ[μK] fun _ => g r := by
    filter_upwards [hFiberConst] with r hr
    rcases hr with ⟨c, hc⟩
    have hgc : g r = c := by
      change (∫ k, F (k, r) ∂μK) = c
      rw [integral_congr_ae hc]
      simp
    exact hc.trans (Eventually.of_forall fun _ => hgc.symm)
  have hswapMeas : MeasurableSet
      {z : ℝ≥0ˣ × K | F (z.2, z.1) = g z.1} := by
    apply measurableSet_eq_fun
    · exact hFstrong.measurable.comp measurable_swap
    · exact hgstrong.measurable.comp measurable_fst
  have hswapRadial :
      (fun z : ℝ≥0ˣ × K => F (z.2, z.1)) =ᵐ[ν.prod μK]
        fun z => g z.1 := by
    exact (Measure.ae_prod_iff_ae_ae hswapMeas).2 hFiberRadial
  have hFRadial : F =ᵐ[μP] fun x => g x.2 := by
    have hcomp := (Measure.measurePreserving_swap (μ := μK) (ν := ν)).quasiMeasurePreserving
      |>.ae_eq_comp hswapRadial
    change F =ᵐ[μK.prod ν] fun x => g x.2
    filter_upwards [hcomp] with x hx
    rcases x with ⟨k, r⟩
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hx
  have hfRadial : (fun x : K × ℝ≥0ˣ => f x) =ᵐ[μP] fun x => g x.2 :=
    hFae.symm.trans hFRadial
  have hgMemLp : MemLp g 2 ν := by
    have hgComp : MemLp (fun x : K × ℝ≥0ˣ => g x.2) 2 μP :=
      (Lp.memLp f).congr_norm hgstrong.aestronglyMeasurable.comp_snd
        (hfRadial.mono fun _ hx => congrArg norm hx)
    have hsnd : MeasurePreserving Prod.snd μP ν := by
      dsimp [μP, μK, ν]
      exact measurePreserving_snd
        (μ := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
        (ν := fieldOnePositiveUnitsHaarMeasure)
    have hmap := memLp_map_measure_iff
      (f := Prod.snd) (g := g) (μ := μP) (p := (2 : ℝ≥0∞))
      (by
        rw [hsnd.map_eq]
        exact hgstrong.aestronglyMeasurable)
      measurable_snd.aemeasurable
    rw [hsnd.map_eq] at hmap
    exact hmap.mpr hgComp
  let gLp : FieldOnePositiveUnitsL2 := hgMemLp.toLp g
  refine ⟨gLp, ?_⟩
  change fieldOneFiniteStageRadialInclusion S gLp = f
  apply Lp.ext
  have hgLp := fieldOneFiniteStageRadialInclusion_ae S gLp
  have hcoe := hgMemLp.coeFn_toLp
  have hcoe' := (measurePreserving_snd (μ := μK) (ν := ν)).quasiMeasurePreserving
    |>.ae_eq_comp hcoe
  filter_upwards [hgLp, hcoe', hfRadial] with x hinc hgx hfx
  rw [hinc]
  change gLp x.2 = g x.2 at hgx
  exact hgx.trans hfx.symm

theorem fieldOneFiniteStageRadialSubmodule_eq_invariants
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageRadialSubmodule S =
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S := by
  apply le_antisymm
  · exact fieldOneFiniteStageRadialSubmodule_le_invariants S
  · intro f hf
    exact fieldOneFiniteStageInvariant_mem_radialSubmodule S f hf

def fieldOneFiniteStagePositiveToProductInvariants
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOnePositiveUnitsL2 →ₗᵢ[ℂ]
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S where
  toFun f := ⟨fieldOneFiniteStageRadialInclusion S f,
    fieldOneFiniteStageRadialInclusion_mem_invariants S f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (fieldOneFiniteStageRadialInclusion S) f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (fieldOneFiniteStageRadialInclusion S) c f
  norm_map' f := (fieldOneFiniteStageRadialInclusion S).norm_map f

theorem fieldOneFiniteStagePositiveToProductInvariants_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneFiniteStagePositiveToProductInvariants S) := by
  intro f
  have hfRadial := fieldOneFiniteStageInvariant_mem_radialSubmodule S f.1 f.2
  rcases hfRadial with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

def fieldOneFiniteStagePositiveProductInvariantUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOnePositiveUnitsL2 ≃ₗᵢ[ℂ]
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S :=
  LinearIsometryEquiv.ofSurjective
    (fieldOneFiniteStagePositiveToProductInvariants S)
    (fieldOneFiniteStagePositiveToProductInvariants_surjective S)

end

end GaloisForLFunctions.RHTower
