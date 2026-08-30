import GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency
import GaloisForLFunctions.HTGeometry.GaussianShiftInformation

/-!
# Hellinger affinity and factorization sufficiency

The Bhattacharyya (Hellinger) affinity of two finite measures is defined through the
Radon--Nikodym derivatives against their sum.  It is computed by any common dominating measure,
it is multiplicative over independent packets, and a deterministic observer through which the
likelihood ratio factors preserves it exactly.  The last statement is the Hellinger companion of
the relative-entropy factorization sufficiency theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Integrating against a density is integrating against the weighted measure. -/
theorem lintegral_rnDeriv_mul' {μ lam : Measure α} [SigmaFinite lam]
    [μ.HaveLebesgueDecomposition lam] (h : μ ≪ lam) {F : α → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x * μ.rnDeriv lam x ∂lam = ∫⁻ x, F x ∂μ := by
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ lam h]
  rw [lintegral_withDensity_eq_lintegral_mul lam (Measure.measurable_rnDeriv _ _) hF]
  exact lintegral_congr fun x => mul_comm _ _

/-- Weighting the first coordinate of a composition product weights the first marginal. -/
theorem compProd_withDensity_fst (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ ⊗ₘ κ).withDensity (fun p => g p.1) = (μ.withDensity g) ⊗ₘ κ := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_compProd (by fun_prop)]
  rw [Measure.compProd_apply hs, lintegral_withDensity_eq_lintegral_mul μ hg
    (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun x => ?_
  have hind : ∀ y : β, s.indicator (fun p : α × β => g p.1) (x, y)
      = (Prod.mk x ⁻¹' s).indicator (fun _ => g x) y := by
    intro y
    by_cases h : (x, y) ∈ s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show y ∈ Prod.mk x ⁻¹' s from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show y ∉ Prod.mk x ⁻¹' s from h)]
  rw [lintegral_congr hind, lintegral_indicator (measurable_prodMk_left hs),
    setLIntegral_const]
  rfl

/-- **Bhattacharyya (Hellinger) affinity**, defined by the Radon--Nikodym derivatives of the two
measures against their sum. -/
def bhattacharyya (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) ∂(μ + ν)

theorem rpow_half_mul_sq (a b c : ℝ≥0∞) :
    (a * c * (b * c)) ^ (1 / 2 : ℝ) = (a * b) ^ (1 / 2 : ℝ) * c := by
  have hc : c * c = c ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, sq]
  rw [show a * c * (b * c) = a * b * (c * c) by ring, hc,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

/-- The affinity is computed by any common dominating measure. -/
theorem bhattacharyya_eq_lintegral (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lam : Measure α) [SigmaFinite lam] (hμ : μ ≪ lam) (hν : ν ≪ lam) :
    bhattacharyya μ ν = ∫⁻ x, (μ.rnDeriv lam x * ν.rnDeriv lam x) ^ (1 / 2 : ℝ) ∂lam := by
  have hκ : μ + ν ≪ lam := by
    intro s hs
    rw [Measure.add_apply, hμ hs, hν hs, add_zero]
  have hμκ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνκ : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hmul₁ := Measure.rnDeriv_mul_rnDeriv (κ := lam) hμκ
  have hmul₂ := Measure.rnDeriv_mul_rnDeriv (κ := lam) hνκ
  have hae : (fun x => (μ.rnDeriv lam x * ν.rnDeriv lam x) ^ (1 / 2 : ℝ))
      =ᵐ[lam] fun x => ((μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ))
        * (μ + ν).rnDeriv lam x := by
    filter_upwards [hmul₁, hmul₂] with x h1 h2
    rw [← h1, ← h2]
    exact rpow_half_mul_sq _ _ _
  rw [lintegral_congr_ae hae, bhattacharyya, lintegral_rnDeriv_mul' hκ (by fun_prop)]

/-- The affinity of two weighted copies of one measure is the integral of the geometric mean of
the two densities. -/
theorem bhattacharyya_withDensity (lam : Measure α) [SigmaFinite lam] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) [IsFiniteMeasure (lam.withDensity f)]
    [IsFiniteMeasure (lam.withDensity g)] :
    bhattacharyya (lam.withDensity f) (lam.withDensity g)
      = ∫⁻ x, (f x * g x) ^ (1 / 2 : ℝ) ∂lam := by
  rw [bhattacharyya_eq_lintegral _ _ lam (withDensity_absolutelyContinuous lam f)
    (withDensity_absolutelyContinuous lam g)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity lam hf, Measure.rnDeriv_withDensity lam hg]
    with x h1 h2
  rw [h1, h2]

/-- If the likelihood ratio is a genuine density, the affinity is the integral of its square
root. -/
theorem bhattacharyya_eq_lintegral_rpow {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → ℝ≥0∞} (hf : Measurable f) (hμ : μ = ν.withDensity f) :
    bhattacharyya μ ν = ∫⁻ x, (f x) ^ (1 / 2 : ℝ) ∂ν := by
  rw [bhattacharyya_eq_lintegral _ _ ν (hμ ▸ withDensity_absolutelyContinuous ν f)
    (Measure.AbsolutelyContinuous.rfl)]
  refine lintegral_congr_ae ?_
  filter_upwards [hμ ▸ Measure.rnDeriv_withDensity ν hf, Measure.rnDeriv_self ν] with x h1 h2
  rw [h1, h2, mul_one]

/-- **Hellinger factorization sufficiency.**  A deterministic observer through which the
likelihood ratio factors preserves the Hellinger affinity exactly. -/
theorem bhattacharyya_map_eq_of_density_comp {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {q : α → β} (hq : Measurable q) {g : β → ℝ≥0∞} (hg : Measurable g)
    (hμν : μ = ν.withDensity (g ∘ q)) :
    bhattacharyya μ ν = bhattacharyya (μ.map q) (ν.map q) := by
  haveI : IsFiniteMeasure (μ.map q) := by
    constructor
    rw [Measure.map_apply hq MeasurableSet.univ]
    exact measure_lt_top μ _
  haveI : IsFiniteMeasure (ν.map q) := by
    constructor
    rw [Measure.map_apply hq MeasurableSet.univ]
    exact measure_lt_top ν _
  have hmap : μ.map q = (ν.map q).withDensity g := by
    rw [hμν, map_withDensity_comp ν hq hg]
  rw [bhattacharyya_eq_lintegral_rpow (hg.comp hq) hμν,
    bhattacharyya_eq_lintegral_rpow hg hmap,
    lintegral_map (f := fun y => (g y) ^ (1 / 2 : ℝ)) (by fun_prop) hq]
  rfl

/-- The affinity of a probability law with itself is one. -/
theorem bhattacharyya_self (μ : Measure α) [IsProbabilityMeasure μ] :
    bhattacharyya μ μ = 1 := by
  rw [bhattacharyya_eq_lintegral μ μ μ Measure.AbsolutelyContinuous.rfl
    Measure.AbsolutelyContinuous.rfl]
  rw [show (∫⁻ x, (μ.rnDeriv μ x * μ.rnDeriv μ x) ^ (1 / 2 : ℝ) ∂μ) = ∫⁻ _, (1 : ℝ≥0∞) ∂μ from
    lintegral_congr_ae (by filter_upwards [Measure.rnDeriv_self μ] with x hx; simp [hx])]
  simp

/-- **The Hellinger affinity is multiplicative over independent packets.** -/
theorem bhattacharyya_pi {d : ℕ} {Z : Type*} [MeasurableSpace Z] (μ ν : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    bhattacharyya (Measure.pi fun _ : Fin d => μ) (Measure.pi fun _ : Fin d => ν)
      = bhattacharyya μ ν ^ d := by
  set lam : Measure Z := μ + ν with hlam
  have hμl : μ ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνl : ν ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set f : Z → ℝ≥0∞ := μ.rnDeriv lam with hf
  set g : Z → ℝ≥0∞ := ν.rnDeriv lam with hg
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hgm : Measurable g := Measure.measurable_rnDeriv _ _
  have hμd : μ = lam.withDensity f := (Measure.withDensity_rnDeriv_eq μ lam hμl).symm
  have hνd : ν = lam.withDensity g := (Measure.withDensity_rnDeriv_eq ν lam hνl).symm
  haveI : IsFiniteMeasure (lam.withDensity f) := hμd ▸ ‹IsFiniteMeasure μ›
  haveI : IsFiniteMeasure (lam.withDensity g) := hνd ▸ ‹IsFiniteMeasure ν›
  have hpiμ : (Measure.pi fun _ : Fin d => μ)
      = (Measure.pi fun _ : Fin d => lam).withDensity (fun x => ∏ i, f (x i)) := by
    rw [pi_withDensity (fun _ : Fin d => lam) (f := fun _ => f) (fun _ => hfm)]
    exact congrArg Measure.pi (funext fun _ => hμd)
  have hpiν : (Measure.pi fun _ : Fin d => ν)
      = (Measure.pi fun _ : Fin d => lam).withDensity (fun x => ∏ i, g (x i)) := by
    rw [pi_withDensity (fun _ : Fin d => lam) (f := fun _ => g) (fun _ => hgm)]
    exact congrArg Measure.pi (funext fun _ => hνd)
  rw [hpiμ, hpiν]
  haveI : IsFiniteMeasure ((Measure.pi fun _ : Fin d => lam).withDensity
      (fun x => ∏ i, f (x i))) := hpiμ ▸ inferInstance
  haveI : IsFiniteMeasure ((Measure.pi fun _ : Fin d => lam).withDensity
      (fun x => ∏ i, g (x i))) := hpiν ▸ inferInstance
  rw [bhattacharyya_withDensity _ (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → Z, ((∏ i, f (x i)) * ∏ i, g (x i)) ^ (1 / 2 : ℝ)
      = ∏ i, (f (x i) * g (x i)) ^ (1 / 2 : ℝ) := by
    intro x
    rw [← Finset.prod_mul_distrib, ENNReal.prod_rpow_of_nonneg (by norm_num)]
  rw [lintegral_congr hprod,
    lintegral_pi_prod (fun _ : Fin d => lam) (f := fun _ z => (f z * g z) ^ (1 / 2 : ℝ))
      (fun _ => by fun_prop),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1

end

end GaloisForLFunctions.HTGeometry
