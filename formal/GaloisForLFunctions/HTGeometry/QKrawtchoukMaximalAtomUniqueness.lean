import GaloisForLFunctions.HTGeometry.QKrawtchoukMaximalAtoms
import GaloisForLFunctions.HTGeometry.KernelOffDiag

/-!
# Equality in the inverse-q Hermite maximal-atom bound

The equality mechanism in arXiv:2609.24149, Section 6, supplies the missing
selection step: a measure attaining the maximal atom must be carried by one
Nevanlinna denominator fiber. The proof uses the actual reproducing kernels.
After removing the selected atom their squared integrals tend to zero;
Fatou's lemma forces the limiting kernel to vanish almost everywhere there.
The B,D Wronskian then identifies the fiber, whose measure is already unique.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace HTGeometry

private theorem kernel_sq_integrable {s : ℕ → ℝ} (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (n : ℕ) (x : ℝ) :
    Integrable (fun y => ((cdKernel s n x).eval y) ^ 2) (μ : Measure ℝ) := by
  refine (integrable_eval (fun k => (hm k).1) ((cdKernel s n x) ^ (2 : ℕ))).congr
    (ae_of_all _ fun y => ?_)
  simp only [Polynomial.eval_pow]

private theorem kernel_sq_integral {s : ℕ → ℝ} (h : PositiveMomentForm s)
    (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (n : ℕ) (x : ℝ) :
    (∫ y, ((cdKernel s n x).eval y) ^ 2 ∂(μ : Measure ℝ)) =
      (cdKernel s n x).eval x := by
  have hi := momentFunctional_mul_eq_integral s (fun k => (hm k).2.symm)
    (fun k => (hm k).1) (cdKernel s n x) (cdKernel s n x)
  rw [← momentInner_def, momentInner_cdKernel_cdKernel h n x x] at hi
  simpa only [pow_two] using hi.symm

private theorem kernel_sq_off_atom {s : ℕ → ℝ} (h : PositiveMomentForm s)
    (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (n : ℕ) (x : ℝ) :
    (∫ y in ({x} : Set ℝ)ᶜ, ((cdKernel s n x).eval y) ^ 2 ∂(μ : Measure ℝ)) =
      (cdKernel s n x).eval x -
        (μ : Measure ℝ).real {x} * ((cdKernel s n x).eval x) ^ 2 := by
  rw [setIntegral_compl (measurableSet_singleton x) (kernel_sq_integrable μ hm n x),
    kernel_sq_integral h μ hm n x, integral_singleton, smul_eq_mul]

private theorem maximal_atom_kernel_vanishes {s : ℕ → ℝ} (h : PositiveMomentForm s)
    (hb : BoundedKernel s 0) (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (x : ℝ) (hmax : (μ : Measure ℝ).real {x} = christoffelLimit s x) :
    ∀ᵐ y ∂(μ : Measure ℝ), y ≠ x → kernelInf s y x = 0 := by
  have hlimit_inv : christoffelLimit s x = (kernelInf s x x)⁻¹ := by
    simpa only [kernelInf, pow_two] using
      christoffelLimit_eq_inv_tsum h x (summable_diag_real h hb x)
  have hlimit_pos := christoffelLimit_pos_of_boundedKernel h x (boundedKernel_global h hb x)
  have hκ : kernelInf s x x ≠ 0 := by
    intro hz
    rw [hlimit_inv, hz, inv_zero] at hlimit_pos
    exact (lt_irrefl 0) hlimit_pos
  have hmass : (μ : Measure ℝ).real {x} * kernelInf s x x = 1 := by
    rw [hmax, hlimit_inv]
    exact inv_mul_cancel₀ hκ
  have hcancel : kernelInf s x x - (μ : Measure ℝ).real {x} * (kernelInf s x x) ^ 2 = 0 := by
    rw [pow_two, ← mul_assoc, hmass, one_mul, sub_self]
  have hd := tendsto_cdKernel_eval h hb x x
  have he : Tendsto (fun n =>
      ∫ y in ({x} : Set ℝ)ᶜ, ((cdKernel s n x).eval y) ^ 2 ∂(μ : Measure ℝ))
      atTop (𝓝 0) := by
    have ht := hd.sub ((hd.pow 2).const_mul ((μ : Measure ℝ).real {x}))
    rw [hcancel] at ht
    simpa only [kernel_sq_off_atom h μ hm] using ht
  let ρ := (μ : Measure ℝ).restrict ({x} : Set ℝ)ᶜ
  have hconv (y : ℝ) : Tendsto
      (fun n => ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((kernelInf s y x) ^ 2))) := by
    simpa only [kernelInf_comm s x y] using
      ENNReal.tendsto_ofReal ((tendsto_cdKernel_eval h hb x y).pow 2)
  have hmeas (n : ℕ) : Measurable
      (fun y => ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2)) := by fun_prop
  have hint (n : ℕ) :
      (∫⁻ y, ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2) ∂ρ) =
        ENNReal.ofReal (∫ y in ({x} : Set ℝ)ᶜ,
          ((cdKernel s n x).eval y) ^ 2 ∂(μ : Measure ℝ)) :=
    (ofReal_integral_eq_lintegral_ofReal (kernel_sq_integrable μ hm n x).restrict
      (ae_of_all ρ fun y => sq_nonneg _)).symm
  have hzero : Tendsto
      (fun n => ∫⁻ y, ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2) ∂ρ)
      atTop (𝓝 0) := by
    simpa only [hint, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal he
  have hfatou : (∫⁻ y, ENNReal.ofReal ((kernelInf s y x) ^ 2) ∂ρ) ≤
      liminf (fun n => ∫⁻ y, ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2) ∂ρ) atTop := by
    calc
      _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal (((cdKernel s n x).eval y) ^ 2)) atTop ∂ρ :=
        lintegral_congr_ae (ae_of_all ρ fun y => (hconv y).liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le hmeas
  have hzint : (∫⁻ y, ENNReal.ofReal ((kernelInf s y x) ^ 2) ∂ρ) = 0 :=
    le_antisymm (hfatou.trans_eq hzero.liminf_eq) zero_le
  have hcont : Continuous (fun y => kernelInf s y x) :=
    continuous_iff_continuousAt.mpr fun y => continuousAt_kernelInf h hb x y
  have hae := (lintegral_eq_zero_iff
    (ENNReal.measurable_ofReal.comp (hcont.pow 2).measurable)).mp hzint
  have hz : ∀ᵐ y ∂ρ, kernelInf s y x = 0 := by
    filter_upwards [hae] with y hy
    have hh := ENNReal.ofReal_eq_zero.mp hy
    change (kernelInf s y x) ^ 2 ≤ 0 at hh
    nlinarith [sq_nonneg (kernelInf s y x)]
  have hr := (ae_restrict_iff' (measurableSet_singleton x).compl).mp hz
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr

private theorem maximal_atom_measure_unique {s : ℕ → ℝ} (h : PositiveMomentForm s)
    (hb : BoundedKernel s 0) (h0 : s 0 = 1) (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (x : ℝ) (hmax : (μ : Measure ℝ).real {x} = christoffelLimit s x) :
    μ = nevLeaf h hb h0 ((nevMatrixDataInf h hb).projectiveLabel x) := by
  have hk := maximal_atom_kernel_vanishes h hb μ hm x hmax
  apply ProbabilityMeasure.toMeasure_injective
  by_cases hx : (nevMatrixDataInf h hb).B x = 0
  · rw [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.projectiveLabel,
      if_pos hx]
    apply nevLeaf_infinity_unique h hb h0 hm
    apply ae_iff.mp
    filter_upwards [hk] with y hy
    change nevBrealInf s y = 0
    by_cases hyx : y = x
    · subst y
      exact hx
    · have hf := nevBrealInf_factor_at_zero h hb hx y
      rw [hy hyx, mul_zero, mul_zero] at hf
      exact (mul_eq_zero.mp hf).resolve_right
        (nevDrealInf_ne_zero_of_nevBrealInf_eq_zero h hb hx)
  · rw [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.projectiveLabel,
      if_neg hx]
    let tau := (nevMatrixDataInf h hb).D x / (nevMatrixDataInf h hb).B x
    have hbase : nevBrealInf s x * tau - nevDrealInf s x = 0 := by
      dsimp [tau]
      change nevBrealInf s x ≠ 0 at hx
      field_simp
      ring
    apply nevLeaf_unique h hb h0 tau hm
    apply ae_iff.mp
    filter_upwards [hk] with y hy
    change nevBrealInf s y * tau - nevDrealInf s y = 0
    by_cases hyx : y = x
    · simpa only [hyx] using hbase
    · have hf := nevDenominator_factor_at_fiber h hb hbase y
      rw [hy hyx, mul_zero, mul_zero] at hf
      exact (mul_eq_zero.mp hf).resolve_right hx

/-- Equality in the atom bound selects exactly one representing probability
measure. The positivity and indeterminacy inputs are proved for this edge. -/
theorem inverseQHermite_maximal_atom_unique (t u x : ℝ) :
    ∃! μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (inverseQHermiteMoment t u)
        (μ : Measure ℝ) ∧
      (μ : Measure ℝ).real {x} = christoffelLimit (inverseQHermiteMoment t u) x := by
  refine ⟨inverseQHermiteAtomMeasure t u x,
    ⟨inverseQHermiteAtomMeasure_moments t u x,
      inverseQHermiteAtomMeasure_atom_real t u x⟩, ?_⟩
  intro μ hμ
  exact maximal_atom_measure_unique (inverseQHermiteMoment_positive t u)
    (inverseQHermiteMoment_boundedKernel t u 0) (inverseQHermiteMoment_zero t u)
    μ hμ.1 x hμ.2

end HTGeometry
