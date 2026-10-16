import GaloisForLFunctions.RHTower.CHMDBoundStateInertia
import GaloisForLFunctions.RHTower.CHMDBirmanSchwingerBound
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization

/-!
# Finite compact test synthesis and the complete Weil form

For real compact tests with both polar samples zero, the complex Weil
quadratic form of a finite combination is exactly the complexification of
their original signed graph Gram matrix. No positivity premise is used.
-/

open MeasureTheory Set Filter Topology Complex Zeta23 Matrix
open scoped ComplexConjugate

noncomputable section

namespace RHTower.CHMDDoobGraph

open WeilWorkPBAP

private theorem compact_sum {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) (f : ι → ℝ → V) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → V))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i).add ih

theorem compact_synthesis {k : ℕ} (f : Fin k → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (c : Fin k → ℂ) :
    ContDiff ℝ 2 (fun x => ∑ i, c i * f i x) ∧
      HasCompactSupport (fun x => ∑ i, c i * f i x) := by
  refine ⟨ContDiff.sum fun i _ => contDiff_const.mul (hf i), ?_⟩
  have he : (fun x => ∑ i, c i * f i x) = ∑ i, c i • f i := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact compact_sum Finset.univ (fun i => c i • f i) (fun i => (hc i).smul_left)

private theorem real_synthesis {k : ℕ} (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (c : Fin k → ℝ) :
    ContDiff ℝ 2 (fun x => ∑ i, c i * f i x) ∧
      HasCompactSupport (fun x => ∑ i, c i * f i x) := by
  refine ⟨ContDiff.sum fun i _ => contDiff_const.mul (hf i), ?_⟩
  have he : (fun x => ∑ i, c i * f i x) = ∑ i, c i • f i := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact compact_sum Finset.univ (fun i => c i • f i) (fun i => (hc i).smul_left)

private theorem testLift_real_synthesis {k : ℕ} (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (c : Fin k → ℝ) :
    testLift (fun x => ∑ i, c i * f i x) (real_synthesis f hf hc c).1
      (real_synthesis f hf hc c).2 = ∑ i, c i • testLift (f i) (hf i) (hc i) := by
  apply source_projection_injective
  apply Lp.ext
  have he : (∑ i, c i • testLift (f i) (hf i) (hc i) : SourceGraph).val.fst =
      ∑ i, c i • (testLift (f i) (hf i) (hc i)).val.fst := by
    change sourceMap (∑ i, c i • testLift (f i) (hf i) (hc i)) = _
    simp only [map_sum, map_smul]
    rfl
  change ((testLift (fun x => ∑ i, c i * f i x)
      (real_synthesis f hf hc c).1 (real_synthesis f hf hc c).2).val.fst : ℝ → ℝ) =ᵐ[massMeasure]
    ((∑ i, c i • testLift (f i) (hf i) (hc i) : SourceGraph).val.fst : ℝ → ℝ)
  rw [he]
  have hall : ∀ᵐ x ∂massMeasure, ∀ i,
      (testLift (f i) (hf i) (hc i)).val.fst x = phiDoobInv (f i) x := by
    rw [Filter.eventually_all]
    exact fun i => testLift_source (f i) (hf i) (hc i)
  filter_upwards [testLift_source (fun x => ∑ i, c i * f i x) _ _,
    CHMDPolar.Lp_coeFn_sum_smul Finset.univ c
      (fun i => (testLift (f i) (hf i) (hc i)).val.fst), hall] with x h1 h2 h3
  rw [h1, h2]
  simp only [h3, phiDoobInv, Finset.sum_div, mul_div_assoc]

private theorem sourceEnergy_sum_eq {k : ℕ} (q : Fin k → SourceGraph) (c : Fin k → ℝ) :
    sourceEnergy (∑ i, c i • q i) =
      ∑ i, ∑ j, c i * c j * sourcePair (q i) (q j) := by
  have hsum (r : SourceGraph) : sourcePair (∑ i, c i • q i) r =
      ∑ i, c i * sourcePair (q i) r := by
    simp only [sourcePair, map_sum, map_smul, sum_inner, real_inner_smul_left]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← sourcePair_self, hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sourcePair_symm (q i), hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourcePair_symm (q j)]
  ring

private theorem real_synthesis_polar {k : ℕ} (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (c : Fin k → ℝ) (z : ℂ) (hp : ∀ i, paperFT (fun x => (f i x : ℂ)) z = 0) :
    paperFT (fun x => ((∑ i, c i * f i x : ℝ) : ℂ)) z = 0 := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [paperFT_finset_sum Finset.univ (fun i => (c i : ℂ))
    (f := fun i x => (f i x : ℂ))
    (fun i => Complex.continuous_ofReal.comp (hf i).continuous)
    (fun i => (hc i).comp_left Complex.ofReal_zero) z]
  simp only [hp, mul_zero, Finset.sum_const_zero]

private theorem re_W_real_synthesis {k : ℕ} (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (hp : ∀ i, paperFT (fun x => (f i x : ℂ)) (I/2) = 0 ∧
      paperFT (fun x => (f i x : ℂ)) (-I/2) = 0) (c : Fin k → ℝ) :
    (zetaZeroConfig.W (fun x => ((∑ i, c i * f i x : ℝ) : ℂ))
      (fun x => ((∑ i, c i * f i x : ℝ) : ℂ))).re =
      ∑ i, ∑ j, c i * c j * sourcePair (testLift (f i) (hf i) (hc i))
        (testLift (f j) (hf j) (hc j)) := by
  have h := real_synthesis f hf hc c
  rw [← CHMDPolar.sourceEnergy_phiDoobInv_eq_re_W h.1 h.2
    (real_synthesis_polar f hf hc c (I/2) fun i => (hp i).1)
    (by simpa only [neg_div] using real_synthesis_polar f hf hc c (-I/2) fun i => (hp i).2)]
  change sourceEnergy (testLift (fun x => ∑ i, c i * f i x) h.1 h.2) = _
  rw [testLift_real_synthesis, sourceEnergy_sum_eq]

/-- Complexification is literal: the original signed Gram is the complete
Weil quadratic form of the corresponding compact polar combination. -/
theorem re_W_compact_synthesis_eq_gram {k : ℕ} (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (hp : ∀ i, paperFT (fun x => (f i x : ℂ)) (I/2) = 0 ∧
      paperFT (fun x => (f i x : ℂ)) (-I/2) = 0) (c : Fin k → ℂ) :
    (zetaZeroConfig.W (fun x => ∑ i, c i * (f i x : ℂ))
      (fun x => ∑ i, c i * (f i x : ℂ))).re =
      (star c ⬝ᵥ Matrix.mulVec (fun i j =>
        (sourcePair (testLift (f i) (hf i) (hc i))
          (testLift (f j) (hf j) (hc j)) : ℂ)) c).re := by
  let F : ℝ → ℂ := fun x => ∑ i, c i * (f i x : ℂ)
  have hF := compact_synthesis (fun i x => (f i x : ℂ))
    (fun i => Complex.ofRealCLM.contDiff.comp (hf i))
    (fun i => (hc i).comp_left Complex.ofReal_zero) c
  let r : ℝ → ℝ := fun x => ∑ i, (c i).re * f i x
  let s : ℝ → ℝ := fun x => ∑ i, (c i).im * f i x
  have hr := real_synthesis f hf hc (fun i => (c i).re)
  have hs := real_synthesis f hf hc (fun i => (c i).im)
  have hsplit : (zetaZeroConfig.W F F).re =
      (zetaZeroConfig.W (fun x => (r x : ℂ)) (fun x => (r x : ℂ))).re +
      (zetaZeroConfig.W (fun x => (s x : ℂ)) (fun x => (s x : ℂ))).re := by
    have hrC : ContDiff ℝ 2 (fun x => (r x : ℂ)) := Complex.ofRealCLM.contDiff.comp hr.1
    have hsC : ContDiff ℝ 2 (fun x => (s x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs.1
    have hrc : HasCompactSupport (fun x => (r x : ℂ)) := hr.2.comp_left Complex.ofReal_zero
    have hsc : HasCompactSupport (fun x => (s x : ℂ)) := hs.2.comp_left Complex.ofReal_zero
    rw [zeta_W_eq_weilFullFunctional hF.1 hF.2,
      zeta_W_eq_weilFullFunctional hrC hrc, zeta_W_eq_weilFullFunctional hsC hsc]
    convert CHMDPolar.re_weilFullFunctional_split _ ⟨F, hF.1, hF.2⟩ using 1 <;>
      simp [F, r, s, paperRealPartTestFn, paperImagPartTestFn, Complex.mul_re, Complex.mul_im]
  change (zetaZeroConfig.W F F).re = _
  rw [hsplit]
  dsimp only [r, s]
  rw [re_W_real_synthesis f hf hc hp, re_W_real_synthesis f hf hc hp,
    ← Finset.sum_add_distrib]
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum,
    Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RHTower.CHMDDoobGraph
