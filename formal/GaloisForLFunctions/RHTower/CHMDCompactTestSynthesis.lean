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

private theorem re_W_split (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    (zetaZeroConfig.W f f).re =
      (zetaZeroConfig.W (fun x => ((f x).re : ℂ)) (fun x => ((f x).re : ℂ))).re +
      (zetaZeroConfig.W (fun x => ((f x).im : ℂ)) (fun x => ((f x).im : ℂ))).re := by
  have hr : ContDiff ℝ 2 (fun x => ((f x).re : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf)
  have hi : ContDiff ℝ 2 (fun x => ((f x).im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf)
  have hrc : HasCompactSupport (fun x => ((f x).re : ℂ)) :=
    hc.comp_left (g := fun z : ℂ => (z.re : ℂ)) (by simp)
  have hic : HasCompactSupport (fun x => ((f x).im : ℂ)) :=
    hc.comp_left (g := fun z : ℂ => (z.im : ℂ)) (by simp)
  rw [zeta_W_eq_weilFullFunctional hf hc, zeta_W_eq_weilFullFunctional hr hrc,
    zeta_W_eq_weilFullFunctional hi hic]
  exact CHMDPolar.re_weilFullFunctional_split _ ⟨f, hf, hc⟩

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
  have hF : ContDiff ℝ 2 F ∧ HasCompactSupport F := compact_synthesis (fun i x => (f i x : ℂ))
    (fun i => Complex.ofRealCLM.contDiff.comp (hf i))
    (fun i => (hc i).comp_left Complex.ofReal_zero) c
  let r : ℝ → ℝ := fun x => ∑ i, (c i).re * f i x
  let s : ℝ → ℝ := fun x => ∑ i, (c i).im * f i x
  have hre (x : ℝ) : (F x).re = r x := by simp [F, r, Complex.mul_re]
  have him (x : ℝ) : (F x).im = s x := by simp [F, s, Complex.mul_im]
  have hsplit := re_W_split F hF.1 hF.2
  simp only [hre, him] at hsplit
  change (zetaZeroConfig.W F F).re = _
  rw [hsplit]
  dsimp only [r, s]
  rw [re_W_real_synthesis f hf hc hp, re_W_real_synthesis f hf hc hp,
    ← Finset.sum_add_distrib]
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum,
    Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RHTower.CHMDDoobGraph
