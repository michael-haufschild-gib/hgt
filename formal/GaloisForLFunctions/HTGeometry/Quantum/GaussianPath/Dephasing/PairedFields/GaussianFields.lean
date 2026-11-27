import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments

/-! # Rotating two independent physical Pauli fields -/

open MeasureTheory ProbabilityTheory Matrix Finset Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
noncomputable section

abbrev Coeff (n : ℕ) := PathLabel n → ℝ
abbrev FieldPair (n : ℕ) := PathLabel n → ℝ × ℝ
abbrev fieldLaw (n : ℕ) : Measure (Coeff n) := Measure.pi fun _ => gaussianReal 0 1
abbrev pairLaw (n : ℕ) : Measure (FieldPair n) :=
  Measure.pi fun _ => (gaussianReal 0 1).prod (gaussianReal 0 1)

def rotated {n : ℕ} (a b : ℝ) (x : FieldPair n) : Coeff n := fun i => a*(x i).1+b*(x i).2

def generator {n : ℕ} (x : Coeff n) :
    selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
  ⟨pathHamiltonian (WithLp.toLp 2 x),isSelfAdjoint_pathHamiltonian _⟩

/-- Every unit direction of a pair of independent Gaussian coefficient fields
has the original nearest-neighbour chain law. -/
theorem rotated_law (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    MeasurePreserving (rotated (n:=n) a b) (pairLaw n) (fieldLaw n) := by
  refine measurePreserving_pi (fun _ : PathLabel n => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ => gaussianReal 0 1) (f:=fun _ z => a*z.1+b*z.2) ?_
  intro i
  let γ := gaussianReal 0 1
  let v (c : ℝ) : NNReal := NNReal.mk (c^2) (sq_nonneg _)
  have scale (c : ℝ) : MeasurePreserving (fun z : ℝ => c*z) γ (gaussianReal 0 (v c)) := by
    refine ⟨by fun_prop,?_⟩
    simp only [γ,gaussianReal_map_const_mul,mul_zero,mul_one,v]
  have h := gaussianReal_add_gaussianReal_of_indepFun
    (indepFun_prod (μ:=γ) (ν:=γ) (X:=fun z : ℝ => a*z) (Y:=fun z : ℝ => b*z)
      (by fun_prop) (by fun_prop))
    ((scale a).comp (measurePreserving_fst (μ:=γ) (ν:=γ))).map_eq
    ((scale b).comp (measurePreserving_snd (μ:=γ) (ν:=γ))).map_eq
  have hv : v a+v b=1 := NNReal.eq hab
  rw [zero_add,hv] at h
  exact ⟨by fun_prop,h⟩

private theorem spread_reindex {I J : Type*} [Fintype I] [Fintype J] (e : J ≃ I) (v : I → ℝ) :
    spread (v ∘ e) = spread v := by
  unfold spread
  simp only [Function.comp_apply]
  calc
    _ = ∑ i : J, ∑ j : I, |v (e i)-v j| :=
      sum_congr rfl fun i _ => e.sum_comp (fun j => |v (e i)-v j|)
    _ = _ := e.sum_comp (fun i => ∑ j, |v i-v j|)

private theorem continuous_field_spread (n : ℕ) :
    Continuous (fun x : Coeff n => spectralSpread (generator x)) := by
  let e := Fintype.equivFin (Fin (n+2) → Bool)
  have hc : Continuous (fun x : Coeff n => (generator x).val) := by
    simp only [generator,pathHamiltonian_eq_sum]
    fun_prop
  have hg : Continuous (fun x : Coeff n => Matrix.reindex e e (generator x).val) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp hc)
  let E (x : Coeff n) := (generator x).2.isHermitian.eigenvalues
  let F (x : Coeff n) := sortedTuple (((generator x).2.isHermitian.reindex e).eigenvalues)
  have hf : Continuous F := continuous_sortedTuple_eigenvalues hg _
  have he (x : Coeff n) : spread (F x)=spectralSpread (generator x) := by
    unfold F
    rw [sortedTuple_eigenvalues_reindex]
    exact (spread_reindex (Tuple.sort (E x ∘ e.symm)) _).trans (spread_reindex e.symm (E x))
  simp_rw [←he]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_apply i).comp hf).sub ((continuous_apply j).comp hf)).abs

/-- The mean spread is bounded by twice the number of ordered pairs times
the root-mean-square energy. The path trace gives the exact second moment. -/
theorem gaussian_spread_moment (n : ℕ) :
    Integrable (fun x : Coeff n => spectralSpread (generator x)) (fieldLaw n) ∧
    (∫ x : Coeff n, spectralSpread (generator x) ∂fieldLaw n) ≤ 2*((2:ℝ)^(n+2))^2*Real.sqrt (Fintype.card (PathLabel n)) := by
  let D := (2:ℝ)^(n+2)
  let m : ℝ := Fintype.card (PathLabel n)
  let r := Real.sqrt m
  let Q (x : Coeff n) := ∑ i, (x i)^2
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0<r := Real.sqrt_pos.mpr hm
  have hr₂ : r^2=m := Real.sq_sqrt hm.le
  have hd : (Fintype.card (Fin (n+2) → Bool):ℝ)=D := by simp [D]
  have hi : Integrable (fun t : ℝ => t^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ:=0) (v:=1) 2 (by simp)).integrable_sq
  have hp (i : PathLabel n) := measurePreserving_eval (fun _ : PathLabel n => gaussianReal 0 1) i
  have hQi : Integrable Q (fieldLaw n) :=
    integrable_finsetSum _ fun i _ => (hp i).integrable_comp_of_integrable hi
  have hQm : (∫ x, Q x ∂fieldLaw n)=m := by
    have hi' (i : PathLabel n) : Integrable (fun x : Coeff n => (x i)^2) (fieldLaw n) :=
      (hp i).integrable_comp_of_integrable hi
    change (∫ x : Coeff n, ∑ i, (x i)^2 ∂fieldLaw n)=m
    rw [integral_finsetSum univ (fun i _ => hi' i)]
    have h (i : PathLabel n) : (∫ x : Coeff n, (x i)^2 ∂fieldLaw n)=1 := by
      have ht := integral_map (μ:=fieldLaw n) (hp i).measurable.aemeasurable
        (f:=fun z : ℝ => z^2) (by fun_prop)
      rw [(hp i).map_eq,gaussianZero_integral_sq] at ht
      exact ht.symm
    simp only [h,sum_const,card_univ,nsmul_eq_mul,mul_one,m]
  let major (x : Coeff n) := D^2*(m+Q x)/r
  have hmajor : Integrable major (fieldLaw n) :=
    (((integrable_const m).add hQi).const_mul (D^2)).div_const r
  have hbound (x : Coeff n) : spectralSpread (generator x) ≤ major x := by
    let E := (generator x).2.isHermitian.eigenvalues
    have hmom : (∑ i, E i^2)=D*Q x := by
      simpa only [E,generator,D,Q,WithLp.ofLp_toLp,Nat.cast_pow,Nat.cast_ofNat] using
        (FluxOccupation.path_spectral_moments (n:=n) (WithLp.toLp 2 x)).2
    have h (i j : Fin (n+2) → Bool) : |E i-E j| *r ≤ (m+E i^2)/2+(m+E j^2)/2 := by
      have ha (z : ℝ) : |z| *r ≤ (m+z^2)/2 := by
        nlinarith only [sq_nonneg (|z|-r),sq_abs z,hr₂]
      have ht := mul_le_mul_of_nonneg_right (abs_sub (E i) (E j)) hr.le
      linarith only [ht,ha (E i),ha (E j)]
    apply (le_div_iff₀ hr).mpr
    change (∑ i, ∑ j, |E i-E j|)*r ≤ _
    simp_rw [sum_mul]
    apply (sum_le_sum (s:=univ) fun i _ => sum_le_sum (s:=univ) fun j _ => h i j).trans_eq
    simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←sum_div,←mul_sum,hd,hmom]
    ring
  have hnon (x : Coeff n) : 0 ≤ spectralSpread (generator x) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hS := hmajor.mono' (continuous_field_spread n).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hnon x)] using hbound x)
  refine ⟨hS,(integral_mono hS hmajor hbound).trans_eq ?_⟩
  change (∫ x, D^2*(m+Q x)/r ∂fieldLaw n)=2*D^2*r
  rw [integral_div,integral_const_mul,integral_add (integrable_const _) hQi,integral_const,
    probReal_univ,one_smul,hQm,div_eq_iff hr.ne']
  rw [←hr₂]
  ring

#print axioms rotated_law
#print axioms gaussian_spread_moment
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
