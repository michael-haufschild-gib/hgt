import GaloisForLFunctions.RHTower.FZZCigarScreeningChargeMoments

/-!
# Original screening integrals in monic coefficient coordinates

The coefficient map sends a full ordered list of complex screening positions
`w` to the non-leading coefficients of `product_j (X - w_j)`. Its actual real
Jacobian is the original squared Vandermonde, including at collisions.

Ordering by distinct real parts gives disjoint open chambers. The coefficient
map is injective on each chamber, all chamber images agree, and the union has
null complement. The exceptional coefficient image is also null. Factorization
over the complex numbers proves surjectivity. Applying change of variables on
every chamber derives the exact factorial multiplicity in the original integral.

The finite-cutoff theorem transports the original outer boundary and every
puncture exclusion to their full coefficient image. Every opposite-charge
inverse sixth power remains as a polynomial evaluation. Original admission
then proves admission of the transformed weight before the Bochner identity.

All public theorems have only integer, position, cutoff or function data. Count
zero, empty cutoff domains and coincident fixed positions are covered. Removing
cutoffs, deriving the affine beta integral, continuing screening count and
producing the complete physical mixed Ward identity remain separate obligations.
-/

open Polynomial Finset Matrix MeasureTheory Set Metric
open scoped Topology ENNReal
noncomputable section
namespace GaloisForLFunctions.RHTower

def fzzScreeningRootPolynomial {n : ℕ} (w : Fin n → ℂ) : ℂ[X] :=
  ∏ j, (X-C (w j))

def fzzScreeningRootCoefficients {n : ℕ} (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (fzzScreeningRootPolynomial w).coeff i.val

def fzzScreeningRootJacobian {n : ℕ} (w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun i j => -((∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]).coeff i.val)

private theorem rootCoeff_contDiff_aux {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :
    ContDiff ℂ ⊤ (fun w : Fin n → ℂ => (∏ j ∈ s, (X-C (w j)) : ℂ[X]).coeff k) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp only [Finset.prod_empty]; exact contDiff_const
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    cases k with
    | zero =>
      simp only [mul_coeff_zero,coeff_sub,coeff_X_zero,coeff_C,zero_sub]
      exact (contDiff_apply ℂ ℂ j).neg.mul (ih 0)
    | succ k =>
      simp only [coeff_X_sub_C_mul]
      exact (ih k).sub ((contDiff_apply ℂ ℂ j).mul (ih (k+1)))

theorem fzzScreeningRootCoefficients_contDiff {n : ℕ} :
    ContDiff ℂ ⊤ (fzzScreeningRootCoefficients (n := n)) := by
  apply contDiff_pi.mpr
  intro i
  exact rootCoeff_contDiff_aux Finset.univ i.val

private theorem rootPolynomial_update {n : ℕ} (w : Fin n → ℂ) (j : Fin n) (t : ℂ) :
    fzzScreeningRootPolynomial (Function.update w j t) =
      (X-C t)*(∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]) := by
  unfold fzzScreeningRootPolynomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

private theorem rootCoeff_partial {n : ℕ} (w : Fin n → ℂ) (i j : Fin n) :
    (fderiv ℂ (fun x => (fzzScreeningRootPolynomial x).coeff i.val) w)
      (Pi.single j 1) = fzzScreeningRootJacobian w i j := by
  have hupdate : HasDerivAt (Function.update w j) (Pi.single j (1 : ℂ)) (w j) := by
    apply (hasFDerivAt_update (𝕜 := ℂ) (i := j) w (w j)).hasDerivAt.congr_deriv
    ext k
    by_cases hk : k = j <;> simp [hk]
  have hc := (rootCoeff_contDiff_aux (n := n) Finset.univ i.val).differentiable
    (by simp)
  have hcomp := (hc (Function.update w j (w j))).hasFDerivAt.comp_hasDerivAt (w j) hupdate
  simp only [Function.update_eq_self] at hcomp
  have heq : (fun t => (fzzScreeningRootPolynomial (Function.update w j t)).coeff i.val) =
      fun t => ((X : ℂ[X])*(∏ k ∈ Finset.univ.erase j, (X-C (w k)))).coeff i.val -
        t*(∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]).coeff i.val := by
    funext t
    rw [rootPolynomial_update,sub_mul,coeff_sub,coeff_C_mul]
  have hd : HasDerivAt (fun t => (fzzScreeningRootPolynomial (Function.update w j t)).coeff i.val)
      (fzzScreeningRootJacobian w i j) (w j) := by
    rw [heq]
    convert ((hasDerivAt_id (w j)).mul_const
      ((∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]).coeff i.val)).const_sub
        (((X : ℂ[X])*(∏ k ∈ Finset.univ.erase j, (X-C (w k)))).coeff i.val) using 1 <;> first | rfl | simp [fzzScreeningRootJacobian]

  exact hcomp.unique hd


/-- The displayed coefficient matrix is the actual derivative of the original root map. -/
theorem fzzScreeningRootCoefficients_derivative_matrix {n : ℕ} (w : Fin n → ℂ) :
    LinearMap.toMatrix' (fderiv ℂ fzzScreeningRootCoefficients w).toLinearMap =
      fzzScreeningRootJacobian w := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  have hc := (fzzScreeningRootCoefficients_contDiff (n := n)).differentiable (by simp) w
  have h := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) (fderiv_apply hc i)
  change (fderiv ℂ (fun x => (fzzScreeningRootPolynomial x).coeff i.val) w)
    (Pi.single j 1) = _ at h
  exact h.symm.trans (rootCoeff_partial w i j)

private theorem deleted_root_eval {n : ℕ} (w : Fin n → ℂ) (j : Fin n) (z : ℂ) :
    (∑ k : Fin n, z^k.val * fzzScreeningRootJacobian w k j) =
      -(∏ k ∈ Finset.univ.erase j, (z-w k)) := by
  have hdeg : (∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]).natDegree < n := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin]
    have := j.isLt
    omega
  have h := Polynomial.eval_eq_sum_range' hdeg z
  rw [← Fin.sum_univ_eq_sum_range] at h
  have hp : (∏ k ∈ Finset.univ.erase j, (X-C (w k)) : ℂ[X]).eval z =
      ∏ k ∈ Finset.univ.erase j, (z-w k) := by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [hp] at h
  rw [h]
  simp only [fzzScreeningRootJacobian,Matrix.of_apply,Finset.sum_neg_distrib,mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem rootJacobian_eval_matrix {n : ℕ} (w : Fin n → ℂ) :
    Matrix.vandermonde w * fzzScreeningRootJacobian w =
      Matrix.diagonal (fun j => -(∏ k ∈ Finset.univ.erase j, (w j-w k))) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.vandermonde_apply]
  rw [deleted_root_eval]
  by_cases h : i=j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    apply neg_eq_zero.mpr
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h,Finset.mem_univ i⟩) (sub_self _)

private theorem root_derivative_norm_product {n : ℕ} (w : Fin n → ℂ) :
    (∏ j, ∏ k ∈ Finset.univ.erase j, ‖w j-w k‖) = ‖(Matrix.vandermonde w).det‖^(2 : ℕ) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j : Fin n => ‖w j-w i‖)
  rw [Matrix.det_vandermonde]
  simp only [norm_prod]
  simp only [← Finset.prod_pow]
  simp only [Finset.compl_singleton] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  rw [norm_sub_rev (w i) (w j)]
  ring

private theorem rootJacobian_det_zero {n : ℕ} (w : Fin n → ℂ)
    (h : ¬ Function.Injective w) : (fzzScreeningRootJacobian w).det = 0 := by
  obtain ⟨i,j,heq,hij⟩ := Function.not_injective_iff.mp h
  have hp : (∏ k ∈ Finset.univ.erase i, (X-C (w k)) : ℂ[X]) =
      ∏ k ∈ Finset.univ.erase j, (X-C (w k)) := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (w i))
    calc
      _ = ∏ k : Fin n, (X-C (w k)) := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      _ = (X-C (w j)) * ∏ k ∈ Finset.univ.erase j, (X-C (w k)) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
      _ = _ := by rw [heq]
  apply Matrix.det_zero_of_column_eq hij
  intro k
  simp only [fzzScreeningRootJacobian,Matrix.of_apply,hp]

/-- The full complex Jacobian norm is the original Vandermonde norm, also at collisions. -/
theorem fzzScreeningRootJacobian_norm_det {n : ℕ} (w : Fin n → ℂ) :
    ‖(fzzScreeningRootJacobian w).det‖ = ‖(Matrix.vandermonde w).det‖ := by
  by_cases hw : Function.Injective w
  · have hn : ‖(Matrix.vandermonde w).det‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hw)
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => ‖A.det‖)
      (rootJacobian_eval_matrix w)
    simp only [Matrix.det_mul,norm_mul,Matrix.det_diagonal,norm_prod,norm_neg] at h
    rw [root_derivative_norm_product] at h
    apply mul_left_cancel₀ hn
    simpa only [pow_two] using h
  · rw [rootJacobian_det_zero w hw]
    have hv : (Matrix.vandermonde w).det = 0 := by
      by_contra hv
      exact hw (Matrix.det_vandermonde_ne_zero_iff.mp hv)
    simp only [hv,norm_zero]

/-- The real Jacobian is exactly the squared Vandermonde factor in the source measure. -/
theorem fzzScreeningRootCoefficients_real_jacobian {n : ℕ} (w : Fin n → ℂ) :
    (fderiv ℝ fzzScreeningRootCoefficients w).det = ‖(Matrix.vandermonde w).det‖^(2 : ℕ) := by
  have hc := (fzzScreeningRootCoefficients_contDiff (n := n)).differentiable (by simp)
  rw [(hc w).hasFDerivAt.restrictScalars ℝ |>.fderiv]
  change LinearMap.det ((fderiv ℂ fzzScreeningRootCoefficients w).toLinearMap.restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply]
  have hd : LinearMap.det (fderiv ℂ fzzScreeningRootCoefficients w).toLinearMap =
      (fzzScreeningRootJacobian w).det := by
    rw [← fzzScreeningRootCoefficients_derivative_matrix]
    exact (LinearMap.det_toMatrix' _).symm
  rw [hd,Complex.normSq_eq_norm_sq,fzzScreeningRootJacobian_norm_det]

/-- One ordering of roots; the complement of all orderings will be audited separately. -/
def fzzScreeningRootChamber (n : ℕ) : Set (Fin n → ℂ) :=
  {w | StrictMono (fun i => (w i).re)}

private theorem rootPolynomial_natDegree {n : ℕ} (w : Fin n → ℂ) :
    (fzzScreeningRootPolynomial w).natDegree = n := by
  simp [fzzScreeningRootPolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

private theorem rootPolynomial_eq_of_coefficients {n : ℕ} (w v : Fin n → ℂ)
    (h : fzzScreeningRootCoefficients w = fzzScreeningRootCoefficients v) :
    fzzScreeningRootPolynomial w = fzzScreeningRootPolynomial v := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · exact congrFun h ⟨k,hk⟩
  · by_cases hkn : k = n
    · subst k
      have hw := (Polynomial.monic_prod_X_sub_C w Finset.univ).coeff_natDegree
      have hv := (Polynomial.monic_prod_X_sub_C v Finset.univ).coeff_natDegree
      change (fzzScreeningRootPolynomial w).coeff (fzzScreeningRootPolynomial w).natDegree = 1 at hw
      change (fzzScreeningRootPolynomial v).coeff (fzzScreeningRootPolynomial v).natDegree = 1 at hv
      rw [rootPolynomial_natDegree] at hw hv
      exact hw.trans hv.symm
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rootPolynomial_natDegree]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rootPolynomial_natDegree]; omega)]

private theorem rootPolynomial_eval_zero_iff {n : ℕ} (w : Fin n → ℂ) (z : ℂ) :
    (fzzScreeningRootPolynomial w).eval z = 0 ↔ z ∈ Set.range w := by
  simp only [fzzScreeningRootPolynomial,eval_prod,eval_sub,eval_X,eval_C,
    Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero,Set.mem_range]
  exact exists_congr (fun i => eq_comm)

/-- Ordering by distinct real parts makes the original coefficient map injective. -/
theorem fzzScreeningRootChamber_injective (n : ℕ) :
    Set.InjOn fzzScreeningRootCoefficients (fzzScreeningRootChamber n) := by
  intro w hw v hv h
  change StrictMono (fun i => (w i).re) at hw
  change StrictMono (fun i => (v i).re) at hv
  have hp := rootPolynomial_eq_of_coefficients w v h
  have hr : Set.range w = Set.range v := by
    ext z
    rw [← rootPolynomial_eval_zero_iff w z,← rootPolynomial_eval_zero_iff v z,hp]
  have hre : (fun i => (w i).re) = (fun i => (v i).re) :=
    (hw.range_inj hv).mp (by rw [Set.range_comp' Complex.re w,Set.range_comp' Complex.re v,hr])
  funext i
  obtain ⟨j,hj⟩ : w i ∈ Set.range v := hr ▸ Set.mem_range_self i
  have hji : j = i := hv.injective (by rw [hj,congrFun hre i])
  subst j
  exact hj.symm

/-- The chamber is open, hence provides a measurable domain for the actual Jacobian theorem. -/
theorem fzzScreeningRootChamber_open (n : ℕ) : IsOpen (fzzScreeningRootChamber n) := by
  have heq : fzzScreeningRootChamber n =
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_h : i < j), {w : Fin n → ℂ | (w i).re < (w j).re} := by
    ext w
    simp [fzzScreeningRootChamber,StrictMono]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_lt (Complex.continuous_re.comp (continuous_apply i))
    (Complex.continuous_re.comp (continuous_apply j))

/-- The original Vandermonde weight is exactly removed on one root ordering. -/
theorem fzzScreeningRootChamber_lintegral (n : ℕ) (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ c in fzzScreeningRootCoefficients '' fzzScreeningRootChamber n, g c) =
      ∫⁻ w in fzzScreeningRootChamber n,
        ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ)) * g (fzzScreeningRootCoefficients w) := by
  have hd := (fzzScreeningRootCoefficients_contDiff (n := n)).differentiable (by simp)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (fzzScreeningRootChamber_open n).measurableSet
    (fun w _ => ((hd w).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    (fzzScreeningRootChamber_injective n) g
  have hj (w : Fin n → ℂ) :
      |((fderiv ℂ fzzScreeningRootCoefficients w).restrictScalars ℝ).det| =
        ‖(Matrix.vandermonde w).det‖^(2 : ℕ) := by
    rw [← (hd w).hasFDerivAt.restrictScalars ℝ |>.fderiv,
      fzzScreeningRootCoefficients_real_jacobian,abs_of_nonneg (sq_nonneg _)]
  simpa only [hj] using h

private theorem root_real_tie_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    volume {w : Fin n → ℂ | (w i).re = (w j).re} = 0 := by
  let L : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    (Complex.reCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ) - ContinuousLinearMap.proj j)).toLinearMap
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hm : Pi.single i (1 : ℂ) ∈ LinearMap.ker L := by rw [htop]; trivial
    simp [L, hij.symm] at hm
  have h := Measure.addHaar_submodule volume (LinearMap.ker L) hker
  convert h using 2
  ext w
  simp [L, sub_eq_zero]

/-- All real-part ties form a null set, including collisions of the original roots. -/
theorem fzzScreeningRoot_real_ties_null (n : ℕ) :
    volume {w : Fin n → ℂ | ¬ Function.Injective (fun i => (w i).re)} = 0 := by
  have heq : {w : Fin n → ℂ | ¬ Function.Injective (fun i => (w i).re)} =
      ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_h : i ≠ j), {w : Fin n → ℂ | (w i).re = (w j).re} := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Function.not_injective_iff]
    aesop
  rw [heq]
  exact measure_iUnion_null (fun i => measure_iUnion_null (fun j =>
    measure_iUnion_null (fun hij => root_real_tie_null i j hij)))

/-- The exceptional coefficient image is also null; no discriminant mass is discarded. -/
theorem fzzScreeningRoot_real_ties_image_null (n : ℕ) :
    volume (fzzScreeningRootCoefficients ''
      {w : Fin n → ℂ | ¬ Function.Injective (fun i => (w i).re)}) = 0 := by
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((fzzScreeningRootCoefficients_contDiff (n := n)).differentiable (by simp)).restrictScalars ℝ).differentiableOn
    (fzzScreeningRoot_real_ties_null n)

private theorem rootCoefficients_perm {n : ℕ} (w : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    fzzScreeningRootCoefficients (w ∘ σ) = fzzScreeningRootCoefficients w := by
  have hp : fzzScreeningRootPolynomial (w ∘ σ) = fzzScreeningRootPolynomial w :=
    Equiv.prod_comp σ (fun j => (X-C (w j) : ℂ[X]))
  exact congrArg (fun p : ℂ[X] => fun i : Fin n => p.coeff i.val) hp

private def permRootChamber {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℂ) :=
  {w | w ∘ σ ∈ fzzScreeningRootChamber n}

private theorem permRootChamber_open {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsOpen (permRootChamber σ) :=
  (fzzScreeningRootChamber_open n).preimage (continuous_pi (fun i => continuous_apply (σ i)))

private theorem permRootChamber_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set.InjOn fzzScreeningRootCoefficients (permRootChamber σ) := by
  intro w hw v hv h
  have he := fzzScreeningRootChamber_injective n hw hv
    (by simpa only [rootCoefficients_perm] using h)
  funext i
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun he (σ.symm i)

private theorem permRootChamber_image {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    fzzScreeningRootCoefficients '' permRootChamber σ =
      fzzScreeningRootCoefficients '' fzzScreeningRootChamber n := by
  ext c
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w ∘ σ,hw,rootCoefficients_perm w σ⟩
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w ∘ σ.symm,?_,rootCoefficients_perm w σ.symm⟩
    simpa [permRootChamber,Function.comp_def] using hw

private theorem permRootChamber_union (n : ℕ) :
    (⋃ σ : Equiv.Perm (Fin n), permRootChamber σ) =
      {w : Fin n → ℂ | Function.Injective (fun i => (w i).re)} := by
  ext w
  simp only [Set.mem_iUnion,Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ,hσ⟩
    exact (show StrictMono (fun i => (w (σ i)).re) from hσ).injective.of_comp_right (f := fun i => (w i).re) σ.surjective
  · intro hw
    let σ := Tuple.sort (fun i => (w i).re)
    refine ⟨σ,?_⟩
    exact (Tuple.monotone_sort (fun i => (w i).re)).strictMono_iff_injective.mpr
      (hw.comp σ.injective)

private theorem permRootChamber_disjoint (n : ℕ) :
    Pairwise (fun σ τ : Equiv.Perm (Fin n) => Disjoint (permRootChamber σ) (permRootChamber τ)) := by
  intro σ τ hστ
  rw [Set.disjoint_left]
  intro w hσ hτ
  have hs : StrictMono (fun i => (w (σ i)).re) := hσ
  have ht : StrictMono (fun i => (w (τ i)).re) := hτ
  have hi : Function.Injective (fun i => (w i).re) := hs.injective.of_comp_right (f := fun i => (w i).re) σ.surjective
  have he : (fun i => (w (σ i)).re) = (fun i => (w (τ i)).re) :=
    (hs.range_inj ht).mp (by
      change Set.range ((fun i => (w i).re) ∘ σ) = Set.range ((fun i => (w i).re) ∘ τ)
      rw [σ.surjective.range_comp,τ.surjective.range_comp])
  exact hστ (Equiv.ext (fun i => hi (congrFun he i)))

private theorem permRootChamber_lintegral {n : ℕ} (σ : Equiv.Perm (Fin n))
    (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ w in permRootChamber σ,
      ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)) =
        ∫⁻ c in fzzScreeningRootCoefficients '' fzzScreeningRootChamber n, g c := by
  have hd := (fzzScreeningRootCoefficients_contDiff (n := n)).differentiable (by simp)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (permRootChamber_open σ).measurableSet
    (fun w _ => ((hd w).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    (permRootChamber_injective σ) g
  have hj (w : Fin n → ℂ) :
      |((fderiv ℂ fzzScreeningRootCoefficients w).restrictScalars ℝ).det| =
        ‖(Matrix.vandermonde w).det‖^(2 : ℕ) := by
    rw [← (hd w).hasFDerivAt.restrictScalars ℝ |>.fderiv,
      fzzScreeningRootCoefficients_real_jacobian,abs_of_nonneg (sq_nonneg _)]
  simpa only [hj,permRootChamber_image] using h.symm

/-- All original root orderings contribute; their exact multiplicity is the factorial. -/
theorem fzzScreeningRootCoefficients_factorial_lintegral (n : ℕ)
    (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ w, ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)) =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ c in fzzScreeningRootCoefficients '' fzzScreeningRootChamber n, g c := by
  have hg : ∀ᵐ w : Fin n → ℂ, Function.Injective (fun i => (w i).re) := by
    rw [ae_iff]
    exact fzzScreeningRoot_real_ties_null n
  have hu : (⋃ σ : Equiv.Perm (Fin n), permRootChamber σ) =ᵐ[volume] Set.univ := by
    filter_upwards [hg] with w hw
    apply propext
    change w ∈ (⋃ σ : Equiv.Perm (Fin n), permRootChamber σ) ↔ w ∈ Set.univ
    rw [permRootChamber_union]
    exact iff_true_intro hw
  calc
    _ = ∫⁻ w in ⋃ σ : Equiv.Perm (Fin n), permRootChamber σ,
        ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w) := by
      simpa only [Measure.restrict_univ] using (setLIntegral_congr (f := fun w : Fin n → ℂ =>
        ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)) hu).symm
    _ = ∑' σ : Equiv.Perm (Fin n), ∫⁻ w in permRootChamber σ,
        ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w) :=
      lintegral_iUnion (fun σ => (permRootChamber_open σ).measurableSet) (permRootChamber_disjoint n) _
    _ = _ := by
      simp only [permRootChamber_lintegral,tsum_fintype,Finset.sum_const,Finset.card_univ,
        Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]

/-- Every monic coefficient vector comes from a full list of complex roots. -/
theorem fzzScreeningRootCoefficients_surjective (n : ℕ) :
    Function.Surjective (fzzScreeningRootCoefficients (n := n)) := by
  intro c
  let p : ℂ[X] := X^n + ∑ i : Fin n, C (c i)*X^i.val
  have hm : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)
  have hd : p.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    change (X^n + ∑ i : Fin n, C (c i)*X^i.val : ℂ[X]).degree = n
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by
      rw [Polynomial.degree_X_pow]
      exact Polynomial.degree_sum_fin_lt c),Polynomial.degree_X_pow]
  have hl : p.roots.toList.length = n := by
    rw [Multiset.length_toList,IsAlgClosed.card_roots_eq_natDegree,hd]
  obtain ⟨w,hw⟩ : ∃ w : Fin n → ℂ, List.ofFn w = p.roots.toList := by
    rw [← hl]
    exact ⟨p.roots.toList.get,List.ofFn_get _⟩
  have hp : fzzScreeningRootPolynomial w = p := by
    calc
      _ = (p.roots.map (fun z => X-C z)).prod := by
        rw [← p.roots.coe_toList,← hw]
        simp only [fzzScreeningRootPolynomial,Multiset.map_coe,Multiset.prod_coe,
          List.map_ofFn,Fin.prod_ofFn,Function.comp_apply]
      _ = p := ((IsAlgClosed.splits p).eq_prod_roots_of_monic hm).symm
  refine ⟨w,?_⟩
  funext i
  change (fzzScreeningRootPolynomial w).coeff i.val = c i
  rw [hp]
  simp only [p,coeff_add,coeff_X_pow,if_neg (Nat.ne_of_lt i.isLt),zero_add,
    finsetSum_coeff,coeff_C_mul_X_pow,Fin.val_inj]
  simp

private theorem rootChamber_image_ae_univ (n : ℕ) :
    fzzScreeningRootCoefficients '' fzzScreeningRootChamber n =ᵐ[volume] Set.univ := by
  have hn : ∀ᵐ c : Fin n → ℂ, c ∉ fzzScreeningRootCoefficients ''
      {w : Fin n → ℂ | ¬ Function.Injective (fun i => (w i).re)} := by
    rw [ae_iff]
    convert fzzScreeningRoot_real_ties_image_null n using 1
    congr 1
    ext c
    simp only [Set.mem_setOf_eq,not_not]
  filter_upwards [hn] with c hc
  apply propext
  change c ∈ fzzScreeningRootCoefficients '' fzzScreeningRootChamber n ↔ c ∈ Set.univ
  simp only [Set.mem_univ,iff_true]
  obtain ⟨w,rfl⟩ := fzzScreeningRootCoefficients_surjective n c
  have hg : Function.Injective (fun i => (w i).re) := by
    by_contra h
    exact hc ⟨w,h,rfl⟩
  have hu : w ∈ ⋃ σ : Equiv.Perm (Fin n), permRootChamber σ := by
    rw [permRootChamber_union]
    exact hg
  obtain ⟨σ,hσ⟩ := Set.mem_iUnion.mp hu
  rw [← permRootChamber_image σ]
  exact ⟨w,hσ,rfl⟩

/-- Full original root-to-coefficient transformation, including exact multiplicity and null sets. -/
theorem fzzScreeningRootCoefficients_lintegral (n : ℕ)
    (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ w, ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)) =
      (n.factorial : ℝ≥0∞) * ∫⁻ c, g c := by
  rw [fzzScreeningRootCoefficients_factorial_lintegral,
    setLIntegral_congr (rootChamber_image_ae_univ n),Measure.restrict_univ]

private def rootChargeDomain {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    Set (Fin n → ℂ) := Set.univ.pi (fun _ => fzzScreeningChargeDomain z R T)

/-- The exact coefficient image of the original outer cutoff and every puncture cutoff. -/
def fzzScreeningCoefficientDomain {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    Set (Fin n → ℂ) := fzzScreeningRootCoefficients '' rootChargeDomain z R T n

private theorem rootChargeDomain_compact {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    IsCompact (rootChargeDomain z R T n) :=
  isCompact_univ_pi (fun _ => (isCompact_closedBall _ _).diff
    (isOpen_iUnion (fun _ => isOpen_ball)))

private theorem coefficientDomain_compact {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    IsCompact (fzzScreeningCoefficientDomain z R T n) :=
  (rootChargeDomain_compact z R T n).image fzzScreeningRootCoefficients_contDiff.continuous

private theorem rootChargeDomain_coefficient_mem {m n : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (w : Fin n → ℂ) :
    fzzScreeningRootCoefficients w ∈ fzzScreeningCoefficientDomain z R T n ↔
      w ∈ rootChargeDomain z R T n := by
  constructor
  · rintro ⟨v,hv,hvw⟩
    have hp := rootPolynomial_eq_of_coefficients v w hvw
    intro i hi
    have hroot : w i ∈ Set.range v := (rootPolynomial_eval_zero_iff v (w i)).mp (by
      rw [hp]
      exact (rootPolynomial_eval_zero_iff w (w i)).mpr (Set.mem_range_self i))
    obtain ⟨j,hj⟩ := hroot
    rw [← hj]
    exact hv j (Set.mem_univ j)
  · intro hw
    exact ⟨w,hw,rfl⟩

/-- Exact transformation with all original finite position cutoffs retained. -/
theorem fzzScreeningRootCoefficients_cutoff_lintegral {m : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (n : ℕ) (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ w, ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)
      ∂fzzScreeningChargeMeasure z R T n) =
      (n.factorial : ℝ≥0∞) * ∫⁻ c in fzzScreeningCoefficientDomain z R T n, g c := by
  have h := fzzScreeningRootCoefficients_lintegral n
    ((fzzScreeningCoefficientDomain z R T n).indicator g)
  have hf : (fun w : Fin n → ℂ => ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*
      (fzzScreeningCoefficientDomain z R T n).indicator g (fzzScreeningRootCoefficients w)) =
      (rootChargeDomain z R T n).indicator (fun w =>
        ENNReal.ofReal (‖(Matrix.vandermonde w).det‖^(2 : ℕ))*g (fzzScreeningRootCoefficients w)) := by
    funext w
    by_cases hw : w ∈ rootChargeDomain z R T n
    · rw [Set.indicator_of_mem ((rootChargeDomain_coefficient_mem z R T w).mpr hw),
        Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem (fun h => hw ((rootChargeDomain_coefficient_mem z R T w).mp h)),
        Set.indicator_of_notMem hw,mul_zero]
  rw [hf,lintegral_indicator (rootChargeDomain_compact z R T n).measurableSet,
    lintegral_indicator (coefficientDomain_compact z R T n).measurableSet] at h
  have hμ : (volume : Measure (Fin n → ℂ)).restrict (rootChargeDomain z R T n) =
      fzzScreeningChargeMeasure z R T n :=
    Measure.restrict_pi_pi (fun _ : Fin n => volume) (fun _ => fzzScreeningChargeDomain z R T)
  rw [hμ] at h
  exact h

/-- Monic polynomial in the new coefficients, with its leading term fixed. -/
def fzzScreeningCoefficientPolynomial {n : ℕ} (c : Fin n → ℂ) : ℂ[X] :=
  X^n + ∑ i : Fin n, C (c i)*X^i.val

private theorem coefficientPolynomial_roots {n : ℕ} (w : Fin n → ℂ) :
    fzzScreeningCoefficientPolynomial (fzzScreeningRootCoefficients w) =
      fzzScreeningRootPolynomial w := by
  have h := (Polynomial.monic_prod_X_sub_C w Finset.univ).as_sum
  change fzzScreeningRootPolynomial w = X^(fzzScreeningRootPolynomial w).natDegree +
    ∑ i ∈ Finset.range (fzzScreeningRootPolynomial w).natDegree,
      C ((fzzScreeningRootPolynomial w).coeff i)*X^i at h
  rw [rootPolynomial_natDegree,← Fin.sum_univ_eq_sum_range] at h
  exact h.symm

/-- Every original opposite-charge factor survives as a polynomial evaluation. -/
def fzzScreeningCoefficientWeight {m n : ℕ} (z : Fin m → ℂ) (c : Fin n → ℂ) : ℝ :=
  ∏ i, (‖(fzzScreeningCoefficientPolynomial c).eval (z i)‖^(6 : ℕ))⁻¹

private theorem coefficientWeight_roots {m n : ℕ} (z : Fin m → ℂ) (w : Fin n → ℂ) :
    fzzScreeningCoefficientWeight z (fzzScreeningRootCoefficients w) =
      ∏ j, fzzScreeningChargeWeight z (w j) := by
  unfold fzzScreeningCoefficientWeight
  rw [coefficientPolynomial_roots]
  simp only [fzzScreeningRootPolynomial,eval_prod,eval_sub,eval_X,eval_C,norm_prod,
    ← Finset.prod_pow,← Finset.prod_inv_distrib]
  rw [Finset.prod_comm]
  simp only [fzzScreeningChargeWeight,norm_sub_rev]

/-- The complete original cutoff charge integral in coefficient coordinates. -/
theorem fzzScreeningChargeKernel_coefficient_lintegral {m : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (n : ℕ) :
    (∫⁻ w, ENNReal.ofReal (fzzScreeningChargeKernel z w) ∂fzzScreeningChargeMeasure z R T n) =
      (n.factorial : ℝ≥0∞) * ∫⁻ c in fzzScreeningCoefficientDomain z R T n,
        ENNReal.ofReal (fzzScreeningCoefficientWeight z c) := by
  have h := fzzScreeningRootCoefficients_cutoff_lintegral z R T n
    (fun c => ENNReal.ofReal (fzzScreeningCoefficientWeight z c))
  simp_rw [coefficientWeight_roots,← ENNReal.ofReal_mul (sq_nonneg _)] at h
  exact h

private theorem screeningCoefficientWeight_nonneg {m n : ℕ}
    (z : Fin m → ℂ) (c : Fin n → ℂ) : 0 ≤ fzzScreeningCoefficientWeight z c := by
  unfold fzzScreeningCoefficientWeight
  positivity

private theorem screeningChargeKernel_nonneg {m n : ℕ}
    (z : Fin m → ℂ) (w : Fin n → ℂ) : 0 ≤ fzzScreeningChargeKernel z w := by
  unfold fzzScreeningChargeKernel fzzScreeningChargeWeight
  positivity

/-- Original source admission transfers to the complete transformed cutoff integral. -/
theorem fzzScreeningCoefficientWeight_integrable {m : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (n : ℕ) :
    IntegrableOn (fzzScreeningCoefficientWeight (n := n) z)
      (fzzScreeningCoefficientDomain z R T n) := by
  have hmeas : Measurable (fzzScreeningCoefficientWeight (n := n) z) := by
    unfold fzzScreeningCoefficientWeight
    simp only [fzzScreeningCoefficientPolynomial,eval_add,eval_finsetSum,eval_mul,
      eval_C,eval_pow,eval_X]
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (screeningCoefficientWeight_nonneg z))]
  have hfin : (n.factorial : ℝ≥0∞) *
      (∫⁻ c in fzzScreeningCoefficientDomain z R T n,
        ENNReal.ofReal (fzzScreeningCoefficientWeight z c)) < ∞ := by
    rw [← fzzScreeningChargeKernel_coefficient_lintegral,
      ← ofReal_integral_eq_lintegral_ofReal (fzzScreeningChargeKernel_integrable z R T)
        (Filter.Eventually.of_forall (screeningChargeKernel_nonneg z))]
    exact ENNReal.ofReal_lt_top
  have hn : (1 : ℝ≥0∞) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
  apply lt_of_le_of_lt _ hfin
  calc
    _ = 1 * (∫⁻ c in fzzScreeningCoefficientDomain z R T n,
        ENNReal.ofReal (fzzScreeningCoefficientWeight z c)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left hn _

/-- The admitted original charge integral, with every cutoff and interaction retained. -/
theorem fzzScreeningChargeKernel_coefficient_integral {m : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (n : ℕ) :
    (∫ w, fzzScreeningChargeKernel z w ∂fzzScreeningChargeMeasure z R T n) =
      (n.factorial : ℝ) * ∫ c in fzzScreeningCoefficientDomain z R T n,
        fzzScreeningCoefficientWeight z c := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (screeningChargeKernel_nonneg z))
      (fzzScreeningChargeKernel_integrable z R T).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (screeningCoefficientWeight_nonneg z))
      (fzzScreeningCoefficientWeight_integrable z R T n).aestronglyMeasurable,
    fzzScreeningChargeKernel_coefficient_lintegral,ENNReal.toReal_mul,ENNReal.toReal_natCast]

end GaloisForLFunctions.RHTower
