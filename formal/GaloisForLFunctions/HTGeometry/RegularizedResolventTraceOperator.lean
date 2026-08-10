import GaloisForLFunctions.HTGeometry.HilbertSchmidtAlgebra
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import Mathlib.Analysis.Normed.Ring.Units

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

theorem opTrace_comp_eq_tsum_matrixOf
    {A B : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    ContinuousLinearMap.opTrace (A ∘L B) = ∑' i, matrixOf (A ∘L B) (i, i) := by
  rw [ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB (lpBasis ι)]
  apply tsum_congr
  intro i
  rw [lpBasis_apply, lp.inner_single_left]
  simp [RCLike.inner_apply, matrixOf]

theorem toOperator_hsPow {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    toOperator (isHS_hsPow hK n) = (toOperator hK) ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change toOperator (isHS_hsComp hK (isHS_hsPow hK n)) =
        (toOperator hK) ^ (n + 1 + 1)
      rw [toOperator_hsComp hK (isHS_hsPow hK n), ih]
      rw [show n + 1 + 1 = n + 2 by omega]
      simp [pow_succ', ContinuousLinearMap.mul_def]

omit [DecidableEq ι] in
theorem hsNorm_toOperator {K : ι × ι → ℂ} (hK : IsHS K) :
    ContinuousLinearMap.hsNorm (toOperator hK) = hsNorm K := by
  rw [ContinuousLinearMap.hsNorm, hsNorm, hsNormSq_toOperator hK]

theorem inner_lpBasis_comp_eq_hsComp
    {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) (i : ι) :
    inner ℂ (lpBasis ι i)
        ((toOperator hK ∘L toOperator hL) (lpBasis ι i)) =
      hsComp K L (i, i) := by
  rw [lpBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [← toOperator_hsComp hK hL, toOperator_single]

theorem inner_lpBasis_toOperator
    {K : ι × ι → ℂ} (hK : IsHS K) (i : ι) :
    inner ℂ (lpBasis ι i) (toOperator hK (lpBasis ι i)) = K (i, i) := by
  rw [lpBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [toOperator_single]

theorem summable_norm_inner_diag_comp
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : F →L[ℂ] E} {B : E →L[ℂ] F}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    {κ : Type*} (b : HilbertBasis κ ℂ E) :
    Summable (fun i => ‖inner ℂ (b i) ((A ∘L B) (b i))‖) := by
  have hcross : Summable (fun i =>
      ‖ContinuousLinearMap.adjoint A (b i)‖ * ‖B (b i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (((hA.adjoint.summable b).mul_left (2 : ℝ)⁻¹).add
        ((hB.summable b).mul_left (2 : ℝ)⁻¹))
    nlinarith [sq_nonneg
      (‖ContinuousLinearMap.adjoint A (b i)‖ - ‖B (b i)‖),
      norm_nonneg (ContinuousLinearMap.adjoint A (b i)), norm_nonneg (B (b i))]
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hcross
  rw [ContinuousLinearMap.inner_comp_apply]
  exact norm_inner_le_norm _ _

theorem tsum_norm_inner_diag_comp_le
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : F →L[ℂ] E} {B : E →L[ℂ] F}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    {κ : Type*} (b : HilbertBasis κ ℂ E) :
    (∑' i, ‖inner ℂ (b i) ((A ∘L B) (b i))‖) ≤
      ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
  have hcross : Summable (fun i =>
      ‖ContinuousLinearMap.adjoint A (b i)‖ * ‖B (b i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (((hA.adjoint.summable b).mul_left (2 : ℝ)⁻¹).add
        ((hB.summable b).mul_left (2 : ℝ)⁻¹))
    nlinarith [sq_nonneg
      (‖ContinuousLinearMap.adjoint A (b i)‖ - ‖B (b i)‖),
      norm_nonneg (ContinuousLinearMap.adjoint A (b i)), norm_nonneg (B (b i))]
  calc
    (∑' i, ‖inner ℂ (b i) ((A ∘L B) (b i))‖)
        ≤ ∑' i, ‖ContinuousLinearMap.adjoint A (b i)‖ * ‖B (b i)‖ := by
          refine Summable.tsum_le_tsum (fun i => ?_)
            (summable_norm_inner_diag_comp hA hB b) hcross
          rw [ContinuousLinearMap.inner_comp_apply]
          exact norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑' i, ‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2) *
          Real.sqrt (∑' i, ‖B (b i)‖ ^ 2) :=
      ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt
        (hA.adjoint.summable b) (hB.summable b)
    _ = ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
      rw [← ContinuousLinearMap.hsNormSq_eq hA.adjoint b,
        ← ContinuousLinearMap.hsNormSq_eq hB b]
      change Real.sqrt (ContinuousLinearMap.hsNormSq
          (ContinuousLinearMap.adjoint A)) * ContinuousLinearMap.hsNorm B = _
      rw [hA.hsNormSq_adjoint]
      rfl

theorem summable_norm_hsPow_diag {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    Summable (fun i => ‖hsPow K (n + 1) (i, i)‖) := by
  have h := summable_norm_inner_diag_comp
    (isHilbertSchmidt_toOperator hK)
    (isHilbertSchmidt_toOperator (isHS_hsPow hK n)) (lpBasis ι)
  simpa only [inner_lpBasis_comp_eq_hsComp hK (isHS_hsPow hK n), hsPow] using h

theorem tsum_norm_hsPow_diag_le {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    (∑' i, ‖hsPow K (n + 1) (i, i)‖) ≤ (hsNorm K) ^ (n + 2) := by
  have h := tsum_norm_inner_diag_comp_le
    (isHilbertSchmidt_toOperator hK)
    (isHilbertSchmidt_toOperator (isHS_hsPow hK n)) (lpBasis ι)
  rw [tsum_congr (fun i => congrArg norm
      (inner_lpBasis_comp_eq_hsComp hK (isHS_hsPow hK n) i))] at h
  rw [hsNorm_toOperator hK,
    hsNorm_toOperator (isHS_hsPow hK n)] at h
  exact h.trans (by
    calc
      hsNorm K * hsNorm (hsPow K n)
          ≤ hsNorm K * (hsNorm K) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (hsNorm_hsPow_le hK n) (hsNorm_nonneg K)
      _ = (hsNorm K) ^ (n + 2) := by ring)

theorem summable_resolventTrace_diagonal
    {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ)
    (hz : ‖z‖ * hsNorm K < 1) :
    Summable (Function.uncurry (fun n i =>
      z ^ (n + 1) * hsPow K (n + 1) (i, i))) := by
  let f : ℕ × ι → ℝ := fun p =>
    ‖z ^ (p.1 + 1) * hsPow K (p.1 + 1) (p.2, p.2)‖
  have hfiber (n : ℕ) : Summable (fun i => f (n, i)) := by
    simpa only [f, norm_mul, norm_pow] using
      (summable_norm_hsPow_diag hK n).mul_left (‖z‖ ^ (n + 1))
  have houter : Summable (fun n => ∑' i, f (n, i)) := by
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg fun i => norm_nonneg _)
      (fun n => ?_)
    · exact Summable.mul_left (hsNorm K)
        ((summable_geometric_of_lt_one
          (mul_nonneg (norm_nonneg z) (hsNorm_nonneg K)) hz).mul_right
            (‖z‖ * hsNorm K))
    · rw [show (∑' i, f (n, i)) =
          ‖z‖ ^ (n + 1) * ∑' i, ‖hsPow K (n + 1) (i, i)‖ by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro i
          simp only [f, norm_mul, norm_pow]]
      calc
        ‖z‖ ^ (n + 1) * ∑' i, ‖hsPow K (n + 1) (i, i)‖
            ≤ ‖z‖ ^ (n + 1) * (hsNorm K) ^ (n + 2) :=
          mul_le_mul_of_nonneg_left (tsum_norm_hsPow_diag_le hK n)
            (pow_nonneg (norm_nonneg z) _)
        _ = hsNorm K * (‖z‖ * hsNorm K) ^ (n + 1) := by
          rw [mul_pow]
          ring
  have hfnorm : Summable f :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨hfiber, houter⟩
  apply Summable.of_norm
  simpa [f, Function.uncurry] using hfnorm

theorem regularizedResolventOperatorTerm_eq
    {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ) (n : ℕ) :
    let T := toOperator hK
    (z • (T ∘L T)) ∘L ((z • T) ^ n) =
      z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1)) := by
  let T := toOperator hK
  rw [toOperator_hsPow hK (n + 1)]
  simp only [smul_pow, pow_succ', ContinuousLinearMap.mul_def]
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply, smul_smul, mul_comm]

theorem summable_regularizedResolventOperator
    {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ)
    (hz : ‖z‖ * hsNorm K < 1) :
    Summable (fun n =>
      z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1))) := by
  let T := toOperator hK
  let X := z • T
  have hX : ‖X‖ < 1 := by
    simp only [X, norm_smul]
    exact (mul_le_mul_of_nonneg_left (norm_toOperator_le hK) (norm_nonneg z)).trans_lt hz
  have hgeom : Summable (fun n : ℕ => X ^ n) :=
    summable_geometric_of_norm_lt_one hX
  let C :
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) →L[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    (ContinuousLinearMap.compL ℂ _ _ _) (z • (T ∘L T))
  refine (hgeom.map C C.continuous).congr (fun n => ?_)
  change C (X ^ n) = _
  simpa only [C, ContinuousLinearMap.compL_apply, X] using
    regularizedResolventOperatorTerm_eq hK z n

theorem regularizedResolventOperator_eq_tsum
    {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ)
    (hz : ‖z‖ * hsNorm K < 1) :
    let T := toOperator hK
    z • ((T ∘L T) ∘L Ring.inverse (1 - z • T)) =
      ∑' n, z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1)) := by
  let T := toOperator hK
  let X := z • T
  have hX : ‖X‖ < 1 := by
    simp only [X, norm_smul]
    exact (mul_le_mul_of_nonneg_left (norm_toOperator_le hK) (norm_nonneg z)).trans_lt hz
  have hgeom : Summable (fun n : ℕ => X ^ n) :=
    summable_geometric_of_norm_lt_one hX
  have hinv : Ring.inverse (1 - X) = ∑' n : ℕ, X ^ n := by
    rw [NormedRing.inverse_one_sub X hX]
    rfl
  let C :
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) →L[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    (ContinuousLinearMap.compL ℂ _ _ _) (z • (T ∘L T))
  change z • ((T ∘L T) ∘L Ring.inverse (1 - X)) = _
  calc
    z • ((T ∘L T) ∘L Ring.inverse (1 - X)) =
        C (Ring.inverse (1 - X)) := by
      simp [C]
    _ = C (∑' n : ℕ, X ^ n) := by rw [hinv]
    _ = ∑' n : ℕ, C (X ^ n) := C.map_tsum hgeom
    _ = ∑' n : ℕ,
        z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1)) := by
      apply tsum_congr
      intro n
      simpa only [C, ContinuousLinearMap.compL_apply, X] using
        regularizedResolventOperatorTerm_eq hK z n

theorem resolventTrace_eq_opTrace_regularizedResolvent
    {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ)
    (hz : ‖z‖ * hsNorm K < 1) :
    let T := toOperator hK
    resolventTrace K z = ContinuousLinearMap.opTrace
      (T ∘L (z • (T ∘L Ring.inverse (1 - z • T)))) := by
  let T := toOperator hK
  let J := Ring.inverse (1 - z • T)
  let S : ℕ →
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    fun n => z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1))
  change resolventTrace K z = ContinuousLinearMap.opTrace
    (T ∘L (z • (T ∘L J)))
  have hT : T.IsHilbertSchmidt := isHilbertSchmidt_toOperator hK
  have hR : (z • (T ∘L J)).IsHilbertSchmidt :=
    (hT.comp_right J).smul z
  have hop : T ∘L (z • (T ∘L J)) = z • ((T ∘L T) ∘L J) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [ContinuousLinearMap.comp_apply]
  have hsumS : Summable S := by
    simpa only [S] using summable_regularizedResolventOperator hK z hz
  have hsumOp : z • ((T ∘L T) ∘L J) = ∑' n, S n := by
    simpa only [T, J, S] using regularizedResolventOperator_eq_tsum hK z hz
  have hpoint (i : ι) :
      inner ℂ (lpBasis ι i) ((∑' n, S n) (lpBasis ι i)) =
        ∑' n, z ^ (n + 1) * hsPow K (n + 1) (i, i) := by
    let e :
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) →L[ℂ]
          lp (fun _ : ι => ℂ) 2 :=
      ContinuousLinearMap.apply ℂ _ (lpBasis ι i)
    let phi : lp (fun _ : ι => ℂ) 2 →L[ℂ] ℂ :=
      InnerProductSpace.toDual ℂ _ (lpBasis ι i)
    have hmap := (phi.comp e).map_tsum hsumS
    change inner ℂ (lpBasis ι i) ((∑' n, S n) (lpBasis ι i)) = _ at hmap
    rw [hmap]
    apply tsum_congr
    intro n
    change inner ℂ (lpBasis ι i)
      ((z ^ (n + 1) • toOperator (isHS_hsPow hK (n + 1))) (lpBasis ι i)) = _
    rw [smul_apply, inner_smul_right]
    rw [inner_lpBasis_toOperator]
  rw [ContinuousLinearMap.opTrace_comp_eq_tsum_basis hT hR (lpBasis ι), hop, hsumOp]
  rw [resolventTrace]
  have hleft :
      (∑' n, z ^ (n + 1) * (∑' i, hsPow K (n + 1) (i, i))) =
        ∑' n, ∑' i, z ^ (n + 1) * hsPow K (n + 1) (i, i) := by
    apply tsum_congr
    intro n
    exact tsum_mul_left.symm
  rw [hleft, tsum_congr hpoint]
  exact (summable_resolventTrace_diagonal hK z hz).tsum_comm.symm

end HilbertSchmidt
