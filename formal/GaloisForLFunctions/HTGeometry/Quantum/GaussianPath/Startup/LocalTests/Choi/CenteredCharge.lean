import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.ScoreOverlap

/-! # A quadratic error bound from orthogonal centered Choi tests -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A Hermitian test has mean zero on y. Write u,v for its actions on
x,y. Expansion in x−y leaves a quadratic remainder. Centering a local
approximation w to u extracts one scalar projection of the fitting error. -/
theorem centered_missing_bound (x y u v w : E) {δ ε : ℝ}
    (hx : ‖x‖=1) (hfit : ‖x-y‖≤ε) (hmove : ‖u-v‖≤ε) (hloc : ‖u-w‖≤δ)
    (htransfer : inner ℂ u y=inner ℂ x v) (hzero : inner ℂ y v=0) :
    (1-2*ε)*‖inner ℂ x w‖≤2*‖inner ℂ (x-y) (w-inner ℂ x w • x)‖+(1+2*ε)*δ+ε^2 := by
  let d := x-y
  let b := inner ℂ x w
  let z := w-b • x
  have h₀ : 0≤ε := (norm_nonneg _).trans hfit
  have hm : ‖b‖≤‖inner ℂ u x‖+δ := calc
    _ = ‖inner ℂ x u+inner ℂ x (w-u)‖ := by congr 1; dsimp only [b]; rw [inner_sub_right]; abel
    _ ≤ ‖inner ℂ x u‖+‖inner ℂ x (w-u)‖ := norm_add_le ..
    _ ≤ _ := by
      rw [norm_inner_symm x u]
      exact add_le_add le_rfl ((norm_inner_le_norm (𝕜:=ℂ) x (w-u)).trans (by
        rw [hx,one_mul,norm_sub_rev w u]; exact hloc))
  have hid : inner ℂ u x=inner ℂ d u+inner ℂ u d-inner ℂ d (u-v) := by
    simp only [d,inner_sub_left,inner_sub_right,htransfer,hzero]
    abel
  have hrem : ‖inner ℂ d (u-v)‖≤ε^2 :=
    (norm_inner_le_norm ..).trans ((mul_le_mul hfit hmove (norm_nonneg _) h₀).trans_eq (sq ε).symm)
  have hcost : ‖inner ℂ u x‖≤2*‖inner ℂ d u‖+ε^2 := calc
    _ = _ := congrArg norm hid
    _ ≤ (‖inner ℂ d u‖+‖inner ℂ u d‖)+‖inner ℂ d (u-v)‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
    _ ≤ _ := by rw [norm_inner_symm u d]; linarith only [hrem]
  have heq : inner ℂ d u=inner ℂ d z+b*inner ℂ d x+inner ℂ d (u-w) := by
    simp only [z,inner_sub_right,inner_smul_right]
    abel
  have hdx : ‖inner ℂ d x‖≤ε := (norm_inner_le_norm ..).trans (by rw [hx,mul_one]; exact hfit)
  have hdu : ‖inner ℂ d (u-w)‖≤ε*δ := (norm_inner_le_norm ..).trans (mul_le_mul hfit hloc (norm_nonneg _) h₀)
  have hlin : ‖inner ℂ d u‖≤‖inner ℂ d z‖+‖b‖*ε+ε*δ := calc
    _ = _ := congrArg norm heq
    _ ≤ (‖inner ℂ d z‖+‖b*inner ℂ d x‖)+‖inner ℂ d (u-w)‖ :=
      (norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
    _ ≤ _ := by rw [norm_mul]; exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdx (norm_nonneg _))) hdu
  change (1-2*ε)*‖b‖≤2*‖inner ℂ d z‖+(1+2*ε)*δ+ε^2
  linarith only [hm,hcost,hlin]

/-- If the squared fitting error is at most an eighth of the signal,
a missing test costs a projection of at least one eighth of that signal. -/
theorem centered_missing_projection (x y u v w : E) {r δ ε : ℝ}
    (hx : ‖x‖=1) (hfit : ‖x-y‖≤ε) (hmove : ‖u-v‖≤ε) (hloc : ‖u-w‖≤δ)
    (htransfer : inner ℂ u y=inner ℂ x v) (hzero : inner ℂ y v=0)
    (hmean : r≤‖inner ℂ x w‖) (hδ : δ≤r/8) (hε : ε≤1/8) (hsq : ε^2≤r/8) :
    r/8≤‖inner ℂ (x-y) (w-inner ℂ x w • x)‖ := by
  have h := centered_missing_bound x y u v w hx hfit hmove hloc htransfer hzero
  have hδ₀ := (norm_nonneg _).trans hloc
  linarith only [h,hmean,hδ,hδ₀,hsq,mul_le_mul_of_nonneg_left hε (norm_nonneg (inner ℂ x w)),
    mul_le_mul_of_nonneg_right hε hδ₀]

/-- Each distinct centered test costs one squared projection of the same
error vector. Only the localized physical tests need be orthogonal. -/
theorem orthogonal_projection_count {ι : Type*} [Fintype ι] (z : ι→E) (d : E) {a : ℝ}
    (ha : 0<a) (hscore : ∀ i, a≤‖inner ℂ d (z i)‖) (hn : ∀ i, ‖z i‖≤1)
    (ho : ∀ i j, i≠j → inner ℂ (z i) (z j)=0) :
    (Fintype.card ι:ℝ)*a^2≤‖d‖^2 := by
  classical
  let v i := (‖z i‖:ℂ)⁻¹ • z i
  have hp (i) : 0<‖z i‖ := norm_pos_iff.mpr fun h => by
    have he := hscore i
    rw [h,inner_zero_right,norm_zero] at he
    exact ha.not_ge he
  have hv (i) : ‖v i‖=1 := by
    simp only [v,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (hp i).ne']
  have hb : Orthonormal ℂ v := by
    apply orthonormal_iff_ite.mpr
    intro i j
    by_cases hij : i=j
    · subst j; rw [if_pos rfl,inner_self_eq_norm_sq_to_K,hv]; norm_num
    · simp only [v,if_neg hij,inner_smul_left,inner_smul_right,ho i j hij,mul_zero]
  have hscale (i) : a≤‖inner ℂ (v i) d‖ := by
    rw [norm_inner_symm (v i) d]
    simp only [v,inner_smul_right,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    rw [mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ (hp i)).mpr ((mul_le_of_le_one_right ha.le (hn i)).trans (hscore i))
  have hh := (sum_le_sum (s:=univ) fun i _ => pow_le_pow_left₀ ha.le (hscale i) 2).trans
    (hb.sum_inner_products_le d)
  simpa only [sum_const,card_univ,nsmul_eq_mul] using hh

#print axioms centered_missing_bound
#print axioms centered_missing_projection
#print axioms orthogonal_projection_count
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
