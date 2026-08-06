import GaloisForLFunctions.HTGeometry.TriangularFrames
import GaloisForLFunctions.HTGeometry.ObserverDistNormBound

/-!
# The pencil of a moved ray

A ray of observer metrics moved by a symmetry, `t ↦ g* exp (t T) g`, is compared with the ray
`t ↦ exp (t S)` through the reference metric whose direction is the transported one.  The pencil
of the two, evaluated on the transported frame, is

```text
(P⁻¹ Q) (gs j) = ∑ i, ⟪b i, (g*)⁻¹ (gs j)⟫ · exp (t (w j - w i)) · g⁻¹ (b i),
```

and the two structural facts of the previous module make it bounded uniformly in `t ≥ 0`:
triangularity kills every term with `i > j`, and antitonicity of the weights makes the surviving
exponents nonpositive.
-/

namespace GaloisForLFunctions.HTGeometry

open Module InnerProductSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The inverse of an observer metric is any left inverse -/

theorem invOp_eq_of_left_inverse {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {M : E →ₗ[ℂ] E}
    (hM : ∀ v, M (P v) = v) (y : E) : invOp hP hn y = M y := by
  have h := comp_invOp hP hn hpos y
  conv_rhs => rw [← h]
  rw [hM]

/-! ## The inverse of a moved ray -/

theorem invOp_congrOp_metricRay (g : E ≃ₗ[ℂ] E) {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ) (y : E) :
    invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn y
      = g.symm (invOp (isSymmetric_metricRay hT hn t) hn
          (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) y)) := by
  have hApos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v ((metricRay T t : E →ₗ[ℂ] E) v)).re :=
    fun v hv => inner_metricRay_pos hT hn hv t
  refine invOp_eq_of_left_inverse _ hn (fun v hv => inner_congrOp_pos g hApos hv)
    (M := (g.symm : E →ₗ[ℂ] E) ∘ₗ ((invOp (isSymmetric_metricRay hT hn t) hn) ∘ₗ
      LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)))) ?_ y
  intro v
  show g.symm (invOp (isSymmetric_metricRay hT hn t) hn
      (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E))
        (congrOp g ((metricRay T t : E →ₗ[ℂ] E)) v))) = v
  rw [congrOp_apply, adjoint_symm_comp_adjoint,
    invOp_comp (isSymmetric_metricRay hT hn t) hn hApos]
  simp

/-! ## The inverse of a ray on its eigenframe -/

theorem invOp_metricRay_frame {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (t : ℝ) (b : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ}
    (hd : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i) (i : Fin n) :
    invOp (isSymmetric_metricRay hT hn t) hn (b i)
      = ((Real.exp (-(t * w i)) : ℝ) : ℂ) • b i := by
  have hApos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v ((metricRay T t : E →ₗ[ℂ] E) v)).re :=
    fun v hv => inner_metricRay_pos hT hn hv t
  have hray : (metricRay T t : E →ₗ[ℂ] E) (b i) = ((Real.exp (t * w i) : ℝ) : ℂ) • b i :=
    metricRay_apply_of_eigenvector (hd i) t
  have hinv := invOp_comp (isSymmetric_metricRay hT hn t) hn hApos (b i)
  rw [hray, map_smul] at hinv
  have hne : ((Real.exp (t * w i) : ℝ) : ℂ) ≠ 0 := by
    simp
  have := congrArg (fun z => ((Real.exp (t * w i) : ℝ) : ℂ)⁻¹ • z) hinv
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  rw [this]
  congr 1
  rw [← Complex.ofReal_inv, ← Real.exp_neg]

/-! ## Expanding a ray and its inverse in an eigenframe -/

theorem metricRay_expand {T : E →ₗ[ℂ] E} (t : ℝ) (b : OrthonormalBasis (Fin n) ℂ E)
    {w : Fin n → ℝ} (hd : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i) (y : E) :
    (metricRay T t : E →ₗ[ℂ] E) y
      = ∑ i, (((Real.exp (t * w i) : ℝ) : ℂ) * (inner ℂ (b i) y : ℂ)) • b i := by
  classical
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hray : (metricRay T t : E →ₗ[ℂ] E) (b i) = ((Real.exp (t * w i) : ℝ) : ℂ) • b i :=
    metricRay_apply_of_eigenvector (hd i) t
  rw [map_smul, hray, smul_smul, b.repr_apply_apply, mul_comm]

theorem invOp_metricRay_expand {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (t : ℝ) (b : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ}
    (hd : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i) (y : E) :
    invOp (isSymmetric_metricRay hT hn t) hn y
      = ∑ i, (((Real.exp (-(t * w i)) : ℝ) : ℂ) * (inner ℂ (b i) y : ℂ)) • b i := by
  classical
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, invOp_metricRay_frame hT hn t b hd i, smul_smul, b.repr_apply_apply, mul_comm]

/-! ## The pencil on the transported frame -/

theorem pencil_apply (g : E ≃ₗ[ℂ] E) {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ)
    (b gs : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ}
    (hdT : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hdS : ∀ j, S (gs j) = ((w j : ℝ) : ℂ) • gs j) (j : Fin n) :
    (invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn ∘ₗ
        ((metricRay S t : E →ₗ[ℂ] E))) (gs j)
      = ∑ i, (((Real.exp (t * (w j - w i)) : ℝ) : ℂ)
          * (inner ℂ (b i) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ))
        • g.symm (b i) := by
  classical
  set y := LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j) with hy
  have hray : (metricRay S t : E →ₗ[ℂ] E) (gs j) = ((Real.exp (t * w j) : ℝ) : ℂ) • gs j :=
    metricRay_apply_of_eigenvector (hdS j) t
  have hexp : (invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn ∘ₗ
      ((metricRay S t : E →ₗ[ℂ] E))) (gs j)
      = ((Real.exp (t * w j) : ℝ) : ℂ) • g.symm
        (invOp (isSymmetric_metricRay hT hn t) hn y) := by
    show invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn
        ((metricRay S t : E →ₗ[ℂ] E) (gs j)) = _
    rw [hray, map_smul, invOp_congrOp_metricRay g hT hn t (gs j), ← hy]
  have hyexp := invOp_metricRay_expand hT hn t b hdT y
  rw [hexp, hyexp, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_smul]
  congr 1
  have harg : t * w j + -(t * w i) = t * (w j - w i) := by ring
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, harg]


/-! ## The pencil is bounded uniformly along the ray -/

/-- **The pencil is bounded on each transported frame vector, uniformly in `t ≥ 0`.**  In the
expansion of the pencil the exponent `t (w j - w i)` occurs only for `i ≤ j`, where antitonicity
makes it nonpositive; the terms with `i > j` vanish by triangularity. -/
theorem norm_pencil_apply_le (g : E ≃ₗ[ℂ] E) {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 ≤ t)
    (b gs : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ} (hw : Antitone w)
    (hdT : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hdS : ∀ j, S (gs j) = ((w j : ℝ) : ℂ) • gs j)
    (htri : ∀ j, LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)
      ∈ Submodule.span ℂ (b '' Set.Iic j)) (j : Fin n) :
    ‖(invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn ∘ₗ
        ((metricRay S t : E →ₗ[ℂ] E))) (gs j)‖
      ≤ ∑ i, ‖(inner ℂ (b i) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ)‖
        * ‖g.symm (b i)‖ := by
  classical
  rw [pencil_apply g hT hn t b gs hdT hdS j]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rcases le_or_gt i j with hij | hij
  · have hle : Real.exp (t * (w j - w i)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hw hij]
    have hstep : Real.exp (t * (w j - w i))
        * ‖(inner ℂ (b i) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ)‖
        ≤ ‖(inner ℂ (b i) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ)‖ := by
      nlinarith [norm_nonneg ((inner ℂ (b i)
        (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ)), Real.exp_pos (t * (w j - w i))]
    exact mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  · rw [inner_eq_zero_of_mem_span_Iic b (htri j) hij]
    simp

/-- **The pencil of a moved ray against the transported ray is bounded uniformly in `t ≥ 0`.** -/
theorem norm_pencil_le (g : E ≃ₗ[ℂ] E) {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 ≤ t)
    (b gs : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ} (hw : Antitone w)
    (hdT : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hdS : ∀ j, S (gs j) = ((w j : ℝ) : ℂ) • gs j)
    (htri : ∀ j, LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)
      ∈ Submodule.span ℂ (b '' Set.Iic j)) :
    ‖LinearMap.toContinuousLinearMap
        (invOp (isSymmetric_congrOp g (isSymmetric_metricRay hT hn t)) hn ∘ₗ
          ((metricRay S t : E →ₗ[ℂ] E)))‖
      ≤ ∑ j, ∑ i, ‖(inner ℂ (b i) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (gs j)) : ℂ)‖
        * ‖g.symm (b i)‖ :=
  le_trans (norm_toCLM_le_sum_norm_apply gs _)
    (Finset.sum_le_sum fun j _ => norm_pencil_apply_le g hT hn ht b gs hw hdT hdS htri j)


/-! ## The mirror pencil -/

/-- The pencil in the other direction, expanded on both frames.  The coefficient of `gs j` carries
the exponent `t (w i - w j)`, and triangularity in the other direction makes the inner product
vanish for `j > i`. -/
theorem mirror_pencil_apply (g : E ≃ₗ[ℂ] E) {T S : E →ₗ[ℂ] E} (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ)
    (b gs : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ}
    (hdT : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hdS : ∀ j, S (gs j) = ((w j : ℝ) : ℂ) • gs j) (x : E) :
    (invOp (isSymmetric_metricRay hS hn t) hn ∘ₗ congrOp g ((metricRay T t : E →ₗ[ℂ] E))) x
      = ∑ i, ∑ j, (((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
          * ((inner ℂ (b i) (g x) : ℂ)
            * (inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ))) • gs j := by
  classical
  show invOp (isSymmetric_metricRay hS hn t) hn
      (congrOp g ((metricRay T t : E →ₗ[ℂ] E)) x) = _
  rw [congrOp_apply, metricRay_expand t b hdT (g x), map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, invOp_metricRay_expand hS hn t gs hdS
    (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  have hsplit : ((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
      = ((Real.exp (t * w i) : ℝ) : ℂ) * ((Real.exp (-(t * w j)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit]
  ring

/-- **The mirror pencil is bounded uniformly in `t ≥ 0`.** -/
theorem norm_mirror_pencil_le (g : E ≃ₗ[ℂ] E) {T S : E →ₗ[ℂ] E} (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 ≤ t)
    (b gs : OrthonormalBasis (Fin n) ℂ E) {w : Fin n → ℝ} (hw : Antitone w)
    (hdT : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hdS : ∀ j, S (gs j) = ((w j : ℝ) : ℂ) • gs j)
    (htri : ∀ i, LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)
      ∈ Submodule.span ℂ (gs '' Set.Iic i)) :
    ‖LinearMap.toContinuousLinearMap
        (invOp (isSymmetric_metricRay hS hn t) hn ∘ₗ congrOp g ((metricRay T t : E →ₗ[ℂ] E)))‖
      ≤ ‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖
        * ∑ i, ∑ j, ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)) fun x => ?_
  have hx : ‖g x‖
      ≤ ‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖ * ‖x‖ :=
    (LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))).le_opNorm x
  have hval : (LinearMap.toContinuousLinearMap
      (invOp (isSymmetric_metricRay hS hn t) hn ∘ₗ
        congrOp g ((metricRay T t : E →ₗ[ℂ] E)))) x
      = ∑ i, ∑ j, (((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
          * ((inner ℂ (b i) (g x) : ℂ)
            * (inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ))) • gs j :=
    mirror_pencil_apply g hS hn t b gs hdT hdS x
  rw [hval]
  have hterm : ∀ i j : Fin n, ‖(((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
      * ((inner ℂ (b i) (g x) : ℂ)
        * (inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ))) • gs j‖
      ≤ (‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖ * ‖x‖)
        * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖ := by
    intro i j
    rw [norm_smul, gs.orthonormal.1 j, mul_one, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_or_gt j i with hji | hji
    · have hle : Real.exp (t * (w i - w j)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hw hji]
      have hinner : ‖(inner ℂ (b i) (g x) : ℂ)‖ ≤ ‖g x‖ := by
        calc ‖(inner ℂ (b i) (g x) : ℂ)‖
            ≤ ‖b i‖ * ‖g x‖ := norm_inner_le_norm _ _
          _ = ‖g x‖ := by rw [b.orthonormal.1 i, one_mul]
      have hbound : ‖(inner ℂ (b i) (g x) : ℂ)‖
          ≤ ‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖ * ‖x‖ := le_trans hinner hx
      calc Real.exp (t * (w i - w j)) * (‖(inner ℂ (b i) (g x) : ℂ)‖
              * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖)
          ≤ 1 * (‖(inner ℂ (b i) (g x) : ℂ)‖
              * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖(inner ℂ (b i) (g x) : ℂ)‖
              * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖ := one_mul _
        _ ≤ (‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖ * ‖x‖)
              * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    · rw [inner_eq_zero_of_mem_span_Iic gs (htri i) hji]
      simp
  calc ‖∑ i, ∑ j, (((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
        * ((inner ℂ (b i) (g x) : ℂ)
          * (inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ))) • gs j‖
      ≤ ∑ i, ‖∑ j, (((Real.exp (t * (w i - w j)) : ℝ) : ℂ)
        * ((inner ℂ (b i) (g x) : ℂ)
          * (inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ))) • gs j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, (‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖ * ‖x‖)
        * ‖(inner ℂ (gs j) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => hterm i j)
    _ = ‖LinearMap.toContinuousLinearMap ((g : E →ₗ[ℂ] E))‖
        * (∑ i, ∑ j, ‖(inner ℂ (gs j)
          (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) : ℂ)‖) * ‖x‖ := by
        simp only [← Finset.mul_sum]
        ring

end GaloisForLFunctions.HTGeometry
