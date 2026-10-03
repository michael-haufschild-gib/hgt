import GaloisForLFunctions.HTGeometry.GraphCapOperatorArea

/-!
# Monotone determinant-line action filtration of a contracted graph cap

Let `A : H₊ → H₋` be Hilbert–Schmidt and `(S_c)_{c ≥ 0}` a contraction semigroup on `H₋`.  Put
`A_c = S_c A`, `K_c = A_c* A_c` and let `E(c) = Tr(K_c(I + K_c)⁻¹)` be the determinant-line area of the
graph cap `z ↦ graph(z A_c)` **(BGAF.1)**.

* **(BGAF.6)** `K_c - K_{c+h} = A_c*(I - S_h* S_h) A_c`, hence `0 ≤ K_d ≤ K_c` for `c ≤ d`.
* **(BGAF.7)** `f(K) - f(L) = (I+L)⁻¹ (K - L)(I+K)⁻¹` for `f(t) = t/(1+t)`, and `f` is operator monotone
  (inversion reverses the Loewner order of `I + K`).
* **Theorem BGAF-A (BGAF.2)–(BGAF.5)** `E` is nonnegative and antitone, tends to `0` when
  `‖A_c‖_HS → 0`; the interval action `E(c) - E(d)` is nonnegative and exactly additive, and its total
  mass is the graph-cap area `E(0) ≤ ‖A‖²_HS`.
-/

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace NNReal ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## Operator monotonicity of `t ↦ t/(1+t)` -/

omit [CompleteSpace E] in
theorem resolventRatio_eq_one_sub {K : E →L[ℂ] E} (hu : IsUnit (1 + K)) :
    resolventRatio K = 1 - Ring.inverse (1 + K) := by
  have h := Ring.mul_inverse_cancel _ hu
  have e : K * Ring.inverse (1 + K) = (1 + K) * Ring.inverse (1 + K) - Ring.inverse (1 + K) := by
    rw [add_mul, one_mul]
    abel
  rw [resolventRatio, e, h]

omit [CompleteSpace E] in
/-- **(BGAF.7) The resolvent identity** `f(K) - f(L) = (I + L)⁻¹ (K - L) (I + K)⁻¹`. -/
theorem resolventRatio_sub {K L : E →L[ℂ] E} (hK : IsUnit (1 + K)) (hL : IsUnit (1 + L)) :
    resolventRatio K - resolventRatio L =
      Ring.inverse (1 + L) * (K - L) * Ring.inverse (1 + K) := by
  rw [resolventRatio_eq_one_sub hK, resolventRatio_eq_one_sub hL]
  have h1 := Ring.inverse_mul_cancel _ hL
  have h2 := Ring.mul_inverse_cancel _ hK
  have e : K - L = (1 + K) - (1 + L) := by abel
  calc 1 - Ring.inverse (1 + K) - (1 - Ring.inverse (1 + L))
      = Ring.inverse (1 + L) * 1 - 1 * Ring.inverse (1 + K) := by rw [mul_one, one_mul]; abel
    _ = Ring.inverse (1 + L) * ((1 + K) * Ring.inverse (1 + K)) -
          Ring.inverse (1 + L) * (1 + L) * Ring.inverse (1 + K) := by rw [h1, h2]
    _ = Ring.inverse (1 + L) * (K - L) * Ring.inverse (1 + K) := by
          simp only [e, mul_sub, sub_mul, mul_assoc]

/-- **Operator monotonicity of `t/(1+t)`.**  If `0 ≤ L ≤ K` and `I + L`, `I + K` are invertible, then
`f(L) ≤ f(K)`: inversion reverses the order `I + L ≤ I + K`. -/
theorem resolventRatio_mono {K L : E →L[ℂ] E} (hL0 : 0 ≤ L) (hLK : L ≤ K) (huL : IsUnit (1 + L))
    (huK : IsUnit (1 + K)) : resolventRatio L ≤ resolventRatio K := by
  rw [resolventRatio_eq_one_sub huL, resolventRatio_eq_one_sub huK]
  refine sub_le_sub_left ?_ 1
  have h0 : (0 : E →L[ℂ] E) ≤ 1 := (nonneg_iff_isPositive 1).2 isPositive_one
  have h1 : (0 : E →L[ℂ] E) ≤ (huL.unit : E →L[ℂ] E) := by
    rw [huL.unit_spec]
    exact add_nonneg h0 hL0
  have h2 : (huL.unit : E →L[ℂ] E) ≤ huK.unit := by
    rw [huL.unit_spec, huK.unit_spec]
    exact add_le_add le_rfl hLK
  have h := CStarAlgebra.inv_le_inv h1 h2
  rwa [← Ring.inverse_unit, ← Ring.inverse_unit, huL.unit_spec, huK.unit_spec] at h

/-- **The trace is monotone in the Loewner order** on Hilbert–Schmidt products. -/
theorem re_opTrace_mono {X Y : E →L[ℂ] E} (hXY : X ≤ Y) {G G' : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup G'] [InnerProductSpace ℂ G']
    [CompleteSpace G'] {S : G →L[ℂ] E} {U : E →L[ℂ] G} {S' : G' →L[ℂ] E} {U' : E →L[ℂ] G'}
    (hS : IsHilbertSchmidt S) (hU : IsHilbertSchmidt U) (hS' : IsHilbertSchmidt S')
    (hU' : IsHilbertSchmidt U') (hX : X = S ∘L U) (hY : Y = S' ∘L U') :
    (opTrace X).re ≤ (opTrace Y).re := by
  have hsX : Summable fun i => ⟪hsBasis ℂ E i, X (hsBasis ℂ E i)⟫_ℂ := by
    rw [hX]
    exact summable_inner_diag_comp hS hU _
  have hsY : Summable fun i => ⟪hsBasis ℂ E i, Y (hsBasis ℂ E i)⟫_ℂ := by
    rw [hY]
    exact summable_inner_diag_comp hS' hU' _
  rw [opTrace, opTrace, Complex.re_tsum hsX, Complex.re_tsum hsY]
  refine (Complex.reCLM.summable hsX).tsum_le_tsum (fun i => ?_) (Complex.reCLM.summable hsY)
  have hpos := ((ContinuousLinearMap.le_def X Y).1 hXY).re_inner_nonneg_right (hsBasis ℂ E i)
  rw [sub_apply, inner_sub_right, map_sub, RCLike.re_to_complex, RCLike.re_to_complex] at hpos
  linarith

/-! ## The damped graph caps -/

section Filtration

variable {A : E →L[ℂ] F} (hA : IsHilbertSchmidt A) (S : ℝ≥0 → F →L[ℂ] F)

theorem graphCapArea_congr {B C : E →L[ℂ] F} (h : B = C) (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : graphCapArea B hB = graphCapArea C hC := by
  subst h
  rfl

/-- **(BGAF.1)** `E(c) = Area_det(z ↦ graph(z S_c A))`. -/
def graphAction (c : ℝ≥0) : ℝ := graphCapArea (S c ∘L A) (hA.comp_left (S c))

/-- **(BGAF.3)** `Action(c, d) = E(c) - E(d)`. -/
def intervalAction (c d : ℝ≥0) : ℝ := graphAction hA S c - graphAction hA S d

include hA in
/-- `E(c) = Tr(K_c (I + K_c)⁻¹)`, nonnegative and at most `‖A_c‖²_HS`. -/
theorem graphAction_spec (c : ℝ≥0) :
    (opTrace (resolventRatio (adjoint (S c ∘L A) ∘L (S c ∘L A)))).re = graphAction hA S c ∧
      0 ≤ graphAction hA S c ∧ graphAction hA S c ≤ hsNormSq (S c ∘L A) := by
  haveI : Fact (IsCompactOperator (adjoint (S c ∘L A) ∘L (S c ∘L A))) :=
    ⟨isCompactOperator_adjoint_comp_self (hA.comp_left (S c))⟩
  obtain ⟨-, h2, h3, h4, -⟩ := graphCapArea_eq (hA.comp_left (S c))
  exact ⟨by rw [h2, Complex.ofReal_re]; rfl, h3, h4⟩

/-- **(BGAF.6)** `K_c - K_{h+c} = A_c* (I - S_h* S_h) A_c` for a semigroup step. -/
theorem gram_sub_damped {c h : ℝ≥0} (hsemi : S (h + c) = S h ∘L S c) :
    adjoint (S c ∘L A) ∘L (S c ∘L A) - adjoint (S (h + c) ∘L A) ∘L (S (h + c) ∘L A) =
      adjoint (S c ∘L A) ∘L (1 - adjoint (S h) ∘L S h) ∘L (S c ∘L A) := by
  rw [hsemi, comp_assoc, adjoint_comp (S h) (S c ∘L A)]
  ext x
  simp only [sub_apply, comp_apply, one_apply_eq_self, map_sub]

/-- The defect `I - S* S` of a contraction is positive. -/
theorem isPositive_one_sub_adjoint_comp_self {T : F →L[ℂ] F} (hT : ‖T‖ ≤ 1) :
    (1 - adjoint T ∘L T).IsPositive := by
  rw [isPositive_iff]
  refine ⟨?_, fun x => ?_⟩
  · intro x y
    simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_comp, LinearMap.sub_apply,
      ContinuousLinearMap.coe_coe, one_apply_eq_self, Function.comp_apply, inner_sub_left,
      inner_sub_right, adjoint_inner_left, adjoint_inner_right]
  · have hle : ‖T x‖ ≤ ‖x‖ := by
      calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
        _ ≤ 1 * ‖x‖ := by gcongr
        _ = ‖x‖ := one_mul _
    have e : ⟪(1 - adjoint T ∘L T) x, x⟫_ℂ = ((‖x‖ ^ 2 - ‖T x‖ ^ 2 : ℝ) : ℂ) := by
      rw [sub_apply, one_apply_eq_self, comp_apply, inner_sub_left, adjoint_inner_left,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [e, Complex.zero_le_real]
    nlinarith [norm_nonneg (T x), norm_nonneg x]

/-- **(BGAF.2), Gram order.**  For a contraction step, `0 ≤ K_{h+c} ≤ K_c`. -/
theorem gram_damped_le {c h : ℝ≥0} (hsemi : S (h + c) = S h ∘L S c) (hcon : ‖S h‖ ≤ 1) :
    0 ≤ adjoint (S (h + c) ∘L A) ∘L (S (h + c) ∘L A) ∧
      adjoint (S (h + c) ∘L A) ∘L (S (h + c) ∘L A) ≤ adjoint (S c ∘L A) ∘L (S c ∘L A) := by
  refine ⟨(nonneg_iff_isPositive _).2 (isPositive_adjoint_comp_self _), ?_⟩
  rw [ContinuousLinearMap.le_def, gram_sub_damped S hsemi]
  exact (isPositive_one_sub_adjoint_comp_self hcon).adjoint_conj (S c ∘L A)

variable (hsemi : ∀ h c, S (h + c) = S h ∘L S c) (hcon : ∀ h, ‖S h‖ ≤ 1)
include hA hsemi hcon

/-- **(BGAF.2), action order.**  `E` is antitone. -/
theorem graphAction_antitone : Antitone (graphAction hA S) := by
  intro c d hcd
  obtain ⟨h, rfl⟩ : ∃ h, d = h + c := ⟨d - c, (tsub_add_cancel_of_le hcd).symm⟩
  obtain ⟨hK0, hKle⟩ := gram_damped_le (A := A) S (hsemi h c) (hcon h)
  have hd := hA.comp_left (S (h + c))
  have hc := hA.comp_left (S c)
  have hmono := resolventRatio_mono hK0 hKle (isUnit_one_add_adjoint_comp_self hd)
    (isUnit_one_add_adjoint_comp_self hc)
  rw [← (graphAction_spec hA S (h + c)).1, ← (graphAction_spec hA S c).1]
  have fd : resolventRatio (adjoint (S (h + c) ∘L A) ∘L (S (h + c) ∘L A)) =
      adjoint (S (h + c) ∘L A) ∘L ((S (h + c) ∘L A) ∘L
        Ring.inverse (1 + adjoint (S (h + c) ∘L A) ∘L (S (h + c) ∘L A))) := by
    rw [resolventRatio, mul_def, comp_assoc]
  have fc : resolventRatio (adjoint (S c ∘L A) ∘L (S c ∘L A)) =
      adjoint (S c ∘L A) ∘L ((S c ∘L A) ∘L Ring.inverse (1 + adjoint (S c ∘L A) ∘L (S c ∘L A))) := by
    rw [resolventRatio, mul_def, comp_assoc]
  exact re_opTrace_mono hmono hd.adjoint (hd.comp_right _) hc.adjoint (hc.comp_right _) fd fc

omit hsemi hcon in
/-- **(BGAF.2), extinction.**  If `‖A_c‖_HS → 0`, then `E(c) → 0`. -/
theorem tendsto_graphAction (hext : Tendsto (fun c => hsNormSq (S c ∘L A)) atTop (𝓝 0)) :
    Tendsto (graphAction hA S) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hext
    (fun c => (graphAction_spec hA S c).2.1) (fun c => (graphAction_spec hA S c).2.2)

/-- **(BGAF.3)** The interval action is nonnegative. -/
theorem intervalAction_nonneg {c d : ℝ≥0} (hcd : c ≤ d) : 0 ≤ intervalAction hA S c d :=
  sub_nonneg.2 (graphAction_antitone hA S hsemi hcon hcd)

omit hsemi hcon in
/-- **(BGAF.4)** The interval action is exactly additive. -/
theorem intervalAction_add (c d e : ℝ≥0) :
    intervalAction hA S c e = intervalAction hA S c d + intervalAction hA S d e := by
  unfold intervalAction
  ring

omit hsemi hcon in
/-- **(BGAF.5)** The total action is the area of the undamped cap, at most `‖A‖²_HS`. -/
theorem tendsto_intervalAction_total (hext : Tendsto (fun c => hsNormSq (S c ∘L A)) atTop (𝓝 0))
    (hone : S 0 = 1) :
    Tendsto (fun d => intervalAction hA S 0 d) atTop (𝓝 (graphCapArea A hA)) ∧
      graphCapArea A hA ≤ hsNormSq A := by
  have hc1 : S 0 ∘L A = A := by
    rw [hone]
    ext x
    simp
  have h0 : graphAction hA S 0 = graphCapArea A hA :=
    graphCapArea_congr hc1 (hA.comp_left (S 0)) hA
  have hA0 : graphCapArea A hA ≤ hsNormSq A := by
    have := (graphAction_spec hA S 0).2.2
    rwa [h0, hc1] at this
  refine ⟨?_, hA0⟩
  have h := (tendsto_const_nhds (x := graphAction hA S 0)).sub (tendsto_graphAction hA S hext)
  rw [sub_zero] at h
  rw [← h0]
  exact h

end Filtration

end GaloisForLFunctions.HTGeometry
