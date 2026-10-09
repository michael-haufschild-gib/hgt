import GaloisForLFunctions.HTGeometry.QKrawtchoukFiniteResolvent
import GaloisForLFunctions.HTGeometry.QKrawtchoukJacobiResolvent
import GaloisForLFunctions.HTGeometry.StrongConvergenceDense

/-!
# Strong resolvent convergence of the pinned Jacobi approximants

The actual finite quadrature operators and the selected infinite operator
act on one common ℓ² space. Their resolvent entries converge by the pinned
quadrature theorem. Self-adjointness identifies the imaginary part of each
diagonal entry with the squared norm of the corresponding resolvent vector.
Thus entry convergence becomes strong convergence on coordinate vectors;
the uniform resolvent bound extends it to every vector.

This implements the scalar-to-operator mechanism of arXiv:2609.24149,
Theorem 6.1, for the explicitly constructed pinned quadratures.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators LinearPMap ComplexConjugate Topology
open GaloisForLFunctions.HTGeometry
  (tendsto_of_dense_of_uniform_bound inner_selfAdjoint_self_im)

namespace HTGeometry

private def convergenceSpace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ℕ → lp (fun _ : ℕ => ℂ) 2 →L[ℂ] F) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] F) :
    Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) where
  carrier := {v | Tendsto (fun n => T n v) atTop (𝓝 (S v))}
  zero_mem' := by
    simpa only [Set.mem_setOf_eq, map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : F)) atTop (𝓝 0))
  add_mem' := by
    intro v w hv hw
    simpa only [Set.mem_setOf_eq, map_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    simpa only [Set.mem_setOf_eq, map_smul] using hv.const_smul c

private theorem coordinate_dense :
    Dense (Submodule.span ℂ (Set.range (fun i : ℕ =>
      (lp.single 2 i (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2))) : Set (lp (fun _ : ℕ => ℂ) 2)) := by
  let B : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) := ⟨LinearIsometryEquiv.refl ℂ _⟩
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hb (i : ℕ) : B i = lp.single 2 i (1 : ℂ) := by
    exact (B.repr_symm_single i).symm
  simpa only [show (B : ℕ → lp (fun _ : ℕ => ℂ) 2) =
    (fun i => lp.single 2 i (1 : ℂ)) from funext hb] using B.dense_span

private theorem tendsto_of_coordinates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : ℕ → lp (fun _ : ℕ => ℂ) 2 →L[ℂ] F} {S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] F}
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ n, ‖T n‖ ≤ C) (hS : ‖S‖ ≤ C)
    (hc : ∀ i : ℕ, Tendsto (fun n => T n (lp.single 2 i (1 : ℂ))) atTop
      (𝓝 (S (lp.single 2 i (1 : ℂ))))) (v : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun n => T n v) atTop (𝓝 (S v)) := by
  have hspan : Submodule.span ℂ (Set.range (fun i : ℕ =>
      (lp.single 2 i (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2))) ≤ convergenceSpace T S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hc i
  exact tendsto_of_dense_of_uniform_bound hC (Eventually.of_forall hT) hS coordinate_dense
    (fun w hw => hspan hw) v

private theorem complex_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : E) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  change (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ)
  exact (Complex.ofReal_pow _ _).symm

private theorem tendsto_of_inner_and_norm_sq
    {v : lp (fun _ : ℕ => ℂ) 2} {u : ℕ → lp (fun _ : ℕ => ℂ) 2}
    (hi : Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ v v)))
    (hn : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2))) :
    Tendsto u atTop (𝓝 v) := by
  have hr : Tendsto (fun n => (inner ℂ (u n) v).re) atTop (𝓝 (‖v‖ ^ 2)) := by
    have h := (Complex.reCLM.continuous.tendsto _).comp hi
    simpa only [Function.comp_def, Complex.reCLM_apply, complex_inner_self,
      Complex.ofReal_re] using h
  have hs : Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 0) := by
    have h := (hn.sub (hr.const_mul 2)).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖v‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2)))
    have hzero : ‖v‖ ^ 2 - 2 * ‖v‖ ^ 2 + ‖v‖ ^ 2 = 0 := by ring
    simp only [norm_sub_sq (𝕜 := ℂ)]
    change Tendsto (fun n => ‖u n‖ ^ 2 - 2 * (inner ℂ (u n) v).re + ‖v‖ ^ 2) atTop (𝓝 0)
    simpa only [hzero] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

private theorem shifted_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (z : ℂ) (f : E)
    (u : A.domain) (hu : A u - z • (u : E) = f) :
    (inner ℂ f (u : E)).im = z.im * ‖(u : E)‖ ^ 2 := by
  have hd := inner_selfAdjoint_self_im hA u
  rw [← hu, inner_sub_left, inner_smul_left, complex_inner_self]
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, hd, mul_zero, zero_add, zero_sub]
  ring

/-- The actual finite self-adjoint operator selected by a pinned node. -/
def inverseQHermitePinnedJacobi (t u x : ℝ) (n : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  inverseQHermiteFiniteJacobi t u (inverseQHermitePinnedLevel t u x n)
    (inverseQHermitePinnedParameter t u x n)

/-- Its resolvent, on the same sequence space as the selected infinite operator. -/
def inverseQHermitePinnedResolvent (t u x : ℝ) (n : ℕ) (a b : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  inverseQHermiteFiniteResolvent t u (inverseQHermitePinnedLevel t u x n)
    (inverseQHermitePinnedParameter t u x n) a b

private theorem pinned_norm_bound (t u x : ℝ) (n : ℕ) (a b : ℝ) :
    ‖inverseQHermitePinnedResolvent t u x n a b‖ ≤ Real.exp (-b) :=
  inverseQHermiteFiniteResolvent_norm_le t u _ _ a b

private theorem pinned_energy (t u x : ℝ) (n : ℕ) (a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    (inner ℂ f (inverseQHermitePinnedResolvent t u x n a b f)).im =
      Real.exp b * ‖inverseQHermitePinnedResolvent t u x n a b f‖ ^ 2 :=
  shifted_energy (inverseQHermiteFiniteJacobi_isSelfAdjoint t u
      (inverseQHermitePinnedLevel t u x n) (inverseQHermitePinnedParameter t u x n))
    (Complex.mk a (Real.exp b)) f ⟨inverseQHermitePinnedResolvent t u x n a b f, by trivial⟩
    (inverseQHermiteFiniteJacobi_resolvent t u _ _ a b f)

private theorem selected_energy (t u x a b : ℝ) (f : lp (fun _ : ℕ => ℂ) 2) :
    (inner ℂ f (inverseQHermiteResolvent t u x a b f)).im =
      Real.exp b * ‖inverseQHermiteResolvent t u x a b f‖ ^ 2 :=
  shifted_energy (inverseQHermiteJacobi_isSelfAdjoint t u x) (Complex.mk a (Real.exp b)) f
    ⟨inverseQHermiteResolvent t u x a b f, inverseQHermiteResolvent_mem_domain t u x a b f⟩
    (inverseQHermiteJacobi_resolvent t u x a b f)

private theorem pinned_entries_tendsto (t u x r a b : ℝ) (i j : ℕ) :
    Tendsto (fun n : ℕ => inner ℂ (lp.single 2 i (1 : ℂ))
      (inverseQHermitePinnedResolvent t u (x + r / ((n : ℝ) + 1)) n a b
        (lp.single 2 j (1 : ℂ)))) atTop
      (𝓝 (inner ℂ (lp.single 2 i (1 : ℂ))
        (inverseQHermiteResolvent t u x a b (lp.single 2 j (1 : ℂ))))) := by
  apply (inverseQHermitePinnedQuadrature_resolventEntry_tendsto t u x r a b i j).congr'
  filter_upwards [eventually_ge_atTop (max i j)] with n hn
  let ξ := x + r / ((n : ℝ) + 1)
  let level := inverseQHermitePinnedLevel t u ξ n
  have hi : i < level + 1 := by
    dsimp [level, inverseQHermitePinnedLevel]
    split <;> omega
  have hj : j < level + 1 := by
    dsimp [level, inverseQHermitePinnedLevel]
    split <;> omega
  exact (inverseQHermiteFiniteResolvent_matrixElement_integral t u level
    (inverseQHermitePinnedParameter t u ξ n) a b ⟨i, hi⟩ ⟨j, hj⟩).symm

/-- The pinned finite Jacobi resolvents converge strongly to the actual selected
self-adjoint extension, for every upper-half-plane parameter and every vector. -/
theorem inverseQHermitePinnedResolvent_strong_tendsto (t u x r a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun n : ℕ => inverseQHermitePinnedResolvent t u (x + r / ((n : ℝ) + 1)) n a b f)
      atTop (𝓝 (inverseQHermiteResolvent t u x a b f)) := by
  let T := fun n : ℕ => inverseQHermitePinnedResolvent t u (x + r / ((n : ℝ) + 1)) n a b
  let S := inverseQHermiteResolvent t u x a b
  let C := Real.exp (-b)
  have hT (n : ℕ) : ‖T n‖ ≤ C := pinned_norm_bound t u _ n a b
  have hS : ‖S‖ ≤ C := inverseQHermiteResolvent_norm_le t u x a b
  apply tendsto_of_coordinates (Real.exp_pos (-b)).le hT hS ?_ f
  intro j
  let e : lp (fun _ : ℕ => ℂ) 2 := lp.single 2 j (1 : ℂ)
  have hn : Tendsto (fun n => ‖T n e‖ ^ 2) atTop (𝓝 (‖S e‖ ^ 2)) := by
    have hi := (Complex.imCLM.continuous.tendsto _).comp (pinned_entries_tendsto t u x r a b j j)
    change Tendsto (fun n => (inner ℂ e (T n e)).im) atTop (𝓝 ((inner ℂ e (S e)).im)) at hi
    have heT (n : ℕ) : (inner ℂ e (T n e)).im = Real.exp b * ‖T n e‖ ^ 2 :=
      pinned_energy t u _ n a b e
    have heS : (inner ℂ e (S e)).im = Real.exp b * ‖S e‖ ^ 2 := selected_energy t u x a b e
    simpa only [heT, heS, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos b).ne', one_mul] using
      hi.const_mul (Real.exp b)⁻¹
  have hdualT (n : ℕ) : ‖innerSL ℂ (T n e)‖ ≤ C * ‖e‖ := by
    rw [innerSL_apply_norm]
    exact ((T n).le_opNorm e).trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg e))
  have hdualS : ‖innerSL ℂ (S e)‖ ≤ C * ‖e‖ := by
    rw [innerSL_apply_norm]
    exact (S.le_opNorm e).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg e))
  have hi : Tendsto (fun n => inner ℂ (T n e) (S e)) atTop (𝓝 (inner ℂ (S e) (S e))) := by
    apply tendsto_of_coordinates (mul_nonneg (Real.exp_pos (-b)).le (norm_nonneg e))
      hdualT hdualS ?_ (S e)
    intro i
    change Tendsto (fun n => inner ℂ (T n e) (lp.single 2 i (1 : ℂ))) atTop
      (𝓝 (inner ℂ (S e) (lp.single 2 i (1 : ℂ))))
    simpa only [Complex.star_def, inner_conj_symm] using (pinned_entries_tendsto t u x r a b i j).star
  exact tendsto_of_inner_and_norm_sq hi hn

end HTGeometry
