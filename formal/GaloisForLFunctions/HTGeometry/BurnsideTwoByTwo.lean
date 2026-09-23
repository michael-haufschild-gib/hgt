import Mathlib

/-!
# Burnside's theorem for `2 × 2` matrices

A matrix algebra acting irreducibly on the plane is the whole matrix algebra.

The proof is the classical one, written out in two dimensions.  An algebra that is not contained in
the scalars has a non-scalar element, and subtracting an eigenvalue — which exists because the base
field is algebraically closed — leaves a nonzero singular element, hence a rank-one element `v wᵀ`.
Multiplying it on both sides inside the algebra gives `(x v)(w y)ᵀ`, and irreducibility makes the
vectors `x v` and the covectors `w y` sweep the whole plane and its dual; the resulting rank-one
matrices span everything.

The dual sweep is itself irreducibility: a covector annihilating every `w y` annihilates the span of
`{y z}` for the vector `z` it comes from, which is everything.

The companion statement here turns the hypothesis into the form a group supplies: a set of matrices
containing the identity and stabilising no line has orbits that span, because in the plane a proper
subspace containing a nonzero vector is exactly its line.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

/-- A singular nonzero `2 × 2` matrix is a rank-one product. -/
theorem exists_vecMulVec_of_det_eq_zero {r : Matrix (Fin 2) (Fin 2) U} (hr : r ≠ 0)
    (hdet : r.det = 0) :
    ∃ v w : Fin 2 → U, v ≠ 0 ∧ w ≠ 0 ∧ r = Matrix.vecMulVec v w := by
  classical
  rw [Matrix.det_fin_two] at hdet
  by_cases hrow : r 0 0 = 0 ∧ r 0 1 = 0
  · obtain ⟨h00, h01⟩ := hrow
    have hne : ¬ (r 1 0 = 0 ∧ r 1 1 = 0) := by
      rintro ⟨h10, h11⟩
      apply hr
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    refine ⟨![0, 1], ![r 1 0, r 1 1], ?_, ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 1
      simp at h1
    · intro h0
      exact hne ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h01]
  · rw [not_and_or] at hrow
    by_cases h00 : r 0 0 = 0
    · have h01 : r 0 1 ≠ 0 := by
        rcases hrow with h | h
        · exact absurd h00 h
        · exact h
      have h10 : r 1 0 = 0 := by
        have hz : r 0 1 * r 1 0 = 0 := by linear_combination -hdet + r 1 1 * h00
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h h01
        · exact h
      refine ⟨![r 0 1, r 1 1], ![0, 1], ?_, ?_, ?_⟩
      · intro h0
        exact h01 (by simpa using congrFun h0 0)
      · intro h0
        have h1 := congrFun h0 1
        simp at h1
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h10]
    · have h01 : r 0 0 * (r 0 1 / r 0 0) = r 0 1 := by field_simp
      have h11 : r 1 0 * (r 0 1 / r 0 0) = r 1 1 := by
        field_simp
        linear_combination -hdet
      refine ⟨![r 0 0, r 1 0], ![1, r 0 1 / r 0 0], ?_, ?_, ?_⟩
      · intro h0
        exact h00 (by simpa using congrFun h0 0)
      · intro h0
        have h1 := congrFun h0 0
        simp at h1
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h01, h11]

theorem mul_vecMulVec_mul (x y : Matrix (Fin 2) (Fin 2) U) (v w : Fin 2 → U) :
    x * Matrix.vecMulVec v w * y = Matrix.vecMulVec (x.mulVec v) (Matrix.vecMul w y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]
  ring

/-- Rank-one matrices, as a linear map in the left factor. -/
def vecMulVecLeft (U : Type*) [Field U] (u₂ : Fin 2 → U) :
    (Fin 2 → U) →ₗ[U] Matrix (Fin 2) (Fin 2) U where
  toFun u₁ := Matrix.vecMulVec u₁ u₂
  map_add' u v := by
    ext i j
    simp [Matrix.vecMulVec_apply, add_mul]
  map_smul' c u := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]

/-- Rank-one matrices, as a linear map in the right factor. -/
def vecMulVecRight (U : Type*) [Field U] (u₁ : Fin 2 → U) :
    (Fin 2 → U) →ₗ[U] Matrix (Fin 2) (Fin 2) U where
  toFun u₂ := Matrix.vecMulVec u₁ u₂
  map_add' u v := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_add]
  map_smul' c u := by
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

/-- **The rows of an irreducible algebra sweep the whole space.** -/
theorem mem_span_vecMul (A : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (hirr : ∀ v : Fin 2 → U, v ≠ 0 → ∀ u : Fin 2 → U,
      u ∈ Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, a.mulVec v = x})
    {w : Fin 2 → U} (hw : w ≠ 0) (u : Fin 2 → U) :
    u ∈ Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, Matrix.vecMul w a = x} := by
  classical
  by_contra hu
  set W : Submodule U (Fin 2 → U) :=
    Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, Matrix.vecMul w a = x} with hW
  have hlt : W < ⊤ := lt_of_le_of_ne le_top (fun h => hu (by rw [h]; exact Submodule.mem_top))
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  set z : Fin 2 → U := fun i => f (Pi.single i 1) with hz
  have hfx : ∀ x : Fin 2 → U, f x = ∑ i, x i * z i := by
    intro x
    have hexpand : x = ∑ i, x i • (Pi.single i (1 : U)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hcon
        exact absurd (Finset.mem_univ k) hcon
    conv_lhs => rw [hexpand]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, hz]
  have hzne : z ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfx x, h0]
    simp
  have hvanish : ∀ a ∈ A, w ⬝ᵥ (a.mulVec z) = 0 := by
    intro a ha
    have hmem : Matrix.vecMul w a ∈ W := Submodule.subset_span ⟨a, ha, rfl⟩
    have hzero : f (Matrix.vecMul w a) = 0 := by
      have := Submodule.mem_map_of_mem (f := f) hmem
      rw [hfle, Submodule.mem_bot] at this
      exact this
    rw [Matrix.dotProduct_mulVec]
    have hdp : Matrix.vecMul w a ⬝ᵥ z = f (Matrix.vecMul w a) := by
      rw [hfx]
      rfl
    rw [hdp, hzero]
  have hwz : ∀ x : Fin 2 → U, w ⬝ᵥ x = 0 := by
    intro x
    have hspan := hirr z hzne x
    induction hspan using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact hvanish a ha
    | zero => simp
    | add y y' _ _ hy hy' => rw [dotProduct_add, hy, hy', add_zero]
    | smul c y _ hy => rw [dotProduct_smul, hy, smul_zero]
  apply hw
  funext i
  have h := hwz (Pi.single i 1)
  fin_cases i <;> simpa [dotProduct, Fin.sum_univ_two, Pi.single_apply] using h

/-- **Burnside's theorem for `2 × 2` matrices.**  A matrix algebra acting irreducibly on the plane
is the whole matrix algebra. -/
theorem mem_of_irreducibleAction [IsAlgClosed U]
    (A : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    (hirr : ∀ v : Fin 2 → U, v ≠ 0 → ∀ u : Fin 2 → U,
      u ∈ Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, a.mulVec v = x})
    (Z : Matrix (Fin 2) (Fin 2) U) : Z ∈ A := by
  classical
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a ∈ A, ∀ c : U, a ≠ c • (1 : Matrix (Fin 2) (Fin 2) U) := by
    by_contra hcon
    simp only [not_exists, not_and, not_forall, not_not] at hcon
    have hv : (![1, 0] : Fin 2 → U) ≠ 0 := by
      intro h0
      have h1 := congrFun h0 0
      simp at h1
    have hle : Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, a.mulVec ![1, 0] = x}
        ≤ Submodule.span U {(![1, 0] : Fin 2 → U)} := by
      rw [Submodule.span_le]
      rintro x ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := hcon a ha
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [hc]
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.smul_apply]
    have hmem := hle (hirr ![1, 0] hv ![0, 1])
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 := congrFun hc 1
    simp at h1
  obtain ⟨lam, hlam⟩ : ∃ lam : U, (a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U)).det = 0 := by
    set p : Polynomial U := Polynomial.C 1 * Polynomial.X ^ (2 : ℕ)
      + Polynomial.C (-a₀.trace) * Polynomial.X + Polynomial.C a₀.det with hp
    have hdeg : p.degree ≠ 0 := by
      rw [hp, Polynomial.degree_quadratic (one_ne_zero)]
      norm_num
    obtain ⟨lam, hroot⟩ := IsAlgClosed.exists_root p hdeg
    refine ⟨lam, ?_⟩
    have heval : lam ^ (2 : ℕ) - a₀.trace * lam + a₀.det = 0 := by
      have hval := hroot
      rw [Polynomial.IsRoot, hp] at hval
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X] at hval
      linear_combination hval
    have e00 : (a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U)) 0 0 = a₀ 0 0 - lam := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    have e11 : (a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U)) 1 1 = a₀ 1 1 - lam := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    have e01 : (a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U)) 0 1 = a₀ 0 1 := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    have e10 : (a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U)) 1 0 = a₀ 1 0 := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    rw [Matrix.det_fin_two, e00, e01, e10, e11]
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at heval
    linear_combination heval
  have hrA : a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U) ∈ A :=
    A.sub_mem ha₀A (A.smul_mem lam hone)
  have hrne : a₀ - lam • (1 : Matrix (Fin 2) (Fin 2) U) ≠ 0 := by
    intro h0
    exact ha₀ lam (by rw [← sub_eq_zero]; exact h0)
  obtain ⟨v, w, hv, hw, hrvw⟩ := exists_vecMulVec_of_det_eq_zero hrne hlam
  have hbase : ∀ x ∈ A, ∀ y ∈ A, Matrix.vecMulVec (x.mulVec v) (Matrix.vecMul w y) ∈ A := by
    intro x hx y hy
    rw [← mul_vecMulVec_mul, ← hrvw]
    exact hmul _ (hmul x hx _ hrA) y hy
  have hstep1 : ∀ y ∈ A, ∀ u₁ : Fin 2 → U,
      Matrix.vecMulVec u₁ (Matrix.vecMul w y) ∈ A := by
    intro y hy u₁
    have hsub : Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, a.mulVec v = x}
        ≤ A.comap (vecMulVecLeft U (Matrix.vecMul w y)) := by
      rw [Submodule.span_le]
      rintro x ⟨a, ha, rfl⟩
      exact hbase a ha y hy
    exact hsub (hirr v hv u₁)
  have hstep2 : ∀ u₁ u₂ : Fin 2 → U, Matrix.vecMulVec u₁ u₂ ∈ A := by
    intro u₁ u₂
    have hsub : Submodule.span U {x : Fin 2 → U | ∃ a ∈ A, Matrix.vecMul w a = x}
        ≤ A.comap (vecMulVecRight U u₁) := by
      rw [Submodule.span_le]
      rintro x ⟨y, hy, rfl⟩
      exact hstep1 y hy u₁
    exact hsub (mem_span_vecMul A hirr hw u₂)
  have hdecomp : Z = ∑ i : Fin 2, Matrix.vecMulVec (Pi.single i (1 : U)) (Z i) := by
    ext a b
    rw [Matrix.sum_apply, Finset.sum_eq_single a]
    · simp [Matrix.vecMulVec_apply]
    · intro j _ hj
      simp [Matrix.vecMulVec_apply, Ne.symm hj]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  rw [hdecomp]
  exact Submodule.sum_mem _ fun i _ => hstep2 _ _

/-- **No stable line means every orbit spans.**  In the plane, a set of matrices containing the
identity and stabilising no line has orbits that span. -/
theorem span_orbit_eq_top_of_no_semiInvariant
    {G : Set (Matrix (Fin 2) (Fin 2) U)} (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ G)
    (hns : ∀ c : Fin 2 → U, c ≠ 0 → ¬ ∀ g ∈ G, ∃ lam : U, g.mulVec c = lam • c)
    (v : Fin 2 → U) (hv : v ≠ 0) (u : Fin 2 → U) :
    u ∈ Submodule.span U {x : Fin 2 → U | ∃ g ∈ G, g.mulVec v = x} := by
  classical
  by_contra hu
  set W : Submodule U (Fin 2 → U) :=
    Submodule.span U {x : Fin 2 → U | ∃ g ∈ G, g.mulVec v = x} with hW
  have hvW : v ∈ W := by
    refine Submodule.subset_span ⟨1, hone, ?_⟩
    simp
  have hWne : W ≠ ⊤ := by
    intro h
    exact hu (by rw [h]; trivial)
  have hspanle : Submodule.span U ({v} : Set (Fin 2 → U)) ≤ W := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hvW
  have hrank1 : Module.finrank U (Submodule.span U ({v} : Set (Fin 2 → U))) = 1 :=
    finrank_span_singleton hv
  have hWrank : Module.finrank U W ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hle2 : Module.finrank U W ≤ Module.finrank U (Fin 2 → U) :=
      Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle2
    have heq : Module.finrank U W = 2 := le_antisymm hle2 hcon
    exact hWne (Submodule.eq_top_of_finrank_eq (by rw [heq, Module.finrank_fin_fun]))
  have hWeq : W = Submodule.span U ({v} : Set (Fin 2 → U)) := by
    refine (Submodule.eq_of_le_of_finrank_le hspanle ?_).symm
    rw [hrank1]
    exact hWrank
  refine hns v hv ?_
  intro g hg
  have hmem : g.mulVec v ∈ Submodule.span U ({v} : Set (Fin 2 → U)) := by
    rw [← hWeq]
    exact Submodule.subset_span ⟨g, hg, rfl⟩
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨lam, hlam⟩ := hmem
  exact ⟨lam, hlam.symm⟩


end

end GaloisForLFunctions.HTGeometry
