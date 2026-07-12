import GaloisForLFunctions.HTGeometry.RationalCoefficientClearing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite full-rank evaluation packets

A finite linearly independent family of complex-valued functions has a finite square evaluation
packet of full rank.  This packages the exclusion of all coefficient vectors at once, rather than
escaping one fixed linear combination at a time.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Evaluation vectors of a finite linearly independent complex function family span the whole
finite coefficient space. -/
theorem span_evaluationVectors_eq_top
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℂ) (hf : LinearIndependent ℂ f) :
    Submodule.span ℂ (Set.range fun x : X => fun i => f i x) = ⊤ := by
  let K : Submodule ℂ (ι → ℂ) :=
    Submodule.span ℂ (Set.range fun x : X => fun i => f i x)
  change K = ⊤
  rw [← Submodule.dualAnnihilator_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  have hvanish : ∀ x : X, φ (fun i => f i x) = 0 := by
    intro x
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _
      (Submodule.subset_span (Set.mem_range_self x))
  let c : ι → ℂ := fun i => φ (fun j => if i = j then 1 else 0)
  have hcomb : ∑ i, c i • f i = 0 := by
    funext x
    have hsum := LinearMap.pi_apply_eq_sum_univ φ (fun i => f i x)
    rw [hvanish x] at hsum
    simpa [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hsum.symm
  have hc : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp hf) c hcomb
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ φ v]
  have hφbasis : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := by
    simpa [c] using hc
  simp [hφbasis]

/-- **Coefficient-uniform finite evaluation law.** A finite linearly independent family of complex
functions admits an equally indexed evaluation packet whose square evaluation matrix is a unit. -/
theorem exists_fullRank_evaluation_packet
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℂ) (hf : LinearIndependent ℂ f) :
    ∃ points : ι → X,
      IsUnit (Matrix.of fun a i => f i (points a) : Matrix ι ι ℂ) := by
  have hspan := span_evaluationVectors_eq_top f hf
  obtain ⟨v, hv_range, hv_span, hv_indep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ
      (Set.range fun x : X => fun i : ι => f i x)
  have hfinrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun x : X => fun i : ι => f i x)) = Fintype.card ι := by
    rw [hspan, finrank_top, Module.finrank_pi]
  let e : Fin (Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun x : X => fun i : ι => f i x))) ≃ ι :=
    (finCongr hfinrank).trans (Fintype.equivFin ι).symm
  let v' : ι → (ι → ℂ) := v ∘ e.symm
  have hv'_range : ∀ i, v' i ∈ Set.range fun x : X => fun j : ι => f j x := by
    intro i
    exact hv_range (e.symm i)
  have hv'_indep : LinearIndependent ℂ v' :=
    hv_indep.comp _ e.symm.injective
  choose points hpoints using hv'_range
  refine ⟨points, ?_⟩
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have hrow :
      (Matrix.of fun a i => f i (points a) : Matrix ι ι ℂ).row = v' := by
    funext a i
    simpa using congrFun (hpoints a) i
  rw [hrow]
  exact hv'_indep

/-- A full-rank evaluation packet excludes every nonzero coefficient vector simultaneously. -/
theorem coefficients_eq_zero_of_fullRank_evaluation_packet
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℂ) (points : ι → X)
    (hfull : IsUnit
      (Matrix.of fun a i => f i (points a) : Matrix ι ι ℂ))
    (c : ι → ℂ) (hvanish : ∀ a, ∑ i, c i * f i (points a) = 0) :
    ∀ i, c i = 0 := by
  let A : Matrix ι ι ℂ := Matrix.of fun a i => f i (points a)
  have hmul : A.mulVec c = 0 := by
    funext a
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using hvanish a
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hfull
  have hc : c = 0 := hinj (by simpa using hmul)
  intro i
  exact congrFun hc i

/-- **Colored spanning selection.** If the vectors available in every one of `n` row classes span
an ambient space of dimension at least `n`, one can choose one vector from each class so that the
chosen family is linearly independent. -/
theorem exists_linearIndependent_dependent_choice_of_spans
    {n : ℕ} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (X : Fin n → Type u) (available : ∀ i, X i → M)
    (hspan : ∀ i, Submodule.span ℂ (Set.range (available i)) = ⊤)
    (hdim : n ≤ Module.finrank ℂ M) :
    ∃ x : ∀ i, X i, LinearIndependent ℂ (fun i => available i (x i)) := by
  induction n with
  | zero =>
      let x : ∀ i : Fin 0, X i := fun i => Fin.elim0 i
      exact ⟨x, linearIndependent_empty_type⟩
  | succ n ih =>
      have hspaninit : ∀ i : Fin n, Submodule.span ℂ
          (Set.range (available i.castSucc)) = ⊤ := by
        intro i
        exact hspan i.castSucc
      have hdiminit : n ≤ Module.finrank ℂ M := Nat.le_trans (Nat.le_succ n) hdim
      obtain ⟨xinit, hxinit⟩ := ih (fun i => X i.castSucc)
        (fun i => available i.castSucc) hspaninit hdiminit
      let chosenInit : Fin n → M := fun i => available i.castSucc (xinit i)
      let S : Submodule ℂ M := Submodule.span ℂ (Set.range chosenInit)
      have hS_ne_top : S ≠ ⊤ := by
        intro htop
        have hfin : Module.finrank ℂ S = n := by
          simpa [S, chosenInit] using finrank_span_eq_card hxinit
        have hM : Module.finrank ℂ M = n := by
          rw [← finrank_top ℂ M, ← htop]
          exact hfin
        omega
      have hexists : ∃ y : X (Fin.last n), available (Fin.last n) y ∉ S := by
        by_contra h
        have hall : ∀ y : X (Fin.last n), available (Fin.last n) y ∈ S := fun y =>
          not_not.mp (not_exists.mp h y)
        have hle : Submodule.span ℂ (Set.range (available (Fin.last n))) ≤ S :=
          Submodule.span_le.mpr (by rintro _ ⟨y, rfl⟩; exact hall y)
        rw [hspan (Fin.last n)] at hle
        exact hS_ne_top (top_unique hle)
      obtain ⟨y, hy⟩ := hexists
      let x : ∀ i : Fin (n + 1), X i :=
        fun i => Fin.lastCases y (fun j => xinit j) i
      refine ⟨x, ?_⟩
      have hsnoc : (fun i : Fin (n + 1) => available i (x i)) =
          Fin.snoc chosenInit (available (Fin.last n) y) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [x]
        · simp [x, chosenInit]
      rw [hsnoc]
      exact hxinit.finSnoc hy

/-- A row-dependent family of spanning evaluation-vector sets admits a square full-rank packet,
with one chosen point from each prescribed row domain. -/
theorem exists_fullRank_dependent_evaluation_packet
    {n : ℕ} (X : Fin n → Type u)
    (evaluationVector : ∀ a, X a → (Fin n → ℂ))
    (hspan : ∀ a, Submodule.span ℂ (Set.range (evaluationVector a)) = ⊤) :
    ∃ points : ∀ a, X a,
      IsUnit (Matrix.of fun a i => evaluationVector a (points a) i :
        Matrix (Fin n) (Fin n) ℂ) := by
  have hdim : n ≤ Module.finrank ℂ (Fin n → ℂ) := by
    rw [Module.finrank_pi]
    simp
  obtain ⟨points, hindep⟩ :=
    exists_linearIndependent_dependent_choice_of_spans X evaluationVector hspan hdim
  refine ⟨points, ?_⟩
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  simpa [Matrix.row_apply] using hindep

end GaloisForLFunctions.HTGeometry
