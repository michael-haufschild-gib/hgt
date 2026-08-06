import GaloisForLFunctions.HTGeometry.FiniteQuditHermitianUnit
import GaloisForLFunctions.HTGeometry.FiniteSupportCounting
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Matrix.Basis

/-!
# Hermitian operator strings on a finite qudit register

A register of sites `σ` with local dimension `D` carries the operator algebra of
matrices indexed by configurations `σ → Fin D`.  The tensor products of the local
Hermitian units form a basis of that algebra consisting of Hermitian matrices,
exactly one of which — the all-ground label — is the identity.  The support of a
label is the set of sites carrying a non-identity factor, so the labels of
support size in `[1, q]` index the non-scalar Hermitian strings acting on at most
`q` sites, and their number is `∑_{k=1}^{q} C(|σ|,k) (D^2-1)^k`.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {D : ℕ} [NeZero D]

/-- The operator string assembled from a family of local matrices. -/
def quditStringOf (M : σ → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (σ → Fin D) (σ → Fin D) ℂ :=
  Matrix.of fun r c => ∏ i, M i (r i) (c i)

omit [DecidableEq σ] [NeZero D] in
@[simp] theorem quditStringOf_apply (M : σ → Matrix (Fin D) (Fin D) ℂ)
    (r c : σ → Fin D) : quditStringOf M r c = ∏ i, M i (r i) (c i) := rfl

/-- The Hermitian operator string attached to a label. -/
noncomputable def quditString (a : σ → Fin D × Fin D) : Matrix (σ → Fin D) (σ → Fin D) ℂ :=
  quditStringOf (fun i => quditHermUnit (a i))

omit [DecidableEq σ] in
@[simp] theorem quditString_apply (a : σ → Fin D × Fin D) (r c : σ → Fin D) :
    quditString a r c = ∏ i, quditHermUnit (a i) (r i) (c i) := rfl

omit [DecidableEq σ] in
/-- Every operator string is Hermitian. -/
theorem quditString_conjTranspose (a : σ → Fin D × Fin D) :
    (quditString a)ᴴ = quditString a := by
  ext r c
  rw [Matrix.conjTranspose_apply, quditString_apply, quditString_apply,
    Complex.star_def, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := congrFun (congrFun (quditHermUnit_conjTranspose (a i)) (r i)) (c i)
  rw [Matrix.conjTranspose_apply] at h
  simpa [Complex.star_def] using h

omit [DecidableEq σ] in
/-- The all-ground label carries the identity operator. -/
@[simp] theorem quditString_zero :
    quditString (fun _ : σ => ((0, 0) : Fin D × Fin D)) = 1 := by
  ext r c
  rw [quditString_apply]
  simp only [quditHermUnit_zero, Matrix.one_apply]
  rw [Finset.prod_boole]
  by_cases h : r = c
  · rw [if_pos h, if_pos (fun i _ => congrFun h i)]
  · rw [if_neg h, if_neg (fun hh => h (funext fun i => hh i (Finset.mem_univ i)))]

/-- **Multilinear expansion.**  A string of local combinations expands into the
corresponding combination of strings. -/
theorem quditStringOf_sum (lam : σ → (Fin D × Fin D) → ℂ) :
    quditStringOf (fun i => ∑ p : Fin D × Fin D, lam i p • quditHermUnit p)
      = ∑ a : σ → (Fin D × Fin D), (∏ i, lam i (a i)) • quditString a := by
  ext r c
  rw [quditStringOf_apply, Matrix.sum_apply]
  have hfac : ∀ i : σ,
      (∑ p : Fin D × Fin D, lam i p • quditHermUnit p) (r i) (c i)
        = ∑ p : Fin D × Fin D, lam i p * quditHermUnit p (r i) (c i) := by
    intro i
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfac i)]
  rw [Finset.prod_univ_sum (fun _ : σ => (Finset.univ : Finset (Fin D × Fin D)))
    (fun i p => lam i p * quditHermUnit p (r i) (c i))]
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.smul_apply, quditString_apply, smul_eq_mul, Finset.prod_mul_distrib]

omit [DecidableEq σ] [NeZero D] in
/-- A matrix unit is the string of local matrix units. -/
theorem single_eq_quditStringOf (r0 c0 : σ → Fin D) :
    Matrix.single r0 c0 (1 : ℂ)
      = quditStringOf (fun i => Matrix.single (r0 i) (c0 i) (1 : ℂ)) := by
  ext r c
  rw [Matrix.single_apply, quditStringOf_apply]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    Matrix.single_apply (r0 i) (c0 i) (1 : ℂ) (r i) (c i))]
  rw [Finset.prod_boole]
  by_cases h : r0 = r ∧ c0 = c
  · rw [if_pos h, if_pos (fun i _ => ⟨congrFun h.1 i, congrFun h.2 i⟩)]
  · rw [if_neg h, if_neg (fun hh => h ⟨funext fun i => (hh i (Finset.mem_univ i)).1,
      funext fun i => (hh i (Finset.mem_univ i)).2⟩)]

/-- Every matrix unit is an explicit complex combination of Hermitian strings. -/
theorem single_eq_sum_quditString (r0 c0 : σ → Fin D) :
    Matrix.single r0 c0 (1 : ℂ)
      = ∑ a : σ → (Fin D × Fin D),
          (∏ i, quditUnitCoeff (r0 i) (c0 i) (a i)) • quditString a := by
  rw [single_eq_quditStringOf, show (fun i => Matrix.single (r0 i) (c0 i) (1 : ℂ))
      = (fun i => ∑ p : Fin D × Fin D, quditUnitCoeff (r0 i) (c0 i) p • quditHermUnit p)
    from funext fun i => single_eq_sum_quditUnitCoeff (r0 i) (c0 i)]
  exact quditStringOf_sum _

/-- **The Hermitian strings span the operator algebra.** -/
theorem span_quditString_eq_top :
    Submodule.span ℂ (Set.range (quditString (σ := σ) (D := D))) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun c _ => ?_
  have hs : Matrix.single r c (M r c) = M r c • Matrix.single r c (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, single_eq_sum_quditString]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- **The Hermitian strings are a complex basis of the operator algebra.** -/
theorem linearIndependent_quditString :
    LinearIndependent ℂ (quditString (σ := σ) (D := D)) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [span_quditString_eq_top]
  · rw [Fintype.card_fun, Module.finrank_matrix ℂ ℂ (σ → Fin D) (σ → Fin D),
      Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
      Module.finrank_self, mul_one, mul_pow]

/-- The Hermitian strings are real-linearly independent as well. -/
theorem linearIndependent_real_quditString :
    LinearIndependent ℝ (quditString (σ := σ) (D := D)) := by
  refine LinearIndependent.restrict_scalars ?_ linearIndependent_quditString
  intro x y hxy
  simpa using hxy

/-- Sites carrying a non-identity local factor. -/
def quditStringSupport (a : σ → Fin D × Fin D) : Finset σ :=
  configSupport ((0, 0) : Fin D × Fin D) a

omit [DecidableEq σ] in
theorem mem_quditStringSupport {a : σ → Fin D × Fin D} {i : σ} :
    i ∈ quditStringSupport a ↔ a i ≠ (0, 0) :=
  mem_configSupport

/-- Labels of non-scalar Hermitian strings acting on at most `q` sites. -/
abbrev QLocalStringLabel (σ : Type*) [Fintype σ] [DecidableEq σ] (D q : ℕ) [NeZero D] :=
  {a : σ → Fin D × Fin D //
    0 < (quditStringSupport a).card ∧ (quditStringSupport a).card ≤ q}

/-- **Dictionary size.**  The number of non-scalar Hermitian strings acting on at
most `q` sites is `∑_{k=1}^{q} C(|σ|,k)(D^2-1)^k`. -/
theorem card_QLocalStringLabel (q : ℕ) :
    Fintype.card (QLocalStringLabel σ D q)
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D * D - 1) ^ k := by
  classical
  rw [Fintype.card_subtype]
  have h := card_configSupport_pos_le (σ := σ) (α := Fin D × Fin D)
    ((0, 0) : Fin D × Fin D) q
  rw [Fintype.card_prod, Fintype.card_fin] at h
  simpa [quditStringSupport] using h

end GaloisForLFunctions.HTGeometry
