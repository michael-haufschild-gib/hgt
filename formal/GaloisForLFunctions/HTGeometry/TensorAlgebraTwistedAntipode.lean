import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Algebra.Opposite

/-!
# Order-preserving covariance is not a twisted antipode

In the tensor algebra `T(V)` over a field, let `C_σ` be the letterwise relabelling by an
involution `σ` and `S(v₁⋯vₙ) = (-1)ⁿ vₙ⋯v₁` the antipode.  Then
`θ₊S(v₁⋯vₙ) = (-1)ⁿ σ(vₙ)⋯σ(v₁)` with `θ₊ = C_σ`, and `θ₋S(v₁⋯vₙ) = σ(vₙ)⋯σ(v₁)` with
`θ₋ = C_{-σ}`.  In characteristic `≠ 2`, `θ₊S` disagrees with `C_σ` on every nonzero
first-grade response, while `θ₋S` agrees with `C_σ` on grade two exactly when the images of `σ`
commute.  Hence on a free ordered response algebra with two noncommuting directions (for instance
two linearly independent vectors), no sign choice turns the covariance into a twisted antipode,
and any quotient on which they agree kills every grade-two commutator.
-/

noncomputable section

open TensorAlgebra MulOpposite

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **(CRS.42)** The antipode of `T(V)`, as an algebra map to the opposite algebra. -/
def tensorAntipodeOp : TensorAlgebra K V →ₐ[K] (TensorAlgebra K V)ᵐᵒᵖ :=
  TensorAlgebra.lift K ((opLinearEquiv K).toLinearMap ∘ₗ (-(ι K)))

/-- The antipode `S(v₁⋯vₙ) = (-1)ⁿ vₙ⋯v₁`. -/
def tensorAntipode (x : TensorAlgebra K V) : TensorAlgebra K V := (tensorAntipodeOp x).unop

theorem tensorAntipode_ι (v : V) : tensorAntipode (ι K v) = -ι K v := by
  simp [tensorAntipode, tensorAntipodeOp]

theorem tensorAntipode_mul (x y : TensorAlgebra K V) :
    tensorAntipode (x * y) = tensorAntipode y * tensorAntipode x := by
  simp [tensorAntipode, map_mul]

theorem tensorAntipode_one : tensorAntipode (1 : TensorAlgebra K V) = 1 := by
  simp [tensorAntipode]

/-- **(CRS.41)** The letterwise relabelling `C_σ(v₁⋯vₙ) = σ(v₁)⋯σ(vₙ)`. -/
def relabelAlg (σ : V →ₗ[K] V) : TensorAlgebra K V →ₐ[K] TensorAlgebra K V :=
  TensorAlgebra.lift K (ι K ∘ₗ σ)

theorem relabelAlg_ι (σ : V →ₗ[K] V) (v : V) : relabelAlg σ (ι K v) = ι K (σ v) := by
  simp [relabelAlg]

/-- **(CRS.42)** `S(v₁⋯vₙ) = (-1)ⁿ vₙ⋯v₁`. -/
theorem tensorAntipode_prod (l : List V) :
    tensorAntipode (l.map (ι K)).prod = (-1 : K) ^ l.length • (l.reverse.map (ι K)).prod := by
  induction l with
  | nil => simp [tensorAntipode_one]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, tensorAntipode_mul, ih, tensorAntipode_ι, List.reverse_cons,
      List.map_append, List.prod_append, List.length_cons, pow_succ]
    simp

/-- **(CRS.45)** `θ₊S(v₁⋯vₙ) = (-1)ⁿ σ(vₙ)⋯σ(v₁)`. -/
theorem relabel_tensorAntipode_prod (σ : V →ₗ[K] V) (l : List V) :
    relabelAlg σ (tensorAntipode (l.map (ι K)).prod) =
      (-1 : K) ^ l.length • (l.reverse.map (fun v => ι K (σ v))).prod := by
  rw [tensorAntipode_prod, map_smul, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun v _ => relabelAlg_ι σ v

/-- **(CRS.43)** `θ₋S(v₁⋯vₙ) = σ(vₙ)⋯σ(v₁)` for `θ₋ = C_{-σ}`. -/
theorem relabelNeg_tensorAntipode_prod (σ : V →ₗ[K] V) (l : List V) :
    relabelAlg (-σ) (tensorAntipode (l.map (ι K)).prod) =
      (l.reverse.map (fun v => ι K (σ v))).prod := by
  rw [relabel_tensorAntipode_prod]
  simp only [LinearMap.neg_apply, map_neg]
  have h : ∀ m : List V, (m.map fun v => -ι K (σ v)).prod =
      (-1 : K) ^ m.length • (m.map fun v => ι K (σ v)).prod := by
    intro m
    induction m with
    | nil => simp
    | cons v m ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons,
        pow_succ]
      simp
  rw [h, List.length_reverse, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_smul]

/-- **§10.6, grade one.**  In characteristic `≠ 2`, `θ₊S(v) = C_σ(v)` exactly when `σ v = 0`. -/
theorem relabel_tensorAntipode_ι_eq_iff (σ : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (v : V) :
    relabelAlg σ (tensorAntipode (ι K v)) = relabelAlg σ (ι K v) ↔ σ v = 0 := by
  rw [tensorAntipode_ι, map_neg, relabelAlg_ι, neg_eq_iff_add_eq_zero, ← two_smul K, smul_eq_zero,
    or_iff_right h2, ← map_zero (ι K), ι_inj]

/-- **§10.6, grade two (CRS.44).**  `θ₋S(uv) = C_σ(uv)` exactly when `σ(u)σ(v) = σ(v)σ(u)`. -/
theorem relabelNeg_tensorAntipode_mul_eq_iff (σ : V →ₗ[K] V) (u v : V) :
    relabelAlg (-σ) (tensorAntipode (ι K u * ι K v)) = relabelAlg σ (ι K u * ι K v) ↔
      ι K (σ u) * ι K (σ v) = ι K (σ v) * ι K (σ u) := by
  have h := relabelNeg_tensorAntipode_prod (K := K) σ [u, v]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at h
  rw [h, map_mul, relabelAlg_ι, relabelAlg_ι]
  exact eq_comm

/-- **Theorem 10.1** If two directions do not commute in `T(V)`, then for an invertible
relabelling neither sign convention turns `C_σ` into a twisted antipode. -/
theorem covariance_ne_twistedAntipode (σ : V ≃ₗ[K] V) (h2 : (2 : K) ≠ 0) {a b : V}
    (hab : ι K a * ι K b ≠ ι K b * ι K a) :
    (∃ x, relabelAlg σ.toLinearMap (tensorAntipode x) ≠ relabelAlg σ.toLinearMap x) ∧
      ∃ x, relabelAlg (-σ.toLinearMap) (tensorAntipode x) ≠ relabelAlg σ.toLinearMap x := by
  have ha : a ≠ 0 := by
    rintro rfl; simp at hab
  refine ⟨⟨ι K (σ.symm a), fun h => ha ?_⟩, ⟨ι K (σ.symm a) * ι K (σ.symm b), fun h => hab ?_⟩⟩
  · have := (relabel_tensorAntipode_ι_eq_iff σ.toLinearMap h2 _).1 h
    simpa using this
  · have := (relabelNeg_tensorAntipode_mul_eq_iff σ.toLinearMap _ _).1 h
    simpa using this

/-- **Theorem 10.1, quotients.**  An algebra map on which `θ₋S` and `C_σ` agree kills every
grade-two commutator. -/
theorem quotient_kills_commutators (σ : V ≃ₗ[K] V) {B : Type*} [Ring B] [Algebra K B]
    (q : TensorAlgebra K V →ₐ[K] B)
    (hq : ∀ x, q (relabelAlg (-σ.toLinearMap) (tensorAntipode x)) = q (relabelAlg σ.toLinearMap x))
    (a b : V) : q (ι K a * ι K b) = q (ι K b * ι K a) := by
  have h := hq (ι K (σ.symm a) * ι K (σ.symm b))
  have h' := relabelNeg_tensorAntipode_prod (K := K) σ.toLinearMap [σ.symm a, σ.symm b]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h'
  rw [h'] at h
  simp only [map_mul, relabelAlg_ι, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  rw [map_mul, map_mul]
  exact h.symm

/-- Two linearly independent vectors give noncommuting directions in `T(V)`. -/
theorem ι_mul_ι_ne_of_linearIndependent {a b : V} (h : LinearIndependent K ![a, b]) :
    ι K a * ι K b ≠ ι K b * ι K a := by
  let E : Fin 2 → Matrix (Fin 2) (Fin 2) K := ![!![0, 1; 0, 0], !![0, 0; 1, 0]]
  let f := (Module.Basis.span h).constr K E
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  have hga : g a = !![0, 1; 0, 0] := by
    have := congrArg (fun F => F ⟨a, Submodule.subset_span ⟨0, rfl⟩⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, show (⟨a, Submodule.subset_span ⟨0, rfl⟩⟩ : Submodule.span K (Set.range ![a, b])) =
      Module.Basis.span h 0 from Subtype.ext (by simp [Module.Basis.span_apply]), Module.Basis.constr_basis]
    rfl
  have hgb : g b = !![0, 0; 1, 0] := by
    have := congrArg (fun F => F ⟨b, Submodule.subset_span ⟨1, rfl⟩⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, show (⟨b, Submodule.subset_span ⟨1, rfl⟩⟩ : Submodule.span K (Set.range ![a, b])) =
      Module.Basis.span h 1 from Subtype.ext (by simp [Module.Basis.span_apply]), Module.Basis.constr_basis]
    rfl
  intro hab
  have := congrArg (TensorAlgebra.lift K g) hab
  rw [map_mul, map_mul, lift_ι_apply, lift_ι_apply, hga, hgb] at this
  have h00 := congrFun (congrFun this 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end GaloisForLFunctions.HTGeometry
