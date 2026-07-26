import GaloisForLFunctions.HTGeometry.DecomposableTensorRigidity
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Eigenlines of a simple spectrum

An operator with a basis of eigenvectors whose eigenvalues are pairwise distinct has
one-dimensional eigenspaces: every eigenvector for `μ i₀` is a scalar multiple of the basis vector
`e i₀`, so two nonzero eigenvectors for the same eigenvalue are proportional.

In the coordinates of the eigenbasis the operator is diagonal — `e.repr (T v) i = μ i · e.repr v i` —
and the eigenvector equation then kills every coordinate outside `i₀`.

Combined with `criticalHorizonSegreTensor_rigidity`, this determines the two factor lines of a
decomposable eigenvector: if two nonzero decomposable tensors are eigenvectors for the same simple
eigenvalue, their factors are proportional.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- In the coordinates of an eigenbasis the operator acts diagonally. -/
theorem repr_apply_of_eigenbasis [DecidableEq ι] (e : Basis ι K V) {T : Module.End K V}
    {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i) (v : V) (i : ι) :
    e.repr (T v) i = μ i * e.repr v i := by
  have hmaps :
      (Finsupp.lapply i).comp ((e.repr : V ≃ₗ[K] ι →₀ K).toLinearMap.comp (T : V →ₗ[K] V)) =
        μ i • ((Finsupp.lapply i).comp (e.repr : V ≃ₗ[K] ι →₀ K).toLinearMap) := by
    apply Basis.ext e
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      LinearMap.smul_apply, smul_eq_mul, hT j, map_smul,
      Basis.repr_self, Finsupp.single_apply]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  exact LinearMap.congr_fun hmaps v

/-- **Eigenvector coordinates vanish off the eigenvalue's block.**  In the coordinates of an
eigenbasis, an eigenvector for `lam` has zero coordinate at every basis index whose eigenvalue
differs from `lam`.  Equivalently, the `lam`-eigenspace is spanned by the basis vectors carrying
that eigenvalue. -/
theorem repr_eq_zero_of_eigenvalue_ne [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i)
    {lam : K} {v : V} (hv : T v = lam • v) {p : ι} (hp : μ p ≠ lam) :
    e.repr v p = 0 := by
  have h1 : μ p * e.repr v p = lam * e.repr v p := by
    rw [← repr_apply_of_eigenbasis e hT v p, hv]
    simp
  have h2 : (μ p - lam) * e.repr v p = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hp
  · exact h3

/-- **An unrepeated eigenvalue has a one-dimensional eigenspace.**  Only the eigenvalue at `i₀` is
required to be distinct from the others; the rest of the spectrum may be degenerate.  An eigenvector
for `μ i₀` is then a scalar multiple of the eigenbasis vector `e i₀`. -/
theorem eigenvector_eq_smul_of_isolated_eigenvalue [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i)
    {i₀ : ι} (hμ : ∀ i, i ≠ i₀ → μ i ≠ μ i₀) {v : V} (hv : T v = μ i₀ • v) :
    ∃ c : K, v = c • e i₀ := by
  have hzero : ∀ i, i ≠ i₀ → e.repr v i = 0 :=
    fun i hi => repr_eq_zero_of_eigenvalue_ne e hT hv (hμ i hi)
  refine ⟨e.repr v i₀, ?_⟩
  have hrepr : e.repr v = Finsupp.single i₀ (e.repr v i₀) := by
    ext i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [hzero i hi, Finsupp.single_apply, if_neg (Ne.symm hi)]
  have := congrArg (e.repr.symm) hrepr
  rwa [LinearEquiv.symm_apply_apply, Basis.repr_symm_apply, Finsupp.linearCombination_single]
    at this

/-- A simple spectrum makes every eigenvalue unrepeated. -/
theorem eigenvector_eq_smul_of_injective_eigenvalues [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i)
    (hμ : Function.Injective μ) {i₀ : ι} {v : V} (hv : T v = μ i₀ • v) :
    ∃ c : K, v = c • e i₀ :=
  eigenvector_eq_smul_of_isolated_eigenvalue e hT (fun _ hi h => hi (hμ h)) hv

/-- Two nonzero eigenvectors for the same unrepeated eigenvalue are proportional. -/
theorem eigenvector_eq_smul_of_eigenvector_of_isolated [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i)
    {i₀ : ι} (hμ : ∀ i, i ≠ i₀ → μ i ≠ μ i₀) {v w : V}
    (hv : T v = μ i₀ • v) (hw : T w = μ i₀ • w) (hw0 : w ≠ 0) :
    ∃ c : K, v = c • w := by
  obtain ⟨cv, hcv⟩ := eigenvector_eq_smul_of_isolated_eigenvalue e hT hμ hv
  obtain ⟨cw, hcw⟩ := eigenvector_eq_smul_of_isolated_eigenvalue e hT hμ hw
  have hcw0 : cw ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcw
    exact hw0 hcw
  refine ⟨cv / cw, ?_⟩
  rw [hcw, smul_smul, div_mul_cancel₀ _ hcw0, hcv]

/-- Two nonzero eigenvectors for the same simple eigenvalue are proportional. -/
theorem eigenvector_eq_smul_of_eigenvector [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {μ : ι → K} (hT : ∀ i, T (e i) = μ i • e i)
    (hμ : Function.Injective μ) {i₀ : ι} {v w : V}
    (hv : T v = μ i₀ • v) (hw : T w = μ i₀ • w) (hw0 : w ≠ 0) :
    ∃ c : K, v = c • w :=
  eigenvector_eq_smul_of_eigenvector_of_isolated e hT (fun _ hi h => hi (hμ h)) hv hw hw0

/-! ### Decomposable eigenvectors of a simple spectrum -/

variable {I J : Type*}

/-- **Simple-spectrum product rigidity.**  Two nonzero decomposable tensors that are eigenvectors of
the same operator for the same simple eigenvalue have proportional factors: the eigenvalue pins the
eigenline, and a decomposable tensor determines its two factor lines. -/
theorem decomposableEigenvector_factors_proportional_of_isolated [DecidableEq ι]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i) {i₀ : ι} (hμ : ∀ i, i ≠ i₀ → μ i ≠ μ i₀)
    {a a' : I → K} {b b' : J → K} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (hv : T (criticalHorizonSegreTensor a b) = μ i₀ • criticalHorizonSegreTensor a b)
    (hw : T (criticalHorizonSegreTensor a' b') = μ i₀ • criticalHorizonSegreTensor a' b') :
    (∃ α : K, α ≠ 0 ∧ a = α • a') ∧ (∃ β : K, β ≠ 0 ∧ b = β • b') := by
  have hw0 : criticalHorizonSegreTensor a' b' ≠ 0 := by
    intro h0
    rcases (criticalHorizonSegreTensor_eq_zero_iff a' b').mp h0 with h1 | h1
    · exact ha' h1
    · exact hb' h1
  obtain ⟨c, hc⟩ := eigenvector_eq_smul_of_eigenvector_of_isolated e hT hμ hv hw hw0
  exact ⟨criticalHorizonSegreTensor_left_line ha hb hc,
    criticalHorizonSegreTensor_right_line ha hb hc⟩

/-- The simple-spectrum form of the previous theorem. -/
theorem decomposableEigenvector_factors_proportional [DecidableEq ι]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i) (hμ : Function.Injective μ) {i₀ : ι}
    {a a' : I → K} {b b' : J → K} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (hv : T (criticalHorizonSegreTensor a b) = μ i₀ • criticalHorizonSegreTensor a b)
    (hw : T (criticalHorizonSegreTensor a' b') = μ i₀ • criticalHorizonSegreTensor a' b') :
    (∃ α : K, α ≠ 0 ∧ a = α • a') ∧ (∃ β : K, β ≠ 0 ∧ b = β • b') :=
  decomposableEigenvector_factors_proportional_of_isolated e hT
    (fun _ hi h => hi (hμ h)) ha hb ha' hb' hv hw

end GaloisForLFunctions.HTGeometry
