import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# The derivative-variable spectral family and its completion carrier

Three exact mechanisms of the card are formalized.

*The generalized problem becomes a shifted multiplier equation.*  Applying the Neumann Laplacian to
`G u = λ K u` and using `−Δ K u = u` turns it into `(W(D) − λ) u = 0`, which is `(2)` → `(7)`.  The
step is pure linear algebra once the two operator identities are given, and it is proved here in
that form.

*The shifted symbol.*  `W_{a,λ}(ξ) = W_a(ξ) − λ` of `(5)`, with the reduction stated against it.

*The conditional finite Morse formula.*  Under the isomorphism `(9)` the kernel dimensions agree
term by term, so `(10)` and the injectivity criterion `(11)` follow.  The isomorphism itself is the
card's missing hypothesis and stays a hypothesis of the statement.

The closed screw form, its completion `H(S_{a,μ})`, the non-inclusion `(3)`, the Neumann inverse and
the logarithmic multiplier are cited parents.  The prime–Gamma resource consequence is the corpus
theorem `HTGeometry.not_summable_primeLogHerglotzTransportMassOrder_of_pos`, reused rather than
rebuilt.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The shifted symbol -/

/-- The shifted exact symbol `(5)`. -/
def shiftedSymbol (W : ℝ → ℂ) (lam : ℂ) : ℝ → ℂ := fun ξ => W ξ - lam

theorem shiftedSymbol_apply (W : ℝ → ℂ) (lam : ℂ) (ξ : ℝ) :
    shiftedSymbol W lam ξ = W ξ - lam := rfl

/-- **Equation (5), null form.**  A vector is annihilated by the shifted symbol exactly when the
symbol acts as multiplication by `λ`. -/
theorem shiftedSymbol_mul_eq_zero_iff {W : ℝ → ℂ} {lam : ℂ} {u : ℝ → ℂ} (ξ : ℝ) :
    shiftedSymbol W lam ξ * u ξ = 0 ↔ W ξ * u ξ = lam * u ξ := by
  rw [shiftedSymbol_apply, sub_mul, sub_eq_zero]

/-! ## The generalized problem becomes a multiplier equation -/

/-- **Equations (2) → (7).**  Applying the Neumann Laplacian to the generalized eigenvalue equation
produces the shifted multiplier equation.  The two operator identities `L ∘ G = W` and `L ∘ K = id`
are exactly the ones Suzuki's construction supplies. -/
theorem multiplier_eq_of_generalized {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (L : F →ₗ[ℂ] E) (G K : E →ₗ[ℂ] F) (W : E →ₗ[ℂ] E)
    (hLG : ∀ x, L (G x) = W x) (hLK : ∀ x, L (K x) = x)
    {lam : ℂ} {u : E} (hu : G u = lam • K u) :
    W u = lam • u := by
  have h := congrArg L hu
  rw [hLG, map_smul, hLK] at h
  exact h

/-- **Equation (7), kernel form.**  The same statement as the vanishing of the shifted operator. -/
theorem shiftedOperator_eq_zero_of_generalized {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (L : F →ₗ[ℂ] E) (G K : E →ₗ[ℂ] F) (W : E →ₗ[ℂ] E)
    (hLG : ∀ x, L (G x) = W x) (hLK : ∀ x, L (K x) = x)
    {lam : ℂ} {u : E} (hu : G u = lam • K u) :
    (W - lam • (LinearMap.id : E →ₗ[ℂ] E)) u = 0 := by
  have h := multiplier_eq_of_generalized L G K W hLG hLK hu
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h]
  exact sub_self _

/-! ## The conditional finite Morse formula -/

/-- **Equation (9) → (10), one fibre.**  Isomorphic kernels have equal dimension. -/
theorem finrank_ker_eq_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.finrank ℂ V = Module.finrank ℂ W :=
  e.finrank_eq

/-- **Equation (10).**  Summing the fibrewise dimensions over the finite negative spectrum. -/
theorem sum_finrank_ker_eq {ι : Type*} (s : Finset ι) {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (e : ∀ i, V i ≃ₗ[ℂ] W i) :
    (∑ i ∈ s, Module.finrank ℂ (V i)) = ∑ i ∈ s, Module.finrank ℂ (W i) :=
  Finset.sum_congr rfl fun i _ => finrank_ker_eq_of_linearEquiv (e i)

/-- **Equation (11).**  Under the fibrewise isomorphism, positivity of the operator is exactly
injectivity of the finite Evans maps. -/
theorem forall_ker_eq_bot_iff {ι : Type*} {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (e : ∀ i, V i ≃ₗ[ℂ] W i) :
    (∀ i, ∀ x : V i, x = 0) ↔ (∀ i, ∀ y : W i, y = 0) := by
  constructor
  · intro h i y
    have hx := h i ((e i).symm y)
    have : (e i) ((e i).symm y) = (e i) 0 := by rw [hx]
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · intro h i x
    have hy := h i ((e i) x)
    have : (e i).symm ((e i) x) = (e i).symm 0 := by rw [hy]
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this

end GaloisForLFunctions.RHTower

end
