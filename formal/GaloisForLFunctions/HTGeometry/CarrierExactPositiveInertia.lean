import GaloisForLFunctions.HTGeometry.CarrierCauchy

/-!
# Exact positive inertia of the factored conjugate-pair carrier

`exact_neg_inertia` gives negative index exactly `k` for the factored Hermitian form
`H = ∑ w_i w_i* − ∑ u_i u_i*` under Cauchy nondegeneracy of the evaluation map.  Exchanging the
roles of `w` and `u` replaces `H` by `-H`, so the same theorem gives positive index exactly `k`.

For the conjugate-pair carrier of `k` distinct upper-half-plane poles
(`w_i = e_i + a_i`, `u_i = e_i − a_i`, `a_i(j) = (t_i − z_j)⁻¹`, `e_i(j) = (t̄_i − z_j)⁻¹`) the
evaluation map is surjective, so the inertia is exactly `(k, k)`: every off-line pair contributes
one hyperbolic plane, one positive and one negative square.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions

noncomputable section

/-- The real Krein value of `-H` is the negative of that of `H`. -/
theorem re_krein_neg_matrix {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    (star y ⬝ᵥ (-H).mulVec y).re = -(star y ⬝ᵥ H.mulVec y).re := by
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]

/-- Exchanging the two factored blocks negates the factored form. -/
theorem factoredForm_swap_eq_neg {N k : ℕ} (w u : Fin k → (Fin N → ℂ)) :
    (∑ i, Matrix.of (fun p q => u i p * star (u i q)))
        - (∑ i, Matrix.of (fun p q => w i p * star (w i q)))
      = -((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
        - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))) := by
  rw [neg_sub]

/-- **Exact Krein–Langer positive inertia `κ₊ = k`** for the factored Hermitian form
`H = ∑ w_i w_i* − ∑ u_i u_i*`, given the evaluation map `(Φ,Ψ)` surjective: every subspace on which
`H` is positive-definite has dimension at most `k`, and one of dimension exactly `k` exists.  This is
`exact_neg_inertia` applied to `-H`, i.e. with the roles of `w` and `u` exchanged. -/
theorem exact_pos_inertia {N k : ℕ} (w u : Fin k → (Fin N → ℂ))
    (Φ Ψ : (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin N → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin N → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) :
    (∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re) := by
  have hT' : Function.Surjective (Ψ.prod Φ) := by
    intro ab
    obtain ⟨y, hy⟩ := hT (ab.2, ab.1)
    refine ⟨y, ?_⟩
    rw [LinearMap.prod_apply] at hy ⊢
    exact Prod.ext (congrArg Prod.snd hy) (congrArg Prod.fst hy)
  have h := exact_neg_inertia u w Ψ Φ hΨ hΦ hT'
  rw [factoredForm_swap_eq_neg] at h
  simp only [re_krein_neg_matrix, neg_lt_zero] at h
  exact h

/-- **The conjugate-pair carrier evaluation is surjective.**  For `k` distinct upper-half-plane poles
and `2k` distinct nodes avoiding the poles and their conjugates, the stacked evaluation map against
the carrier vectors `w_i = e_i + a_i`, `u_i = e_i − a_i` is surjective.  This is the linear
independence of the carrier family (`multiPair_carrier_linearIndependent`) turned into surjectivity
by `eval_surjective_rect`. -/
theorem multiPair_carrier_eval_surjective {k : ℕ} (t : Fin k → ℂ) (z : Fin (k + k) → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) (hz : Function.Injective z)
    (htz : ∀ i j, t i ≠ z j) (hstz : ∀ i j, star (t i) ≠ z j)
    (w u : Fin k → (Fin (k + k) → ℂ))
    (hw : w = fun i j => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹)
    (hu : u = fun i j => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹) :
    ∃ Φ Ψ : (Fin (k + k) → ℂ) →ₗ[ℂ] (Fin k → ℂ),
      (∀ (y : Fin (k + k) → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y) ∧
      (∀ (y : Fin (k + k) → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y) ∧
      Function.Surjective (Φ.prod Ψ) := by
  classical
  let Φ : (Fin (k + k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (w i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a })
  let Ψ : (Fin (k + k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (u i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a })
  have hΦ : ∀ (y : Fin (k + k) → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y := fun y i => rfl
  have hΨ : ∀ (y : Fin (k + k) → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y := fun y i => rfl
  have hLI : LinearIndependent ℂ (Sum.elim w u) := by
    rw [hw, hu]
    exact multiPair_carrier_linearIndependent t z ht htinj hz htz hstz
  have hE := eval_surjective_rect (Sum.elim w u) hLI
  refine ⟨Φ, Ψ, hΦ, hΨ, ?_⟩
  intro ab
  obtain ⟨y, hy⟩ := hE (Sum.elim ab.1 ab.2)
  refine ⟨y, ?_⟩
  rw [LinearMap.prod_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have hcf := congrFun hy (Sum.inl i)
    simpa [hΦ y i] using hcf
  · have hcf := congrFun hy (Sum.inr i)
    simpa [hΨ y i] using hcf

/-- **Exact positive inertia `κ₊ = k` of the conjugate-pair carrier.**  For `k` distinct off-line
poles and `2k` admissible nodes, every positive-definite subspace of the factored carrier form has
dimension at most `k`, and one of dimension exactly `k` exists. -/
theorem multiPair_carrier_exact_pos_inertia {k : ℕ} (t : Fin k → ℂ) (z : Fin (k + k) → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) (hz : Function.Injective z)
    (htz : ∀ i j, t i ≠ z j) (hstz : ∀ i j, star (t i) ≠ z j)
    (w u : Fin k → (Fin (k + k) → ℂ))
    (hw : w = fun i j => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹)
    (hu : u = fun i j => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹) :
    (∀ W : Submodule ℂ (Fin (k + k) → ℂ),
        (∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (k + k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re) := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hT⟩ :=
    multiPair_carrier_eval_surjective t z ht htinj hz htz hstz w u hw hu
  exact exact_pos_inertia w u Φ Ψ hΦ hΨ hT

/-- **One hyperbolic plane per off-line pair.**  The conjugate-pair carrier of `k` distinct
upper-half-plane poles has negative index exactly `k` and positive index exactly `k`. -/
theorem multiPair_carrier_exact_inertia {k : ℕ} (t : Fin k → ℂ) (z : Fin (k + k) → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) (hz : Function.Injective z)
    (htz : ∀ i j, t i ≠ z j) (hstz : ∀ i j, star (t i) ≠ z j)
    (w u : Fin k → (Fin (k + k) → ℂ))
    (hw : w = fun i j => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹)
    (hu : u = fun i j => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹) :
    ((∀ W : Submodule ℂ (Fin (k + k) → ℂ),
        (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (k + k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0))
    ∧ ((∀ W : Submodule ℂ (Fin (k + k) → ℂ),
        (∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (k + k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re)) :=
  ⟨multiPair_carrier_exact_neg_inertia t z ht htinj hz htz hstz w u hw hu,
    multiPair_carrier_exact_pos_inertia t z ht htinj hz htz hstz w u hw hu⟩

end

end GaloisForLFunctions
