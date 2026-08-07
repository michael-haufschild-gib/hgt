import GaloisForLFunctions.HTGeometry.CDGATensorSingle
import GaloisForLFunctions.HTGeometry.CDGAShiftQuasiIso

/-!
# Tensoring commutes with the degree shift in the second variable

A bidegree of `M ⊗ N[−k]` in total degree `n` with second index below `k` contributes nothing, and
one with second index `b + k` is the bidegree `(a, b)` of `M ⊗ N` in total degree `n − k`.  So the
two carriers agree.

The whole difficulty is that the correspondence is stated with a subtraction; the pattern that keeps
it harmless is the one used throughout this layer — destructure the degree with `Nat.le.dest` so the
subtraction disappears from every *proof*, and let it appear only inside the definition.

* `HTGeometry.tensorShiftMap` : the comparison.
* `HTGeometry.tensorShiftMap_bijective` : it is a degreewise bijection.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **The comparison of a tensor product with a shifted factor.** -/
noncomputable def tensorShiftMap (k n : ℕ) :
    TensorCarrier (R := R) (M := M) (N := ShiftCarrier N k) n →ₗ[R]
      ShiftCarrier (TensorCarrier (R := R) M N) k n where
  toFun f := fun r p' =>
    TensorProduct.map LinearMap.id
      ((shiftEvalAt (R := R) (M := N) k p'.1.2 (p'.1.2 + k) rfl :
        ShiftCarrier N k (p'.1.2 + k) →ₗ[R] N p'.1.2))
      (f ⟨(p'.1.1, p'.1.2 + k), by
        have h1 := r.2
        have h2 := p'.2
        omega⟩)
  map_add' f g := by
    funext r p'
    show TensorProduct.map LinearMap.id _ ((f + g) _) = _
    rw [tensorCarrier_add_apply, map_add]
    rfl
  map_smul' c f := by
    funext r p'
    show TensorProduct.map LinearMap.id _ ((c • f) _) = _
    rw [tensorCarrier_smul_apply, map_smul]
    rfl

/-- Below the shift the tensor factor is trivial. -/
theorem tensorShift_component_subsingleton {k b : ℕ} (h : b < k) (a : ℕ) :
    Subsingleton (TensorProduct R (M a) (ShiftCarrier N k b)) := by
  haveI := shiftCarrier_subsingleton (M := N) h
  have hz : ∀ z : TensorProduct R (M a) (ShiftCarrier N k b), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m w => rw [show w = 0 from Subsingleton.elim _ _, TensorProduct.tmul_zero]
    | add u v hu hv => rw [hu, hv, add_zero]
  exact ⟨fun z w => by rw [hz z, hz w]⟩

/-- **The comparison is injective.** -/
theorem tensorShiftMap_injective (k n : ℕ) :
    Function.Injective (tensorShiftMap (R := R) (M := M) (N := N) k n) := by
  intro f g hfg
  funext p
  obtain ⟨⟨a, b⟩, hp⟩ := p
  by_cases hb : k ≤ b
  · obtain ⟨γ, rfl⟩ : ∃ γ, γ + k = b := ⟨b - k, by omega⟩
    have hr : a + γ + k = n := by omega
    have hp' : (a, γ).1 + (a, γ).2 = a + γ := rfl
    have := congrFun (congrFun hfg ⟨a + γ, hr⟩) ⟨(a, γ), hp'⟩
    show f ⟨(a, γ + k), hp⟩ = g ⟨(a, γ + k), hp⟩
    refine (TensorProduct.congr (LinearEquiv.refl R (M a))
      (shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl)).injective ?_
    exact this
  · haveI := tensorShift_component_subsingleton (R := R) (M := M) (N := N) (b := b) (not_le.1 hb) a
    exact Subsingleton.elim _ _

/-- **The comparison is surjective.** -/
theorem tensorShiftMap_surjective (k n : ℕ) :
    Function.Surjective (tensorShiftMap (R := R) (M := M) (N := N) k n) := by
  classical
  intro g
  refine ⟨fun p =>
    if h : k ≤ p.1.2 then
      TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k (p.1.2 - k) p.1.2 (by omega)).symm :
          N (p.1.2 - k) →ₗ[R] ShiftCarrier N k p.1.2)
        (g ⟨n - k, by have := p.2; omega⟩ ⟨(p.1.1, p.1.2 - k), by
          show p.1.1 + (p.1.2 - k) = n - k
          have := p.2
          omega⟩)
    else 0, ?_⟩
  funext r p'
  obtain ⟨c, hc⟩ := r
  obtain ⟨⟨a, γ⟩, hp'⟩ := p'
  show TensorProduct.map LinearMap.id
      ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
        ShiftCarrier N k (γ + k) →ₗ[R] N γ))
      (if h : k ≤ (a, γ + k).2 then
        TensorProduct.map LinearMap.id
          ((shiftEvalAt (R := R) (M := N) k ((a, γ + k).2 - k) (a, γ + k).2 (by omega)).symm :
            N ((a, γ + k).2 - k) →ₗ[R] ShiftCarrier N k (a, γ + k).2)
          (g ⟨n - k, by omega⟩ ⟨((a, γ + k).1, (a, γ + k).2 - k), by
            have h1 : a + γ = c := hp'
            show a + (γ + k - k) = n - k
            omega⟩)
      else 0) = g ⟨c, hc⟩ ⟨(a, γ), hp'⟩
  have h1 : a + γ = c := hp'
  rw [dif_pos (by omega : k ≤ (a, γ + k).2)]
  have gen : ∀ (δ : ℕ) (e : δ + k = γ + k) (hδ : (a, δ).1 + (a, δ).2 = n - k)
      (hnk : n - k + k = n),
      TensorProduct.map LinearMap.id
          ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
            ShiftCarrier N k (γ + k) →ₗ[R] N γ))
          (TensorProduct.map LinearMap.id
            ((shiftEvalAt (R := R) (M := N) k δ (γ + k) e).symm :
              N δ →ₗ[R] ShiftCarrier N k (γ + k))
            (g ⟨n - k, hnk⟩ ⟨(a, δ), hδ⟩))
        = g ⟨c, hc⟩ ⟨(a, γ), hp'⟩ := by
    intro δ e hδ hnk
    obtain rfl : δ = γ := by omega
    obtain rfl : c = n - k := by omega
    have hcomp : (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
          ((shiftEvalAt (R := R) (M := N) k δ (δ + k) rfl :
            ShiftCarrier N k (δ + k) →ₗ[R] N δ))).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
          (((shiftEvalAt (R := R) (M := N) k δ (δ + k) e).symm :
            N δ →ₗ[R] ShiftCarrier N k (δ + k))))
        = LinearMap.id := by
      rw [← TensorProduct.map_comp, LinearMap.id_comp,
        show ((shiftEvalAt (R := R) (M := N) k δ (δ + k) rfl :
              ShiftCarrier N k (δ + k) →ₗ[R] N δ)).comp
            (((shiftEvalAt (R := R) (M := N) k δ (δ + k) e).symm :
              N δ →ₗ[R] ShiftCarrier N k (δ + k))) = LinearMap.id from
          LinearMap.ext fun z =>
            (shiftEvalAt (R := R) (M := N) k δ (δ + k) rfl).apply_symm_apply z,
        TensorProduct.map_id]
    exact congrArg (fun L => L (g ⟨n - k, hnk⟩ ⟨(a, δ), hδ⟩)) hcomp
  exact gen (γ + k - k) (by omega) (by omega) (by omega)

/-- **The comparison sends a single-bidegree element to a single-bidegree element.** -/
theorem tensorShiftMap_tensorSingle (k n : ℕ) {a γ : ℕ}
    (h : (a, γ + k).1 + (a, γ + k).2 = n)
    (z : TensorProduct R (M a) (ShiftCarrier N k (γ + k)))
    (r : {a' : ℕ // a' + k = n}) :
    tensorShiftMap (R := R) (M := M) (N := N) k n
        (tensorSingle (N := ShiftCarrier N k) ⟨(a, γ + k), h⟩ z) r
      = tensorSingle (N := N)
        (⟨(a, γ), by have := r.2; omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = r.1})
        (TensorProduct.map LinearMap.id
          ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
            ShiftCarrier N k (γ + k) →ₗ[R] N γ)) z) := by
  funext p'
  obtain ⟨⟨a', γ'⟩, hp'⟩ := p'
  have hr := r.2
  have hidx : (a', γ' + k).1 + (a', γ' + k).2 = n := by omega
  have hrγ : (a, γ).1 + (a, γ).2 = r.1 := by omega
  show TensorProduct.map LinearMap.id
      ((shiftEvalAt (R := R) (M := N) k γ' (γ' + k) rfl :
        ShiftCarrier N k (γ' + k) →ₗ[R] N γ'))
      (tensorSingle (N := ShiftCarrier N k) ⟨(a, γ + k), h⟩ z ⟨(a', γ' + k), hidx⟩)
    = tensorSingle (N := N) ⟨(a, γ), hrγ⟩
      (TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
          ShiftCarrier N k (γ + k) →ₗ[R] N γ)) z) ⟨(a', γ'), hp'⟩
  by_cases hc : a' = a ∧ γ' = γ
  · obtain ⟨rfl, rfl⟩ := hc
    rw [tensorSingle_same, tensorSingle_same]
  · rw [tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega), map_zero, tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega)]

theorem tensorShiftMap_bijective (k n : ℕ) :
    Function.Bijective (tensorShiftMap (R := R) (M := M) (N := N) k n) :=
  ⟨tensorShiftMap_injective k n, tensorShiftMap_surjective k n⟩

end GaloisForLFunctions.HTGeometry
