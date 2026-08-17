import Mathlib

/-!
# The weighted atom Hilbert space

A positive integer weight `w : A → ℕ` on an index set is realised, without any weighted-measure
machinery, by splitting each index into `w a` atoms: the `ℓ²` space of the sigma type
`Σ a, Fin (w a)` carries exactly the weighted form

```text
‖c‖² = ∑ a, w a · |c a|².
```

This file provides the two structural facts that a positive semisimple boundary Hilbert space
needs:

* `tsum_sigma_fiberConst` — the weighted-norm identity for data constant along each fibre;
* `lpPhaseUnitary` — multiplication by a unimodular function on the atoms is a unitary, together
  with its group law `lpPhaseUnitary_one`, `lpPhaseUnitary_mul`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

theorem lp_two_norm_sq_eq_tsum (f : lp (fun _ : ι => ℂ) 2) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  simpa using h

theorem memℓp_two_of_eq_zero_outside {f : ι → ℂ} {s : Finset ι}
    (h : ∀ i, i ∉ s → f i = 0) : Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_of_ne_finset_zero (s := s) (fun i hi => ?_)
  rw [h i hi]
  simp

theorem memℓp_phase {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1) (f : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun i => u i * f i) 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  refine hf.congr (fun i => ?_)
  rw [norm_mul, hu i, one_mul]

/-- Multiplication by a unimodular function on the atoms. -/
def lpPhaseMap (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) (f : lp (fun _ : ι => ℂ) 2) :
    lp (fun _ : ι => ℂ) 2 := ⟨fun i => u i * f i, memℓp_phase hu f⟩

@[simp] theorem lpPhaseMap_apply (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPhaseMap u hu f i = u i * f i := rfl

theorem norm_lpPhaseMap (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) (f : lp (fun _ : ι => ℂ) 2) :
    ‖lpPhaseMap u hu f‖ = ‖f‖ := by
  have h1 : ‖lpPhaseMap u hu f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [lp_two_norm_sq_eq_tsum, lp_two_norm_sq_eq_tsum]
    refine tsum_congr (fun i => ?_)
    rw [lpPhaseMap_apply, norm_mul, hu i, one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (lpPhaseMap u hu f)), ← Real.sqrt_sq (norm_nonneg f), h1]

/-- **A unimodular atom phase is a unitary of the atom Hilbert space.** -/
def lpPhaseUnitary (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun := lpPhaseMap u hu
  map_add' := by
    intro f g
    refine lp.ext (funext fun i => ?_)
    simp [mul_add]
  map_smul' := by
    intro a f
    refine lp.ext (funext fun i => ?_)
    simp [mul_comm, mul_assoc, mul_left_comm]
  invFun := lpPhaseMap (fun i => (starRingEnd ℂ) (u i))
    (fun i => by rw [RCLike.norm_conj]; exact hu i)
  left_inv := by
    intro f
    refine lp.ext (funext fun i => ?_)
    have hnormSq : (starRingEnd ℂ) (u i) * u i = 1 := by
      have h := Complex.mul_conj' (u i)
      have hn : ‖u i‖ = 1 := hu i
      rw [mul_comm]
      rw [h, hn]
      norm_num
    simp only [lpPhaseMap_apply, ← mul_assoc, hnormSq, one_mul]
  right_inv := by
    intro f
    refine lp.ext (funext fun i => ?_)
    have hnormSq : u i * (starRingEnd ℂ) (u i) = 1 := by
      have h := Complex.mul_conj' (u i)
      have hn : ‖u i‖ = 1 := hu i
      rw [h, hn]
      norm_num
    simp only [lpPhaseMap_apply, ← mul_assoc, hnormSq, one_mul]
  norm_map' := norm_lpPhaseMap u hu

@[simp] theorem lpPhaseUnitary_apply (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPhaseUnitary u hu f i = u i * f i := rfl

theorem lpPhaseUnitary_one : lpPhaseUnitary (fun _ : ι => (1 : ℂ)) (fun _ => norm_one)
    = LinearIsometryEquiv.refl ℂ (lp (fun _ : ι => ℂ) 2) := by
  refine LinearIsometryEquiv.ext (fun f => ?_)
  refine lp.ext (funext fun i => ?_)
  simp

theorem lpPhaseUnitary_mul (u v : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) :
    lpPhaseUnitary (fun i => u i * v i) (fun i => by rw [norm_mul, hu i, hv i]; norm_num)
      = (lpPhaseUnitary v hv).trans (lpPhaseUnitary u hu) := by
  refine LinearIsometryEquiv.ext (fun f => ?_)
  refine lp.ext (funext fun i => ?_)
  simp [mul_assoc]

theorem tsum_sigma_fiberConst {A : Type*} (w : A → ℕ) (c : A → ℂ) (s : Finset A)
    (hc : ∀ a, a ∉ s → c a = 0) :
    ∑' q : (Σ a : A, Fin (w a)), ‖c q.1‖ ^ 2 = ∑ a ∈ s, (w a : ℝ) * ‖c a‖ ^ 2 := by
  classical
  rw [tsum_eq_sum (s := s.sigma (fun _ => Finset.univ)) ?_]
  · rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hfib : ∀ j : Fin (w a), ‖c (⟨a, j⟩ : Σ a : A, Fin (w a)).1‖ ^ 2 = ‖c a‖ ^ 2 :=
      fun _ => rfl
    rw [Finset.sum_congr rfl (fun j _ => hfib j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  · intro q hq
    have hz : c q.1 = 0 := by
      refine hc _ (fun hcon => ?_)
      exact hq (Finset.mem_sigma.mpr ⟨hcon, Finset.mem_univ _⟩)
    rw [hz]
    simp

end GaloisForLFunctions.HTGeometry
