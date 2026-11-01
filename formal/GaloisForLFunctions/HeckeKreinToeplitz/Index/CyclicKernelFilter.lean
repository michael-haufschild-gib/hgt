import GaloisForLFunctions.HeckeKreinToeplitz.Index.FrameUnitaryEigenvector
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeUnitaryFilter

/-!
# A unitary index-reducing filter for cyclic kernels

Every subexponentially growing finite-index cyclic kernel is either
positive definite or admits a unitary twisted second-difference filter
with one fewer possible negative square. The filter is extracted from
the completed column representation, so no spectral hypothesis is needed.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

namespace NegativeFrame

variable {G : Type*} [Group G] {k : G → ℂ} {m : ℕ}
    (hk : IsHermKernel k) (e : Fin m → kernelColumnSpan k) (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)

/-- The completed translations as an algebraic group representation. -/
def representation : G →* End ℂ (Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) where
  toFun g := (action hk e he hp g).toLinearEquiv.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    exact action_one hk e he hp v
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    exact action_mul hk e he hp a b v

theorem representation_pairing (g : G) (v w : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :
    FiniteNegative.pairing (representation hk e he hp g v) (representation hk e he hp g w) =
      FiniteNegative.pairing v w := action_pairing hk e he hp g v w

/-- The initial column recovers the original kernel as a representation coefficient. -/
theorem representation_point_coefficient (g : G) :
    FiniteNegative.pairing (embedding hk e he hp (kernelColumnPoint k 1))
      (representation hk e he hp g (embedding hk e he hp (kernelColumnPoint k 1))) = k g := by
  change FiniteNegative.pairing (embedding hk e he hp (kernelColumnPoint k 1))
    (action hk e he hp g (embedding hk e he hp (kernelColumnPoint k 1))) = k g
  rw [action_point, embedding_pairing, kernelColumnPairing_point_left hk]
  change k (1⁻¹ * (g * 1)) = k g
  rw [inv_one, one_mul, mul_one]

end NegativeFrame

/-- The unitary second-difference filter at the generator of the integer group. -/
def cyclicKernelFilter (k : Multiplicative ℤ → ℂ) (a : ℂ) (g : Multiplicative ℤ) : ℂ :=
  2 * k g - a * k ((Multiplicative.ofAdd 1)⁻¹ * g) - conj a * k (g * Multiplicative.ofAdd 1)

/-- A nonpositive direction can be removed by a unitary cyclic filter. -/
theorem isPosDef_or_exists_unitary_cyclic_filter {k : Multiplicative ℤ → ℂ} {r : ℕ}
    (hk : IsHermKernel k) (hi : negIndex k ≤ r + 1)
    (hsub : HasSubexponentialIntegerGrowth (fun z => k (Multiplicative.ofAdd z))) :
    IsPosDefKernel k ∨ ∃ a : ℂ, ‖a‖ = 1 ∧ IsHermKernel (cyclicKernelFilter k a) ∧
      negIndex (cyclicKernelFilter k a) ≤ r := by
  obtain ⟨m, hm, e, he, hp⟩ := exists_maximal_negative_column_frame hk (r := r + 1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hi)
  by_cases hm0 : m = 0
  · subst m
    left
    refine ⟨hk, fun n x c => ?_⟩
    have h := hp (∑ i, c i • kernelColumnPoint k (x i)) (fun i => Fin.elim0 i)
    rwa [kernelColumnPoint_sum_self_re hk] at h
  · right
    obtain ⟨w, a, hw, ha, hwq, heig⟩ :=
      NegativeFrame.exists_unitary_nonpositive_eigenvector hk e he hp (Nat.pos_of_ne_zero hm0) hsub
    let ρ := NegativeFrame.representation hk e he hp
    let v := NegativeFrame.embedding hk e he hp (kernelColumnPoint k 1)
    let u := ρ (Multiplicative.ofAdd 1) v - a • v
    have hρ := NegativeFrame.representation_pairing hk e he hp
    have hcoef : (fun g => FiniteNegative.pairing u (ρ g u)) = cyclicKernelFilter k a := by
      funext g
      change FiniteNegative.pairing (ρ (Multiplicative.ofAdd 1) v - a • v)
        (ρ g (ρ (Multiplicative.ofAdd 1) v - a • v)) = _
      rw [FiniteNegative.coefficient_unitary_filter ρ hρ _ g v ha]
      simp only [v, ρ, NegativeFrame.representation_point_coefficient, cyclicKernelFilter]
    refine ⟨a, ha, ?_, ?_⟩
    · rw [← hcoef]
      exact FiniteNegative.isHermKernel_coefficient ρ hρ u
    · rw [← hcoef]
      apply FiniteNegative.negIndex_unitary_filter_le ρ hρ (t := Multiplicative.ofAdd 1)
        (v := v) (w := w) (a := a) _ hw hwq ha heig
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hm

#print axioms isPosDef_or_exists_unitary_cyclic_filter

end GaloisForLFunctions.HeckeKreinToeplitz
