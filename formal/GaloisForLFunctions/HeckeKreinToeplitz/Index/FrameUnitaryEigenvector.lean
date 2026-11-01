import GaloisForLFunctions.HeckeKreinToeplitz.Index.FrameOrbitSubexponential
import GaloisForLFunctions.HeckeKreinToeplitz.Index.NonpositiveFiniteIndexEigenvector
import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubexponentialScalarRecurrence

/-!
# Unitary nonpositive eigenvectors in the cyclic column representation

Density makes a nonzero nonpositive eigenvector visible to some column.
Its pairing with that column's integer orbit is a nonzero scalar recurrence.
Subexponential orbit growth forces the eigenvalue onto the unit circle.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame

variable {G : Type*} [Group G] {k : G → ℂ} {m : ℕ}
    (hk : IsHermKernel k) (e : Fin m → kernelColumnSpan k) (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)

/-- Every nonzero nonpositive vector is detected by a column. -/
theorem exists_point_nonorthogonal
    {w : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)}
    (hw : w ≠ 0) (hwq : (FiniteNegative.pairing w w).re ≤ 0) :
    ∃ g : G, FiniteNegative.pairing w (embedding hk e he hp (kernelColumnPoint k g)) ≠ 0 := by
  by_contra hn
  push Not at hn
  let L : kernelColumnSpan k →ₗ[ℂ] ℂ :=
    { toFun := fun v => FiniteNegative.pairing w (embedding hk e he hp v)
      map_add' := fun v t => by rw [map_add, FiniteNegative.pairing_add_right]
      map_smul' := fun c v => by rw [map_smul, FiniteNegative.pairing_smul_right]; rfl }
  have hl (g : G) : L (kernelColumnPoint k g) = 0 := hn g
  have hv (v : kernelColumnSpan k) : FiniteNegative.pairing w (embedding hk e he hp v) = 0 := by
    obtain ⟨n, x, c, hc⟩ := exists_kernelColumnPoint_fin_sum k v
    change L v = 0
    rw [← hc, map_sum]
    simp only [map_smul, hl, smul_zero, Finset.sum_const_zero]
  have hall (v : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :
      FiniteNegative.pairing w v = 0 :=
    (embedding_dense hk e he hp).induction_on v
      (isClosed_eq (FiniteNegative.continuous_pairing.comp
        (continuous_const.prodMk continuous_id)) continuous_const) hv
  have hs : w.2 = 0 := by
    have h := hall (0, w.2)
    simp only [FiniteNegative.pairing, inner_zero_right, zero_sub] at h
    exact inner_self_eq_zero.mp (neg_eq_zero.mp h)
  exact hw (FiniteNegative.eq_zero_of_nonpositive_snd_eq_zero hwq hs)

variable {q : Multiplicative ℤ → ℂ} (hq : IsHermKernel q)
    (v : Fin m → kernelColumnSpan q) (hv : IsNegativeColumnFrame v)
    (hpos : ∀ t : kernelColumnSpan q, (∀ i, kernelColumnPairing q (v i) t = 0) →
      0 ≤ (kernelColumnPairing q t t).re)

/-- A finite-index cyclic kernel with subexponential growth has a unitary nonpositive eigenvector. -/
theorem exists_unitary_nonpositive_eigenvector (hm : 0 < m)
    (hsub : HasSubexponentialIntegerGrowth (fun z => q (Multiplicative.ofAdd z))) :
    ∃ (w : Hilbert hq v hv hpos × EuclideanSpace ℂ (Fin m)) (a : ℂ),
      w ≠ 0 ∧ ‖a‖ = 1 ∧ (FiniteNegative.pairing w w).re ≤ 0 ∧
        action hq v hv hpos (Multiplicative.ofAdd 1) w = a • w := by
  obtain ⟨w, a, hw, _, hwq, heig⟩ := FiniteNegative.exists_nonpositive_eigenvector
    (action hq v hv hpos (Multiplicative.ofAdd 1))
    (action_pairing hq v hv hpos (Multiplicative.ofAdd 1)) hm
  obtain ⟨g, hg⟩ := exists_point_nonorthogonal hq v hv hpos hw hwq
  let b : ℤ := Multiplicative.toAdd g
  let u (z : ℤ) := embedding hq v hv hpos (kernelColumnPoint q (Multiplicative.ofAdd (b + z)))
  have hu : HasSubexponentialIntegerGrowth u :=
    (embedding_point_subexponential hq hsub v hv hpos).translate b
  have hf : HasSubexponentialIntegerGrowth (fun z => FiniteNegative.pairing w (u z)) := by
    let C : ℝ := ‖w.1‖ + ‖w.2‖
    have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
    apply (hu.norm.smul C).of_norm_le
    intro z
    change ‖FiniteNegative.pairing w (u z)‖ ≤ ‖C * ‖u z‖‖
    rw [Real.norm_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    exact FiniteNegative.norm_pairing_le w (u z)
  have h0 : FiniteNegative.pairing w (u 0) ≠ 0 := by
    simpa [u, b] using hg
  have hshift (z : ℤ) : action hq v hv hpos (Multiplicative.ofAdd 1) (u z) = u (z + 1) := by
    dsimp only [u]
    rw [action_point]
    congr 2
    change Multiplicative.ofAdd (1 + (b + z)) = Multiplicative.ofAdd (b + (z + 1))
    congr 1
    omega
  have hrec (z : ℤ) : conj a * FiniteNegative.pairing w (u (z + 1)) =
      FiniteNegative.pairing w (u z) := by
    have h := action_pairing hq v hv hpos (Multiplicative.ofAdd 1) w (u z)
    rw [heig, hshift, FiniteNegative.pairing_smul_left] at h
    exact h
  refine ⟨w, a, hw, ?_, hwq, heig⟩
  simpa only [Complex.norm_conj] using norm_eq_one_of_subexponential_recurrence hf h0 hrec

#print axioms exists_unitary_nonpositive_eigenvector

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame
