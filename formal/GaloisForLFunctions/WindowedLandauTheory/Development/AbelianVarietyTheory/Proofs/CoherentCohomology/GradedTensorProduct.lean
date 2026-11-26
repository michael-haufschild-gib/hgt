import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GradedTensorContraction
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! The degree projections on a tensor total complex sum over the antidiagonal. -/

noncomputable section

open TensorProduct

namespace GlobalTheory.CechDR.FiniteGradedComplex

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable (G : FiniteGradedComplex K V) (H : FiniteGradedComplex K W)

/-- The degree projections of the factors suffice to test maps out of their tensor product. -/
theorem tensor_ext_degrees {U : Type} [AddCommGroup U] [Module K U]
    {f g : V ⊗[K] W →ₗ[K] U}
    (h : ∀ p q a b, f (G.π p a ⊗ₜ H.π q b) = g (G.π p a ⊗ₜ H.π q b)) : f = g := by
  refine TensorProduct.ext' fun a b => ?_
  rw [← G.sum a, sum_tmul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← H.sum b, tmul_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => h p q a b

/-- Projection to the specified total degree. -/
def tensorProjection (n : ℕ) : V ⊗[K] W →ₗ[K] V ⊗[K] W :=
  ∑ x ∈ Finset.Nat.antidiagonal n, TensorProduct.map (G.π x.1) (H.π x.2)

theorem tensorProjection_tmul (n p q : ℕ) (a : V) (b : W)
    (ha : G.π p a = a) (hb : H.π q b = b) :
    tensorProjection G H n (a ⊗ₜ b) = if p + q = n then a ⊗ₜ b else 0 := by
  rw [tensorProjection, LinearMap.sum_apply]
  simp only [TensorProduct.map_tmul]
  have hz (x : ℕ × ℕ) (hx : x ≠ (p, q)) : G.π x.1 a ⊗ₜ[K] H.π x.2 b = 0 := by
    by_cases hp : x.1 = p
    · have hq : x.2 ≠ q := fun hq => hx (Prod.ext hp hq)
      rw [← hb, H.orth _ _ _ hq, tmul_zero]
    · rw [← ha, G.orth _ _ _ hp, zero_tmul]
  by_cases h : p + q = n
  · rw [if_pos h, Finset.sum_eq_single_of_mem (p, q) (Finset.Nat.mem_antidiagonal.2 h)
      (fun x _ hx => hz x hx), ha, hb]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x hx => hz x fun he => h ?_
    exact (Finset.Nat.mem_antidiagonal.1 hx : x.1 + x.2 = n) |> fun he' => he ▸ he'

private theorem sign_of_fixed {p : ℕ} {a : V} (ha : G.π p a = a) :
    G.σ a = ((-1 : ℤ) ^ p) • a := by
  simpa only [ha] using G.σπ p a

private theorem d_fixed {p : ℕ} {a : V} (ha : G.π p a = a) :
    G.π (p + 1) (G.d a) = G.d a := by
  simpa only [ha] using (G.dπ p a).symm

private theorem sign_fixed {p : ℕ} {a : V} (ha : G.π p a = a) :
    G.π p (G.σ a) = G.σ a := by
  rw [G.sign_of_fixed ha, map_zsmul, ha]

/-- The signed differential and the total-degree projections define a finite graded complex. -/
def tensorComplex : FiniteGradedComplex K (V ⊗[K] W) where
  d := tensorDifferential G H
  π := tensorProjection G H
  σ := TensorProduct.map G.σ H.σ
  N := G.N + H.N
  dd z := by
    have h : tensorDifferential G H ∘ₗ tensorDifferential G H = 0 := by
      refine TensorProduct.ext' fun a b => ?_
      simp only [tensorDifferential, LinearMap.comp_apply, LinearMap.add_apply, map_add,
        TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply,
        G.dd, H.dd, G.σd, zero_tmul, tmul_zero, neg_tmul, zero_add, add_zero, add_neg_cancel]
    exact LinearMap.congr_fun h z
  idem n z := by
    have h : tensorProjection G H n ∘ₗ tensorProjection G H n = tensorProjection G H n := by
      refine tensor_ext_degrees G H fun p q a b => ?_
      simp only [LinearMap.comp_apply, tensorProjection_tmul G H n p q _ _ (G.idem p a) (H.idem q b)]
      split_ifs with h
      · exact tensorProjection_tmul G H n p q _ _ (G.idem p a) (H.idem q b) |>.trans (if_pos h)
      · exact map_zero _
    exact LinearMap.congr_fun h z
  orth n m z hnm := by
    have h : tensorProjection G H n ∘ₗ tensorProjection G H m = 0 := by
      refine tensor_ext_degrees G H fun p q a b => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply,
        tensorProjection_tmul G H m p q _ _ (G.idem p a) (H.idem q b)]
      split_ifs with hm
      · rw [tensorProjection_tmul G H n p q _ _ (G.idem p a) (H.idem q b),
          if_neg (hm.trans_ne hnm.symm)]
      · exact map_zero _
    exact LinearMap.congr_fun h z
  sum z := by
    have h : ∑ n ∈ Finset.range (G.N + H.N), tensorProjection G H n = LinearMap.id := by
      refine tensor_ext_degrees G H fun p q a b => ?_
      simp only [LinearMap.sum_apply, LinearMap.id_apply,
        tensorProjection_tmul G H _ p q _ _ (G.idem p a) (H.idem q b)]
      by_cases h : p + q ∈ Finset.range (G.N + H.N)
      · rw [Finset.sum_eq_single_of_mem (p + q) h (fun _ _ hne => if_neg hne.symm), if_pos rfl]
      · rw [Finset.sum_eq_zero fun n hn => if_neg fun he => h (he ▸ hn)]
        have hj : G.N ≤ p ∨ H.N ≤ q := by
          rw [Finset.mem_range] at h
          omega
        rcases hj with hp | hq
        · rw [G.big hp, zero_tmul]
        · rw [H.big hq, tmul_zero]
    exact LinearMap.congr_fun h z
  zero z := by
    have h : tensorProjection G H 0 = 0 := TensorProduct.ext' fun a b => by
      simp [tensorProjection, LinearMap.sum_apply, G.zero]
    exact LinearMap.congr_fun h z
  dπ n z := by
    have h : tensorDifferential G H ∘ₗ tensorProjection G H n =
        tensorProjection G H (n + 1) ∘ₗ tensorDifferential G H := by
      refine tensor_ext_degrees G H fun p q a b => ?_
      have ha := G.idem p a
      have hb := H.idem q b
      simp only [LinearMap.comp_apply, tensorProjection_tmul G H n p q _ _ ha hb]
      rw [show tensorDifferential G H (G.π p a ⊗ₜ H.π q b) =
          G.d (G.π p a) ⊗ₜ H.π q b + G.σ (G.π p a) ⊗ₜ H.d (H.π q b) by
            simp only [tensorDifferential, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply],
        map_add, tensorProjection_tmul G H _ (p + 1) q _ _ (G.d_fixed ha) hb,
        tensorProjection_tmul G H _ p (q + 1) _ _ (G.sign_fixed ha) (H.d_fixed hb)]
      by_cases hpq : p + q = n
      · simp only [if_pos hpq, if_pos (show p + 1 + q = n + 1 by omega),
          if_pos (show p + (q + 1) = n + 1 by omega), tensorDifferential,
          LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]
      · simp only [if_neg hpq, if_neg (show p + 1 + q ≠ n + 1 by omega),
          if_neg (show p + (q + 1) ≠ n + 1 by omega), map_zero, add_zero]
    exact LinearMap.congr_fun h z
  σπ n z := by
    have h : TensorProduct.map G.σ H.σ ∘ₗ tensorProjection G H n =
        ((-1 : ℤ) ^ n) • tensorProjection G H n := by
      refine tensor_ext_degrees G H fun p q a b => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply,
        tensorProjection_tmul G H n p q _ _ (G.idem p a) (H.idem q b)]
      split_ifs with hpq
      · rw [TensorProduct.map_tmul, G.sign_of_fixed (G.idem p a), H.sign_of_fixed (H.idem q b),
          zsmul_tmul', tmul_zsmul, smul_smul, ← pow_add, hpq]
      · rw [map_zero, smul_zero]
    exact LinearMap.congr_fun h z

end GlobalTheory.CechDR.FiniteGradedComplex
