import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle

/-!
# Charge cancellation preserves the certified floor

Every nonempty window of ratio at most `103/50` has floor `1/5000` above its
positive ground vector, including windows shorter than a dyadic interval.
For a Schur complement, canceling charge with the middle's negative ground
vector preserves the full charge-free floor, independently of the middle's
positive spectral floor. The harmonic form gives the local overlap index law.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section
namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-- The certified floor on the zero-charge hyperplane, in finite-vector form. -/
private theorem chargedWindow_floor {Q R J : ℕ} (hR : 1 ≤ R)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    1 / 5000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, neutralWindow,
    sum_fin_windowMatrix_eq, dotProduct_self_eq_sum_range_extendFin]
  exact sum_neutralBlock_ge_of_short hR hJ hQ
    (Or.inl ((sum_fin_eq_sum_range_extendFin z).symm.trans hz))

/-- Above its positive ground vector, every certified window has floor `1/5000`. -/
theorem neutralWindow_floor_orthogonal {Q R J : ℕ} (hR : 1 ≤ R)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q)
    {φ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ) (z : Fin J → ℝ)
    (hz : φ ⬝ᵥ z = 0) :
    1 / 5000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · simp [dotProduct]
  haveI : Nonempty (Fin J) := ⟨⟨0, hJpos⟩⟩
  rcases le_total (1 / 5000 : ℝ) lam with hlow | hhigh
  · have h := lam_mul_sum_sq_le_bilin (neutralWindow_symm Q R J)
      (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig z
    rw [← dotProduct_mulVec_eq_bilin] at h
    have hn : z ⬝ᵥ z = ∑ i, z i ^ 2 := by simp only [dotProduct, sq]
    rw [← hn] at h
    exact (mul_le_mul_of_nonneg_right hlow (dotProduct_self_star_nonneg (v := z))).trans h
  · have hℓ : (fun _ : Fin J => (1 : ℝ)) ⬝ᵥ φ ≠ 0 := by
      have hp : 0 < ∑ i, φ i := Finset.sum_pos (fun i _ => hφ i) Finset.univ_nonempty
      simpa only [dotProduct, one_mul] using hp.ne'
    have he : (neutralWindow Q R J + diagonal (fun _ => -(1 / 5000 : ℝ))) *ᵥ φ =
        (-(1 / 5000 - lam)) • φ := by
      rw [Matrix.add_mulVec, heig, diagonal_const_mulVec, ← add_smul]
      congr 1
      ring
    have hf := floor_orthogonal_of_floor_hyperplane
      (symm_add_diagonal (neutralWindow_symm Q R J) _)
      (sub_nonneg.mpr hhigh) (le_refl (0 : ℝ)) he hℓ
      (fun y hy => by
        have h := chargedWindow_floor hR hJ hQ y
          (by simpa only [dotProduct, one_mul] using hy)
        rw [dotProduct_add_diagonal_mulVec]
        linarith) z hz
    rw [dotProduct_add_diagonal_mulVec] at hf
    linarith

/-- A floor on a charged hyperplane passes unchanged to the Schur complement of a
negative middle state. Charge cancellation leaves the end coordinates fixed. -/
theorem schur_floor_of_charge_cancellation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c d : ℝ}
    (h : OneBoundState M φ μ c) (P : Matrix ι κ ℝ) (N : Matrix κ κ ℝ)
    (ℓ : ι ⊕ κ → ℝ) (hℓ : (ℓ ∘ Sum.inl) ⬝ᵥ φ ≠ 0) (hd : 0 ≤ d)
    (hf : ∀ y : ι ⊕ κ → ℝ, ℓ ⬝ᵥ y = 0 →
      d * (y ⬝ᵥ y) ≤ y ⬝ᵥ (fromBlocks M P Pᵀ N *ᵥ y)) (e : κ → ℝ) :
    d * (e ⬝ᵥ e) ≤ e ⬝ᵥ ((N - Pᵀ * M⁻¹ * P) *ᵥ e) := by
  let g := M⁻¹ *ᵥ (P *ᵥ e)
  let t := (ℓ ⬝ᵥ Sum.elim (-g) e) / ((ℓ ∘ Sum.inl) ⬝ᵥ φ)
  let m := -g - t • φ
  have hy : ℓ ⬝ᵥ Sum.elim m e = 0 := by
    have hs := Sum.elim_comp_inl_inr ℓ
    rw [← hs, sumElim_dotProduct_sumElim]
    dsimp only [m, t]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have heq : ℓ ⬝ᵥ Sum.elim (-g) e =
        (ℓ ∘ Sum.inl) ⬝ᵥ (-g) + (ℓ ∘ Sum.inr) ⬝ᵥ e := by
      conv_lhs => rw [← hs]
      rw [sumElim_dotProduct_sumElim]
    rw [heq, div_mul_cancel₀ _ hℓ]
    ring
  have hb := hf (Sum.elim m e) hy
  rw [sumElim_dotProduct_sumElim, dotProduct_fromBlocks_mulVec_eq_schur h.symm h.isUnit] at hb
  have hm : m + M⁻¹ *ᵥ (P *ᵥ e) = -t • φ := by
    dsimp only [m, g]
    module
  rw [hm, Matrix.mulVec_smul, h.eig, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, h.unit] at hb
  have hmnonneg : 0 ≤ d * (m ⬝ᵥ m) :=
    mul_nonneg hd (dotProduct_self_star_nonneg (v := m))
  have ht := mul_nonneg h.depth_pos.le (sq_nonneg t)
  nlinarith only [hb, hmnonneg, ht]


/-- Every eigenvalue other than the ground eigenvalue is at least `1/5000`. -/
theorem eigenvalue_ge_of_ne_ground_of_short {Q R J : ℕ} (hR : 1 ≤ R)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q)
    {φ ψ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam eta : ℝ}
    (hground : neutralWindow Q R J *ᵥ φ = lam • φ)
    (heig : neutralWindow Q R J *ᵥ ψ = eta • ψ) (hψ : ψ ≠ 0) (hne : eta ≠ lam) :
    1 / 5000 ≤ eta := by
  have hz : φ ⬝ᵥ ψ = 0 := by
    have hs := dotProduct_mulVec_symm (neutralWindow_symm Q R J) φ ψ
    rw [heig, hground, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_comm ψ φ] at hs
    have he : (eta - lam) * (φ ⬝ᵥ ψ) = 0 := by linarith
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  have hf := neutralWindow_floor_orthogonal hR hJ hQ hφ hground ψ hz
  rw [heig, dotProduct_smul, smul_eq_mul] at hf
  have hn : 0 < ψ ⬝ᵥ ψ := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := ψ))
    (Ne.symm (fun hz => hψ (dotProduct_self_eq_zero.mp hz)))
  exact le_of_mul_le_mul_right hf hn


/-- Every nonempty certified window has a positive ground vector and floor `1/5000`
on its orthogonal complement. -/
theorem exists_groundVector_with_floor_of_short {Q R J : ℕ} (hR : 1 ≤ R)
    (hJpos : 1 ≤ J) (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q) :
    ∃ (φ : Fin J → ℝ) (lam : ℝ), (∀ i, 0 < φ i) ∧
      neutralWindow Q R J *ᵥ φ = lam • φ ∧
      ∀ z : Fin J → ℝ, φ ⬝ᵥ z = 0 →
        1 / 5000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  obtain ⟨φ, hφ, lam, heig⟩ := exists_groundVector_neutralWindow Q R hJpos
  exact ⟨φ, lam, hφ, heig, neutralWindow_floor_orthogonal hR hJ hQ hφ heig⟩


/-- A window has exactly one negative square iff its form is nonnegative on the
vectors orthogonal to its dyadic middle for the neutral bilinear form. -/
theorem hermNegIndex_neutralWindow_eq_one_iff_harmonic_nonneg {Q R : ℕ}
    (a b : ℕ) (hR : 1 ≤ R) (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      ∀ (m : Fin (R + a) → ℝ) (e : Fin a ⊕ Fin b → ℝ),
        primeFreeMiddle (R + a) *ᵥ m + endCoupling Q R a b *ᵥ e = 0 →
          0 ≤ Sum.elim m e ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a))
            (endCoupling Q R a b) (endCoupling Q R a b)ᵀ (endForm Q R a b) *ᵥ
              Sum.elim m e) := by
  rw [hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b hR hQ]
  have hD : 1 ≤ R + a := by omega
  constructor
  · intro h m e hme
    rw [overlapSchur_form_eq_harmonic Q R a b hD hme]
    exact h e
  · intro h e
    have hme : primeFreeMiddle (R + a) *ᵥ
        (-(greenMatrix (R + a) *ᵥ (endCoupling Q R a b *ᵥ e))) +
        endCoupling Q R a b *ᵥ e = 0 := by
      rw [Matrix.mulVec_neg, greenMatrix, (oneBoundState_primeFreeMiddle hD).mulVec_inv_mulVec,
        neg_add_cancel]
    rw [← overlapSchur_form_eq_harmonic Q R a b hD hme]
    exact h _ _ hme

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

#print axioms GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.eigenvalue_ge_of_ne_ground_of_short

#print axioms GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.exists_groundVector_with_floor_of_short

#print axioms GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.schur_floor_of_charge_cancellation

#print axioms GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.hermNegIndex_neutralWindow_eq_one_iff_harmonic_nonneg
