import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.HTGeometry.HaynsworthInertia
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia

/-!
# Finite index is positive definite minus finite rank

This is the structure theorem behind the index. It holds on any group, with no covariance and no
growth hypothesis.

**Attainment** (`exists_hermNegIndex_gram_eq_negIndex`). A finite index is attained on one finite
family.

**Pontryagin decomposition** (`exists_pontryagin_decomposition`). Suppose `κ(k) = m` is finite.
Then there are a finite family `x₀` and `m` functions `φ_i(y) = Σ_b w_{ib} k(x₀_b⁻¹ y)` such that
`k(y⁻¹z) + Σ_i conj(φ_i(y)) φ_i(z)` is positive semidefinite. Each `φ_i` lies in the span of the
translates of `k`. The `φ_i` are read off the negative eigenvectors of an extremal Gram matrix. On
the family `x₀ ⊔ x`, the Haynsworth formula then forces the Schur complement of the negative block
to have no negative square, because `x₀` already carries all `m` of them.

**Finite index is positive minus finite rank** (`negIndex_le_iff_exists_rank`). A Hermitian kernel
has `κ(k) ≤ m` iff it becomes positive semidefinite after adding `m` squares of functions on `G`.
Subadditivity `κ(k₁ + k₂) ≤ κ(k₁) + κ(k₂)` follows (`negIndex_add_le`).
This is the converse of the upper half of the index formula, with no covariance. The covariant
version, where the `φ_i` assemble into hyperbolic pairs of characters, is the Krein–Langer theorem.
On `ℚ_{>0}` that version is proved for the orbit kernels of zero configurations.
-/

open Complex Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (negIndex_le_card_of_nonneg_on_ker
  hermQuad_nonneg_of_negIndex_eq_zero)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- **A finite index is attained on one finite family.** -/
theorem exists_hermNegIndex_gram_eq_negIndex {k : G → ℂ} (h : negIndex k < ⊤) :
    ∃ (n : ℕ) (x : Fin n → G), (hermNegIndex (gram k x) : ℕ∞) = negIndex k := by
  have h' : ⨆ p : (Σ n : ℕ, Fin n → G), (hermNegIndex (gram k p.2) : ℕ∞) = negIndex k := by
    rw [negIndex, iSup_sigma]
  haveI : Nonempty (Σ n : ℕ, Fin n → G) := ⟨⟨0, Fin.elim0⟩⟩
  obtain ⟨⟨n, x⟩, hx⟩ := ENat.exists_eq_iSup_of_lt_top (h'.symm ▸ h)
  exact ⟨n, x, hx.trans h'⟩

/-- **Pontryagin decomposition.** A Hermitian kernel with `m` negative squares becomes positive
semidefinite after adding the squares of `m` functions spanned by translates of itself. -/
theorem exists_pontryagin_decomposition {k : G → ℂ} (hk : IsHermKernel k) {m : ℕ}
    (hm : negIndex k = m) :
    ∃ (n₀ : ℕ) (x₀ : Fin n₀ → G) (w : Fin m → Fin n₀ → ℂ),
      ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
        0 ≤ hermQuad (gram k x) c + ∑ i, normSq (∑ a, c a * ∑ b, w i b * k ((x₀ b)⁻¹ * x a)) := by
  classical
  obtain ⟨n₀, x₀, hx₀⟩ := exists_hermNegIndex_gram_eq_negIndex (k := k) (by
    rw [hm]; exact ENat.coe_lt_top m)
  rw [hm, Nat.cast_inj] at hx₀
  have hH : (gram k x₀).IsHermitian := gram_isHermitian hk x₀
  set U : Matrix (Fin n₀) (Fin n₀) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n₀) (Fin n₀) ℂ)
  set lam := hH.eigenvalues with hlam
  set J := {i : Fin n₀ // lam i < 0}
  have hJ : Fintype.card J = m := by
    rw [Fintype.card_subtype, ← hx₀, negIndex_eq_card_neg_eigenvalues hH]
  let e : Fin m ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  refine ⟨n₀, x₀, fun i b => star (U b (e i)) / (Real.sqrt (-lam (e i)) : ℂ), fun n x c => ?_⟩
  -- the negative eigenvectors, the cross block, and the negative block
  set V : Matrix (Fin n₀) J ℂ := fun b j => U b j
  set K : Matrix (Fin n₀) (Fin n) ℂ := fun b a => k ((x₀ b)⁻¹ * x a)
  set A : Matrix J J ℂ := diagonal fun j => ((lam j : ℝ) : ℂ)
  set B : Matrix J (Fin n) ℂ := Vᴴ * K
  have hA : Vᴴ * gram k x₀ * V = A := by
    ext i j
    change (Uᴴ * gram k x₀ * U) i.1 j.1 = _
    rw [conjTranspose_mul_mul_eigenvectorUnitary hH]
    simp only [A, diagonal_apply, ← hlam]
    by_cases h : i = j
    · rw [if_pos (congrArg Subtype.val h), if_pos h]
    · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]
  -- the Gram matrix of `x₀ ⊔ x`, compressed to the negative eigenvectors of `x₀`
  have hz : gram k (Sum.elim x₀ x) = fromBlocks (gram k x₀) K Kᴴ (gram k x) := by
    ext p q
    rcases p with b | a <;> rcases q with b' | a'
    · rfl
    · rfl
    · simp only [gram, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁, conjTranspose_apply, K,
        Complex.star_def]
      rw [show (x a)⁻¹ * x₀ b' = ((x₀ b')⁻¹ * x a)⁻¹ by group, hk]
    · rfl
  set P : Matrix (Fin n₀ ⊕ Fin n) (J ⊕ Fin n) ℂ := fromBlocks V 0 0 1
  have hT : Pᴴ * gram k (Sum.elim x₀ x) * P = fromBlocks A B Bᴴ (gram k x) := by
    rw [hz, ← hA]
    simp [P, B, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_mul, Matrix.mul_assoc]
  have hTle : hermNegIndex (fromBlocks A B Bᴴ (gram k x)) ≤ m := by
    rw [← hT]
    have h1 : hermNegIndex (Pᴴ * gram k (Sum.elim x₀ x) * P) ≤
        hermNegIndex (gram k (Sum.elim x₀ x)) :=
      hermNegIndex_le_of_hermQuad_eq _ _ P.mulVecLin fun v => by
        rw [mulVecLin_apply, hermQuad_rect_conjugate]
    have h2 := hermNegIndex_gram_le_negIndex k (Sum.elim x₀ x)
    rw [hm] at h2
    exact h1.trans (by exact_mod_cast h2)
  -- the negative block carries all `m` squares, so the Schur complement carries none
  have hAneg : hermNegIndex A = m := by
    rw [negIndex_diagonal, Finset.filter_true_of_mem fun j _ => j.2, Finset.card_univ, hJ]
  have hAu : IsUnit A := isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun j =>
    isUnit_iff_ne_zero.mpr (by exact_mod_cast j.2.ne))
  have hAh : A.IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (funext fun j => by simp [Pi.star_apply])
  rw [haynsworth_negIndex hAu hAh B (gram_isHermitian hk x), hAneg] at hTle
  have hq := hermQuad_nonneg_of_negIndex_eq_zero (show hermNegIndex (gram k x - Bᴴ * A⁻¹ * B) = 0 by omega) c
  have hAinv : A⁻¹ = diagonal fun j : J => (((lam j)⁻¹ : ℝ) : ℂ) := by
    refine inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    rw [← ofReal_mul, mul_inv_cancel₀ j.2.ne, ofReal_one]
  rw [sub_eq_add_neg, hermQuad_add, hermQuad_neg, hAinv, hermQuad_rect_conjugate,
    hermQuad_diagonal] at hq
  -- the defect squares are the coordinates of `B c`, normalized by `|λ_j|`
  have hterm : ∀ i, normSq (∑ a, c a * ∑ b, star (U b (e i)) / (Real.sqrt (-lam (e i)) : ℂ) *
      k ((x₀ b)⁻¹ * x a)) = -((lam (e i))⁻¹ * normSq ((B *ᵥ c) (e i))) := fun i => by
    have hneg : 0 ≤ -lam (e i) := by linarith [(e i).2]
    have : ∑ a, c a * ∑ b, star (U b (e i)) / (Real.sqrt (-lam (e i)) : ℂ) * k ((x₀ b)⁻¹ * x a) =
        ((Real.sqrt (-lam (e i)) : ℝ) : ℂ)⁻¹ * (B *ᵥ c) (e i) := by
      simp only [B, mulVec, dotProduct, mul_apply, conjTranspose_apply, V, K, Finset.mul_sum,
        Finset.sum_mul, div_eq_mul_inv]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [this, normSq_mul, map_inv₀, normSq_ofReal, Real.mul_self_sqrt hneg, inv_neg]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib,
    e.sum_comp (fun j : J => (lam j)⁻¹ * normSq ((B *ᵥ c) j))]
  exact hq

/-- Adding `m` squares that make every Toeplitz form nonnegative bounds the index by `m`. -/
theorem negIndex_le_of_rank {k : G → ℂ} {m : ℕ} (φ : Fin m → G → ℂ)
    (h : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      0 ≤ hermQuad (gram k x) c + ∑ i, normSq (∑ a, c a * φ i (x a))) :
    negIndex k ≤ m := by
  refine negIndex_le_iff.mpr fun n x => ?_
  have := negIndex_le_card_of_nonneg_on_ker (gram k x)
    (fun i => Fintype.linearCombination ℂ fun a => φ i (x a)) fun c hc => by
      have h0 : ∀ i, ∑ a, c a * φ i (x a) = 0 := fun i => by
        simpa [Fintype.linearCombination_apply, smul_eq_mul] using hc i
      simpa [h0] using h n x c
  exact_mod_cast this.trans (Fintype.card_fin m).le

/-- **Finite index is positive definite minus finite rank.** A Hermitian kernel has at most `m`
negative squares iff it becomes positive semidefinite after adding `m` squares of functions. -/
theorem negIndex_le_iff_exists_rank {k : G → ℂ} (hk : IsHermKernel k) (m : ℕ) :
    negIndex k ≤ m ↔ ∃ φ : Fin m → G → ℂ, ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      0 ≤ hermQuad (gram k x) c + ∑ i, normSq (∑ a, c a * φ i (x a)) := by
  refine ⟨fun h => ?_, fun ⟨φ, hφ⟩ => negIndex_le_of_rank φ hφ⟩
  obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top m) h)
  have hle : m' ≤ m := by rw [← hm'] at h; exact_mod_cast h
  obtain ⟨n₀, x₀, w, hw⟩ := exists_pontryagin_decomposition hk hm'.symm
  set φ : Fin m → G → ℂ := fun i y =>
    if hi : (i : ℕ) < m' then ∑ b, w ⟨i, hi⟩ b * k ((x₀ b)⁻¹ * y) else 0
  refine ⟨φ, fun n x c => (hw n x c).trans (add_le_add_right ?_ _)⟩
  have hsub := Finset.sum_le_univ_sum_of_nonneg (s := univ.map (Fin.castLEEmb hle))
    (f := fun i => normSq (∑ a, c a * φ i (x a))) fun _ => normSq_nonneg _
  rw [Finset.sum_map] at hsub
  refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) hsub
  simp [φ, Fin.castLEEmb, j.2]

/-- **The index is subadditive**: the squares that pay `k₁` and those that pay `k₂` together pay
`k₁ + k₂`. -/
theorem negIndex_add_le {k₁ k₂ : G → ℂ} (h₁ : IsHermKernel k₁) (h₂ : IsHermKernel k₂) :
    negIndex (fun u => k₁ u + k₂ u) ≤ negIndex k₁ + negIndex k₂ := by
  rcases eq_or_ne (negIndex k₁) ⊤ with h | h
  · simp [h]
  rcases eq_or_ne (negIndex k₂) ⊤ with h' | h'
  · simp [h']
  obtain ⟨m₁, hm₁⟩ := ENat.ne_top_iff_exists.mp h
  obtain ⟨m₂, hm₂⟩ := ENat.ne_top_iff_exists.mp h'
  obtain ⟨φ, hφ⟩ := (negIndex_le_iff_exists_rank h₁ m₁).mp hm₁.ge
  obtain ⟨ψ, hψ⟩ := (negIndex_le_iff_exists_rank h₂ m₂).mp hm₂.ge
  rw [← hm₁, ← hm₂, ← Nat.cast_add]
  refine negIndex_le_of_rank (Fin.append φ ψ) fun n x c => ?_
  rw [Fin.sum_univ_add, hermQuad_gram_add]
  simp only [Fin.append_left, Fin.append_right]
  linarith [hφ n x c, hψ n x c]

end GaloisForLFunctions.HeckeKreinToeplitz
