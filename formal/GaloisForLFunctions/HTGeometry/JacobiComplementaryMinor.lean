import GaloisForLFunctions.HTGeometry.BlockShuffleSign
import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderK
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Jacobi's complementary minor theorem and reciprocal Toeplitz minors

**Theorem** (`det_submatrix_mul_sign_mul_det`).  Let `B A = 1` in `Fin N`.  For `S, T` of size
`m`, take the rows `S` and columns `T` of `B`, and the rows `Tᶜ` and columns `Sᶜ` of `A`.  Then
`det B[S,T] · sign(σ) · det A = det A[Tᶜ, Sᶜ]`, where `σ` matches the increasing enumerations of
`S, Sᶜ` with those of `T, Tᶜ`.  So `sign σ = (−1)^{ΣS+ΣT}` (`sign_blockEnum_symm_trans`).

Proof.  Reindex `A` by `(T, Tᶜ) × (S, Sᶜ)` and `B` by `(S, Sᶜ) × (T, Tᶜ)`.  Then
`A' · [[B'₁₁, 0], [B'₂₁, 1]] = [[1, A'₁₂], [0, A'₂₂]]`, and both sides are block triangular.

**Toeplitz form** (`toeplitzMinor_reciprocal_mul_pow`).  Let `a₀ ≠ 0` and
`Σ_{k ≤ n} (−1)^k a_k β_{n−k} = [n = 0]`, so `Σ β_n xⁿ = 1/Σ a_n (−x)ⁿ`.  Every Toeplitz minor of
`β` with rows `S` and columns `T` in `{0, …, N−1}` satisfies
`β[S,T] · a₀^N = a[Tᶜ, Sᶜ]`, with no sign.  The alternating signs `(−1)^{q−p}` give
`(−1)^{ΣSᶜ + ΣTᶜ}`, which cancels `sign σ`.

**Transfer** (`pfSeq_reciprocal_minor_nonneg`).  If `a` is `PF_k`, every minor of `β` whose
complement in a window `{0, …, N−1}` has size `≤ k` is nonnegative.  So `PF_∞` of `a` gives
nonnegative minors of `β` of all orders (`toeplitzMinor_reciprocal_nonneg_of_forall_pfSeq`).
-/

open Finset Equiv Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- **Jacobi's complementary minor theorem.** -/
theorem det_submatrix_mul_sign_mul_det {R : Type*} [CommRing R]
    (A B : Matrix (Fin N) (Fin N) R) (hBA : B * A = 1) (S T : Finset (Fin N)) {m : ℕ}
    (hS : S.card = m) (hT : T.card = m) :
    (B.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT)).det *
        (((Perm.sign ((blockEnum S hS).symm.trans (blockEnum T hT)) : ℤ) : R) * A.det) =
      (A.submatrix (Tᶜ.orderEmbOfFin (card_compl_fin hT))
        (Sᶜ.orderEmbOfFin (card_compl_fin hS))).det := by
  set eS := blockEnum S hS
  set eT := blockEnum T hT
  set σ : Perm (Fin N) := eS.symm.trans eT with hσ
  set A' := A.submatrix eT eS with hA'
  set B' := B.submatrix eS eT with hB'
  have hB'A' : B' * A' = 1 := by
    rw [hA', hB', Matrix.submatrix_mul_equiv, hBA, Matrix.submatrix_one_equiv]
  have hA'B' : A' * B' = 1 := mul_eq_one_comm.mp hB'A'
  -- the blocks of `A' B' = 1`
  have hblk := hA'B'
  rw [← Matrix.fromBlocks_toBlocks A', ← Matrix.fromBlocks_toBlocks B', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one] at hblk
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.mp hblk
  have hprod : A' * Matrix.fromBlocks B'.toBlocks₁₁ 0 B'.toBlocks₂₁ 1 =
      Matrix.fromBlocks 1 A'.toBlocks₁₂ 0 A'.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A']
    rw [Matrix.fromBlocks_multiply, h11, h21]
    simp
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁] at hdet
  simp only [Matrix.det_one, mul_one, one_mul] at hdet
  have hA'det : A'.det = ((Perm.sign σ : ℤ) : R) * A.det := by
    have : A' = (A.submatrix (⇑σ) id).submatrix eS eS := by
      ext i j
      simp [hA', hσ]
    rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_permute]
  have hB11 : B'.toBlocks₁₁ = B.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT) := by
    ext i j
    rfl
  have hA22 : A'.toBlocks₂₂ = A.submatrix (Tᶜ.orderEmbOfFin (card_compl_fin hT))
      (Sᶜ.orderEmbOfFin (card_compl_fin hS)) := by
    ext i j
    rfl
  rw [← hB11, ← hA22, ← hdet, hA'det]
  ring

/-- The upper triangular Toeplitz matrix `(c_{q−p})_{p,q < N}`. -/
def upperToeplitz (c : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun p q => zext c (((q : ℕ) : ℤ) - (p : ℕ))

theorem det_upperToeplitz (c : ℕ → ℝ) (N : ℕ) : (upperToeplitz c N).det = c 0 ^ N := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upperToeplitz, zext]
  · intro i j hij
    simp only [upperToeplitz, Matrix.of_apply]
    exact zext_of_neg c (by simp only [id] at hij; have := Fin.lt_def.mp hij; omega)

theorem det_upperToeplitz_submatrix (c : ℕ → ℝ) {s : ℕ} (f g : Fin s → Fin N) :
    ((upperToeplitz c N).submatrix f g).det =
      toeplitzMinor c s (fun r => (f r : ℕ)) (fun r => (g r : ℕ)) := rfl

/-- `ã_k = (−1)^k a_k`. -/
def altSeq (a : ℕ → ℝ) (k : ℕ) : ℝ := (-1) ^ k * a k

theorem zext_altSeq (a : ℕ → ℝ) (p q : ℕ) :
    zext (altSeq a) ((q : ℤ) - p) = (-1) ^ q * (-1) ^ p * zext a ((q : ℤ) - p) := by
  by_cases h : p ≤ q
  · rw [show ((q : ℤ) - p) = ((q - p : ℕ) : ℤ) by push_cast [h]; ring, zext_natCast,
      zext_natCast, altSeq]
    have : (-1 : ℝ) ^ q * (-1) ^ p = (-1) ^ (q - p) := by
      obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
      rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((-1 : ℝ) ^ p), mul_assoc, ← pow_add,
        ← two_mul, pow_mul]
      simp
    rw [this]
  · rw [zext_of_neg _ (by omega), zext_of_neg _ (by omega), mul_zero]

theorem det_upperToeplitz_altSeq_submatrix (a : ℕ → ℝ) {s : ℕ} (f g : Fin s → Fin N) :
    ((upperToeplitz (altSeq a) N).submatrix f g).det =
      (-1) ^ (∑ r, (f r : ℕ) + ∑ r, (g r : ℕ)) *
        toeplitzMinor a s (fun r => (f r : ℕ)) (fun r => (g r : ℕ)) := by
  have hM : (upperToeplitz (altSeq a) N).submatrix f g =
      Matrix.of fun r c => (-1 : ℝ) ^ (f r : ℕ) * ((-1 : ℝ) ^ (g c : ℕ) *
        zext a (((g c : ℕ) : ℤ) - (f r : ℕ))) := by
    ext r c
    simp only [Matrix.submatrix_apply, upperToeplitz, Matrix.of_apply, zext_altSeq]
    ring
  rw [hM]
  have h1 := Matrix.det_mul_column (fun r => (-1 : ℝ) ^ (f r : ℕ))
    (Matrix.of fun r c => (-1 : ℝ) ^ (g c : ℕ) * zext a (((g c : ℕ) : ℤ) - (f r : ℕ)))
  have h2 := Matrix.det_mul_row (fun c => (-1 : ℝ) ^ (g c : ℕ))
    (Matrix.of fun r c => zext a (((g c : ℕ) : ℤ) - (f r : ℕ)))
  simp only [Matrix.of_apply] at h1 h2
  rw [h1, h2, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
  unfold toeplitzMinor
  ring

theorem upperToeplitz_mul_eq_one {a β : ℕ → ℝ}
    (hrec : ∀ n, ∑ k ∈ Finset.range (n + 1), (-1) ^ k * a k * β (n - k) = if n = 0 then 1 else 0) :
    upperToeplitz (altSeq a) N * upperToeplitz β N = 1 := by
  have hconv : cauchyConv (altSeq a) β = fun n => if n = 0 then 1 else 0 := by
    funext n
    rw [← hrec n]
    rfl
  ext p q
  simp only [Matrix.mul_apply, upperToeplitz, Matrix.of_apply]
  have h := zext_cauchyConv_eq_sum (altSeq a) β p q q.isLt
  rw [Fin.sum_univ_eq_sum_range (fun l => zext (altSeq a) ((l : ℤ) - (p : ℕ)) *
    zext β (((q : ℕ) : ℤ) - l)) N, ← h, hconv]
  by_cases hpq : (p : ℕ) ≤ q
  · rw [show (((q : ℕ) : ℤ) - (p : ℕ)) = (((q : ℕ) - (p : ℕ) : ℕ) : ℤ) by push_cast [hpq]; ring,
      zext_natCast, Matrix.one_apply]
    by_cases h' : p = q
    · subst h'
      simp
    · have : (q : ℕ) - p ≠ 0 := by
        intro h0
        apply h'
        exact Fin.ext (by omega)
      simp [this, h']
  · rw [zext_of_neg _ (by omega), Matrix.one_apply, if_neg]
    intro h'
    exact hpq (h' ▸ le_rfl)

/-- `ΣS + ΣSᶜ = Σ_{p<N} p`. -/
theorem idxSum_add_idxSum_compl (S : Finset (Fin N)) :
    idxSum S + idxSum Sᶜ = ∑ p : Fin N, (p : ℕ) := by
  unfold idxSum
  rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]

theorem sum_orderEmbOfFin (S : Finset (Fin N)) {k : ℕ} (h : S.card = k) :
    ∑ r : Fin k, ((S.orderEmbOfFin h r : Fin N) : ℕ) = idxSum S := by
  unfold idxSum
  rw [← Finset.sum_image (f := fun p : Fin N => (p : ℕ))
    (fun x _ y _ hxy => (S.orderEmbOfFin h).injective hxy)]
  congr 1
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl⟩
    exact S.orderEmbOfFin_mem h r
  · intro hp
    have : p ∈ Set.range (S.orderEmbOfFin h) := by
      rw [Finset.range_orderEmbOfFin]
      exact hp
    exact this

/-- **Reciprocal Toeplitz minors are complementary minors.**  If
`Σ_{k ≤ n} (−1)^k a_k β_{n−k} = [n = 0]`, then for `S, T ⊆ {0, …, N−1}` of size `m`,
`β[S,T] · a₀^N = a[Tᶜ, Sᶜ]`. -/
theorem toeplitzMinor_reciprocal_mul_pow {a β : ℕ → ℝ}
    (hrec : ∀ n, ∑ k ∈ Finset.range (n + 1), (-1) ^ k * a k * β (n - k) = if n = 0 then 1 else 0)
    (S T : Finset (Fin N)) {m : ℕ} (hS : S.card = m) (hT : T.card = m) :
    toeplitzMinor β m (fun r => (S.orderEmbOfFin hS r : ℕ)) (fun r => (T.orderEmbOfFin hT r : ℕ)) *
        a 0 ^ N =
      toeplitzMinor a (N - m) (fun r => (Tᶜ.orderEmbOfFin (card_compl_fin hT) r : ℕ))
        (fun r => (Sᶜ.orderEmbOfFin (card_compl_fin hS) r : ℕ)) := by
  have hAB := upperToeplitz_mul_eq_one (N := N) hrec
  have hBA : upperToeplitz β N * upperToeplitz (altSeq a) N = 1 := mul_eq_one_comm.mp hAB
  have hJ := det_submatrix_mul_sign_mul_det (upperToeplitz (altSeq a) N) (upperToeplitz β N) hBA
    S T hS hT
  rw [det_upperToeplitz_submatrix, det_upperToeplitz_altSeq_submatrix, det_upperToeplitz,
    sign_blockEnum_symm_trans, sum_orderEmbOfFin, sum_orderEmbOfFin] at hJ
  have ha0 : altSeq a 0 = a 0 := by simp [altSeq]
  rw [ha0] at hJ
  push_cast at hJ
  have h1 := idxSum_add_idxSum_compl S
  have h2 := idxSum_add_idxSum_compl T
  have hs : (-1 : ℝ) ^ (idxSum S + idxSum T) = (-1) ^ (idxSum Tᶜ + idxSum Sᶜ) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := idxSum Tᶜ + idxSum Sᶜ)]
    congr 1
    omega
  have hss : (-1 : ℝ) ^ (idxSum Tᶜ + idxSum Sᶜ) * (-1) ^ (idxSum Tᶜ + idxSum Sᶜ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [hs] at hJ
  set X := toeplitzMinor β m (fun r => (S.orderEmbOfFin hS r : ℕ))
    (fun r => (T.orderEmbOfFin hT r : ℕ)) * a 0 ^ N
  set Y := toeplitzMinor a (N - m) (fun r => (Tᶜ.orderEmbOfFin (card_compl_fin hT) r : ℕ))
    (fun r => (Sᶜ.orderEmbOfFin (card_compl_fin hS) r : ℕ))
  linear_combination ((-1 : ℝ) ^ (idxSum Tᶜ + idxSum Sᶜ)) * hJ - (X - Y) * hss

/-- The increasing enumeration of the image of a strictly increasing index map. -/
theorem orderEmbOfFin_image_eq {m : ℕ} {i : Fin m → ℕ} (hi : StrictMono i) (hN : ∀ r, i r < N) :
    ∃ (S : Finset (Fin N)) (hS : S.card = m), ∀ r, ((S.orderEmbOfFin hS r : Fin N) : ℕ) = i r := by
  set f : Fin m → Fin N := fun r => ⟨i r, hN r⟩ with hf
  have hfm : StrictMono f := fun a b hab => by
    rw [Fin.lt_def]
    exact hi hab
  refine ⟨Finset.univ.image f, ?_, fun r => ?_⟩
  · rw [Finset.card_image_of_injective _ hfm.injective, Finset.card_univ, Fintype.card_fin]
  · have h := Finset.orderEmbOfFin_unique (s := Finset.univ.image f)
      (by rw [Finset.card_image_of_injective _ hfm.injective, Finset.card_univ, Fintype.card_fin])
      (f := f) (fun r => Finset.mem_image_of_mem f (Finset.mem_univ r)) hfm
    rw [← congrFun h r]

/-- **Finite-order transfer.**  If `a` is `PF_k` with `a₀ > 0`, every Toeplitz minor of the
reciprocal sequence `β` with indices in `{0, …, N−1}` and `N − m ≤ k` is nonnegative. -/
theorem toeplitzMinor_reciprocal_nonneg_of_pfSeq {a β : ℕ → ℝ} {k : ℕ} (hk : PFSeq k a)
    (ha0 : 0 < a 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (n + 1), (-1) ^ k * a k * β (n - k) = if n = 0 then 1 else 0)
    {m : ℕ} {i j : Fin m → ℕ} (hi : StrictMono i) (hj : StrictMono j) (hiN : ∀ r, i r < N)
    (hjN : ∀ c, j c < N) (hNm : N - m ≤ k) : 0 ≤ toeplitzMinor β m i j := by
  obtain ⟨S, hS, hSi⟩ := orderEmbOfFin_image_eq hi hiN
  obtain ⟨T, hT, hTj⟩ := orderEmbOfFin_image_eq hj hjN
  have hmin : toeplitzMinor β m i j = toeplitzMinor β m (fun r => (S.orderEmbOfFin hS r : ℕ))
      (fun r => (T.orderEmbOfFin hT r : ℕ)) := by
    congr 1
    · funext r
      exact (hSi r).symm
    · funext r
      exact (hTj r).symm
  have hJ := toeplitzMinor_reciprocal_mul_pow (N := N) hrec S T hS hT
  have hpos : 0 ≤ toeplitzMinor a (N - m) (fun r => (Tᶜ.orderEmbOfFin (card_compl_fin hT) r : ℕ))
      (fun r => (Sᶜ.orderEmbOfFin (card_compl_fin hS) r : ℕ)) :=
    hk _ hNm _ _ (fun a b hab => by
        have := (Tᶜ.orderEmbOfFin (card_compl_fin hT)).strictMono hab
        exact this)
      (fun a b hab => by
        have := (Sᶜ.orderEmbOfFin (card_compl_fin hS)).strictMono hab
        exact this)
  rw [hmin]
  rw [← hJ] at hpos
  exact nonneg_of_mul_nonneg_left hpos (pow_pos ha0 N)

/-- **`PF_∞` passes to the reciprocal sequence.** -/
theorem pfSeq_reciprocal_of_forall_pfSeq {a β : ℕ → ℝ} (h : ∀ k, PFSeq k a) (ha0 : 0 < a 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (n + 1), (-1) ^ k * a k * β (n - k) = if n = 0 then 1 else 0)
    (k : ℕ) : PFSeq k β := by
  intro m _ i j hi hj
  set M := (∑ r, i r) + (∑ c, j c) + 1 with hM
  have hiN : ∀ r, i r < M := fun r => by
    have := Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  have hjN : ∀ c, j c < M := fun c => by
    have := Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  exact toeplitzMinor_reciprocal_nonneg_of_pfSeq (h M) ha0 hrec hi hj hiN hjN (Nat.sub_le _ _)

end

end GaloisForLFunctions.HTGeometry
