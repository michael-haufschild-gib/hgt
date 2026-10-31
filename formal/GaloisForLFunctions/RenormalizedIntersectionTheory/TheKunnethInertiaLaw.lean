import GaloisForLFunctions.HTGeometry.TensorPolarizationAmplification
import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# The Künneth inertia law

On the product `G × H` of two groups the **tensor (Künneth) kernel** of `k` and `l` is
`(k ⊠ l)(g, h) = k(g) l(h)`. Its Gram matrix on a product family is the Kronecker product of the two
Gram matrices, and on an arbitrary family it is a principal submatrix of one (the Hadamard product on
the diagonal). With the positive index `κ₊(k) = κ(−k)`:

* **Lower bound** (`hermIndex_kronecker_le_negIndex_tensor`): for all finite families `x`, `y`,
  `κ₊(x)κ(y) + κ(x)κ₊(y) ≤ κ(k ⊠ l)`.
* **Upper bound** (`negIndex_tensorKernel_le`): `κ(k ⊠ l) ≤ κ₊(k)κ(l) + κ(k)κ₊(l)`.
* **Positive ⊠ positive** (`negIndex_tensorKernel_eq_zero`): tensor kernels of positive-definite
  kernels are positive definite.
* **All or nothing** (`negIndex_tensorKernel_self_eq_zero_or_top`): if `k` has infinitely many
  positive squares, its Künneth square has index `0` or `∞`.
* **Hadamard square** (`negIndex_mul_le_negIndex_tensorKernel`): the pointwise product `k l` on `G`
  is the restriction of `k ⊠ l` to the diagonal, so its index is at most that of `k ⊠ l`.
* **The Künneth square of Weil's kernel** (`negIndex_kunnethZeta_eq_zero_iff`): the tensor square
  of `K_ζ` on `ℚ_{>0} × ℚ_{>0}` is positive definite iff RH holds or `K_ζ` has no positive square.

The weight route over `𝔽_q` amplifies a fixed loss through tensor powers; the sign version of
that amplification is all-or-nothing: tensor squares carry no finite nonzero index once the
positive part is infinite.
-/

open Complex Finset Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

variable {G H : Type*} [Group G] [Group H]

/-- The **positive index** `κ₊(k) = κ(−k)`: the supremum of the positive squares of all finite
Gram matrices. -/
def posIndex (k : G → ℂ) : ℕ∞ := negIndex fun g => -k g

theorem gram_neg (k : G → ℂ) {ι : Type*} (x : ι → G) : gram (fun g => -k g) x = -gram k x := by
  ext a b; simp [gram]

theorem hermPosIndex_gram_le_posIndex (k : G → ℂ) {ι : Type*} [Fintype ι] (x : ι → G) :
    (hermPosIndex (gram k x) : ℕ∞) ≤ posIndex k := by
  have h := hermNegIndex_gram_le_negIndex (fun g => -k g) x
  rwa [gram_neg, hermNegIndex, neg_neg] at h

theorem hermPosIndex_submatrix_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) (f : α → β) : hermPosIndex (M.submatrix f f) ≤ hermPosIndex M := by
  have h := hermNegIndex_submatrix_le (-M) f
  rwa [hermNegIndex, hermNegIndex, neg_neg, submatrix_neg, neg_neg] at h

/-- The **tensor (Künneth) kernel** `(g, h) ↦ k(g) l(h)` on `G × H`. -/
def tensorKernel (k : G → ℂ) (l : H → ℂ) (z : G × H) : ℂ := k z.1 * l z.2

theorem isHermKernel_tensorKernel {k : G → ℂ} {l : H → ℂ} (hk : IsHermKernel k)
    (hl : IsHermKernel l) : IsHermKernel (tensorKernel k l) := fun z => by
  simp only [tensorKernel, Prod.fst_inv, Prod.snd_inv, hk z.1, hl z.2, map_mul]

/-- On a product family the Gram matrix is the Kronecker product of the Gram matrices. -/
theorem gram_tensorKernel_prod (k : G → ℂ) (l : H → ℂ) {ι κ : Type*} (x : ι → G) (y : κ → H) :
    gram (tensorKernel k l) (fun ab : ι × κ => (x ab.1, y ab.2)) = kronecker (gram k x) (gram l y) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [gram, tensorKernel, kronecker, kroneckerMap]

/-- On any family the Gram matrix is the diagonal principal submatrix of a Kronecker product. -/
theorem gram_tensorKernel (k : G → ℂ) (l : H → ℂ) {ι : Type*} (z : ι → G × H) :
    gram (tensorKernel k l) z =
      (kronecker (gram k (Prod.fst ∘ z)) (gram l (Prod.snd ∘ z))).submatrix (fun a => (a, a))
        (fun a => (a, a)) := by
  ext a b
  simp [gram, tensorKernel, kronecker, kroneckerMap]

/-- **Lower bound.** Every pair of finite families gives
`κ₊(x)κ(y) + κ(x)κ₊(y)` negative squares of the tensor kernel. -/
theorem hermIndex_kronecker_le_negIndex_tensor {k : G → ℂ} {l : H → ℂ} (hk : IsHermKernel k)
    (hl : IsHermKernel l) {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → G) (y : κ → H) :
    ((hermPosIndex (gram k x) * hermNegIndex (gram l y) +
      hermNegIndex (gram k x) * hermPosIndex (gram l y) : ℕ) : ℕ∞) ≤ negIndex (tensorKernel k l) := by
  classical
  rw [← negIndex_kronecker (gram_isHermitian hk x) (gram_isHermitian hl y),
    ← gram_tensorKernel_prod]
  exact hermNegIndex_gram_le_negIndex _ _

/-- **Upper bound.** `κ(k ⊠ l) ≤ κ₊(k)κ(l) + κ(k)κ₊(l)`. -/
theorem negIndex_tensorKernel_le {k : G → ℂ} {l : H → ℂ} (hk : IsHermKernel k)
    (hl : IsHermKernel l) :
    negIndex (tensorKernel k l) ≤ posIndex k * negIndex l + negIndex k * posIndex l := by
  classical
  rw [negIndex_le_iff]
  intro n z
  rw [gram_tensorKernel]
  calc (hermNegIndex ((kronecker (gram k (Prod.fst ∘ z)) (gram l (Prod.snd ∘ z))).submatrix
        (fun a => (a, a)) (fun a => (a, a))) : ℕ∞)
      ≤ hermNegIndex (kronecker (gram k (Prod.fst ∘ z)) (gram l (Prod.snd ∘ z))) :=
        Nat.cast_le.mpr (hermNegIndex_submatrix_le _ _)
    _ = ((hermPosIndex (gram k (Prod.fst ∘ z)) * hermNegIndex (gram l (Prod.snd ∘ z)) +
          hermNegIndex (gram k (Prod.fst ∘ z)) * hermPosIndex (gram l (Prod.snd ∘ z)) : ℕ) : ℕ∞) := by
        rw [negIndex_kronecker (gram_isHermitian hk _) (gram_isHermitian hl _)]
    _ ≤ posIndex k * negIndex l + negIndex k * posIndex l := by
        push_cast
        exact add_le_add
          (mul_le_mul' (hermPosIndex_gram_le_posIndex k _) (hermNegIndex_gram_le_negIndex l _))
          (mul_le_mul' (hermNegIndex_gram_le_negIndex k _) (hermPosIndex_gram_le_posIndex l _))

/-- **Positive ⊠ positive is positive.** -/
theorem negIndex_tensorKernel_eq_zero {k : G → ℂ} {l : H → ℂ} (hk : IsPosDefKernel k)
    (hl : IsPosDefKernel l) : negIndex (tensorKernel k l) = 0 := by
  have h := negIndex_tensorKernel_le hk.1 hl.1
  rw [hk.negIndex_eq_zero, hl.negIndex_eq_zero, mul_zero, zero_mul, add_zero] at h
  exact nonpos_iff_eq_zero.mp h

theorem eq_top_of_forall_natCast_le {m : ℕ∞} (h : ∀ n : ℕ, (n : ℕ∞) ≤ m) : m = ⊤ := by
  induction m using ENat.recTopCoe with
  | top => rfl
  | coe k => exact absurd (h (k + 1)) (by exact_mod_cast (Nat.lt_succ_self k).not_ge)

theorem exists_hermNegIndex_pos {k : G → ℂ} (hk : negIndex k ≠ 0) :
    ∃ (n : ℕ) (y : Fin n → G), 0 < hermNegIndex (gram k y) := by
  by_contra h
  push Not at h
  exact hk (nonpos_iff_eq_zero.mp (negIndex_le_iff.mpr fun n y => by
    simp [Nat.le_zero.mp (h n y)]))

theorem exists_hermPosIndex_ge {k : G → ℂ} (hk : posIndex k = ⊤) (M : ℕ) :
    ∃ (n : ℕ) (x : Fin n → G), M ≤ hermPosIndex (gram k x) := by
  by_contra h
  push Not at h
  have hle : posIndex k ≤ M := negIndex_le_iff.mpr fun n x => by
    have := (h n x).le
    rw [gram_neg, hermNegIndex, neg_neg]
    exact_mod_cast this
  rw [hk] at hle
  exact absurd hle (by simp)

/-- **All or nothing.** If `k` has infinitely many positive squares, its Künneth square has no
negative square or infinitely many. -/
theorem negIndex_tensorKernel_self_eq_zero_or_top {k : G → ℂ} (hk : IsHermKernel k)
    (hpos : posIndex k = ⊤) :
    negIndex (tensorKernel k k) = 0 ∨ negIndex (tensorKernel k k) = ⊤ := by
  by_cases h0 : negIndex k = 0
  · left
    have h := negIndex_tensorKernel_le hk hk
    rw [h0, mul_zero, zero_mul, add_zero] at h
    exact nonpos_iff_eq_zero.mp h
  · right
    obtain ⟨n, y, hy⟩ := exists_hermNegIndex_pos h0
    refine eq_top_of_forall_natCast_le fun M => ?_
    obtain ⟨m, x, hx⟩ := exists_hermPosIndex_ge hpos M
    refine le_trans ?_ (hermIndex_kronecker_le_negIndex_tensor hk hk x y)
    exact_mod_cast le_add_right (le_mul_of_le_of_one_le hx hy)

/-- The diagonal `g ↦ (g, g)`. -/
def diagHom (G : Type*) [Group G] : G →* G × G := MonoidHom.prod (MonoidHom.id G) (MonoidHom.id G)

/-- **Hadamard square.** The pointwise product is the restriction of the tensor kernel to the
diagonal. -/
theorem negIndex_mul_le_negIndex_tensorKernel (k l : G → ℂ) :
    negIndex (fun g => k g * l g) ≤ negIndex (tensorKernel k l) :=
  negIndex_comp_le (tensorKernel k l) (diagHom G)

/-! ### The Künneth square of Weil's kernel -/

/-- The Künneth square `K_ζ ⊠ K_ζ` of Weil's kernel on `ℚ_{>0} × ℚ_{>0}`. -/
def kunnethZeta : HeckeLattice × HeckeLattice → ℂ := tensorKernel zetaKernel zetaKernel

/-- **The Künneth square of `K_ζ` is positive iff RH holds or `K_ζ` has no positive square.** -/
theorem negIndex_kunnethZeta_eq_zero_iff :
    negIndex kunnethZeta = 0 ↔ RiemannHypothesis ∨ posIndex zetaKernel = 0 := by
  have hk := isHermKernel_zetaKernel
  rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨n, y, hy⟩ := exists_hermNegIndex_pos hne.1
    obtain ⟨m, x, hx⟩ : ∃ (m : ℕ) (x : Fin m → HeckeLattice), 0 < hermPosIndex (gram zetaKernel x) := by
      by_contra hc
      push Not at hc
      exact hne.2 (nonpos_iff_eq_zero.mp (negIndex_le_iff.mpr fun m x => by
        rw [gram_neg, hermNegIndex, neg_neg]; simp [Nat.le_zero.mp (hc m x)]))
    have hle := hermIndex_kronecker_le_negIndex_tensor hk hk x y
    rw [show negIndex (tensorKernel zetaKernel zetaKernel) = 0 from h, nonpos_iff_eq_zero,
      Nat.cast_eq_zero] at hle
    have := Nat.mul_pos hx hy
    omega
  · rintro (h | h)
    · have hle := negIndex_tensorKernel_le hk hk
      rw [h, mul_zero, zero_mul, add_zero] at hle
      exact nonpos_iff_eq_zero.mp hle
    · have hle := negIndex_tensorKernel_le hk hk
      rw [h, zero_mul, mul_zero, zero_add] at hle
      exact nonpos_iff_eq_zero.mp hle

end GaloisForLFunctions.RenormalizedIntersectionTheory
