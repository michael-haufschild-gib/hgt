/-
# Hilbert–Schmidt kernels

Mathlib has no Hilbert–Schmidt / Schatten / trace-class operator theory.  This file builds the
foundational layer: **Hilbert–Schmidt kernels** on a countable index type `ι` — the square-summable
matrices of coefficients that represent Hilbert–Schmidt operators on `ℓ²(ι)`, with their inner product,
norm, and the fundamental positivity and sesquilinearity.

A kernel `K : ι × ι → ℂ` is **Hilbert–Schmidt** (`IsHS K`) when its entries are square-summable,
`∑ ‖K p‖² < ∞`.  The **Hilbert–Schmidt inner product** is `⟨K, L⟩_HS = ∑ conj(K p)·L p`, and the
**Hilbert–Schmidt norm** is `‖K‖²_HS = ∑ ‖K p‖²` — the `ℓ²(ι × ι)` structure on the entries.  This is
the natural home of the seam crossing tower, whose energy law `⟨B_{p,r}, B_{p,s}⟩_HS = r·δ_{r,s}` is a
statement about these inner products (finitely supported kernels, so all sums are finite).

Proved here:
* `isHS_of_support_subset` — a kernel supported on a finite set is Hilbert–Schmidt.
* `hsNormSq_nonneg` — the Hilbert–Schmidt norm is nonnegative.
* `hsInner_summable` — the Hilbert–Schmidt inner product converges (`ℓ²·ℓ² ⊆ ℓ¹`): it is well-defined
  on every pair of Hilbert–Schmidt kernels.
* `hsInner_self` — `⟨K, K⟩_HS = ‖K‖²_HS` (real, nonnegative): the inner product is a genuine squared
  norm on the diagonal.
* `hsInner_self_re_nonneg` — `Re⟨K, K⟩_HS ≥ 0` (positivity of the Hilbert–Schmidt form).
* `hsInner_smul_left`, `hsInner_smul_right`, `hsInner_add_left`, `hsInner_conj_symm` — the sesquilinear
  structure.
* `hsNormSq_eq_zero_iff` — positive-definiteness: `‖K‖²_HS = 0 ↔ K = 0`, so the form is a genuine inner
  product.
* `hsAdjoint`, `hsAdjoint_hsAdjoint`, `hsNormSq_hsAdjoint`, `isHS_hsAdjoint`, `hsInner_hsAdjoint` — the
  adjoint (conjugate-transpose): an involutive Hilbert–Schmidt isometry reversing the inner product.
* `hsInner_eq_tsum_tsum` — `⟨K, L⟩_HS = tr(Kᴴ L)` as an iterated sum (Fubini).
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*}

/-- A **Hilbert–Schmidt kernel**: a matrix of coefficients `K : ι × ι → ℂ` with square-summable
entries, `∑ ‖K p‖² < ∞`.  These represent the Hilbert–Schmidt operators on `ℓ²(ι)`. -/
def IsHS (K : ι × ι → ℂ) : Prop := Summable (fun p => ‖K p‖ ^ 2)

/-- The **Hilbert–Schmidt inner product** `⟨K, L⟩_HS = ∑ conj(K p)·L p` — the `ℓ²(ι × ι)` inner product
of the entry matrices. -/
noncomputable def hsInner (K L : ι × ι → ℂ) : ℂ := ∑' p, (starRingEnd ℂ) (K p) * L p

/-- The **Hilbert–Schmidt norm squared** `‖K‖²_HS = ∑ ‖K p‖²`. -/
noncomputable def hsNormSq (K : ι × ι → ℂ) : ℝ := ∑' p, ‖K p‖ ^ 2

/-- A kernel supported on a finite set is Hilbert–Schmidt. -/
theorem isHS_of_support_subset {K : ι × ι → ℂ} (s : Finset (ι × ι))
    (hs : ∀ p ∉ s, K p = 0) : IsHS K := by
  apply summable_of_ne_finset_zero (s := s)
  intro p hp; rw [hs p hp]; simp

/-- The Hilbert–Schmidt norm is nonnegative. -/
theorem hsNormSq_nonneg (K : ι × ι → ℂ) : 0 ≤ hsNormSq K :=
  tsum_nonneg fun p => by positivity

/-- **The Hilbert–Schmidt inner product converges.**  The product of two Hilbert–Schmidt kernels is
absolutely summable: `ℓ²·ℓ² ⊆ ℓ¹`, because `‖conj(K p)·L p‖ = ‖K p‖·‖L p‖ ≤ (‖K p‖² + ‖L p‖²)/2` and the
bound is summable.  So `hsInner K L` is a genuine convergent sum for any pair of Hilbert–Schmidt
kernels — the Hilbert–Schmidt inner product is well-defined. -/
theorem hsInner_summable {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    Summable fun p => (starRingEnd ℂ) (K p) * L p := by
  apply Summable.of_norm_bounded (g := fun p => (‖K p‖ ^ 2 + ‖L p‖ ^ 2) / 2)
  · exact (hK.add hL).div_const 2
  · intro p
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖K p‖ - ‖L p‖), norm_nonneg (K p), norm_nonneg (L p)]

/-- **The Hilbert–Schmidt inner product is a squared norm on the diagonal.**  `⟨K, K⟩_HS = ‖K‖²_HS`,
because `conj(z)·z = ‖z‖²`.  In particular the diagonal value is a nonnegative real. -/
theorem hsInner_self (K : ι × ι → ℂ) : hsInner K K = (hsNormSq K : ℂ) := by
  rw [hsInner, hsNormSq, Complex.ofReal_tsum]
  refine tsum_congr fun p => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Positivity of the Hilbert–Schmidt form.**  `Re⟨K, K⟩_HS = ‖K‖²_HS ≥ 0`. -/
theorem hsInner_self_re_nonneg (K : ι × ι → ℂ) : 0 ≤ (hsInner K K).re := by
  rw [hsInner_self, Complex.ofReal_re]; exact hsNormSq_nonneg K

/-- Conjugate symmetry: `⟨K, L⟩_HS = conj⟨L, K⟩_HS`. -/
theorem hsInner_conj_symm (K L : ι × ι → ℂ) :
    hsInner K L = (starRingEnd ℂ) (hsInner L K) := by
  rw [hsInner, hsInner, Complex.conj_tsum]
  refine tsum_congr fun p => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- Left additivity: `⟨K₁ + K₂, L⟩_HS = ⟨K₁, L⟩_HS + ⟨K₂, L⟩_HS` for Hilbert–Schmidt kernels. -/
theorem hsInner_add_left {K₁ K₂ L : ι × ι → ℂ} (h₁ : IsHS K₁) (h₂ : IsHS K₂) (hL : IsHS L) :
    hsInner (K₁ + K₂) L = hsInner K₁ L + hsInner K₂ L := by
  rw [hsInner, hsInner, hsInner, ← (hsInner_summable h₁ hL).tsum_add (hsInner_summable h₂ hL)]
  refine tsum_congr fun p => ?_
  simp only [Pi.add_apply, map_add]; ring

/-- Left scalar homogeneity (conjugate-linear): `⟨c • K, L⟩_HS = conj(c)·⟨K, L⟩_HS`. -/
theorem hsInner_smul_left (c : ℂ) (K L : ι × ι → ℂ) :
    hsInner (c • K) L = (starRingEnd ℂ) c * hsInner K L := by
  rw [hsInner, hsInner, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

/-- Right scalar homogeneity (linear): `⟨K, c • L⟩_HS = c·⟨K, L⟩_HS`. -/
theorem hsInner_smul_right (c : ℂ) (K L : ι × ι → ℂ) :
    hsInner K (c • L) = c * hsInner K L := by
  rw [hsInner, hsInner, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **Positive-definiteness of the Hilbert–Schmidt norm.**  `‖K‖²_HS = 0 ↔ K = 0`: a sum of the
nonnegative terms `‖K p‖²` vanishes only when every term does.  Together with `hsInner_self` this makes
the Hilbert–Schmidt inner product a genuine (positive-definite) inner product, not merely a
seminorm. -/
theorem hsNormSq_eq_zero_iff {K : ι × ι → ℂ} (hK : IsHS K) : hsNormSq K = 0 ↔ K = 0 := by
  rw [hsNormSq]
  constructor
  · intro h
    funext p
    have hle : ‖K p‖ ^ 2 ≤ ∑' q, ‖K q‖ ^ 2 := hK.le_tsum p (fun q _ => by positivity)
    rw [h] at hle
    have hz : ‖K p‖ ^ 2 = 0 := le_antisymm hle (by positivity)
    simpa [pow_eq_zero_iff] using hz
  · intro h; rw [h]; simp

/-- The **Hilbert–Schmidt adjoint kernel**: the conjugate-transpose `Kᴴ(i, j) = conj(K(j, i))` — the
kernel of the adjoint Hilbert–Schmidt operator. -/
def hsAdjoint (K : ι × ι → ℂ) : ι × ι → ℂ := fun p => (starRingEnd ℂ) (K (p.2, p.1))

/-- The adjoint is an involution: `(Kᴴ)ᴴ = K`. -/
theorem hsAdjoint_hsAdjoint (K : ι × ι → ℂ) : hsAdjoint (hsAdjoint K) = K := by
  funext p; simp [hsAdjoint]

/-- **The adjoint is a Hilbert–Schmidt isometry.**  `‖Kᴴ‖²_HS = ‖K‖²_HS`: transposing and conjugating
the entries permutes the sum and preserves each `‖·‖²`. -/
theorem hsNormSq_hsAdjoint (K : ι × ι → ℂ) : hsNormSq (hsAdjoint K) = hsNormSq K := by
  rw [hsNormSq, hsNormSq, ← (Equiv.prodComm ι ι).tsum_eq (fun p => ‖K p‖ ^ 2)]
  refine tsum_congr fun p => ?_
  simp only [hsAdjoint, RCLike.norm_conj, Equiv.prodComm_apply, Prod.swap]

/-- The adjoint of a Hilbert–Schmidt kernel is Hilbert–Schmidt. -/
theorem isHS_hsAdjoint {K : ι × ι → ℂ} (hK : IsHS K) : IsHS (hsAdjoint K) := by
  have hre : (fun p => ‖hsAdjoint K p‖ ^ 2) = (fun p => ‖K p‖ ^ 2) ∘ (Equiv.prodComm ι ι) := by
    funext p
    simp only [hsAdjoint, RCLike.norm_conj, Function.comp, Equiv.prodComm_apply, Prod.swap]
  rw [IsHS, hre]
  exact (Equiv.prodComm ι ι).summable_iff.mpr hK

/-- **The adjoint reverses the Hilbert–Schmidt inner product.**  `⟨Kᴴ, Lᴴ⟩_HS = ⟨L, K⟩_HS` — the
defining compatibility of the adjoint with the inner product, via the transpose reindexing. -/
theorem hsInner_hsAdjoint (K L : ι × ι → ℂ) :
    hsInner (hsAdjoint K) (hsAdjoint L) = hsInner L K := by
  rw [hsInner, hsInner, ← (Equiv.prodComm ι ι).tsum_eq (fun p => (starRingEnd ℂ) (L p) * K p)]
  refine tsum_congr fun p => ?_
  simp only [hsAdjoint, Equiv.prodComm_apply, Prod.swap, Complex.conj_conj]
  ring

/-- **The Hilbert–Schmidt inner product is the trace of the adjoint composition.**
`⟨K, L⟩_HS = ∑_i ∑_j conj(K(i, j))·L(i, j) = tr(Kᴴ L)` as an iterated (row-then-column) sum — the
defining property of the Hilbert–Schmidt inner product on operators.  Fubini for the absolutely
summable entrywise product (`hsInner_summable`) turns the single sum over `ι × ι` into the iterated
sum. -/
theorem hsInner_eq_tsum_tsum {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    hsInner K L = ∑' i : ι, ∑' j : ι, (starRingEnd ℂ) (K (i, j)) * L (i, j) := by
  rw [hsInner]
  exact (hsInner_summable hK hL).tsum_prod

end HilbertSchmidt
