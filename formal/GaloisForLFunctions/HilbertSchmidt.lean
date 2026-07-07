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
* `IsHS.memℓp`, `hsInner_eq_lp_inner`, `lp_norm_sq` — identify Hilbert–Schmidt kernels with `ℓ²(ι × ι)`,
  so the inner product and norm are the `ℓ²` ones.
* `hsInner_norm_le` — the **Cauchy–Schwarz inequality** `‖⟨K, L⟩_HS‖ ≤ ‖K‖_HS · ‖L‖_HS`, inherited from
  the `ℓ²` Hilbert space.
* `isHS_row`, `isHS_col`, `hsComp_summable`, `hsComp`, `hsAdjoint_hsComp` — the composition algebra: the
  matrix product `(K∘L)(i,j) = ∑ₖ K(i,k)·L(k,j)` is well-defined and `(K∘L)ᴴ = Lᴴ∘Kᴴ`.
* `hsTrace_hsComp` — the trace identity `tr(K∘L) = ⟨Kᴴ, L⟩_HS`: the composition is trace-class with trace
  the Hilbert–Schmidt pairing.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
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

/-- A Hilbert–Schmidt kernel is a member of `ℓ²(ι × ι)`: square-summability is exactly `Memℓp _ 2`. -/
theorem IsHS.memℓp {K : ι × ι → ℂ} (hK : IsHS K) : Memℓp K 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  refine hK.congr ?_
  intro p
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The Hilbert–Schmidt inner product is the `ℓ²(ι × ι)` inner product of the kernels. -/
theorem hsInner_eq_lp_inner {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    hsInner K L
      = @inner ℂ _ _ (⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2) ⟨L, hL.memℓp⟩ := by
  rw [hsInner, lp.inner_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [RCLike.inner_apply]; simp [mul_comm]

/-- The `ℓ²` norm squared of a Hilbert–Schmidt kernel is its Hilbert–Schmidt norm `‖K‖²_HS`. -/
theorem lp_norm_sq {K : ι × ι → ℂ} (hK : IsHS K) :
    ‖(⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ ^ 2 = hsNormSq K := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  rw [h, hsNormSq]
  exact tsum_congr fun p => Real.rpow_natCast _ 2

/-- **Cauchy–Schwarz for the Hilbert–Schmidt inner product.**  `‖⟨K, L⟩_HS‖ ≤ ‖K‖_HS · ‖L‖_HS`,
inherited from the `ℓ²(ι × ι)` Hilbert space via `norm_inner_le_norm`.  This is the fundamental
inequality that bounds the Hilbert–Schmidt pairing by the Hilbert–Schmidt norms. -/
theorem hsInner_norm_le {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    ‖hsInner K L‖ ≤ Real.sqrt (hsNormSq K) * Real.sqrt (hsNormSq L) := by
  rw [hsInner_eq_lp_inner hK hL,
    show Real.sqrt (hsNormSq K) = ‖(⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ by
      rw [← lp_norm_sq hK, Real.sqrt_sq (norm_nonneg _)],
    show Real.sqrt (hsNormSq L) = ‖(⟨L, hL.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ by
      rw [← lp_norm_sq hL, Real.sqrt_sq (norm_nonneg _)]]
  exact norm_inner_le_norm _ _

/-- A row of a Hilbert–Schmidt kernel is square-summable (`ℓ²`): the `i`-th row `k ↦ K(i, k)` is a
section of the summable entry family. -/
theorem isHS_row {K : ι × ι → ℂ} (hK : IsHS K) (i : ι) : Summable (fun k => ‖K (i, k)‖ ^ 2) := by
  have hinj : Function.Injective (fun k : ι => (i, k)) := fun a b h => (Prod.ext_iff.mp h).2
  exact hK.comp_injective hinj

/-- A column of a Hilbert–Schmidt kernel is square-summable (`ℓ²`). -/
theorem isHS_col {K : ι × ι → ℂ} (hK : IsHS K) (j : ι) : Summable (fun k => ‖K (k, j)‖ ^ 2) := by
  have hinj : Function.Injective (fun k : ι => (k, j)) := fun a b h => (Prod.ext_iff.mp h).1
  exact hK.comp_injective hinj

/-- **The Hilbert–Schmidt composition converges.**  For Hilbert–Schmidt `K, L` and fixed `(i, j)`, the
inner sum `∑ₖ K(i,k)·L(k,j)` is absolutely summable — the `i`-th row of `K` and `j`-th column of `L` are
both `ℓ²`, and `ℓ²·ℓ² ⊆ ℓ¹`.  This is what makes the matrix product of two Hilbert–Schmidt operators
well-defined. -/
theorem hsComp_summable {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) (i j : ι) :
    Summable (fun k => K (i, k) * L (k, j)) := by
  apply Summable.of_norm_bounded (g := fun k => (‖K (i, k)‖ ^ 2 + ‖L (k, j)‖ ^ 2) / 2)
  · exact ((isHS_row hK i).add (isHS_col hL j)).div_const 2
  · intro k
    rw [norm_mul]
    nlinarith [sq_nonneg (‖K (i, k)‖ - ‖L (k, j)‖), norm_nonneg (K (i, k)), norm_nonneg (L (k, j))]

/-- The **Hilbert–Schmidt composition** `(K ∘ L)(i, j) = ∑ₖ K(i,k)·L(k,j)` — the matrix product of the
kernels, well-defined by `hsComp_summable`.  Composition equips the Hilbert–Schmidt operators with
their algebra structure. -/
noncomputable def hsComp (K L : ι × ι → ℂ) : ι × ι → ℂ := fun p => ∑' k, K (p.1, k) * L (k, p.2)

/-- A square-summable complex sequence is a member of `ℓ²`. -/
theorem memℓp_of_sq {a : ι → ℂ} (ha : Summable (fun k => ‖a k‖ ^ 2)) : Memℓp a 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  refine ha.congr ?_
  intro k
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The `ℓ²` product-sum Cauchy–Schwarz bound.**  For square-summable sequences `a, b`,
`‖∑ₖ aₖ·bₖ‖² ≤ (∑ₖ ‖aₖ‖²)·(∑ₖ ‖bₖ‖²)` — the `ℓ²` inner product bound applied to `conj a` and `b`. -/
theorem hsComp_entry_bound {a b : ι → ℂ}
    (ha : Summable (fun k => ‖a k‖ ^ 2)) (hb : Summable (fun k => ‖b k‖ ^ 2)) :
    ‖∑' k, a k * b k‖ ^ 2 ≤ (∑' k, ‖a k‖ ^ 2) * (∑' k, ‖b k‖ ^ 2) := by
  have hca : Summable (fun k => ‖(starRingEnd ℂ) (a k)‖ ^ 2) := by simpa using ha
  set A : lp (fun _ : ι => ℂ) 2 := ⟨fun k => (starRingEnd ℂ) (a k), memℓp_of_sq hca⟩ with hA
  set B : lp (fun _ : ι => ℂ) 2 := ⟨b, memℓp_of_sq hb⟩ with hB
  have hinner : @inner ℂ _ _ A B = ∑' k, a k * b k := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [RCLike.inner_apply]; simp [hA, hB, mul_comm]
  have hnA : ‖A‖ ^ 2 = ∑' k, ‖a k‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) A
    simp only [ENNReal.toReal_ofNat] at h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
    simp only [Real.rpow_natCast] at h
    rw [h]; refine tsum_congr fun k => ?_; simp [hA]
  have hnB : ‖B‖ ^ 2 = ∑' k, ‖b k‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) B
    simp only [ENNReal.toReal_ofNat] at h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
    simp only [Real.rpow_natCast] at h
    rw [h]
  calc ‖∑' k, a k * b k‖ ^ 2 = ‖@inner ℂ _ _ A B‖ ^ 2 := by rw [hinner]
    _ ≤ (‖A‖ * ‖B‖) ^ 2 := by gcongr; exact norm_inner_le_norm A B
    _ = (∑' k, ‖a k‖ ^ 2) * (∑' k, ‖b k‖ ^ 2) := by rw [mul_pow, hnA, hnB]

/-- **The Hilbert–Schmidt composition entry is bounded by the row and column energies.**
`‖(K∘L)(i,j)‖² ≤ (∑ₖ ‖K(i,k)‖²)·(∑ₖ ‖L(k,j)‖²)` — the entrywise operator bound underlying the
submultiplicative Hilbert–Schmidt norm.  Summing over `(i,j)` gives `‖K∘L‖²_HS ≤ ‖K‖²_HS·‖L‖²_HS`
(the Hilbert–Schmidt ideal bound), once the row/column energies are summed. -/
theorem hsComp_entry_normSq_le {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) (i j : ι) :
    ‖hsComp K L (i, j)‖ ^ 2 ≤ (∑' k, ‖K (i, k)‖ ^ 2) * (∑' k, ‖L (k, j)‖ ^ 2) := by
  have h := hsComp_entry_bound (a := fun k => K (i, k)) (b := fun k => L (k, j))
    (isHS_row hK i) (isHS_col hL j)
  simpa only [hsComp] using h

/-- The Hilbert–Schmidt composition is compatible with the adjoint: `(K ∘ L)ᴴ = Lᴴ ∘ Kᴴ`. -/
theorem hsAdjoint_hsComp (K L : ι × ι → ℂ) :
    hsAdjoint (hsComp K L) = hsComp (hsAdjoint L) (hsAdjoint K) := by
  funext p
  rw [hsAdjoint, hsComp, hsComp, Complex.conj_tsum]
  refine tsum_congr fun k => ?_
  simp only [hsAdjoint, map_mul]
  ring

/-- The `swap`-reindexed square-entries of a Hilbert–Schmidt kernel are summable. -/
theorem isHS_swap {L : ι × ι → ℂ} (hL : IsHS L) :
    Summable (fun p : ι × ι => ‖L (p.2, p.1)‖ ^ 2) :=
  ((Equiv.prodComm ι ι).summable_iff (f := fun p => ‖L p‖ ^ 2)).mpr hL

/-- The diagonal of a Hilbert–Schmidt composition is summable — its trace `∑ᵢ (K∘L)(i,i)` converges,
because `(i,k) ↦ K(i,k)·L(k,i)` is dominated by `½(‖K(i,k)‖² + ‖L(k,i)‖²)`, summable over `ι × ι`. -/
theorem hsComp_diag_summable {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    Summable (fun p : ι × ι => K p * L (p.2, p.1)) := by
  apply Summable.of_norm_bounded (g := fun p => (‖K p‖ ^ 2 + ‖L (p.2, p.1)‖ ^ 2) / 2)
  · exact (hK.add (isHS_swap hL)).div_const 2
  · intro p
    rw [norm_mul]
    nlinarith [sq_nonneg (‖K p‖ - ‖L (p.2, p.1)‖), norm_nonneg (K p), norm_nonneg (L (p.2, p.1))]

/-- **The trace of a Hilbert–Schmidt composition is the Hilbert–Schmidt pairing.**
`tr(K ∘ L) = ∑ᵢ (K∘L)(i,i) = ⟨Kᴴ, L⟩_HS`.  The composition of two Hilbert–Schmidt operators is
trace-class, and its trace is the Hilbert–Schmidt inner product of the adjoint of the first with the
second — the foundational trace identity of the Hilbert–Schmidt ideal. -/
theorem hsTrace_hsComp {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    ∑' i : ι, hsComp K L (i, i) = hsInner (hsAdjoint K) L := by
  have hdiag : ∑' i : ι, hsComp K L (i, i) = ∑' p : ι × ι, K p * L (p.2, p.1) := by
    simp only [hsComp]
    rw [← (hsComp_diag_summable hK hL).tsum_prod]
  rw [hdiag, hsInner,
    ← (Equiv.prodComm ι ι).tsum_eq (fun p => (starRingEnd ℂ) (hsAdjoint K p) * L p)]
  refine tsum_congr fun p => ?_
  simp only [hsAdjoint, Equiv.prodComm_apply, Prod.swap, Complex.conj_conj]

end HilbertSchmidt
