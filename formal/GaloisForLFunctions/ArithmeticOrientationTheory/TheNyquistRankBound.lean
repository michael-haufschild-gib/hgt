import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValues
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Nyquist rank bound: sections of a node divisor

A **reading** of a finite-dimensional space of tests at a finite set of **nodes** is a matrix
`A : Matrix m n ℂ` (rows = nodes, columns = coordinates of the test).  Its **sections** are the
tests it annihilates, `ker A`, and `h⁰(A) = dim ker A` counts them.  The **degrees of freedom**
of the reading is its Frobenius mass `Σ ‖A_ij‖²`, and a **frame bound** `K` is a constant with
`Σ_i ‖(A x)_i‖² ≤ K Σ_j ‖x_j‖²` for every test `x`.

* **Rank–trace law** (`frobeniusMass_le_rank_mul`): `Σ ‖A_ij‖² ≤ K · rank A`.  The Gram
  `AᴴA` is Hermitian positive semidefinite, its trace is the Frobenius mass, each eigenvalue is a
  Rayleigh quotient of the frame and so at most `K`, and the rank counts the nonzero eigenvalues.
* **Nyquist bound on sections** (`h0_le_nyquist`): `h⁰(A) ≤ dim − (Frobenius mass)/K`.  A
  reading cannot annihilate more tests than its degrees of freedom allow.
* **Dirichlet polynomials at separated heights** (`h0_dirichletSampling_le`): for `N`
  coefficients read at `R + 1` heights `δ`-separated in `[0, T]`, the unit modulus of every
  phase gives Frobenius mass `(R+1) N`, the large-values estimate gives the frame bound
  `K = (T + 4N(1 + log N))(δ⁻¹ + 2 log N)`, and so the Dirichlet polynomials of length `N`
  vanishing at all the heights form a space of dimension at most `N (1 − (R+1)/K)`.  Below the
  diagonal `N ≪ T` the sampling is essentially injective; above it, hiding is possible.  This is
  the square-root threshold of the aperture read as a sampling threshold.
-/

open Finset Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Frobenius mass, frame bounds, and sections -/

/-- The Frobenius mass `Σ_{i,j} ‖A_ij‖²`: the degrees of freedom of the reading. -/
def frobeniusMass (A : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- A frame bound: `Σ_i ‖(A x)_i‖² ≤ K Σ_j ‖x_j‖²` for every test `x`. -/
def HasFrameBound (A : Matrix m n ℂ) (K : ℝ) : Prop :=
  ∀ x : n → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ K * ∑ j, ‖x j‖ ^ 2

/-- The number of sections: the dimension of the space of tests the reading annihilates. -/
def h0 (A : Matrix m n ℂ) : ℕ := Module.finrank ℂ (LinearMap.ker A.mulVecLin)

omit [Fintype m] [DecidableEq n] in
/-- `h⁰(A) + rank A = dim`: the rank–nullity form of Riemann–Roch for a reading. -/
theorem h0_add_rank (A : Matrix m n ℂ) : h0 A + A.rank = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  unfold h0 Matrix.rank
  linarith

omit [DecidableEq n] in
/-- **Sections exist beyond the nodes**: `h⁰(A) ≥ dim − #nodes`, the rank–nullity half of
Riemann–Roch. -/
theorem card_sub_card_le_h0 (A : Matrix m n ℂ) :
    (Fintype.card n : ℝ) - Fintype.card m ≤ h0 A := by
  have h1 := h0_add_rank A
  have h2 : A.rank ≤ Fintype.card m := rank_le_card_height A
  have h3 : (h0 A : ℝ) + A.rank = Fintype.card n := by exact_mod_cast h1
  have h4 : (A.rank : ℝ) ≤ Fintype.card m := by exact_mod_cast h2
  linarith

/-- The number of obstructions: the codimension of the range of the reading in the node space. -/
def h1 (A : Matrix m n ℂ) : ℕ := Fintype.card m - A.rank

omit [DecidableEq n] in
/-- **Riemann–Roch for readings**: `h⁰ − h¹ = dim − #nodes`, the Euler characteristic of the
node divisor. -/
theorem h0_sub_h1 (A : Matrix m n ℂ) :
    (h0 A : ℤ) - h1 A = (Fintype.card n : ℤ) - Fintype.card m := by
  have h := h0_add_rank A
  have hr : A.rank ≤ Fintype.card m := rank_le_card_height A
  unfold h1
  omega

omit [DecidableEq n] in
/-- Interpolation at every node is possible iff there are no obstructions. -/
theorem h1_eq_zero_iff (A : Matrix m n ℂ) : h1 A = 0 ↔ A.rank = Fintype.card m := by
  have hr : A.rank ≤ Fintype.card m := rank_le_card_height A
  unfold h1
  omega

/-- The real part of `star u ⬝ u` is `Σ ‖u_i‖²`. -/
theorem re_star_dotProduct_self (u : m → ℂ) : (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  unfold dotProduct
  rw [Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re]

omit [DecidableEq n] in
/-- The Gram `AᴴA` has trace equal to the Frobenius mass (real part). -/
theorem re_trace_conjTranspose_mul_self (A : Matrix m n ℂ) :
    (trace (Aᴴ * A)).re = frobeniusMass A := by
  unfold trace frobeniusMass
  rw [Complex.re_sum, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp only [diag_apply, mul_apply, conjTranspose_apply]
  rw [Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Every eigenvalue of the Gram `AᴴA` is a Rayleigh quotient of the frame, hence at most `K`. -/
theorem eigenvalues_le_of_hasFrameBound {A : Matrix m n ℂ} {K : ℝ} (hK : HasFrameBound A K)
    (i : n) : (isHermitian_conjTranspose_mul_self A).eigenvalues i ≤ K := by
  set hA := isHermitian_conjTranspose_mul_self A
  rw [hA.eigenvalues_eq i]
  set v : n → ℂ := ⇑(hA.eigenvectorBasis i) with hv
  have hnorm : ∑ j, ‖v j‖ ^ 2 = 1 := by
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
    have h2 := EuclideanSpace.norm_eq (hA.eigenvectorBasis i)
    rw [h1] at h2
    have h3 : (∑ j, ‖(hA.eigenvectorBasis i) j‖ ^ 2) = 1 := by
      have := congrArg (fun t => t ^ 2) h2
      simp only [one_pow] at this
      rw [this, Real.sq_sqrt (sum_nonneg fun j _ => by positivity)]
    simpa [hv] using h3
  have hdot : star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  change (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re ≤ K
  rw [hdot, re_star_dotProduct_self]
  calc ∑ j, ‖(A *ᵥ v) j‖ ^ 2 ≤ K * ∑ j, ‖v j‖ ^ 2 := hK v
    _ = K := by rw [hnorm, mul_one]

/-- **Rank–trace law**: `Σ ‖A_ij‖² ≤ K · rank A` for every frame bound `K`. -/
theorem frobeniusMass_le_rank_mul {A : Matrix m n ℂ} {K : ℝ} (hK : HasFrameBound A K) :
    frobeniusMass A ≤ K * A.rank := by
  set hA := isHermitian_conjTranspose_mul_self A
  have hpsd : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have htr : frobeniusMass A = ∑ i, hA.eigenvalues i := by
    rw [← re_trace_conjTranspose_mul_self, hA.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have hrank : A.rank = (univ.filter fun i => hA.eigenvalues i ≠ 0).card := by
    rw [← rank_conjTranspose_mul_self, hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  rw [htr, hrank]
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have hle : ∀ i, hA.eigenvalues i ≤ K := eigenvalues_le_of_hasFrameBound hK
  calc ∑ i, hA.eigenvalues i
      = ∑ i ∈ univ.filter (fun i => hA.eigenvalues i ≠ 0), hA.eigenvalues i := by
        rw [sum_filter_of_ne]
        intro i _ hne
        exact hne
    _ ≤ ∑ _i ∈ univ.filter (fun i => hA.eigenvalues i ≠ 0), K :=
        sum_le_sum fun i _ => hle i
    _ = K * ((univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_comm]

/-- **The Nyquist bound on sections**: `h⁰(A) ≤ dim − (Frobenius mass)/K`. -/
theorem h0_le_nyquist {A : Matrix m n ℂ} {K : ℝ} (hK0 : 0 < K) (hK : HasFrameBound A K) :
    (h0 A : ℝ) ≤ Fintype.card n - frobeniusMass A / K := by
  have h1 := h0_add_rank A
  have h2 := frobeniusMass_le_rank_mul hK
  have h3 : frobeniusMass A / K ≤ A.rank := by
    rw [div_le_iff₀ hK0]; linarith
  have h4 : (h0 A : ℝ) + A.rank = Fintype.card n := by exact_mod_cast h1
  linarith

/-- **No sections at full degrees of freedom**: if the Frobenius mass reaches `K · dim`, the
reading is injective. -/
theorem h0_eq_zero_of_frobeniusMass_ge {A : Matrix m n ℂ} {K : ℝ} (hK0 : 0 < K)
    (hK : HasFrameBound A K) (hmass : K * Fintype.card n ≤ frobeniusMass A) : h0 A = 0 := by
  have h := h0_le_nyquist hK0 hK
  have h2 : (Fintype.card n : ℝ) ≤ frobeniusMass A / K := by
    rw [le_div_iff₀ hK0]; linarith
  have h3 : (h0 A : ℝ) ≤ 0 := by linarith
  exact_mod_cast le_antisymm h3 (Nat.cast_nonneg _)

/-- **Interpolation at full degrees of freedom**: if the Frobenius mass reaches `K · #nodes`, the
reading is onto and every node datum is interpolated (`h¹ = 0`). -/
theorem h1_eq_zero_of_frobeniusMass_ge {A : Matrix m n ℂ} {K : ℝ} (hK0 : 0 < K)
    (hK : HasFrameBound A K) (hmass : K * Fintype.card m ≤ frobeniusMass A) : h1 A = 0 := by
  rw [h1_eq_zero_iff]
  have h := frobeniusMass_le_rank_mul hK
  have hr : A.rank ≤ Fintype.card m := rank_le_card_height A
  have h2 : (Fintype.card m : ℝ) ≤ A.rank := by
    by_contra hlt
    push_neg at hlt
    have : K * (A.rank : ℝ) < K * Fintype.card m := mul_lt_mul_of_pos_left hlt hK0
    linarith
  have h3 : Fintype.card m ≤ A.rank := by exact_mod_cast h2
  omega

/-! ### Dirichlet polynomials read at separated heights -/

/-- The sampling matrix of Dirichlet polynomials of length `N` at the heights `lam 0, …, lam R`:
entry `(r, k) = (k+1)^{i lam r}`. -/
def dirichletSampling (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) : Matrix (Fin (R + 1)) (Fin N) ℂ :=
  fun r k => Complex.exp (((lam r * Real.log ((k : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

theorem dirichletSampling_mulVec (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) (a : Fin N → ℂ)
    (r : Fin (R + 1)) :
    (dirichletSampling N lam R *ᵥ a) r = RHTower.Sieve.dirPoly N a (lam r) := by
  unfold dirichletSampling RHTower.Sieve.dirPoly
  simp only [mulVec, dotProduct]
  exact sum_congr rfl fun k _ => mul_comm _ _

/-- Every phase has unit modulus, so the Frobenius mass is the number of samples times the
length. -/
theorem frobeniusMass_dirichletSampling (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) :
    frobeniusMass (dirichletSampling N lam R) = (R + 1) * N := by
  unfold frobeniusMass dirichletSampling
  simp only [Complex.norm_exp_ofReal_mul_I, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The large-values estimate is a frame bound for the sampling matrix at `δ`-separated heights
in `[δ/2, T − δ/2]`. -/
theorem hasFrameBound_dirichletSampling (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0)
    (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    HasFrameBound (dirichletSampling N lam R)
      ((T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)) := by
  intro a
  have h := RHTower.Sieve.largeValues_dirPoly N hN a hδ hT hgap hlow R hhigh
  simp only [dirichletSampling_mulVec]
  rw [Fin.sum_univ_eq_sum_range (fun r => ‖RHTower.Sieve.dirPoly N a (lam r)‖ ^ 2) (R + 1)]
  exact h

/-- **Nyquist bound for Dirichlet polynomials**: at `R + 1` heights `δ`-separated in `[0, T]`,
the Dirichlet polynomials of length `N ≥ 2` vanishing at all of them form a space of dimension
at most `N − (R+1) N / K`, `K = (T + 4N(1 + log N))(δ⁻¹ + 2 log N)`. -/
theorem h0_dirichletSampling_le (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0)
    (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    (h0 (dirichletSampling N lam R) : ℝ) ≤
      N - (R + 1) * N / ((T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hK0 : 0 < (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N) := by
    positivity
  have h := h0_le_nyquist hK0 (hasFrameBound_dirichletSampling N hN hδ hT hgap hlow R hhigh)
  rw [frobeniusMass_dirichletSampling, Fintype.card_fin] at h
  exact h

end

end GaloisForLFunctions.ArithmeticOrientationTheory
