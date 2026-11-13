import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize
import GaloisForLFunctions.HTGeometry.HermitianLowerSpectralWindows

/-!
# One bound state is the Hodge index inequality on positive packets without common blocks

The neutral part `N` of a window is a real symmetric matrix whose entries off the diagonal are
negative: two different blocks are coupled by minus their jet and their floor-map contacts. For
a symmetric matrix `G` with entries `≤ 0` off the diagonal the count of negative squares is
decided on the positive cone.

* **Two wells.** `G` has two negative squares iff there are vectors `x, y ≥ 0` without a common
  index such that `G(x, x) < 0` and `G(x, y)² < G(x, x) G(y, y)`. The vectors are two wells of
  depths `−G(x, x)`, `−G(y, y)`; their coupling `−G(x, y)` is nonnegative, and they stay
  apart when it is below the geometric mean of the depths.
* **One bound state.** `G` has at most one negative square iff
  `G(x, x) G(y, y) ≤ G(x, y)²` for all such `x, y` with `G(x, x) < 0`. For the pairing
  `⟨x, y⟩ = −G(x, y)` this is the Hodge index inequality `⟨x, x⟩ ⟨y, y⟩ ≤ ⟨x, y⟩²`, tested only
  on positive vectors without a common index, which meet nonnegatively.
* **Nodal form.** If the entries off the diagonal are negative, `G` has two negative squares iff
  an eigenvector with negative eigenvalue takes both signs.

On windows: the Riemann hypothesis holds iff on every window that contains the dyadic window
two positive step packets without a common block obey the Hodge index inequality, and iff every
bound state of every such window has one sign. The inequality is an exact gluing law: the depth
of a union of two wells is the sum of the depths minus twice their coupling, and the coupling is
the sum of the jets and contacts between the blocks of the two wells.

Proofs. Two negative squares give two orthonormal eigenvectors `u, v` with negative eigenvalues.
If one of them, `ψ` with eigenvalue `λ`, takes both signs, its positive and negative parts
`p, n` satisfy `G(p, p) = c + λ|p|²`, `G(n, n) = c + λ|n|²` with `c = G(p, n) ≤ 0`, hence
`G(p, p) G(n, n) − c² = λ c (|p|² + |n|²) + λ² |p|² |n|² > 0`. Otherwise `|u|`, `|v|` are
orthogonal vectors of one sign, so they have no common index, and `G(|u|, |v|) = 0`. If the
entries off the diagonal are negative the second case does not occur: at an index of `v` the
eigenvector `u` vanishes while its row sum against `u` is strictly of one sign.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open scoped RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

section Wells

variable {ι : Type*} [Fintype ι]

/-! ### The bilinear form -/

theorem bilin_swap {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i) (x y : ι → ℝ) :
    bilin G x y = bilin G y x := by
  unfold bilin
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hG j i]
    ring

theorem bilin_comb (G : Matrix ι ι ℝ) (x y : ι → ℝ) (s t : ℝ) :
    bilin G (fun i => s * x i + t * y i) (fun i => s * x i + t * y i) =
      s ^ 2 * bilin G x x + s * t * (bilin G x y + bilin G y x) + t ^ 2 * bilin G y y := by
  simp only [bilin, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilin_eq_sum_mul_mulVec (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    bilin G x y = ∑ i, x i * (G *ᵥ y) i := by
  simp only [bilin, mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilin_sub_right (G : Matrix ι ι ℝ) (x p n : ι → ℝ) :
    bilin G x (fun i => p i - n i) = bilin G x p - bilin G x n := by
  simp only [bilin, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilin_smul_smul (G : Matrix ι ι ℝ) (a b : ℝ) (x y : ι → ℝ) :
    bilin G (fun k => a * x k) (fun k => b * y k) = a * b * bilin G x y := by
  simp only [bilin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Against an eigenvector the form is the eigenvalue times the scalar product. -/
theorem bilin_eigen {G : Matrix ι ι ℝ} {ψ : ι → ℝ} {lam : ℝ} (hψ : G *ᵥ ψ = lam • ψ)
    (x : ι → ℝ) : bilin G x ψ = lam * ∑ k, x k * ψ k := by
  rw [bilin_eq_sum_mul_mulVec, hψ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- **Positive vectors without a common index meet nonnegatively**: their form is `≤ 0` when the
entries off the diagonal are. -/
theorem bilin_nonpos_of_disjoint {G : Matrix ι ι ℝ} (hoff : ∀ i j, i ≠ j → G i j ≤ 0)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hxy : ∀ i, x i * y i = 0) :
    bilin G x y ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
  by_cases hij : i = j
  · rw [← hij, hxy i, zero_mul]
  · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hx i) (hy j)) (hoff i j hij)

/-- A form with a negative vector `x` and `G(x, y)² < G(x, x) G(y, y)` has two negative
squares. -/
theorem two_le_hermNegIndex_of_unbound_pair {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    {x y : ι → ℝ} (hx : bilin G x x < 0)
    (hxy : bilin G x y ^ 2 < bilin G x x * bilin G y y) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) :=
  two_le_hermNegIndex_of_two_vectors G x y (fun s t => by
    rw [bilin_comb, bilin_swap hG y x]
    exact le_of_eq (by ring)) hx hxy

/-! ### The two parts of an eigenvector -/

/-- The positive part of a vector. -/
def positiveWell (ψ : ι → ℝ) (i : ι) : ℝ := max (ψ i) 0

/-- The negative part of a vector. -/
def negativeWell (ψ : ι → ℝ) (i : ι) : ℝ := max (-ψ i) 0

omit [Fintype ι] in
theorem positiveWell_nonneg (ψ : ι → ℝ) (i : ι) : 0 ≤ positiveWell ψ i := le_max_right _ _

omit [Fintype ι] in
theorem negativeWell_nonneg (ψ : ι → ℝ) (i : ι) : 0 ≤ negativeWell ψ i := le_max_right _ _

omit [Fintype ι] in
theorem positiveWell_sub_negativeWell (ψ : ι → ℝ) (i : ι) :
    positiveWell ψ i - negativeWell ψ i = ψ i := by
  rw [positiveWell, negativeWell]
  rcases le_total 0 (ψ i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

omit [Fintype ι] in
theorem positiveWell_mul_negativeWell (ψ : ι → ℝ) (i : ι) :
    positiveWell ψ i * negativeWell ψ i = 0 := by
  rw [positiveWell, negativeWell]
  rcases le_total 0 (ψ i) with h | h
  · rw [max_eq_right (by linarith : -ψ i ≤ 0), mul_zero]
  · rw [max_eq_right h, zero_mul]

/-- With `c ≤ 0`, `λ < 0` and `P, N > 0`: `c² < (c + λP)(c + λN)`. -/
theorem sq_lt_mul_of_coupling_nonpos {c l P N : ℝ} (hc : c ≤ 0) (hl : l < 0) (hP : 0 < P)
    (hN : 0 < N) : c ^ 2 < (c + l * P) * (c + l * N) := by
  have h1 : 0 ≤ l * c * (P + N) :=
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hl.le hc) (add_pos hP hN).le
  have h2 : 0 < l * P * (l * N) :=
    mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hl hP) (mul_neg_of_neg_of_pos hl hN)
  have e : (c + l * P) * (c + l * N) = c ^ 2 + l * c * (P + N) + l * P * (l * N) := by ring
  rw [e]
  linarith

/-- **The two parts of a bound state that takes both signs are two wells that stay apart.** -/
theorem exists_unbound_wells_of_eigenvector {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {ψ : ι → ℝ} {lam : ℝ} (hlam : lam < 0)
    (hψ : G *ᵥ ψ = lam • ψ) {i j : ι} (hi : 0 < ψ i) (hj : ψ j < 0) :
    ∃ x y : ι → ℝ, (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧ (∀ k, x k * y k = 0) ∧
      bilin G x x < 0 ∧ bilin G x y ^ 2 < bilin G x x * bilin G y y := by
  obtain ⟨p, n, hp0, hn0, hpn, hψk, hpi, hnj⟩ : ∃ p n : ι → ℝ, (∀ k, 0 ≤ p k) ∧
      (∀ k, 0 ≤ n k) ∧ (∀ k, p k * n k = 0) ∧ (∀ k, ψ k = p k - n k) ∧ 0 < p i ∧ 0 < n j :=
    ⟨positiveWell ψ, negativeWell ψ, positiveWell_nonneg ψ, negativeWell_nonneg ψ,
      positiveWell_mul_negativeWell ψ, fun k => (positiveWell_sub_negativeWell ψ k).symm,
      by rw [positiveWell, max_eq_left hi.le]; exact hi,
      by rw [negativeWell, max_eq_left (by linarith)]; linarith⟩
  have hψe : ψ = fun k => p k - n k := funext hψk
  have hc : bilin G p n ≤ 0 := bilin_nonpos_of_disjoint hoff hp0 hn0 hpn
  have hP : 0 < ∑ k, p k ^ 2 :=
    Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨i, Finset.mem_univ i, pow_pos hpi 2⟩
  have hN : 0 < ∑ k, n k ^ 2 :=
    Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨j, Finset.mem_univ j, pow_pos hnj 2⟩
  -- the eigenvalue equation paired with the two parts
  have h1 : bilin G p p - bilin G p n = lam * ∑ k, p k ^ 2 := by
    rw [← bilin_sub_right, ← hψe, bilin_eigen hψ]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by
      rw [hψk k]
      linear_combination (-1 : ℝ) * hpn k
  have h2 : bilin G n p - bilin G n n = -(lam * ∑ k, n k ^ 2) := by
    rw [← bilin_sub_right, ← hψe, bilin_eigen hψ, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by
      rw [hψk k]
      linear_combination hpn k
  have h3 : bilin G n p = bilin G p n := bilin_swap hG n p
  have ha : bilin G p p = bilin G p n + lam * ∑ k, p k ^ 2 := by linarith
  have hb : bilin G n n = bilin G p n + lam * ∑ k, n k ^ 2 := by linarith
  refine ⟨p, n, hp0, hn0, hpn, ?_, ?_⟩
  · have := mul_neg_of_neg_of_pos hlam hP
    rw [ha]
    linarith
  · rw [ha, hb]
    exact sq_lt_mul_of_coupling_nonpos hc hlam hP hN

omit [Fintype ι] in
/-- A vector that does not take both signs is nonnegative up to a sign. -/
theorem exists_sign_of_not_changing {u : ι → ℝ} (h : ¬((∃ k, 0 < u k) ∧ ∃ k, u k < 0)) :
    ∃ e : ℝ, e ^ 2 = 1 ∧ ∀ k, 0 ≤ e * u k := by
  by_cases hpos : ∃ k, 0 < u k
  · refine ⟨1, by norm_num, fun k => ?_⟩
    rw [one_mul]
    by_contra hk
    exact h ⟨hpos, k, not_le.mp hk⟩
  · refine ⟨-1, by norm_num, fun k => ?_⟩
    have hk : u k ≤ 0 := not_lt.mp fun hk => hpos ⟨k, hk⟩
    linarith

/-- Orthogonal nonnegative vectors have no common index. -/
theorem mul_eq_zero_of_sum_eq_zero {x y : ι → ℝ} (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k)
    (h : ∑ k, x k * y k = 0) (k : ι) : x k * y k = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hx k) (hy k)).mp h k
    (Finset.mem_univ k)

/-- **Two orthonormal bound states give two wells that stay apart**: the two parts of one of
them, or their moduli. -/
theorem exists_unbound_wells_of_two_eigenvectors {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {u v : ι → ℝ} {a b : ℝ} (ha : a < 0) (hb : b < 0)
    (hu : G *ᵥ u = a • u) (hv : G *ᵥ v = b • v) (huu : ∑ k, u k * u k = 1)
    (hvv : ∑ k, v k * v k = 1) (huv : ∑ k, u k * v k = 0) :
    ∃ x y : ι → ℝ, (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧ (∀ k, x k * y k = 0) ∧
      bilin G x x < 0 ∧ bilin G x y ^ 2 < bilin G x x * bilin G y y := by
  by_cases hcu : (∃ k, 0 < u k) ∧ ∃ k, u k < 0
  · obtain ⟨⟨i, hi⟩, j, hj⟩ := hcu
    exact exists_unbound_wells_of_eigenvector hG hoff ha hu hi hj
  by_cases hcv : (∃ k, 0 < v k) ∧ ∃ k, v k < 0
  · obtain ⟨⟨i, hi⟩, j, hj⟩ := hcv
    exact exists_unbound_wells_of_eigenvector hG hoff hb hv hi hj
  -- both have one sign: their moduli are orthogonal, hence without a common index
  obtain ⟨e, he, heu⟩ := exists_sign_of_not_changing hcu
  obtain ⟨f, hf, hfv⟩ := exists_sign_of_not_changing hcv
  have hxx : bilin G (fun k => e * u k) (fun k => e * u k) = a := by
    rw [bilin_smul_smul, bilin_eigen hu, huu]
    linear_combination a * he
  have hyy : bilin G (fun k => f * v k) (fun k => f * v k) = b := by
    rw [bilin_smul_smul, bilin_eigen hv, hvv]
    linear_combination b * hf
  have hxy : bilin G (fun k => e * u k) (fun k => f * v k) = 0 := by
    rw [bilin_smul_smul, bilin_eigen hv, huv]
    ring
  have hsum : ∑ k, e * u k * (f * v k) = 0 := by
    have e1 : ∑ k, e * u k * (f * v k) = e * f * ∑ k, u k * v k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, huv, mul_zero]
  refine ⟨fun k => e * u k, fun k => f * v k, heu, hfv,
    mul_eq_zero_of_sum_eq_zero heu hfv hsum, by rw [hxx]; exact ha, ?_⟩
  rw [hxy, hxx, hyy]
  have := mul_pos_of_neg_of_neg ha hb
  linarith

/-- **With negative entries off the diagonal, one of two orthonormal bound states takes both
signs**: two eigenvectors of one sign have no common index, and at an index of the second the
row of the matrix against the first is strictly of one sign and vanishes. -/
theorem exists_sign_changing_eigenvector_of_two_eigenvectors {G : Matrix ι ι ℝ}
    (hoff : ∀ i j, i ≠ j → G i j < 0) {u v : ι → ℝ} {a b : ℝ} (ha : a < 0) (hb : b < 0)
    (hu : G *ᵥ u = a • u) (hv : G *ᵥ v = b • v) (huu : ∑ k, u k * u k = 1)
    (hvv : ∑ k, v k * v k = 1) (huv : ∑ k, u k * v k = 0) :
    ∃ ψ : ι → ℝ, ∃ lam : ℝ, lam < 0 ∧ G *ᵥ ψ = lam • ψ ∧ (∃ k, 0 < ψ k) ∧ ∃ k, ψ k < 0 := by
  by_cases hcu : (∃ k, 0 < u k) ∧ ∃ k, u k < 0
  · exact ⟨u, a, ha, hu, hcu.1, hcu.2⟩
  by_cases hcv : (∃ k, 0 < v k) ∧ ∃ k, v k < 0
  · exact ⟨v, b, hb, hv, hcv.1, hcv.2⟩
  exfalso
  obtain ⟨e, he, heu⟩ := exists_sign_of_not_changing hcu
  obtain ⟨f, hf, hfv⟩ := exists_sign_of_not_changing hcv
  have he0 : e ≠ 0 := by
    rintro rfl
    norm_num at he
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at hf
  have hsum : ∑ k, e * u k * (f * v k) = 0 := by
    have e1 : ∑ k, e * u k * (f * v k) = e * f * ∑ k, u k * v k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, huv, mul_zero]
  have hdisj := mul_eq_zero_of_sum_eq_zero heu hfv hsum
  obtain ⟨k₀, hk₀⟩ : ∃ k, v k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hvv
  obtain ⟨j₀, hj₀⟩ : ∃ k, u k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at huu
  have huk : u k₀ = 0 := by
    rcases mul_eq_zero.mp (hdisj k₀) with h | h
    · exact (mul_eq_zero.mp h).resolve_left he0
    · exact absurd ((mul_eq_zero.mp h).resolve_left hf0) hk₀
  -- the row `k₀` of the eigenvalue equation of `u`
  have hrow : ∑ j, G k₀ j * (e * u j) = 0 := by
    have h := congrFun hu k₀
    rw [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, huk, mul_zero] at h
    have e1 : ∑ j, G k₀ j * (e * u j) = e * ∑ j, G k₀ j * u j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, h, mul_zero]
  have hneg : ∑ j, G k₀ j * (e * u j) < 0 := by
    refine Finset.sum_neg' (fun j _ => ?_) ⟨j₀, Finset.mem_univ j₀, ?_⟩
    · by_cases hj : j = k₀
      · rw [hj, huk, mul_zero, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff k₀ j (Ne.symm hj)).le (heu j)
    · have hne : k₀ ≠ j₀ := fun h => hj₀ (h ▸ huk)
      exact mul_neg_of_neg_of_pos (hoff k₀ j₀ hne)
        (lt_of_le_of_ne (heu j₀) (Ne.symm (mul_ne_zero he0 hj₀)))
  linarith

/-! ### The negative squares of a real symmetric matrix and its eigenvalues -/

omit [Fintype ι] in
theorem isHermitian_of_symm {A : Matrix ι ι ℝ} (h : ∀ i j, A i j = A j i) : A.IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by simpa using h j i

section Spectral

variable [DecidableEq ι]

theorem inner_toEuclideanLin_toLp (A : Matrix ι ι ℝ) (σ : ι → ℝ) :
    ⟪Matrix.toEuclideanLin A (WithLp.toLp 2 σ), (WithLp.toLp 2 σ : EuclideanSpace ℝ ι)⟫ =
      σ ⬝ᵥ (A *ᵥ σ) := by
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]

theorem inner_toLp_eigenvector {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (σ : ι → ℝ) (i : ι) :
    ⟪(WithLp.toLp 2 σ : EuclideanSpace ℝ ι), hA.eigenvectorBasis i⟫ =
      ∑ k, σ k * hA.eigenvectorBasis i k := by
  simp [PiLp.inner_apply, mul_comm]

/-- The form of a real symmetric matrix in its eigenvector coordinates. -/
theorem dotProduct_mulVec_eq_sum_eigen {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (σ : ι → ℝ) :
    σ ⬝ᵥ (A *ᵥ σ) = ∑ i, hA.eigenvalues i * (∑ k, σ k * hA.eigenvectorBasis i k) ^ 2 := by
  rw [← inner_toEuclideanLin_toLp, hermitianEnergy_eq_sum hA]
  exact Finset.sum_congr rfl fun i _ => by rw [inner_toLp_eigenvector]

theorem eigenvector_orthonormal {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i j : ι) :
    ∑ k, hA.eigenvectorBasis i k * hA.eigenvectorBasis j k = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i j
  rw [← h]
  simp [PiLp.inner_apply, mul_comm]

/-- **The negative squares of a real symmetric matrix are at most its negative eigenvalues**:
the form is nonnegative on the vectors orthogonal to the eigenvectors of negative eigenvalue. -/
theorem hermNegIndex_le_card_neg_eigenvalues {G : Matrix ι ι ℝ} (hB : G.IsHermitian) :
    hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ Fintype.card {i // hB.eigenvalues i < 0} := by
  have key : ∀ σ : ι → ℝ,
      (∀ k : {i // hB.eigenvalues i < 0}, ∑ m, hB.eigenvectorBasis k.1 m * σ m = 0) →
        0 ≤ σ ⬝ᵥ (G *ᵥ σ) := by
    intro σ hσ
    rw [dotProduct_mulVec_eq_sum_eigen hB]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases hi : hB.eigenvalues i < 0
    · have e : ∑ k, σ k * hB.eigenvectorBasis i k = 0 := by
        rw [← hσ ⟨i, hi⟩]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [e]
      norm_num
    · exact mul_nonneg (not_lt.mp hi) (sq_nonneg _)
  refine ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
    (G.map (↑) : Matrix ι ι ℂ)
    (fun k : {i // hB.eigenvalues i < 0} => realChargeForm fun m => hB.eigenvectorBasis k.1 m)
    fun x hx => ?_
  -- the real and the imaginary part are orthogonal to the negative eigenvectors
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal]
  refine add_nonneg (key _ fun k => ?_) (key _ fun k => ?_)
  · have hc : ∑ m, ((hB.eigenvectorBasis k.1 m : ℝ) : ℂ) * x m = 0 := hx k
    have h1 := congrArg Complex.re hc
    rw [Complex.re_sum, Complex.zero_re] at h1
    exact (Finset.sum_congr rfl fun m _ => (Complex.re_ofReal_mul _ _).symm).trans h1
  · have hc : ∑ m, ((hB.eigenvectorBasis k.1 m : ℝ) : ℂ) * x m = 0 := hx k
    have h1 := congrArg Complex.im hc
    rw [Complex.im_sum, Complex.zero_im] at h1
    exact (Finset.sum_congr rfl fun m _ => (Complex.im_ofReal_mul _ _).symm).trans h1

end Spectral

/-- **Two negative squares give two orthonormal bound states.** -/
theorem exists_two_bound_states_of_two_le_hermNegIndex {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (h : 2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ)) :
    ∃ (u v : ι → ℝ) (a b : ℝ), a < 0 ∧ b < 0 ∧ G *ᵥ u = a • u ∧ G *ᵥ v = b • v ∧
      ∑ k, u k * u k = 1 ∧ ∑ k, v k * v k = 1 ∧ ∑ k, u k * v k = 0 := by
  classical
  have hB : G.IsHermitian := isHermitian_of_symm hG
  have hle := hermNegIndex_le_card_neg_eigenvalues hB
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij⟩ := Fintype.one_lt_card_iff.mp
    (by omega : 1 < Fintype.card {i // hB.eigenvalues i < 0})
  exact ⟨fun k => hB.eigenvectorBasis i k, fun k => hB.eigenvectorBasis j k, hB.eigenvalues i,
    hB.eigenvalues j, hi, hj, hB.mulVec_eigenvectorBasis i, hB.mulVec_eigenvectorBasis j,
    (eigenvector_orthonormal hB i i).trans (if_pos rfl),
    (eigenvector_orthonormal hB j j).trans (if_pos rfl),
    (eigenvector_orthonormal hB i j).trans (if_neg fun h => hij (Subtype.ext h))⟩

/-! ### The criteria -/

/-- **The two-well criterion.** A real symmetric matrix with entries `≤ 0` off the diagonal has
two negative squares iff two nonnegative vectors without a common index, the first of them
negative, violate the reverse Cauchy–Schwarz inequality. -/
theorem two_le_hermNegIndex_iff_exists_unbound_wells {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j ≤ 0) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ↔
      ∃ x y : ι → ℝ, (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧ (∀ k, x k * y k = 0) ∧
        bilin G x x < 0 ∧ bilin G x y ^ 2 < bilin G x x * bilin G y y := by
  constructor
  · intro h
    obtain ⟨u, v, a, b, ha, hb, hu, hv, huu, hvv, huv⟩ :=
      exists_two_bound_states_of_two_le_hermNegIndex hG h
    exact exists_unbound_wells_of_two_eigenvectors hG hoff ha hb hu hv huu hvv huv
  · rintro ⟨x, y, -, -, -, hx, hxy⟩
    exact two_le_hermNegIndex_of_unbound_pair hG hx hxy

/-- **The Hodge index inequality on the positive cone.** A real symmetric matrix with entries
`≤ 0` off the diagonal has at most one negative square iff `G(x, x) G(y, y) ≤ G(x, y)²` for all
nonnegative `x`, `y` without a common index with `G(x, x) < 0`. -/
theorem hermNegIndex_le_one_iff_forall_wells_bound {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j ≤ 0) :
    hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ 1 ↔
      ∀ x y : ι → ℝ, (∀ k, 0 ≤ x k) → (∀ k, 0 ≤ y k) → (∀ k, x k * y k = 0) →
        bilin G x x < 0 → bilin G x x * bilin G y y ≤ bilin G x y ^ 2 := by
  constructor
  · intro h x y _ _ _ hx
    by_contra hlt
    have := two_le_hermNegIndex_of_unbound_pair hG hx (not_le.mp hlt)
    omega
  · intro h
    by_contra hlt
    obtain ⟨x, y, hx0, hy0, hxy0, hx, hxy⟩ :=
      (two_le_hermNegIndex_iff_exists_unbound_wells hG hoff).mp (by omega)
    exact absurd (h x y hx0 hy0 hxy0 hx) (not_le.mpr hxy)

/-- **The nodal criterion.** A real symmetric matrix with negative entries off the diagonal has
two negative squares iff an eigenvector with negative eigenvalue takes both signs. -/
theorem two_le_hermNegIndex_iff_exists_sign_changing_bound_state {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j < 0) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ↔
      ∃ ψ : ι → ℝ, ∃ lam : ℝ, lam < 0 ∧ G *ᵥ ψ = lam • ψ ∧ (∃ k, 0 < ψ k) ∧ ∃ k, ψ k < 0 := by
  constructor
  · intro h
    obtain ⟨u, v, a, b, ha, hb, hu, hv, huu, hvv, huv⟩ :=
      exists_two_bound_states_of_two_le_hermNegIndex hG h
    exact exists_sign_changing_eigenvector_of_two_eigenvectors hoff ha hb hu hv huu hvv huv
  · rintro ⟨ψ, lam, hlam, hψ, ⟨i, hi⟩, j, hj⟩
    obtain ⟨x, y, -, -, -, hx, hxy⟩ := exists_unbound_wells_of_eigenvector hG
      (fun i j hij => (hoff i j hij).le) hlam hψ hi hj
    exact two_le_hermNegIndex_of_unbound_pair hG hx hxy

end Wells

/-! ### The windows -/

/-- The neutral part of a window is symmetric. -/
theorem neutralWindow_symm (Q R J : ℕ) (i j : Fin J) :
    neutralWindow Q R J i j = neutralWindow Q R J j i := neutralBlock_comm Q _ _

/-- Two different blocks of a window are coupled negatively. -/
theorem neutralWindow_neg_of_ne (Q R : ℕ) {J : ℕ} {i j : Fin J} (hij : i ≠ j) :
    neutralWindow Q R J i j < 0 :=
  neutralBlock_neg (fun h => hij (Fin.ext (Nat.add_left_cancel h))) Q

/-- **Positive step packets without a common block meet nonnegatively.** -/
theorem bilin_neutralWindow_nonpos_of_disjoint (Q R : ℕ) {J : ℕ} {x y : Fin J → ℝ}
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) (hxy : ∀ k, x k * y k = 0) :
    bilin (neutralWindow Q R J) x y ≤ 0 :=
  bilin_nonpos_of_disjoint (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hx hy hxy

/-- **A second bound state of a window is two wells that stay apart**: two positive step
packets without a common block whose coupling is below the geometric mean of their depths. -/
theorem two_le_hermNegIndex_neutralWindow_iff_exists_unbound_wells (Q R J : ℕ) :
    2 ≤ hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ↔
      ∃ x y : Fin J → ℝ, (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧ (∀ k, x k * y k = 0) ∧
        bilin (neutralWindow Q R J) x x < 0 ∧
        bilin (neutralWindow Q R J) x y ^ 2 <
          bilin (neutralWindow Q R J) x x * bilin (neutralWindow Q R J) y y :=
  two_le_hermNegIndex_iff_exists_unbound_wells (neutralWindow_symm Q R J)
    fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le

/-- **A second bound state of a window is a bound state that takes both signs.** -/
theorem two_le_hermNegIndex_neutralWindow_iff_exists_sign_changing_bound_state (Q R J : ℕ) :
    2 ≤ hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ↔
      ∃ ψ : Fin J → ℝ, ∃ lam : ℝ, lam < 0 ∧ neutralWindow Q R J *ᵥ ψ = lam • ψ ∧
        (∃ k, 0 < ψ k) ∧ ∃ k, ψ k < 0 :=
  two_le_hermNegIndex_iff_exists_sign_changing_bound_state (neutralWindow_symm Q R J)
    fun _ _ hij => neutralWindow_neg_of_ne Q R hij

/-- **A window that contains the dyadic window holds one bound state iff its positive step
packets without a common block obey the Hodge index inequality.** -/
theorem hermNegIndex_neutralWindow_eq_one_iff_forall_wells_bound (Q : ℕ) {R J : ℕ}
    (hR : 1 ≤ R) (hRJ : R ≤ J) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 ↔
      ∀ x y : Fin J → ℝ, (∀ k, 0 ≤ x k) → (∀ k, 0 ≤ y k) → (∀ k, x k * y k = 0) →
        bilin (neutralWindow Q R J) x x < 0 →
        bilin (neutralWindow Q R J) x x * bilin (neutralWindow Q R J) y y ≤
          bilin (neutralWindow Q R J) x y ^ 2 := by
  rw [← hermNegIndex_le_one_iff_forall_wells_bound (neutralWindow_symm Q R J)
    fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le]
  exact ⟨fun h => h.le, fun h => le_antisymm h (one_le_hermNegIndex_neutralWindow Q hR hRJ)⟩

/-- **A window that contains the dyadic window holds one bound state iff each of its bound
states has one sign.** -/
theorem hermNegIndex_neutralWindow_eq_one_iff_forall_bound_state_one_sign (Q : ℕ) {R J : ℕ}
    (hR : 1 ≤ R) (hRJ : R ≤ J) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 ↔
      ∀ (ψ : Fin J → ℝ) (lam : ℝ), lam < 0 → neutralWindow Q R J *ᵥ ψ = lam • ψ →
        (∀ k, 0 ≤ ψ k) ∨ ∀ k, ψ k ≤ 0 := by
  have h1 := one_le_hermNegIndex_neutralWindow Q hR hRJ
  have hiff := two_le_hermNegIndex_neutralWindow_iff_exists_sign_changing_bound_state Q R J
  constructor
  · intro h ψ lam hlam hψ
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hp, hn⟩ := hcon
    push Not at hp hn
    have := hiff.mpr ⟨ψ, lam, hlam, hψ, hn, hp⟩
    omega
  · intro h
    by_contra hne
    obtain ⟨ψ, lam, hlam, hψ, ⟨i, hi⟩, j, hj⟩ := hiff.mp (by omega)
    rcases h ψ lam hlam hψ with h0 | h0
    · linarith [h0 j]
    · linarith [h0 i]

/-! ### The Riemann hypothesis -/

/-- **The Riemann hypothesis is the Hodge index inequality on positive step packets without a
common block**: on every window `(R, R + J]` with `R ≤ J`, two such packets `x`, `y` with
`N(x, x) < 0` satisfy `N(x, x) N(y, y) ≤ N(x, y)²` for the neutral part `N`. -/
theorem riemannHypothesis_iff_forall_wells_bound :
    RiemannHypothesis ↔ ∀ Q R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      ∀ x y : Fin J → ℝ, (∀ k, 0 ≤ x k) → (∀ k, 0 ≤ y k) → (∀ k, x k * y k = 0) →
        bilin (neutralWindow Q R J) x x < 0 →
        bilin (neutralWindow Q R J) x x * bilin (neutralWindow Q R J) y y ≤
          bilin (neutralWindow Q R J) x y ^ 2 := by
  rw [riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one]
  exact forall_congr' fun Q => forall_congr' fun R => forall_congr' fun J =>
    ⟨fun h hR hRJ hQ =>
      (hermNegIndex_neutralWindow_eq_one_iff_forall_wells_bound Q hR hRJ).mp (h hR hRJ hQ),
    fun h hR hRJ hQ =>
      (hermNegIndex_neutralWindow_eq_one_iff_forall_wells_bound Q hR hRJ).mpr (h hR hRJ hQ)⟩

/-- **The Riemann hypothesis is the absence of nodes**: every eigenvector with negative
eigenvalue of the neutral part of every window `(R, R + J]` with `R ≤ J` has one sign. -/
theorem riemannHypothesis_iff_forall_bound_state_one_sign :
    RiemannHypothesis ↔ ∀ Q R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      ∀ (ψ : Fin J → ℝ) (lam : ℝ), lam < 0 → neutralWindow Q R J *ᵥ ψ = lam • ψ →
        (∀ k, 0 ≤ ψ k) ∨ ∀ k, ψ k ≤ 0 := by
  rw [riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one]
  exact forall_congr' fun Q => forall_congr' fun R => forall_congr' fun J =>
    ⟨fun h hR hRJ hQ =>
      (hermNegIndex_neutralWindow_eq_one_iff_forall_bound_state_one_sign Q hR hRJ).mp
        (h hR hRJ hQ),
    fun h hR hRJ hQ =>
      (hermNegIndex_neutralWindow_eq_one_iff_forall_bound_state_one_sign Q hR hRJ).mpr
        (h hR hRJ hQ)⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
