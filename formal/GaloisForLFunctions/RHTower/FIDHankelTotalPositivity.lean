import GaloisForLFunctions.HTGeometry.CauchyBinet
import GaloisForLFunctions.HTGeometry.GeneralizedVandermondePositive

/-!
# The shifted FID Hankel matrix is strictly Hankel totally positive

The FID node `PS12` gives `ζ(2k+3) = Σ_{n ≥ 1} n^{-3} (n^{-2})^k`, so the shifted Hankel matrix
`H[i,j] = ζ(2(i+j)+3)` is the moment matrix of the **integer divisor**
`μ = Σ_{n ≥ 1} n^{-3} δ_{n^{-2}}`.  This file proves that *every* minor of `H` with strictly
increasing row and column indices is strictly positive — the all-minor strengthening of the retired
"FID Hankel PSD ⟹ RH" bridge, and hence a negative control: even the strict total-positivity
certificate is automatic from the integer divisor and carries no RH content.

The proof is the one the card records: Cauchy–Binet applied to the truncation
`H_N = A_N · B_N` (`CauchyBinet`, in the permutation-symmetrised form that avoids increasing
enumerations), each Cauchy–Binet term being a product of two **generalized Vandermonde**
determinants on the same ordered support points, hence positive
(`GeneralizedVandermondePositive`); the truncated determinants are therefore positive and
nondecreasing along the truncation (adding support points only adds nonnegative terms), and the
determinant is continuous in the entries, so the limiting minor is at least the `N = m` truncation,
which is already strictly positive.

## Main results

* `fidHankel` — the entry `ζ(2(i+j)+3)`, with `fidHankel_eq_riemannZeta`;
* `det_fidTrunc_pos`, `det_fidTrunc_ge` — the truncated minors are positive and nondecreasing;
* `det_fidHankel_pos` — **every shifted minor is strictly positive**.
-/

namespace GaloisForLFunctions

open Matrix Finset

/-! ### The FID moment data -/

/-- The FID node `x_n = (1/(n+1))^(2 : ℕ)`. -/
noncomputable def fidNode (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) ^ (2 : ℕ)

/-- The FID weight `w_n = (1/(n+1))^(3 : ℕ)`. -/
noncomputable def fidWeight (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) ^ (3 : ℕ)

theorem fidNode_pos (n : ℕ) : 0 < fidNode n := by
  rw [fidNode]
  positivity

theorem fidWeight_pos (n : ℕ) : 0 < fidWeight n := by
  rw [fidWeight]
  positivity

theorem fidNode_strictAnti : StrictAnti fidNode := by
  intro i j hij
  rw [fidNode, fidNode]
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h2 : ((i : ℝ) + 1) < ((j : ℝ) + 1) := by
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  have h3 : 1 / ((j : ℝ) + 1) < 1 / ((i : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt h1 h2
  have h4 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  exact pow_lt_pow_left₀ h3 h4.le (by norm_num)

theorem fidNode_injective : Function.Injective fidNode := fidNode_strictAnti.injective

theorem fidWeight_mul_fidNode_pow (n k : ℕ) :
    fidWeight n * (fidNode n) ^ k = (1 / ((n : ℝ) + 1)) ^ (2 * k + 3) := by
  rw [fidWeight, fidNode, ← pow_mul, ← pow_add]
  ring_nf

theorem summable_fidMoment (k : ℕ) : Summable (fun n : ℕ => fidWeight n * (fidNode n) ^ k) := by
  have hEq : ∀ n : ℕ, fidWeight n * (fidNode n) ^ k = 1 / ((n : ℝ) + 1) ^ (2 * k + 3) := by
    intro n
    rw [fidWeight_mul_fidNode_pow, div_pow, one_pow]
  rw [summable_congr hEq]
  have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 3)) := by
    rw [Real.summable_one_div_nat_pow]
    omega
  exact (summable_nat_add_iff 1).mpr h1 |>.congr (fun n => by push_cast; ring_nf)

/-- The shifted FID Hankel entry, the moment `∫ x^{i+j}` of the FID divisor — equal to
`ζ(2(i+j)+3)`. -/
noncomputable def fidHankel (i j : ℕ) : ℝ := ∑' n : ℕ, fidWeight n * (fidNode n) ^ (i + j)

/-! ### Generalized Vandermonde pairs on unordered nodes -/

theorem det_genVandermonde_eq_zero_of_not_injective {m : ℕ} (s : Fin m → ℕ) {u : Fin m → ℝ}
    (hu : ¬ Function.Injective u) : (genVandermonde s u).det = 0 := by
  rw [Function.not_injective_iff] at hu
  obtain ⟨i, j, hij, hne⟩ := hu
  refine Matrix.det_zero_of_column_eq hne ?_
  intro a
  simp only [genVandermonde, Matrix.of_apply, hij]

theorem det_genVandermonde_mul_pos {m : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r)
    (hc : StrictMono c) {u : Fin m → ℝ} (hupos : ∀ l, 0 < u l)
    (huinj : Function.Injective u) :
    0 < (genVandermonde r u).det * (genVandermonde c u).det := by
  classical
  set τ := Tuple.sort u with hτ
  have hmono : StrictMono (u ∘ (τ : Fin m → Fin m)) :=
    (Tuple.monotone_sort u).strictMono_of_injective (huinj.comp τ.injective)
  have hpos' : ∀ l, 0 < (u ∘ (τ : Fin m → Fin m)) l := fun l => hupos _
  have hgv : ∀ s : Fin m → ℕ, genVandermonde s (u ∘ (τ : Fin m → Fin m))
      = (genVandermonde s u).submatrix id (τ : Fin m → Fin m) := fun s => rfl
  have hrd : (genVandermonde r (u ∘ (τ : Fin m → Fin m))).det
      = ((Equiv.Perm.sign τ : ℤ) : ℝ) * (genVandermonde r u).det := by
    rw [hgv, Matrix.det_permute']
  have hcd : (genVandermonde c (u ∘ (τ : Fin m → Fin m))).det
      = ((Equiv.Perm.sign τ : ℤ) : ℝ) * (genVandermonde c u).det := by
    rw [hgv, Matrix.det_permute']
  have hprod := mul_pos (det_genVandermonde_pos m r _ hr hmono hpos')
    (det_genVandermonde_pos m c _ hc hmono hpos')
  rw [hrd, hcd] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] at hprod <;> simpa using hprod

/-! ### The truncated FID moment matrix and Cauchy–Binet -/

/-- The weighted node matrix of the truncated FID divisor. -/
noncomputable def fidA (m N : ℕ) (r : Fin m → ℕ) : Matrix (Fin m) (Fin N) ℝ :=
  Matrix.of fun a n => fidWeight (n : ℕ) * (fidNode (n : ℕ)) ^ (r a)

/-- The node matrix of the truncated FID divisor. -/
noncomputable def fidB (m N : ℕ) (c : Fin m → ℕ) : Matrix (Fin N) (Fin m) ℝ :=
  Matrix.of fun n b => (fidNode (n : ℕ)) ^ (c b)

theorem fidA_mul_fidB_apply (m N : ℕ) (r c : Fin m → ℕ) (a b : Fin m) :
    (fidA m N r * fidB m N c) a b
      = ∑ n ∈ Finset.range N, fidWeight n * (fidNode n) ^ (r a + c b) := by
  rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
    (fun n => fidWeight n * (fidNode n) ^ (r a + c b)) N]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [fidA, fidB, Matrix.of_apply]
  rw [pow_add]
  ring

theorem det_fidA_submatrix {m N : ℕ} (r : Fin m → ℕ) (f : Fin m → Fin N) :
    ((fidA m N r).submatrix id f).det
      = (∏ l, fidWeight (f l : ℕ)) *
        (genVandermonde r (fun l => fidNode (f l : ℕ))).det := by
  have h : (fidA m N r).submatrix id f
      = Matrix.of fun a l => fidWeight (f l : ℕ) *
        (genVandermonde r (fun l => fidNode (f l : ℕ))) a l := by
    ext a l
    simp only [Matrix.submatrix_apply, id_eq, fidA, genVandermonde, Matrix.of_apply]
  rw [h, Matrix.det_mul_row]

theorem det_fidB_submatrix {m N : ℕ} (c : Fin m → ℕ) (f : Fin m → Fin N) :
    ((fidB m N c).submatrix f id).det = (genVandermonde c (fun l => fidNode (f l : ℕ))).det := by
  have h : (fidB m N c).submatrix f id = (genVandermonde c (fun l => fidNode (f l : ℕ)))ᵀ := by
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, fidB, genVandermonde, Matrix.of_apply,
      Matrix.transpose_apply]
  rw [h, Matrix.det_transpose]

theorem fid_term_nonneg {m N : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r) (hc : StrictMono c)
    (f : Fin m → Fin N) :
    0 ≤ ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det := by
  rw [det_fidA_submatrix, det_fidB_submatrix]
  by_cases hf : Function.Injective (fun l => fidNode (f l : ℕ))
  · have hpos : 0 < (genVandermonde r (fun l => fidNode (f l : ℕ))).det *
        (genVandermonde c (fun l => fidNode (f l : ℕ))).det :=
      det_genVandermonde_mul_pos r c hr hc (fun l => fidNode_pos _) hf
    have hw : 0 < ∏ l, fidWeight (f l : ℕ) :=
      Finset.prod_pos fun l _ => fidWeight_pos _
    nlinarith
  · rw [det_genVandermonde_eq_zero_of_not_injective r hf, mul_zero, zero_mul]

theorem fid_term_pos {m N : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r) (hc : StrictMono c)
    {f : Fin m → Fin N} (hf : Function.Injective f) :
    0 < ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det := by
  rw [det_fidA_submatrix, det_fidB_submatrix]
  have hu : Function.Injective (fun l => fidNode (f l : ℕ)) := by
    intro i j hij
    exact hf (Fin.val_injective (fidNode_injective hij))
  have hpos : 0 < (genVandermonde r (fun l => fidNode (f l : ℕ))).det *
      (genVandermonde c (fun l => fidNode (f l : ℕ))).det :=
    det_genVandermonde_mul_pos r c hr hc (fun l => fidNode_pos _) hu
  have hw : 0 < ∏ l, fidWeight (f l : ℕ) := Finset.prod_pos fun l _ => fidWeight_pos _
  nlinarith

/-! ### Strict positivity of every shifted minor -/

theorem factorial_mul_det_fid (m N : ℕ) (r c : Fin m → ℕ) :
    ((Nat.factorial m : ℕ) : ℝ) * (fidA m N r * fidB m N c).det
      = ∑ f : Fin m → Fin N,
        ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det :=
  factorial_mul_det_mul _ _

theorem det_fidTrunc_pos {m N : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r) (hc : StrictMono c)
    (hN : m ≤ N) : 0 < (fidA m N r * fidB m N c).det := by
  classical
  have hcast : Function.Injective (fun a : Fin m => Fin.castLE hN a) := by
    intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  have hsum : 0 < ∑ f : Fin m → Fin N,
      ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det :=
    lt_of_lt_of_le (fid_term_pos r c hr hc hcast)
      (Finset.single_le_sum (fun f _ => fid_term_nonneg r c hr hc f) (Finset.mem_univ _))
  rw [← factorial_mul_det_fid] at hsum
  have hfac : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  nlinarith

theorem det_fidTrunc_ge {m N : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r) (hc : StrictMono c)
    (hN : m ≤ N) : (fidA m m r * fidB m m c).det ≤ (fidA m N r * fidB m N c).det := by
  classical
  have hinj : Function.Injective
      (fun f : Fin m → Fin m => (fun l => Fin.castLE hN (f l))) := by
    intro f g h
    funext l
    have hl := congrFun h l
    exact Fin.ext (by simpa using congrArg Fin.val hl)
  have hmap : ∀ f : Fin m → Fin m,
      ((fidA m N r).submatrix id (fun l => Fin.castLE hN (f l))).det
          * ((fidB m N c).submatrix (fun l => Fin.castLE hN (f l)) id).det
        = ((fidA m m r).submatrix id f).det * ((fidB m m c).submatrix f id).det := by
    intro f
    have hA : (fidA m N r).submatrix id (fun l => Fin.castLE hN (f l))
        = (fidA m m r).submatrix id f := by
      ext a l
      simp only [Matrix.submatrix_apply, id_eq, fidA, Matrix.of_apply, Fin.val_castLE]
    have hB : (fidB m N c).submatrix (fun l => Fin.castLE hN (f l)) id
        = (fidB m m c).submatrix f id := by
      ext a b
      simp only [Matrix.submatrix_apply, id_eq, fidB, Matrix.of_apply, Fin.val_castLE]
    rw [hA, hB]
  have h1 : ∑ f ∈ Finset.univ.image (fun f : Fin m → Fin m => (fun l => Fin.castLE hN (f l))),
      ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det
      ≤ ∑ f : Fin m → Fin N,
        ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => fid_term_nonneg r c hr hc i)
  have h2 : ∑ f ∈ Finset.univ.image (fun f : Fin m → Fin m => (fun l => Fin.castLE hN (f l))),
      ((fidA m N r).submatrix id f).det * ((fidB m N c).submatrix f id).det
      = ∑ f : Fin m → Fin m,
        ((fidA m m r).submatrix id f).det * ((fidB m m c).submatrix f id).det := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    exact Finset.sum_congr rfl fun f _ => hmap f
  rw [h2] at h1
  rw [← factorial_mul_det_fid, ← factorial_mul_det_fid] at h1
  have hfac : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  exact le_of_mul_le_mul_left h1 hfac

theorem tendsto_fidTrunc {m : ℕ} (r c : Fin m → ℕ) :
    Filter.Tendsto (fun N => (fidA m N r * fidB m N c))
      Filter.atTop (nhds (Matrix.of fun a b => fidHankel (r a) (c b))) := by
  refine tendsto_pi_nhds.mpr fun a => ?_
  refine tendsto_pi_nhds.mpr fun b => ?_
  simp only [fidA_mul_fidB_apply]
  exact (summable_fidMoment (r a + c b)).hasSum.tendsto_sum_nat

/-- **The shifted FID Hankel matrix is strictly Hankel totally positive.**  Every minor with
strictly increasing row and column indices `r`, `c` is strictly positive.  Since
`fidHankel i j = ζ(2(i+j)+3)`, this is the all-minor negative control for the FID certificate: the
whole shifted Hankel total positivity is automatic from the integer divisor
`Σ_{n ≥ 1} n^{-3} δ_{n^{-2}}` and carries no RH content. -/
theorem det_fidHankel_pos {m : ℕ} (r c : Fin m → ℕ) (hr : StrictMono r) (hc : StrictMono c) :
    0 < (Matrix.of fun a b => fidHankel (r a) (c b)).det := by
  have hlim : Filter.Tendsto (fun N => (fidA m N r * fidB m N c).det) Filter.atTop
      (nhds (Matrix.of fun a b => fidHankel (r a) (c b)).det) :=
    ((Continuous.matrix_det continuous_id).tendsto _).comp (tendsto_fidTrunc r c)
  refine lt_of_lt_of_le (det_fidTrunc_pos r c hr hc (le_refl m)) ?_
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop m] with N hN
  exact det_fidTrunc_ge r c hr hc hN

/-! ### The entries are the odd zeta values -/

/-- **The FID Hankel entry is `ζ(2(i+j)+3)`.** -/
theorem fidHankel_eq_riemannZeta (i j : ℕ) :
    riemannZeta ((2 * (i + j) + 3 : ℕ) : ℂ) = (fidHankel i j : ℂ) := by
  have hre : 1 < ((((2 * (i + j) + 3 : ℕ)) : ℂ)).re := by
    rw [Complex.natCast_re]
    have : (1 : ℝ) < ((2 * (i + j) + 3 : ℕ) : ℝ) := by
      have : (3 : ℝ) ≤ ((2 * (i + j) + 3 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 3 (2 * (i + j))
      linarith
    exact this
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (((2 * (i + j) + 3 : ℕ)) : ℂ)
      = ((fidWeight n * (fidNode n) ^ (i + j) : ℝ) : ℂ) := by
    intro n
    rw [Complex.cpow_natCast, fidWeight_mul_fidNode_pow]
    push_cast
    rw [div_pow, one_pow]
  rw [tsum_congr hterm, fidHankel]
  exact (Complex.ofReal_tsum _).symm

end GaloisForLFunctions
