import GaloisForLFunctions.HTGeometry.ThreePointVerticalAverageStripFailure

/-!
# Vertical averages: the extremal balance condition for the energy law

For weights `w_i ≥ 0` and real shifts `x_i` the vertical average of a real polynomial is
`A p (z) = Σ_i w_i p(z + i x_i)`; for a probability law `X` (`P(X = x_i) = w_i`) this is
`E p(z + iX)`.  The energy law with budget `m = E X²` asks that the squared heights of the upper
roots of `A p` be weakly submajorized by `(y_j² − m)_+`, where `y_j` are the root heights of `p`.
In particular it asks that `A (X² + m)ⁿ` be real-rooted, since every root of `(X² + m)ⁿ` has
squared height exactly `m` (`pairPower_root`).

* **Odd-moment obstruction** (`exists_verticalAverage_root_im_pos`).  On the imaginary axis
  `A (X² + m)ⁿ (iv) = Σ_i w_i (m − (v + x_i)²)ⁿ`.  For odd `n` this is negative for large `v`, so
  if the odd moment `E (m − X²)ⁿ` is positive the average has a root `iv` with `v > 0`.
* **Extremal balance** (`exists_odd_pos_moment_of_extremal`,
  `exists_verticalAverage_root_of_extremal`).  If some atom `x_j` with `w_j > 0` has
  `m − x_j² > x_i² − m` for every `i`, i.e. `min X² + max X² < 2m` with the minimum charged, then the
  odd moments `E (m − X²)ⁿ` are positive for all large odd `n`, so the energy law fails.

Hence every law obeying the energy law satisfies the balance `min X² + max X² ≥ 2 E X²` (the
minimum over charged atoms).  The Rademacher pairs `aε₁ + bε₂` meet it with equality
(`(a + b)² + (a − b)² = 2(a² + b²)`), and an atom at `0` forces `max X² ≥ 2 E X²`.  For the
three-point law `P(X = 0) = 1 − μ`, `P(X = ±1) = μ/2` the balance reads `μ ≤ 1/2`, which with
the Laguerre–Pólya condition `μ ≥ 1/2` leaves exactly the Rademacher sum `μ = 1/2` besides `μ = 1`.
-/

open Polynomial Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : ℕ}

/-- The vertical average `Σ_i w_i p(z + i x_i)` of a real polynomial. -/
def verticalAverage (w x : Fin k → ℝ) (p : ℝ[X]) : ℂ[X] :=
  ∑ i, C (w i : ℂ) * (p.map ofRealHom).comp (X + C ((x i : ℂ) * I))

/-- The power `(X² + m)ⁿ`. -/
def pairPower (m : ℝ) (n : ℕ) : ℝ[X] := (X ^ 2 + C m) ^ n

/-- **Every root of `(X² + m)ⁿ` has squared height `m`.** -/
theorem pairPower_root {m : ℝ} (hm : 0 < m) {n : ℕ} {z : ℂ}
    (hz : ((pairPower m n).map ofRealHom).eval z = 0) : z.re = 0 ∧ z.im ^ 2 = m := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp [pairPower] at hz
  simp only [pairPower, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_X, eval_pow, eval_add, eval_X, eval_C, pow_eq_zero_iff hn] at hz
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp [pow_two] at h1 h2
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp (by linarith : z.re * z.im * 2 = 0) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · rw [h'] at h1; nlinarith [sq_nonneg z.re]
    · norm_num at h
  refine ⟨hre, ?_⟩
  rw [hre] at h1
  nlinarith

/-- The average on the imaginary axis. -/
theorem eval_verticalAverage_pairPower (w x : Fin k → ℝ) (m : ℝ) (n : ℕ) (v : ℝ) :
    (verticalAverage w x (pairPower m n)).eval ((v : ℂ) * I) =
      ((∑ i, w i * (m - (v + x i) ^ 2) ^ n : ℝ) : ℂ) := by
  simp only [verticalAverage, pairPower, eval_finsetSum, eval_mul, eval_C, eval_comp,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, eval_pow,
    eval_add, eval_X, ofRealHom_eq_coe]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  linear_combination ((v : ℂ) + (x i : ℂ)) ^ 2 * I_sq

/-- **Odd-moment obstruction.**  If `n` is odd and `Σ_i w_i (m − x_i²)ⁿ > 0`, the vertical average
of `(X² + m)ⁿ` has a root `iv` with `v > 0`. -/
theorem exists_verticalAverage_root_im_pos (w x : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (m : ℝ)
    {n : ℕ} (hn : Odd n) (hpos : 0 < ∑ i, w i * (m - x i ^ 2) ^ n) :
    ∃ v : ℝ, 0 < v ∧ (verticalAverage w x (pairPower m n)).eval ((v : ℂ) * I) = 0 := by
  set f : ℝ → ℝ := fun v => ∑ i, w i * (m - (v + x i) ^ 2) ^ n with hf
  set V : ℝ := |m| + 1 + ∑ i, |x i| with hV
  have hVpos : 0 ≤ V := by positivity
  have hterm : ∀ i, m - (V + x i) ^ 2 < 0 := by
    intro i
    have hxi : |x i| ≤ ∑ j, |x j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    have h1 : |m| + 1 ≤ V + x i := by
      have := neg_abs_le (x i); linarith
    have h2 : (|m| + 1) ^ 2 ≤ (V + x i) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith [le_abs_self m, abs_nonneg m]
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra h
    push Not at h
    have : ∑ i, w i * (m - x i ^ 2) ^ n = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [le_antisymm (h i) (hw i), zero_mul]
    linarith
  have hfV : f V < 0 := by
    have hsum : 0 < ∑ i, -(w i * (m - (V + x i) ^ 2) ^ n) := by
      refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
      · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hw i) (hn.pow_neg (hterm i)).le)
      · exact neg_pos.mpr (mul_neg_of_pos_of_neg hj (hn.pow_neg (hterm j)))
    rw [Finset.sum_neg_distrib] at hsum
    simp only [hf]
    linarith
  have hf0 : 0 < f 0 := by simpa [hf] using hpos
  have hcont : ContinuousOn f (Set.Icc 0 V) := by
    simp only [hf]; fun_prop
  obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hVpos hcont ⟨hfV.le, hf0.le⟩
  have hvne : v ≠ 0 := by rintro rfl; linarith
  refine ⟨v, lt_of_le_of_ne hv.1 (Ne.symm hvne), ?_⟩
  rw [eval_verticalAverage_pairPower]
  have : (∑ i, w i * (m - (v + x i) ^ 2) ^ n) = 0 := hv0
  rw [this, Complex.ofReal_zero]

/-- **Extremal balance: large odd moments are positive.**  If `w_j > 0`, `a_j > 0` and every
`−a_i < a_j`, then `Σ_i w_i a_iⁿ > 0` for some odd `n`. -/
theorem exists_odd_pos_moment_of_extremal (w a : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (j : Fin k)
    (hwj : 0 < w j) (haj : 0 < a j) (hdom : ∀ i, -a i < a j) :
    ∃ n, Odd n ∧ 0 < ∑ i, w i * a i ^ n := by
  set c : ℝ := Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ (fun i => max (-a i) 0) with hc
  have hc0 : 0 ≤ c := le_trans (le_max_right _ _) (Finset.le_sup' (fun i => max (-a i) 0)
    (Finset.mem_univ j))
  have hcj : c < a j := by
    rw [hc, Finset.sup'_lt_iff]
    intro i _
    exact max_lt (hdom i) haj
  have hci : ∀ i, -a i ≤ c := fun i =>
    le_trans (le_max_left _ _) (Finset.le_sup' (fun i => max (-a i) 0) (Finset.mem_univ i))
  set W : ℝ := ∑ i, w i with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => hw i
  have hr0 : 0 ≤ c / a j := div_nonneg hc0 haj.le
  have hr1 : c / a j < 1 := (div_lt_one haj).mpr hcj
  have hlim : Tendsto (fun n : ℕ => W * (c / a j) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul W
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hlim.eventually (gt_mem_nhds hwj)))
  refine ⟨2 * N + 1, odd_two_mul_add_one N, ?_⟩
  set n := 2 * N + 1 with hn
  have hodd : Odd n := odd_two_mul_add_one N
  have hsmall : W * (c / a j) ^ n < w j := hN n (by omega)
  -- each term is at least `−w_i cⁿ`
  have hlow : ∀ i, -(w i * c ^ n) ≤ w i * a i ^ n := by
    intro i
    rcases le_or_gt 0 (a i) with h | h
    · have : 0 ≤ w i * a i ^ n := mul_nonneg (hw i) (pow_nonneg h n)
      have : 0 ≤ w i * c ^ n := mul_nonneg (hw i) (pow_nonneg hc0 n)
      linarith
    · have h1 : (-a i) ^ n ≤ c ^ n := pow_le_pow_left₀ (by linarith) (hci i) n
      have h2 : a i ^ n = -(-a i) ^ n := by rw [hodd.neg_pow, neg_neg]
      rw [h2]
      nlinarith [hw i]
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => w i * a i ^ n) (Finset.mem_univ j)
  have hrest : -(W * c ^ n) ≤ ∑ i ∈ Finset.univ.erase j, w i * a i ^ n := by
    have h1 : -(∑ i ∈ Finset.univ.erase j, w i * c ^ n) ≤
        ∑ i ∈ Finset.univ.erase j, w i * a i ^ n := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun i _ => hlow i
    have h2 : ∑ i ∈ Finset.univ.erase j, w i * c ^ n ≤ W * c ^ n := by
      rw [hW, Finset.sum_mul]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j _)
        fun i _ _ => mul_nonneg (hw i) (pow_nonneg hc0 n)
    linarith
  have hpow : W * c ^ n < w j * a j ^ n := by
    have hajn : 0 < a j ^ n := pow_pos haj n
    have : W * (c / a j) ^ n * a j ^ n < w j * a j ^ n := mul_lt_mul_of_pos_right hsmall hajn
    rwa [div_pow, mul_assoc, div_mul_cancel₀ _ hajn.ne'] at this
  rw [← hsplit]
  linarith

/-- **Extremal balance for vertical averages.**  If an atom `x_j` with `w_j > 0` has
`m − x_j² > 0` and `x_i² − m < m − x_j²` for all `i`, some odd power `(X² + m)ⁿ` has a vertical
average with a root `iv`, `v > 0`. -/
theorem exists_verticalAverage_root_of_extremal (w x : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (m : ℝ)
    (j : Fin k) (hwj : 0 < w j) (hxj : x j ^ 2 < m) (hbal : ∀ i, x i ^ 2 - m < m - x j ^ 2) :
    ∃ n, Odd n ∧ ∃ v : ℝ, 0 < v ∧ (verticalAverage w x (pairPower m n)).eval ((v : ℂ) * I) = 0 := by
  obtain ⟨n, hn, hpos⟩ := exists_odd_pos_moment_of_extremal w (fun i => m - x i ^ 2) hw j hwj
    (by linarith) (fun i => by have := hbal i; linarith)
  exact ⟨n, hn, exists_verticalAverage_root_im_pos w x hw m hn hpos⟩

/-- **An atom at the origin forces `max X² ≥ 2m`.**  If `w_j > 0` at `x_j = 0`, `m > 0`, and every
`x_i² < 2m`, some odd power `(X² + m)ⁿ` has a vertical average with a root `iv`, `v > 0`. -/
theorem exists_verticalAverage_root_of_atom_zero (w x : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) {m : ℝ}
    (hm : 0 < m) (j : Fin k) (hwj : 0 < w j) (hxj : x j = 0) (hmax : ∀ i, x i ^ 2 < 2 * m) :
    ∃ n, Odd n ∧ ∃ v : ℝ, 0 < v ∧ (verticalAverage w x (pairPower m n)).eval ((v : ℂ) * I) = 0 :=
  exists_verticalAverage_root_of_extremal w x hw m j hwj (by rw [hxj]; linarith)
    fun i => by rw [hxj]; linarith [hmax i]

end

end GaloisForLFunctions.HTGeometry
