import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# Explicit polygamma decay away from the real axis

From the Hurwitz-series representation `ψ^{(m+1)}(z) = (−1)^m (m+1)! ζ(m+2, z)` and the trivial
lower bound `|k + z| ≥ |Im z|` one gets, for `Re z ≥ 0` and `|Im z| ≥ 1`,

  `‖ψ^{(m+1)}(z)‖ ≤ 4 (m+1)! / |Im z|^{m+1}`,

and the shift law `ψ^{(j)}(z+1) = ψ^{(j)}(z) + (−1)^j j!/z^{j+1}` extends this with constant `5` to
`Re z > −1`.  These are the derivative inputs for the height derivatives of the archimedean factor
`χ` along Levinson lines.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex

/-! ## A shifted `p`-series bound -/

/-- Telescoping bound `∑_{k<n} 1/(T+k+1)² ≤ 1/T − 1/(T+n)`. -/
theorem sum_range_inv_succ_sq_le {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (T + k + 1) ^ 2 ≤ 1 / T - 1 / (T + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : (1 : ℝ) / (T + n + 1) ^ 2 ≤ 1 / (T + n) - 1 / (T + n + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    rw [show T + ((n : ℝ) + 1) = T + n + 1 by ring]
    linarith

theorem sum_range_inv_add_sq_le {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + T) ^ 2 ≤ 1 / T ^ 2 + 1 / T := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    rw [Finset.sum_range_succ']
    have h1 := sum_range_inv_succ_sq_le hT n
    have hsum : ∑ k ∈ Finset.range n, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + T) ^ 2
        = ∑ k ∈ Finset.range n, (1 : ℝ) / (T + k + 1) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring_nf
    rw [hsum]
    simp only [Nat.cast_zero, zero_add]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ 1 / (T + n) := by positivity
    linarith

theorem summable_inv_add_sq {T : ℝ} (hT : 0 < T) :
    Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + T) ^ 2 :=
  summable_of_sum_range_le (fun k => by positivity) (sum_range_inv_add_sq_le hT)

theorem tsum_inv_add_sq_le {T : ℝ} (hT : 0 < T) :
    ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + T) ^ 2 ≤ 1 / T ^ 2 + 1 / T :=
  Real.tsum_le_of_sum_range_le (fun k => by positivity) (sum_range_inv_add_sq_le hT)

/-! ## The Hurwitz series off the real axis -/

theorem norm_natCast_add_ge_abs_im (z : ℂ) (k : ℕ) : |z.im| ≤ ‖(k : ℂ) + z‖ := by
  have := Complex.abs_im_le_norm ((k : ℂ) + z)
  simpa using this

theorem sq_norm_natCast_add_ge {z : ℂ} (hre : 0 ≤ z.re) (k : ℕ) :
    ((k : ℝ) + |z.im|) ^ 2 ≤ 2 * ‖(k : ℂ) + z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, zero_add]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + z.re) * ((k : ℝ) + z.re) := by nlinarith
  have h2 : |z.im| ^ 2 = z.im * z.im := by rw [sq_abs]; ring
  have h3 : 0 ≤ ((k : ℝ) - |z.im|) ^ 2 := sq_nonneg _
  nlinarith [abs_nonneg z.im, h1, h2, h3]

/-- Termwise bound for the Hurwitz series at integer exponent `m + 2`. -/
theorem norm_hurwitzTerm_le {m : ℕ} {z : ℂ} (hre : 0 ≤ z.re) (him : 1 ≤ |z.im|) (k : ℕ) :
    ‖((k : ℂ) + z) ^ (-((m + 2 : ℕ) : ℂ))‖
      ≤ (1 / |z.im| ^ m) * (2 * (1 / ((k : ℝ) + |z.im|) ^ 2)) := by
  have hT : (0 : ℝ) < |z.im| := by linarith
  have hnorm : |z.im| ≤ ‖(k : ℂ) + z‖ := norm_natCast_add_ge_abs_im z k
  have hpos : 0 < ‖(k : ℂ) + z‖ := lt_of_lt_of_le hT hnorm
  rw [Complex.cpow_neg, Complex.cpow_natCast, norm_inv, norm_pow]
  have hsplit : ‖(k : ℂ) + z‖ ^ (m + 2) = ‖(k : ℂ) + z‖ ^ m * ‖(k : ℂ) + z‖ ^ 2 := by ring
  rw [hsplit, mul_inv]
  have h1 : (‖(k : ℂ) + z‖ ^ m)⁻¹ ≤ 1 / |z.im| ^ m := by
    rw [one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hT.le hnorm m)
  have h2 : (‖(k : ℂ) + z‖ ^ 2)⁻¹ ≤ 2 * (1 / ((k : ℝ) + |z.im|) ^ 2) := by
    have hk : (0 : ℝ) < (k : ℝ) + |z.im| := by positivity
    have := sq_norm_natCast_add_ge hre k
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    rw [show (2 : ℝ) * (1 / ((k : ℝ) + |z.im|) ^ 2) * ‖(k : ℂ) + z‖ ^ 2
        = (2 * ‖(k : ℂ) + z‖ ^ 2) / ((k : ℝ) + |z.im|) ^ 2 by ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Hurwitz-series bound off the real axis**: `‖ζ(m+2, z)‖ ≤ 4 / |Im z|^{m+1}` for `Re z ≥ 0`,
`|Im z| ≥ 1`. -/
theorem norm_hzeta_le {m : ℕ} {z : ℂ} (hre : 0 ≤ z.re) (him : 1 ≤ |z.im|) :
    ‖HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) z‖ ≤ 4 / |z.im| ^ (m + 1) := by
  have hT : (0 : ℝ) < |z.im| := by linarith
  have hmaj : Summable fun k : ℕ => (1 / |z.im| ^ m) * (2 * (1 / ((k : ℝ) + |z.im|) ^ 2)) :=
    ((summable_inv_add_sq hT).mul_left 2).mul_left _
  have hnorm : Summable fun k : ℕ => ‖((k : ℂ) + z) ^ (-((m + 2 : ℕ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_hurwitzTerm_le hre him k) hmaj
  unfold HurwitzZetaShift.hzeta
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (hnorm.tsum_le_tsum (fun k => norm_hurwitzTerm_le hre him k) hmaj).trans ?_
  rw [tsum_mul_left, tsum_mul_left]
  have hsum := tsum_inv_add_sq_le hT
  have hT1 : 1 / |z.im| ^ 2 ≤ 1 / |z.im| := by
    rw [div_le_div_iff_of_pos_left one_pos (by positivity) hT]
    nlinarith
  have hbound : (1 / |z.im| ^ m) * (2 * ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + |z.im|) ^ 2)
      ≤ (1 / |z.im| ^ m) * (2 * (2 / |z.im|)) := by
    have h2 : (2 : ℝ) / |z.im| = 1 / |z.im| + 1 / |z.im| := by ring
    gcongr
    linarith
  refine hbound.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## Polygamma decay -/

/-- **Polygamma decay on the right half-plane**: for `Re z > 0` and `|Im z| ≥ 1`,
`‖ψ^{(m+1)}(z)‖ ≤ 4 (m+1)! / |Im z|^{m+1}`. -/
theorem norm_iteratedDeriv_digamma_le_of_re_pos {m : ℕ} {z : ℂ} (hre : 0 < z.re)
    (him : 1 ≤ |z.im|) :
    ‖iteratedDeriv (m + 1) Complex.digamma z‖ ≤ 4 * (m + 1).factorial / |z.im| ^ (m + 1) := by
  rw [polygamma_eq_hzeta m hre, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  calc ((m + 1).factorial : ℝ) * ‖HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) z‖
      ≤ ((m + 1).factorial : ℝ) * (4 / |z.im| ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left (norm_hzeta_le hre.le him) (by positivity)
    _ = _ := by ring

/-- **Polygamma decay for `Re z > −1`**, with constant `5`, via the shift law. -/
theorem norm_iteratedDeriv_digamma_le {m : ℕ} {z : ℂ} (hre : -1 < z.re) (him : 1 ≤ |z.im|) :
    ‖iteratedDeriv (m + 1) Complex.digamma z‖ ≤ 5 * (m + 1).factorial / |z.im| ^ (m + 1) := by
  have hT : (0 : ℝ) < |z.im| := by linarith
  rcases lt_or_ge 0 z.re with hpos | hnonpos
  · refine (norm_iteratedDeriv_digamma_le_of_re_pos hpos him).trans ?_
    gcongr
    norm_num
  · have hz : ∀ p : ℕ, z ≠ -(p : ℂ) := by
      intro p h
      have := congrArg Complex.im h
      simp at this
      rw [this, abs_zero] at him
      linarith
    have hshift := digammaJet_shift (m + 1) hz
    have hre1 : 0 < (z + 1).re := by simp; linarith
    have him1 : 1 ≤ |(z + 1).im| := by simpa using him
    have h1 := norm_iteratedDeriv_digamma_le_of_re_pos (m := m) hre1 him1
    have him1' : |(z + 1).im| = |z.im| := by simp
    rw [him1'] at h1
    have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hzpow : |z.im| ^ (m + 2) ≤ ‖z‖ ^ (m + 2) := pow_le_pow_left₀ hT.le hzn _
    have hterm : ‖(-1 : ℂ) ^ (m + 1) * ((m + 1).factorial : ℂ) / z ^ (m + 2)‖
        ≤ (m + 1).factorial / |z.im| ^ (m + 1) := by
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
        Complex.norm_natCast]
      have hz0' : 0 < ‖z‖ := lt_of_lt_of_le hT hzn
      have hz0 : 0 < ‖z‖ ^ (m + 2) := pow_pos hz0' _
      rw [div_le_div_iff₀ hz0 (by positivity)]
      have : |z.im| ^ (m + 1) ≤ |z.im| ^ (m + 2) := by
        exact pow_le_pow_right₀ him (by omega)
      have hf : (0 : ℝ) ≤ (m + 1).factorial := by positivity
      nlinarith
    have heq : iteratedDeriv (m + 1) Complex.digamma z
        = iteratedDeriv (m + 1) Complex.digamma (z + 1)
          - (-1 : ℂ) ^ (m + 1) * ((m + 1).factorial : ℂ) / z ^ (m + 2) := by
      rw [hshift]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add h1 hterm).trans (le_of_eq ?_)
    ring

end GaloisForLFunctions.HTGeometry

end
