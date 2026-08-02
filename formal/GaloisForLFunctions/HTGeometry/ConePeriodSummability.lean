import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import Mathlib.Analysis.PSeries
import GaloisForLFunctions.HTGeometry.WeierstrassGenusFactor

/-!
# Summability over the period cone at the critical exponent

A Barnes period frame lies in a common open half-plane.  Taking the imaginary part as the
half-plane functional, the value of the frame on a nonzero exponent vector has modulus at least a
positive multiple of the exponent sum, so the cone values grow at least linearly in the total
degree.

The number of exponent vectors of a given total degree grows polynomially of order one less than
the number of directions, so the inverse cone values are summable at the exponent `N + 1`, one
above the critical one.  That is exactly the exponent at which the regularized Barnes series
converges: the `N`-fold subtraction of the expansion of `1/(z + w)` in powers of `1/w` leaves a
term of size `|z|^N / |w|^{N+1}`.

The proof compares with a product of one-dimensional series: the product of the shifted exponents
is at most the `N`-th power of the shifted total degree, so raising to the power `(N+1)/N` turns
the cone majorant into a finite product of convergent `p`-series with `p = 1 + 1/N`.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## The cone value of an exponent vector -/

/-- The value of a period frame on an exponent vector. -/
def conePeriod (ω : ι → ℂ) (n : ι → ℕ) : ℂ := ∑ i, (n i : ℂ) * ω i

theorem exists_pos_le_im (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ (ω i).im := by
  classical
  refine ⟨Finset.univ.inf' Finset.univ_nonempty fun i => (ω i).im, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun i _ => hω i
  · exact fun i => Finset.inf'_le _ (Finset.mem_univ i)

omit [Nonempty ι] in
theorem im_conePeriod (ω : ι → ℂ) (n : ι → ℕ) :
    (conePeriod ω n).im = ∑ i, (n i : ℝ) * (ω i).im := by
  rw [conePeriod, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_im]
  simp

omit [Nonempty ι] in
/-- **Linear growth of the cone.**  On a frame in the open upper half-plane the cone value is at
least a fixed multiple of the total degree. -/
theorem mul_sum_le_norm_conePeriod {δ : ℝ} (ω : ι → ℂ) (hδ : ∀ i, δ ≤ (ω i).im)
    (n : ι → ℕ) : δ * ∑ i, (n i : ℝ) ≤ ‖conePeriod ω n‖ := by
  calc δ * ∑ i, (n i : ℝ) = ∑ i, (n i : ℝ) * δ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ ∑ i, (n i : ℝ) * (ω i).im :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hδ i) (Nat.cast_nonneg _)
    _ = (conePeriod ω n).im := (im_conePeriod ω n).symm
    _ ≤ |(conePeriod ω n).im| := le_abs_self _
    _ ≤ ‖conePeriod ω n‖ := Complex.abs_im_le_norm _

/-! ## The comparison series -/

theorem one_lt_coneExponent : (1 : ℝ) < 1 + 1 / (Fintype.card ι : ℝ) := by
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
  linarith

theorem summable_succ_rpow_neg :
    Summable fun m : ℕ => ((m : ℝ) + 1) ^ (-(1 + 1 / (Fintype.card ι : ℝ))) := by
  have hbase : Summable fun m : ℕ =>
      (((m : ℝ)) ^ (1 + 1 / (Fintype.card ι : ℝ)))⁻¹ :=
    Iff.mpr Real.summable_nat_rpow_inv (one_lt_coneExponent (ι := ι))
  have hshift := (summable_nat_add_iff (G := ℝ) 1).mpr hbase
  refine hshift.congr fun m => ?_
  rw [Real.rpow_neg (by positivity)]
  norm_num

theorem summable_prod_succ_rpow_neg :
    Summable fun n : ι → ℕ =>
      ∏ i, ((n i : ℝ) + 1) ^ (-(1 + 1 / (Fintype.card ι : ℝ))) := by
  refine summable_fintype_pi_product_of_nonneg ι
    (fun _ m => ((m : ℝ) + 1) ^ (-(1 + 1 / (Fintype.card ι : ℝ))))
    (fun _ => summable_succ_rpow_neg) (fun _ m => ?_)
  positivity

/-! ## The critical-exponent summability -/

omit [Nonempty ι] in
theorem prod_succ_le_pow (n : ι → ℕ) :
    ∏ i, ((n i : ℝ) + 1) ≤ (1 + ∑ i, (n i : ℝ)) ^ Fintype.card ι := by
  classical
  calc ∏ i, ((n i : ℝ) + 1) ≤ ∏ _i : ι, (1 + ∑ k, (n k : ℝ)) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        have hle : (n i : ℝ) ≤ ∑ k, (n k : ℝ) :=
          Finset.single_le_sum (f := fun k => (n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
            (Finset.mem_univ i)
        linarith
    _ = (1 + ∑ k, (n k : ℝ)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]

/-- **Cone summability at the critical exponent.**  For a period frame in the open upper
half-plane the inverse cone values are summable at the exponent one above the number of
directions. -/
theorem summable_conePeriod_inv_pow (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    Summable fun n : ι → ℕ =>
      if n = 0 then 0 else (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_im ω hω
  set N : ℕ := Fintype.card ι with hN
  set t : ℝ := 1 + 1 / (N : ℝ) with ht
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Fintype.card_pos
  have hNt : (N : ℝ) * t = (N : ℝ) + 1 := by
    rw [ht]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_prod_succ_rpow_neg (ι := ι)).mul_left ((2 / δ) ^ (N + 1)))
  · split_ifs with h
    · exact le_rfl
    · positivity
  · split_ifs with hzero
    · have hnn : (0 : ℝ) ≤ ∏ i, ((n i : ℝ) + 1) ^ (-t) := by positivity
      have h2 : (0 : ℝ) ≤ (2 / δ) ^ (N + 1) := by positivity
      exact mul_nonneg h2 hnn
    -- the nonzero exponent vectors
    obtain ⟨i₀, hi₀⟩ : ∃ i, n i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hzero (funext fun i => hcon i)
    have hone : (1 : ℝ) ≤ ∑ i, (n i : ℝ) := by
      have hle : (n i₀ : ℝ) ≤ ∑ k, (n k : ℝ) :=
        Finset.single_le_sum (f := fun k => (n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
          (Finset.mem_univ i₀)
      have : (1 : ℝ) ≤ (n i₀ : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
      linarith
    set s : ℝ := ∑ i, (n i : ℝ) with hs
    have hspos : (0 : ℝ) < s := lt_of_lt_of_le one_pos hone
    have hhalf : δ / 2 * (1 + s) ≤ δ * s := by nlinarith
    have hnorm : δ / 2 * (1 + s) ≤ ‖conePeriod ω n‖ :=
      le_trans hhalf (mul_sum_le_norm_conePeriod ω hδ n)
    have hpos : (0 : ℝ) < δ / 2 * (1 + s) := by positivity
    -- compare the powers
    have hpow : (δ / 2 * (1 + s)) ^ (N + 1) ≤ ‖conePeriod ω n‖ ^ (N + 1) :=
      pow_le_pow_left₀ hpos.le hnorm _
    have hinv : (‖conePeriod ω n‖ ^ (N + 1))⁻¹ ≤ ((δ / 2) ^ (N + 1) * (1 + s) ^ (N + 1))⁻¹ := by
      rw [← mul_pow]
      exact inv_anti₀ (by positivity) hpow
    refine le_trans hinv ?_
    rw [mul_inv, ← inv_pow]
    have hrewrite : (δ / 2 : ℝ)⁻¹ = 2 / δ := inv_div _ _
    rw [hrewrite]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- the product majorant
    have hprodle : ∏ i, ((n i : ℝ) + 1) ≤ (1 + s) ^ N := prod_succ_le_pow n
    have hbasepos : (0 : ℝ) < 1 + s := by linarith
    have hrpow : (∏ i, ((n i : ℝ) + 1)) ^ t ≤ (1 + s) ^ (N + 1) := by
      have h1 : (∏ i, ((n i : ℝ) + 1)) ^ t ≤ ((1 + s) ^ N) ^ t :=
        Real.rpow_le_rpow (by positivity) hprodle (le_of_lt (lt_trans one_pos
          (one_lt_coneExponent (ι := ι))))
      refine le_trans h1 (le_of_eq ?_)
      rw [← Real.rpow_natCast (1 + s) N, ← Real.rpow_mul hbasepos.le, hNt,
        Real.rpow_add hbasepos, Real.rpow_natCast, Real.rpow_one]
      exact (pow_succ _ _).symm
    have hfinal : ((1 + s) ^ (N + 1))⁻¹ ≤ ∏ i, ((n i : ℝ) + 1) ^ (-t) := by
      rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity),
        Real.rpow_neg (by positivity)]
      exact inv_anti₀ (by positivity) hrpow
    exact hfinal

/-! ## The Weierstrass majorant on the cone -/

/-- **The product majorant.**  Outside the finitely many small cone values, the genus-`N`
elementary factor at `-z/w_n` deviates from one by at most a constant times the summable weight
`|w_n|^{-(N+1)}`.  Combined with `summable_conePeriod_inv_pow` this is the convergence input of the
genus-`N` Weierstrass product over the period cone. -/
theorem norm_weierstrassFactor_conePeriod_sub_one_le (ω : ι → ℂ) (z : ℂ) (n : ι → ℕ)
    (hn : 2 * ‖z‖ ≤ ‖conePeriod ω n‖) :
    ‖weierstrassFactor (Fintype.card ι) (-(z / conePeriod ω n)) - 1‖ ≤
      Real.exp (weierstrassLogBound (Fintype.card ι)) * ‖z‖ ^ (Fintype.card ι + 1) *
        (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ := by
  rcases eq_or_lt_of_le (norm_nonneg (conePeriod ω n)) with hw | hw
  · have hz : ‖z‖ = 0 := le_antisymm (by linarith [hw.symm ▸ hn]) (norm_nonneg z)
    have hz0 : z = 0 := norm_eq_zero.mp hz
    simp [hz0]
  · have hhalf : ‖-(z / conePeriod ω n)‖ ≤ 1 / 2 := by
      rw [norm_neg, norm_div, div_le_iff₀ hw]
      linarith
    refine (norm_weierstrassFactor_sub_one_le (Fintype.card ι) hhalf).trans (le_of_eq ?_)
    rw [norm_neg, norm_div, div_pow, div_eq_mul_inv]
    ring

end

end GaloisForLFunctions
