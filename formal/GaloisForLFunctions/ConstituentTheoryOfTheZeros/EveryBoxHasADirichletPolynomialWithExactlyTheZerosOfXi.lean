import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Every box has a Dirichlet polynomial with exactly the zeros of `ξ`

Sharing zeros with `ξ` in a box costs length and nothing else.

The two-term Dirichlet polynomial `m^{-s} − ((m+1)/m)^ρ (m+1)^{-s}` vanishes exactly on the
vertical progression `ρ + 2πi ℤ / log((m+1)/m)`, whose step exceeds `2πm`. For `m > H/π` its only
zero in the band `|Im s| ≤ H` is `ρ`, if `ρ` lies in the band. Products of Dirichlet polynomials
are Dirichlet polynomials (Dirichlet convolution), so:

* every finite set of points of the band is the zero set in the band of a Dirichlet polynomial
  (`exists_dirichletPolynomial_zeros_eq`);
* for every height `H` there is a nonzero Dirichlet polynomial whose zeros with `|Im s| ≤ H` are
  exactly the zeros of `ξ` there (`exists_dirichletPolynomial_zeros_eq_xi`);
* its length cannot stay bounded: for every `N` there is a height beyond which no Dirichlet
  polynomial of length at most `N` has exactly the zeros of `ξ`
  (`exists_height_forall_not_zeros_eq_xi`).

So a box alone constrains nothing; the constraint on approximants that share zeros in growing
boxes is the bound on the length, or convergence in the norm of absolute convergence.
-/

open Complex Set

open scoped LSeries.notation

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower

/-! ### Coefficients of finite support -/

/-- A coefficient function that vanishes beyond `N` has an absolutely convergent series. -/
theorem lSeriesSummable_of_forall_gt {a : ℕ → ℂ} {N : ℕ} (ha : ∀ n, N < n → a n = 0) (s : ℂ) :
    LSeriesSummable a s :=
  summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    rw [LSeries.term_of_ne_zero (by omega), ha n (by omega), zero_div]

/-- Such a series is a Dirichlet polynomial of length `N`. -/
theorem LSeries_eq_polyCoeff {a : ℕ → ℂ} {N : ℕ} (ha : ∀ n, N < n → a n = 0) (s : ℂ) :
    LSeries a s = LSeries (polyCoeff fun i : Fin N => a (i + 1)) s := by
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
    congr 1
    by_cases hN : n ≤ N
    · unfold polyCoeff
      rw [dif_pos ⟨hn, hN⟩]
      show a n = a (n - 1 + 1)
      rw [Nat.sub_add_cancel hn]
    · rw [polyCoeff_of_gt _ (by omega), ha n (by omega)]

/-- The Dirichlet convolution of coefficient functions of finite support has finite support. -/
theorem convolution_eq_zero_of_gt {f g : ℕ → ℂ} {A B : ℕ} (hf : ∀ n, A < n → f n = 0)
    (hg : ∀ n, B < n → g n = 0) (n : ℕ) (hn : A * B < n) : (f ⍟ g) n = 0 := by
  rw [LSeries.convolution_def]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h1 : A < p.1
  · rw [hf _ h1, zero_mul]
  · by_cases h2 : B < p.2
    · rw [hg _ h2, mul_zero]
    · exfalso
      have h := Nat.mul_le_mul (not_lt.mp h1) (not_lt.mp h2)
      rw [hp'] at h
      exact absurd h (not_le.mpr hn)

/-! ### The two-term factor -/

/-- The coefficients of `m^{-s} − c (m+1)^{-s}`. -/
def twoTermCoeff (m : ℕ) (c : ℂ) (n : ℕ) : ℂ :=
  if n = m then 1 else if n = m + 1 then -c else 0

theorem twoTermCoeff_of_gt (m : ℕ) (c : ℂ) (n : ℕ) (hn : m + 1 < n) : twoTermCoeff m c n = 0 := by
  unfold twoTermCoeff
  rw [if_neg (by omega), if_neg (by omega)]

theorem LSeries_twoTermCoeff {m : ℕ} (hm : 0 < m) (c s : ℂ) :
    LSeries (twoTermCoeff m c) s = 1 / (m : ℂ) ^ s - c / ((m + 1 : ℕ) : ℂ) ^ s := by
  unfold LSeries
  rw [tsum_eq_sum (s := {m, m + 1}) fun n hn => by
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hn0.ne']
      unfold twoTermCoeff
      rw [if_neg hn.1, if_neg hn.2, zero_div],
    Finset.sum_pair (by omega), LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero (Nat.succ_ne_zero m)]
  unfold twoTermCoeff
  rw [if_pos rfl, if_neg (by omega), if_pos rfl]
  ring

/-- The logarithm of the ratio of the two scales of the factor. -/
def stepLog (m : ℕ) : ℝ := Real.log (((m + 1 : ℕ) : ℝ) / m)

theorem stepLog_pos {m : ℕ} (hm : 0 < m) : 0 < stepLog m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine Real.log_pos ?_
  rw [lt_div_iff₀ hm', one_mul]
  exact_mod_cast Nat.lt_succ_self m

/-- `log(1 + 1/m) ≤ 1/m`: the zeros of the factor are at least `2πm` apart. -/
theorem stepLog_le {m : ℕ} (hm : 0 < m) : stepLog m ≤ 1 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have h1 : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by
    push_cast
    field_simp
    ring
  unfold stepLog
  linarith

/-- The factor with the constant `((m+1)/m)^ρ` vanishes exactly where `((m+1)/m)^{s − ρ} = 1`. -/
theorem LSeries_twoTermCoeff_eq_zero_iff {m : ℕ} (hm : 0 < m) (ρ s : ℂ) :
    LSeries (twoTermCoeff m (exp (ρ * stepLog m))) s = 0 ↔ exp ((s - ρ) * stepLog m) = 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hL : (stepLog m : ℂ) = Complex.log ((m + 1 : ℕ) : ℂ) - Complex.log (m : ℂ) := by
    unfold stepLog
    rw [Real.log_div (by positivity) hm'.ne', ofReal_sub, Complex.natCast_log,
      Complex.natCast_log]
  rw [LSeries_twoTermCoeff hm, Complex.cpow_def_of_ne_zero hm0, Complex.cpow_def_of_ne_zero hm1,
    sub_eq_zero, div_eq_div_iff (exp_ne_zero _) (exp_ne_zero _), one_mul, ← exp_add,
    Complex.exp_eq_exp_iff_exp_sub_eq_one]
  have harg : Complex.log ((m + 1 : ℕ) : ℂ) * s - (ρ * stepLog m + Complex.log (m : ℂ) * s) =
      (s - ρ) * stepLog m := by
    rw [hL]
    ring
  rw [harg]

/-- In a band of height below `πm` the factor has the single zero `ρ`. -/
theorem eq_of_exp_stepLog_eq_one {m : ℕ} (hm : 0 < m) {H : ℝ} (hH : H < π * m) {ρ s : ℂ}
    (hρ : |ρ.im| ≤ H) (hs : |s.im| ≤ H) (h : exp ((s - ρ) * stepLog m) = 1) : s = ρ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hLpos := stepLog_pos hm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have him : (s.im - ρ.im) * stepLog m = n * (2 * π) := by
    have h1 := congrArg Complex.im hn
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, Complex.sub_im,
      Complex.mul_im] at h1
    simpa using h1
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have habs : |s.im - ρ.im| * stepLog m = |(n : ℝ)| * (2 * π) := by
      have h2 := congrArg abs him
      rwa [abs_mul, abs_mul, abs_of_pos hLpos, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h2
    have h2 : |s.im - ρ.im| ≤ 2 * H :=
      (abs_sub _ _).trans (by linarith)
    have h3 : |s.im - ρ.im| * stepLog m ≤ 2 * H * (1 / m) :=
      mul_le_mul h2 (stepLog_le hm) hLpos.le (by linarith [abs_nonneg (s.im - ρ.im)])
    have h4 : 2 * H * (1 / m) < 2 * π := by
      rw [mul_one_div, div_lt_iff₀ hm']
      linarith
    nlinarith [Real.pi_pos]
  rw [hn0, Int.cast_zero, zero_mul, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact sub_eq_zero.mp hn
  · exact absurd (ofReal_eq_zero.mp hn) hLpos.ne'

/-! ### Prescribed zeros in a band -/

/-- **Every finite set of points of a band is the zero set, in the band, of a Dirichlet
polynomial.** -/
theorem exists_dirichletPolynomial_zeros_eq (H : ℝ) (Z : Finset ℂ) (hZ : ∀ z ∈ Z, |z.im| ≤ H) :
    ∃ (a : ℕ → ℂ) (N : ℕ), (∀ n, N < n → a n = 0) ∧
      ∀ s : ℂ, |s.im| ≤ H → (LSeries a s = 0 ↔ s ∈ Z) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max H 0 / π)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (le_max_right _ _) Real.pi_pos.le) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hH : H < π * m := by
    rw [div_lt_iff₀ Real.pi_pos] at hm
    linarith [le_max_left H 0]
  induction Z using Finset.induction_on with
  | empty =>
    refine ⟨δ, 1, fun n hn => ?_, fun s _ => ?_⟩
    · unfold LSeries.delta
      rw [if_neg (by omega)]
    · rw [LSeries_delta, Pi.one_apply]
      exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h (Finset.notMem_empty s)⟩
  | insert ρ Z' _ ih =>
    obtain ⟨a, N, ha, hiff⟩ := ih fun z hz => hZ z (Finset.mem_insert_of_mem hz)
    have hρ : |ρ.im| ≤ H := hZ ρ (Finset.mem_insert_self ρ Z')
    refine ⟨a ⍟ twoTermCoeff m (exp (ρ * stepLog m)), N * (m + 1),
      convolution_eq_zero_of_gt ha (twoTermCoeff_of_gt m _), fun s hs => ?_⟩
    rw [LSeries_convolution' (lSeriesSummable_of_forall_gt ha s)
      (lSeriesSummable_of_forall_gt (twoTermCoeff_of_gt m _) s), mul_eq_zero, hiff s hs,
      LSeries_twoTermCoeff_eq_zero_iff hm0, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (eq_of_exp_stepLog_eq_one hm0 hH hρ hs h)
    · rintro (h | h)
      · right
        rw [h, sub_self, zero_mul, Complex.exp_zero]
      · exact Or.inl h

theorem polyCoeff_zero_vec (N : ℕ) : polyCoeff (0 : Fin N → ℂ) = 0 := by
  funext n
  unfold polyCoeff
  split_ifs <;> rfl

/-- **Every box has a Dirichlet polynomial with exactly the zeros of `ξ`.** For every height `H`
there is a nonzero Dirichlet polynomial whose zeros with `|Im s| ≤ H` are exactly the zeros of `ξ`
with `|Im s| ≤ H`. -/
theorem exists_dirichletPolynomial_zeros_eq_xi (H : ℝ) :
    ∃ (N : ℕ) (v : Fin N → ℂ), v ≠ 0 ∧
      ∀ s : ℂ, |s.im| ≤ H → (LSeries (polyCoeff v) s = 0 ↔ xi s = 0) := by
  have hfin := xiZerosUpTo_finite (max H 0)
  obtain ⟨a, N, ha, hiff⟩ := exists_dirichletPolynomial_zeros_eq (max H 0) hfin.toFinset
    fun z hz => (hfin.mem_toFinset.mp hz).2
  have hiff' : ∀ s : ℂ, |s.im| ≤ max H 0 →
      (LSeries (polyCoeff fun i : Fin N => a (i + 1)) s = 0 ↔ xi s = 0) := fun s hs => by
    rw [← LSeries_eq_polyCoeff ha, hiff s hs, hfin.mem_toFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩
  refine ⟨N, fun i => a (i + 1), fun hv => ?_, fun s hs => hiff' s (hs.trans (le_max_left _ _))⟩
  have h2im : |(2 : ℂ).im| ≤ max H 0 := by
    have h : (2 : ℂ).im = 0 := by simp
    rw [h, abs_zero]
    exact le_max_right _ _
  have h2 := (hiff' 2 h2im).mp (by rw [hv, polyCoeff_zero_vec, LSeries_zero, Pi.zero_apply])
  have h3 := (xi_zero_re_mem_open_unit h2).2
  have h4 : (2 : ℂ).re = 2 := by simp
  linarith

/-- **The length is unbounded.** For every `N` there is a height `H₀` such that no Dirichlet
polynomial of length at most `N` has exactly the zeros of `ξ` in the band `|Im s| ≤ H₀`. -/
theorem exists_height_forall_not_zeros_eq_xi (N : ℕ) :
    ∃ H₀ : ℝ, ∀ v : Fin N → ℂ,
      ¬ ∀ s : ℂ, |s.im| ≤ H₀ → (LSeries (polyCoeff v) s = 0 ↔ xi s = 0) := by
  obtain ⟨ρ, hρ⟩ := xiZeros_infinite.nonempty
  have hρ0 : xi ρ = 0 := hρ
  have hstrip := xi_zero_re_mem_open_unit hρ0
  have hω' : |ρ.re - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  obtain ⟨H₀, hH₀⟩ := exists_height_forall_dirichletPolynomial N (abs_nonneg (ρ.re - 1 / 2)) hω'
    le_rfl
  refine ⟨max H₀ |ρ.im|, fun v hv => ?_⟩
  have hv0 : v ≠ 0 := fun h0 => by
    have h2im : |(2 : ℂ).im| ≤ max H₀ |ρ.im| := by
      have h : (2 : ℂ).im = 0 := by simp
      rw [h, abs_zero]
      exact le_max_of_le_right (abs_nonneg _)
    have h2 := (hv 2 h2im).mp (by rw [h0, polyCoeff_zero_vec, LSeries_zero, Pi.zero_apply])
    have h3 := (xi_zero_re_mem_open_unit h2).2
    have h4 : (2 : ℂ).re = 2 := by simp
    linarith
  exact hH₀ v hv0 (fun s _ hs hs0 => (hv s (hs.trans (le_max_left _ _))).mp hs0) ρ le_rfl
    ((hv ρ (le_max_right _ _)).mpr hρ0)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
