import GaloisForLFunctions.RHTower.PrimeLagLandauWeights
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The prime-lag Dirichlet series and its zero-side form

For a bound `a_n ≤ M` on the lag values at prime powers, the Dirichlet series with the nonnegative
coefficients `c_n = (M − a_n) Λ(n)/n` converges for `Re s > θ − ½` whenever every zero has real
part at most `θ`, and there it equals

`M·(−ζ'/ζ)(1+s) − Σ_ρ w_ρ (−ζ'/ζ)(s + 3/2 − ρ)`,

by the lag identity `a_n = Σ_ρ w_ρ n^{ρ−½}` and the Dirichlet series of the von Mangoldt function.
-/

open Complex Filter Topology Set
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The lag value as a zero sum with complex powers -/

theorem complexLog_natCast_eq (n : ℕ) :
    Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0]

theorem integerLag_eq_tsum_cpow {n : ℕ} (hn : 1 ≤ n) :
    (integerLag n : ℂ) = ∑' q : XiZeroCopy, lagWeight q * (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (integerLag n : ℂ) = weilLagFunction (Real.log n) := by
    unfold integerLag; exact (weilLagFunction_eq_ofReal _).symm
  rw [h1, weilLagFunction_eq_tsum_lagWeight]
  refine tsum_congr fun q => ?_
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), complexLog_natCast_eq n]

theorem norm_natCast_cpow_le {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {n : ℕ} (hn : 1 ≤ n)
    (q : XiZeroCopy) : ‖(n : ℂ) ^ ((q.1 : ℂ) - 1 / 2)‖ ≤ (n : ℝ) ^ (θ - 1 / 2) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.rpow_le_rpow_of_exponent_le hn1
  have := hθ q
  simp only [Complex.sub_re]
  have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [h2]
  linarith

theorem summable_lagWeight_mul_cpow {n : ℕ} (hn : 1 ≤ n) :
    Summable fun q : XiZeroCopy => lagWeight q * (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (summable_lagWeight_mul_exp (Real.log n)).congr fun q => ?_
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), complexLog_natCast_eq n]

/-- `|a_n| ≤ W n^{θ−½}` when every zero has real part at most `θ`. -/
theorem abs_integerLag_le_rpow {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {n : ℕ}
    (hn : 1 ≤ n) : |integerLag n| ≤ lagWeightTotal * (n : ℝ) ^ (θ - 1 / 2) := by
  have h1 : |integerLag n| = ‖(integerLag n : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h1, integerLag_eq_tsum_cpow hn]
  have hs := summable_lagWeight_mul_cpow hn
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  unfold lagWeightTotal
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun q => ?_) hs.norm (summable_norm_lagWeight.mul_right _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_natCast_cpow_le hθ hn q) (norm_nonneg _)

/-! ## The coefficients -/

/-- `c_n = (M − a_n) Λ(n)/n`. -/
def primeLagCoeff (M : ℝ) (n : ℕ) : ℝ := (M - integerLag n) * vonMangoldt n / n

theorem lagCoeff_nonneg {M : ℝ} (hM : ∀ n : ℕ, vonMangoldt n ≠ 0 → integerLag n ≤ M) (n : ℕ) :
    0 ≤ primeLagCoeff M n := by
  unfold primeLagCoeff
  by_cases h : vonMangoldt n = 0
  · rw [h]; simp
  · have := hM n h
    exact div_nonneg (mul_nonneg (by linarith) ArithmeticFunction.vonMangoldt_nonneg)
      (Nat.cast_nonneg n)

theorem lagCoeff_zero (M : ℝ) : primeLagCoeff M 0 = 0 := by simp [primeLagCoeff]

/-- `|c_n| ≤ (|M| + W) log n · n^{θ−½} / n`. -/
theorem abs_lagCoeff_le {θ M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    {n : ℕ} (hn : 1 ≤ n) :
    |primeLagCoeff M n| ≤ (|M| + lagWeightTotal) * Real.log n * (n : ℝ) ^ (θ - 1 / 2) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ : vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hΛ0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have ha := abs_integerLag_le_rpow hθ hn
  have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ (θ - 1 / 2) := Real.one_le_rpow hn1 (by linarith)
  have hW := lagWeightTotal_nonneg
  unfold primeLagCoeff
  rw [abs_div, abs_of_pos hn0, abs_mul, abs_of_nonneg hΛ0]
  apply div_le_div_of_nonneg_right _ hn0.le
  have h1 : |M - integerLag n| ≤ |M| + lagWeightTotal * (n : ℝ) ^ (θ - 1 / 2) := by
    calc |M - integerLag n| ≤ |M| + |integerLag n| := abs_sub _ _
      _ ≤ _ := by linarith
  have h2 : |M| + lagWeightTotal * (n : ℝ) ^ (θ - 1 / 2)
      ≤ (|M| + lagWeightTotal) * (n : ℝ) ^ (θ - 1 / 2) := by nlinarith [abs_nonneg M]
  calc |M - integerLag n| * vonMangoldt n
      ≤ ((|M| + lagWeightTotal) * (n : ℝ) ^ (θ - 1 / 2)) * Real.log n :=
        mul_le_mul (h1.trans h2) hΛ hΛ0 (by positivity)
    _ = (|M| + lagWeightTotal) * Real.log n * (n : ℝ) ^ (θ - 1 / 2) := by ring

/-- The coefficient series converges for `Re s > θ − ½`. -/
theorem lagCoeff_LSeriesSummable {θ M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeriesSummable (fun n => (primeLagCoeff M n : ℂ)) s := by
  set ε : ℝ := (s.re - (θ - 1 / 2)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  refine LSeriesSummable_of_le_const_mul_rpow (x := θ - 1 / 2 + ε) (by rw [hε]; linarith)
    ⟨(|M| + lagWeightTotal) / ε, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_lagCoeff_le hθ hθ2 hn1).trans ?_
  have hlog : Real.log n ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div hn0.le hεpos
  have hW := lagWeightTotal_nonneg
  have hC : 0 ≤ |M| + lagWeightTotal := by positivity
  have hr : 0 ≤ (n : ℝ) ^ (θ - 1 / 2) := by positivity
  calc (|M| + lagWeightTotal) * Real.log n * (n : ℝ) ^ (θ - 1 / 2) / n
      ≤ (|M| + lagWeightTotal) * ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (θ - 1 / 2) / n := by gcongr
    _ = (|M| + lagWeightTotal) / ε * ((n : ℝ) ^ (θ - 1 / 2 + ε) / n) := by
        rw [Real.rpow_add hn0]; field_simp
    _ = (|M| + lagWeightTotal) / ε * (n : ℝ) ^ (θ - 1 / 2 + ε - 1) := by
        rw [Real.rpow_sub_one hn0.ne']

/-! ## The identity with the zero-side expression -/

/-- The von Mangoldt function as a complex sequence. -/
def vonMangoldtC (k : ℕ) : ℂ := (vonMangoldt k : ℂ)

/-- The von Mangoldt series shifted by a zero: `Λ(n) n^{ρ−½}/n^{1+s} = term Λ (s + 3/2 − ρ) n`. -/
theorem lagCoeff_term_eq {M : ℝ} {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun k => (primeLagCoeff M k : ℂ)) s n
      = (M : ℂ) * LSeries.term vonMangoldtC (1 + s) n
        - ∑' q : XiZeroCopy, lagWeight q
            * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp_rw [LSeries.term_of_ne_zero hn]
  unfold primeLagCoeff vonMangoldtC
  push_cast
  rw [integerLag_eq_tsum_cpow hn1]
  have hs := summable_lagWeight_mul_cpow hn1
  -- rewrite each shifted term
  have hterm : ∀ q : XiZeroCopy,
      lagWeight q * ((vonMangoldt n : ℂ) / (n : ℂ) ^ (s + 3 / 2 - (q.1 : ℂ)))
        = (lagWeight q * (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2)) * ((vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + s)) := by
    intro q
    have e : (n : ℂ) ^ (s + 3 / 2 - (q.1 : ℂ))
        = (n : ℂ) ^ (1 + s) / (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) := by
      rw [← Complex.cpow_sub _ _ hnc]; congr 1; ring
    rw [e]
    have h1 : (n : ℂ) ^ (1 + s) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
    have h2 : (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
    field_simp
  rw [tsum_congr hterm, tsum_mul_right]
  have h1 : (n : ℂ) ^ (1 + s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
  have h3 : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
  rw [Complex.cpow_add _ _ hnc, Complex.cpow_one]
  field_simp
  ring

theorem tsum_term_vonMangoldtC_eq {w : ℂ} (hw : 1 < w.re) :
    ∑' n, LSeries.term vonMangoldtC w n = -logDeriv riemannZeta w := by
  have := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw
  rw [logDeriv_apply, ← neg_div]
  exact this

theorem summable_term_vonMangoldtC {w : ℂ} (hw : 1 < w.re) :
    Summable (LSeries.term vonMangoldtC w) :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hw

/-- The shifted von Mangoldt term is dominated by the term at `1 + ε'` when `Re w ≥ 1 + ε'`. -/
theorem norm_term_vonMangoldtC_le {w : ℂ} {ε' : ℝ} (hw : 1 + ε' ≤ w.re) (n : ℕ) :
    ‖LSeries.term vonMangoldtC w n‖ ≤ ‖LSeries.term vonMangoldtC ((1 + ε' : ℝ) : ℂ) n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hn1
    simp only [Complex.ofReal_re]
    exact hw

/-- The shifted family `w_q · term Λ (s + 3/2 − ρ_q) n` is absolutely summable on `ℕ × copies`. -/
theorem summable_lagFam {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {s : ℂ}
    (hs : θ - 1 / 2 < s.re) :
    Summable (fun p : ℕ × XiZeroCopy =>
      lagWeight p.2 * LSeries.term vonMangoldtC (s + 3 / 2 - (p.2.1 : ℂ)) p.1) := by
  set ε' : ℝ := s.re + 1 / 2 - θ with hε'
  have hε'pos : 0 < ε' := by rw [hε']; linarith
  have h32 : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
  have hreq' : ∀ q : XiZeroCopy, 1 + ε' ≤ (s + 3 / 2 - (q.1 : ℂ)).re := fun q => by
    have := hθ q
    simp only [Complex.sub_re, Complex.add_re, h32]; rw [hε']; linarith
  have hsumΛ : Summable fun n => ‖LSeries.term vonMangoldtC ((1 + ε' : ℝ) : ℂ) n‖ :=
    (summable_term_vonMangoldtC (by simp; linarith)).norm
  have h1 : Summable fun n : ℕ => ‖‖LSeries.term vonMangoldtC ((1 + ε' : ℝ) : ℂ) n‖‖ := by
    simpa using hsumΛ
  have h2 : Summable fun q : XiZeroCopy => ‖‖lagWeight q‖‖ := by
    simpa using summable_norm_lagWeight
  have hprodmaj := summable_mul_of_summable_norm
    (f := fun n : ℕ => ‖LSeries.term vonMangoldtC ((1 + ε' : ℝ) : ℂ) n‖)
    (g := fun q : XiZeroCopy => ‖lagWeight q‖) h1 h2
  refine Summable.of_norm_bounded hprodmaj fun p => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_term_vonMangoldtC_le (hreq' p.2) p.1) (norm_nonneg _)

/-- **The coefficient series equals the zero-side expression on `Re s > θ − ½`.** -/
theorem LSeries_lagCoeff_eq {θ M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeries (fun n => (primeLagCoeff M n : ℂ)) s
      = (M : ℂ) * (-logDeriv riemannZeta (1 + s))
        - ∑' q : XiZeroCopy, lagWeight q * (-logDeriv riemannZeta (s + 3 / 2 - (q.1 : ℂ))) := by
  have hre1 : 1 < (1 + s).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have h32 : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
  have hreq : ∀ q : XiZeroCopy, 1 < (s + 3 / 2 - (q.1 : ℂ)).re := fun q => by
    have := hθ q
    simp only [Complex.sub_re, Complex.add_re, h32]; linarith
  have hprod := summable_lagFam hθ hs
  have hrow : ∀ n, Summable fun q : XiZeroCopy =>
      lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n :=
    fun n => hprod.prod_factor n
  have hcol : ∀ q : XiZeroCopy, Summable fun n =>
      lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n :=
    fun q => (summable_term_vonMangoldtC (hreq q)).mul_left _
  have hfib : Summable fun n => ∑' q : XiZeroCopy,
      lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n :=
    (hprod.hasSum.prod_fiberwise fun n => (hrow n).hasSum).summable
  have hterm : ∀ n, LSeries.term (fun k => (primeLagCoeff M k : ℂ)) s n
      = (M : ℂ) * LSeries.term vonMangoldtC (1 + s) n
        - ∑' q : XiZeroCopy, lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · exact lagCoeff_term_eq hn.ne'
  have hsumM : Summable fun n => (M : ℂ) * LSeries.term vonMangoldtC (1 + s) n :=
    (summable_term_vonMangoldtC hre1).mul_left _
  have hswap := Summable.tsum_comm'
    (f := fun (n : ℕ) (q : XiZeroCopy) =>
      lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n) hprod hrow hcol
  calc LSeries (fun n => (primeLagCoeff M n : ℂ)) s
      = ∑' n, ((M : ℂ) * LSeries.term vonMangoldtC (1 + s) n
          - ∑' q : XiZeroCopy, lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n) :=
        tsum_congr hterm
    _ = (M : ℂ) * ∑' n, LSeries.term vonMangoldtC (1 + s) n
          - ∑' n, ∑' q : XiZeroCopy,
              lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n := by
        rw [Summable.tsum_sub hsumM hfib, tsum_mul_left]
    _ = (M : ℂ) * (-logDeriv riemannZeta (1 + s))
          - ∑' q : XiZeroCopy, ∑' n,
              lagWeight q * LSeries.term vonMangoldtC (s + 3 / 2 - (q.1 : ℂ)) n := by
        rw [tsum_term_vonMangoldtC_eq hre1, hswap]
    _ = _ := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [tsum_mul_left, tsum_term_vonMangoldtC_eq (hreq q)]

end

end RHTower
