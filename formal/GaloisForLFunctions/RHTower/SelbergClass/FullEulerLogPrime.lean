import GaloisForLFunctions.RHTower.SelbergClass.Full
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Coefficient identity for a full Euler logarithm

Differentiating the exponentiated Euler identity gives a convolution identity
for every coefficient. At a prime, the two divisor pairs `(1,p)` and `(p,1)`
show that the Dirichlet coefficient equals its Euler-log coefficient.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private theorem mul_apply_prime {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  have hanti :
      p.divisorsAntidiagonal = {(1, p), (p, 1)} := by
    ext xy
    rw [Nat.mem_divisorsAntidiagonal]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hprod, _⟩
      rcases hp.eq_one_or_self_of_dvd xy.1 ⟨xy.2, hprod.symm⟩ with hx | hx
      · left
        apply Prod.ext
        · exact hx
        · simpa [hx] using hprod
      · right
        apply Prod.ext
        · exact hx
        · exact Nat.mul_left_cancel hp.pos (by simpa [hx] using hprod)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hp.ne_zero]
  rw [ArithmeticFunction.mul_apply, hanti]
  simp [hp.ne_one]

/-- Logarithmic differentiation of the Euler product identifies every
log-weighted coefficient with its Dirichlet convolution. -/
theorem SelbergClass.logMul_coeff_apply (F : SelbergClass) (n : ℕ) :
    LSeries.logMul F.coeff n = ∑ ij ∈ n.divisorsAntidiagonal,
      F.coeff ij.1 * LSeries.logMul F.eulerLogCoeff ij.2 := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.logMul]
  let D : ArithmeticFunction ℂ :=
    ⟨LSeries.logMul F.eulerLogCoeff, by simp [LSeries.logMul]⟩
  have hderivMul : ∀ s : ℂ, 2 < s.re →
      LSeries (LSeries.logMul F.coeff) s =
        LSeries (fun n => (F.coeff * D) n) s := by
    intro s hs
    have ha2 : LSeriesSummable F.coeff (2 : ℂ) :=
      F.lSeriesSummable (2 : ℂ) (by norm_num)
    have hg2 : LSeriesSummable F.eulerLogCoeff (2 : ℂ) :=
      F.eulerLogSummable (2 : ℂ) (by norm_num)
    have habs : LSeries.abscissaOfAbsConv F.coeff < s.re := by
      calc
        LSeries.abscissaOfAbsConv F.coeff ≤ (2 : ℝ) := by
          simpa using ha2.abscissaOfAbsConv_le
        _ < s.re := by exact_mod_cast hs
    have hgbs : LSeries.abscissaOfAbsConv F.eulerLogCoeff < s.re := by
      calc
        LSeries.abscissaOfAbsConv F.eulerLogCoeff ≤ (2 : ℝ) := by
          simpa using hg2.abscissaOfAbsConv_le
        _ < s.re := by exact_mod_cast hs
    have hA := LSeries_hasDerivAt habs
    have hG := LSeries_hasDerivAt hgbs
    have hlocal :
        (fun z : ℂ => Complex.exp (LSeries F.eulerLogCoeff z)) =ᶠ[𝓝 s]
          LSeries F.coeff := by
      have hs1 : (1 : ℝ) < s.re := lt_trans (by norm_num) hs
      have hmem : {z : ℂ | (1 : ℝ) < z.re} ∈ 𝓝 s :=
        (isOpen_lt continuous_const continuous_re).mem_nhds hs1
      apply Filter.eventuallyEq_of_mem hmem
      intro z hz
      exact (F.eulerProduct z hz).trans (F.lSeries_eq_value z hz).symm
    have hEq :
        Complex.exp (LSeries F.eulerLogCoeff s) *
            (-LSeries (LSeries.logMul F.eulerLogCoeff) s) =
          -LSeries (LSeries.logMul F.coeff) s := by
      have hleft : HasDerivAt (LSeries F.coeff)
          (Complex.exp (LSeries F.eulerLogCoeff s) *
            (-LSeries (LSeries.logMul F.eulerLogCoeff) s)) s :=
        hG.cexp.congr_of_eventuallyEq hlocal.symm
      exact hleft.deriv.symm.trans hA.deriv
    have hvalue : Complex.exp (LSeries F.eulerLogCoeff s) = LSeries F.coeff s :=
      (F.eulerProduct s (by linarith)).trans (F.lSeries_eq_value s (by linarith)).symm
    have hlog : LSeries (LSeries.logMul F.coeff) s =
        LSeries F.coeff s * LSeries (LSeries.logMul F.eulerLogCoeff) s := by
      calc
        LSeries (LSeries.logMul F.coeff) s =
            -(-LSeries (LSeries.logMul F.coeff) s) := by ring
        _ = -(Complex.exp (LSeries F.eulerLogCoeff s) *
            (-LSeries (LSeries.logMul F.eulerLogCoeff) s)) := by rw [hEq]
        _ = Complex.exp (LSeries F.eulerLogCoeff s) *
            LSeries (LSeries.logMul F.eulerLogCoeff) s := by ring
        _ = LSeries F.coeff s * LSeries (LSeries.logMul F.eulerLogCoeff) s := by
          rw [hvalue]
    have hD : LSeriesSummable D s := by
      simpa [D] using LSeriesSummable_logMul_of_lt_re hgbs
    have hmul : LSeries (fun n => (F.coeff * D) n) s =
        LSeries F.coeff s * LSeries (fun n => D n) s := by
      simpa using ArithmeticFunction.LSeries_mul' (F.lSeriesSummable s (by linarith)) hD
    simpa [D] using hlog.trans hmul.symm
  have ha3 : LSeriesSummable F.coeff (3 : ℂ) :=
    F.lSeriesSummable (3 : ℂ) (by norm_num)
  have hg3 : LSeriesSummable F.eulerLogCoeff (3 : ℂ) :=
    F.eulerLogSummable (3 : ℂ) (by norm_num)
  have habs4 : LSeries.abscissaOfAbsConv F.coeff < (4 : ℂ).re := by
    calc
      LSeries.abscissaOfAbsConv F.coeff ≤ (3 : ℝ) := by
        simpa using ha3.abscissaOfAbsConv_le
      _ < (4 : ℂ).re := by norm_num
  have hgbs4 : LSeries.abscissaOfAbsConv F.eulerLogCoeff < (4 : ℂ).re := by
    calc
      LSeries.abscissaOfAbsConv F.eulerLogCoeff ≤ (3 : ℝ) := by
        simpa using hg3.abscissaOfAbsConv_le
      _ < (4 : ℂ).re := by norm_num
  have hlogA4 : LSeriesSummable (LSeries.logMul F.coeff) (4 : ℂ) :=
    LSeriesSummable_logMul_of_lt_re habs4
  have hD4 : LSeriesSummable D (4 : ℂ) := by
    simpa [D] using LSeriesSummable_logMul_of_lt_re hgbs4
  have hconv4 : LSeriesSummable (fun n => (F.coeff * D) n) (4 : ℂ) := by
    simpa using ArithmeticFunction.LSeriesSummable_mul
      (F.lSeriesSummable (4 : ℂ) (by norm_num)) hD4
  have hcoeff : LSeries.logMul F.coeff n = (F.coeff * D) n := by
    apply LSeries.eq_of_LSeries_eventually_eq
    · exact hlogA4.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
    · exact hconv4.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
    · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
      exact hderivMul (x : ℂ) (by simpa using hx)
    · exact hn
  exact hcoeff

/-- The Dirichlet coefficient at a prime equals the corresponding coefficient
of the Euler logarithm. -/
theorem SelbergClass.coeff_prime_eq_eulerLogCoeff
    (F : SelbergClass) {p : ℕ} (hp : p.Prime) :
    F.coeff p = F.eulerLogCoeff p := by
  let D : ArithmeticFunction ℂ :=
    ⟨LSeries.logMul F.eulerLogCoeff, by simp [LSeries.logMul]⟩
  have hcoeff := F.logMul_coeff_apply p
  have hD_one : D 1 = 0 := by simp [D, LSeries.logMul]
  have hD_prime : D p = Complex.log (p : ℂ) * F.eulerLogCoeff p := by rfl
  change Complex.log (p : ℂ) * F.coeff p = (F.coeff * D) p at hcoeff
  rw [mul_apply_prime F.coeff D hp, F.coeff_one, hD_one, hD_prime] at hcoeff
  simp only [one_mul, mul_zero, add_zero] at hcoeff
  apply mul_left_cancel₀ ?_ hcoeff
  rw [← Complex.natCast_log]
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

end

end RHTower
