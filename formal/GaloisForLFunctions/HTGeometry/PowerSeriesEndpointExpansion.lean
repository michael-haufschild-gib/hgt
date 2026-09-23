import GaloisForLFunctions.HTGeometry.MvPolynomialFirstOrderTaylor
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order

/-!
# The endpoint expansion of a differential-polynomial coefficient

Split every jet series at degree `K = N − R` into its low part `S` (degrees `≤ K`) and high part
`L` (degrees `> K`).  The high parts generate the ideal `(X^{K+1})`, whose square is `(X^{2K+2})`,
and `2K + 2 > N` as soon as `N ≥ 2R`.  So the first-order Taylor expansion of a polynomial at the
perturbed point is an **exact** identity for the coefficient of `X^N`:

`[X^N] P(jets) = ∑ⱼ ∑_{q<R} [X^q]((∂ⱼP)(jets)) · [X^{N−q}](jetsⱼ) + [X^N] P(S)`.

The first sum is the endpoint contribution: one jet carries all but `q < R` of the degree, and the
complementary coefficient is exactly the partial derivative of `P` in that jet — including
multiplicities for repeated factors, which the derivative supplies automatically.  The last term is
the remainder: every convolution index occurring in it is at most `N − R`.

No asymptotics enter here; this is pure algebra.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

variable {k : Type*} [CommRing k]

noncomputable section

/-! ## Splitting a power series at a degree -/

/-- The truncation of a power series to degrees at most `K`. -/
def lowPart (K : ℕ) (f : PowerSeries k) : PowerSeries k :=
  PowerSeries.mk fun n => if n ≤ K then PowerSeries.coeff n f else 0

/-- The tail of a power series above degree `K`. -/
def highPart (K : ℕ) (f : PowerSeries k) : PowerSeries k := f - lowPart K f

@[simp]
theorem coeff_lowPart (K n : ℕ) (f : PowerSeries k) :
    PowerSeries.coeff n (lowPart K f) = if n ≤ K then PowerSeries.coeff n f else 0 := by
  rw [lowPart, PowerSeries.coeff_mk]

@[simp]
theorem coeff_highPart (K n : ℕ) (f : PowerSeries k) :
    PowerSeries.coeff n (highPart K f) = if n ≤ K then 0 else PowerSeries.coeff n f := by
  rw [highPart, map_sub, coeff_lowPart]
  by_cases h : n ≤ K <;> simp [h]

theorem lowPart_add_highPart (K : ℕ) (f : PowerSeries k) :
    lowPart K f + highPart K f = f := by
  rw [highPart]
  ring

/-- The tail above degree `K` is divisible by `X^{K+1}`. -/
theorem X_pow_dvd_highPart (K : ℕ) (f : PowerSeries k) :
    (PowerSeries.X : PowerSeries k) ^ (K + 1) ∣ highPart K f := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [coeff_highPart, if_pos (by omega)]

/-- A member of `(X^K)` has vanishing coefficients below `K`. -/
theorem coeff_eq_zero_of_mem_span_X_pow {K n : ℕ} (hn : n < K) {f : PowerSeries k}
    (hf : f ∈ Ideal.span {(PowerSeries.X : PowerSeries k) ^ K}) :
    PowerSeries.coeff n f = 0 := by
  rw [Ideal.mem_span_singleton] at hf
  rw [PowerSeries.X_pow_dvd_iff] at hf
  exact hf n hn

/-! ## The endpoint expansion -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {R : Type*} [CommRing R] [Algebra R (PowerSeries k)]

/-- Replacing the jets by their truncations does not change low coefficients. -/
theorem coeff_aeval_lowPart_eq {K : ℕ} (jets : σ → PowerSeries k) (P : MvPolynomial σ R)
    {q : ℕ} (hq : q ≤ K) :
    PowerSeries.coeff q (aeval (fun j => lowPart K (jets j)) P)
      = PowerSeries.coeff q (aeval jets P) := by
  classical
  set J : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k) ^ (K + 1)} with hJ
  set S : σ → PowerSeries k := fun j => lowPart K (jets j) with hS
  set L : σ → PowerSeries k := fun j => highPart K (jets j) with hL
  have hLmem : ∀ j, L j ∈ J := by
    intro j
    rw [hJ, Ideal.mem_span_singleton]
    exact X_pow_dvd_highPart K (jets j)
  have hSL : S + L = jets := by
    funext j
    exact lowPart_add_highPart K (jets j)
  have hdef := taylorDefect_mem_sq J S L hLmem P
  have hsq : J ^ (2 : ℕ) ≤ J := Ideal.pow_le_self (by norm_num)
  have hmem : aeval jets P - aeval S P ∈ J := by
    have hexp := aeval_add_eq_add_sum_pderiv_mod_sq S L P
    rw [hSL] at hexp
    have hsum : (∑ j, (aeval S (pderiv j P)) * L j) ∈ J :=
      Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left J _ (hLmem j)
    have hval : aeval jets P - aeval S P
        = (∑ j, (aeval S (pderiv j P)) * L j) + taylorDefect S L P := by
      rw [hexp]
      ring
    rw [hval]
    exact Submodule.add_mem _ hsum (hsq hdef)
  have hzero : PowerSeries.coeff q (aeval jets P - aeval S P) = 0 :=
    coeff_eq_zero_of_mem_span_X_pow (by omega) hmem
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.symm

/-- The coefficient of a product with a tail is the endpoint sum. -/
theorem coeff_mul_highPart {N R : ℕ} (hRN : R ≤ N) (H f : PowerSeries k) :
    PowerSeries.coeff N (H * highPart (N - R) f)
      = ∑ q ∈ Finset.range R, PowerSeries.coeff q H * PowerSeries.coeff (N - q) f := by
  classical
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsub : Finset.range R ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hvanish : ∀ q ∈ Finset.range (N + 1), q ∉ Finset.range R →
      PowerSeries.coeff q H * PowerSeries.coeff (N - q) (highPart (N - R) f) = 0 := by
    intro q hq hqR
    have hqN : q < N + 1 := Finset.mem_range.mp hq
    have hqR' : R ≤ q := by
      by_contra hcon
      exact hqR (Finset.mem_range.mpr (by omega))
    rw [coeff_highPart, if_pos (by omega), mul_zero]
  rw [← Finset.sum_subset hsub hvanish]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqR : q < R := Finset.mem_range.mp hq
  rw [coeff_highPart, if_neg (by omega)]

/-- **The endpoint expansion.**  For `N ≥ 2R` the coefficient of `X^N` of a differential polynomial
splits exactly into the endpoint contributions of the jets and a remainder built only from
convolution indices at most `N − R`. -/
theorem coeff_aeval_endpoint_expansion (jets : σ → PowerSeries k) (P : MvPolynomial σ R)
    {N R : ℕ} (hNR : 2 * R ≤ N) :
    PowerSeries.coeff N (aeval jets P)
      = (∑ j, ∑ q ∈ Finset.range R,
          PowerSeries.coeff q (aeval jets (pderiv j P))
            * PowerSeries.coeff (N - q) (jets j))
        + PowerSeries.coeff N (aeval (fun j => lowPart (N - R) (jets j)) P) := by
  classical
  have hKR : R ≤ N - R := by omega
  set K : ℕ := N - R with hK
  set J : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k) ^ (K + 1)} with hJ
  set S : σ → PowerSeries k := fun j => lowPart K (jets j) with hS
  set L : σ → PowerSeries k := fun j => highPart K (jets j) with hL
  have hLmem : ∀ j, L j ∈ J := by
    intro j
    rw [hJ, Ideal.mem_span_singleton]
    exact X_pow_dvd_highPart K (jets j)
  have hSL : S + L = jets := by
    funext j
    exact lowPart_add_highPart K (jets j)
  have hexp := aeval_add_eq_add_sum_pderiv_mod_sq S L P
  rw [hSL] at hexp
  -- the defect is invisible at degree `N`
  have hsqspan : J ^ (2 : ℕ) = Ideal.span {(PowerSeries.X : PowerSeries k) ^ (2 * K + 2)} := by
    rw [hJ, pow_two, Ideal.span_singleton_mul_span_singleton, ← pow_add]
    have harith : K + 1 + (K + 1) = 2 * K + 2 := by ring
    rw [harith]
  have hdef : taylorDefect S L P ∈ J ^ (2 : ℕ) := taylorDefect_mem_sq J S L hLmem P
  rw [hsqspan] at hdef
  have hdefzero : PowerSeries.coeff N (taylorDefect S L P) = 0 := by
    refine coeff_eq_zero_of_mem_span_X_pow ?_ hdef
    omega
  -- the endpoint terms
  have hRN : R ≤ N := by omega
  have hterm : ∀ j : σ, PowerSeries.coeff N ((aeval S (pderiv j P)) * L j)
      = ∑ q ∈ Finset.range R,
        PowerSeries.coeff q (aeval jets (pderiv j P)) * PowerSeries.coeff (N - q) (jets j) := by
    intro j
    rw [hL, coeff_mul_highPart hRN]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqR : q < R := Finset.mem_range.mp hq
    rw [coeff_aeval_lowPart_eq (K := K) jets (pderiv j P) (by omega)]
  rw [hexp, map_add, map_add, hdefzero, add_zero, map_sum,
    Finset.sum_congr rfl fun j _ => hterm j]
  ring

end

end GaloisForLFunctions.HTGeometry
