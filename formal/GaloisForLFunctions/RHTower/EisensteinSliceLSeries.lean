import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivity
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# The WD slice is an Eisenstein L-function

For real `τ` let `a_τ(n) = Σ_{d ∣ n} d^{iτ}(n/d)^{−iτ}`, the Hecke eigenvalues (up to normalization)
of the Eisenstein series `E(·, ½ + iτ)`.  Its Dirichlet series is

`Σ a_τ(n) n^{−w} = ζ(w − iτ) ζ(w + iτ)`   for `Re w > 1`   (`LSeries_eisensteinCoeff`).

So in the Euler region the horizontal slice `ξ(½+x+iτ) ξ(½−x+iτ) = ξ(½+x+iτ) ξ(½+x−iτ)` (functional
equation) is, up to its Gamma factors, the Dirichlet series of `a_τ` at `w = ½ + x`: the slice is the
completed standard L-function `Λ(½ + x, E(·, ½ + iτ))` of a self-dual Eisenstein series, and the WD
coefficients are its even central derivatives.

* `twistPow`: the completely multiplicative function `n ↦ n^{iτ}` (zero at `0`).
* `LSeriesHasSum_twistPow`: `Σ n^{iτ} n^{−w} = ζ(w − iτ)`.
* `eisensteinCoeff_eq`: `a_τ = n^{iτ} ⋆ n^{−iτ}` (Dirichlet convolution).
* `LSeries_eisensteinCoeff`: the product formula.
* `xiSliceProduct_eq_gamma_mul_LSeries_eisenstein`: for real `x > ½`, the slice
  `ξ(½+x+it)ξ(½−x+it)` equals `G_t(x) · Σ a_t(n) n^{−(½+x)}` with the explicit Gamma factor
  `G_t(x) = Π_± s_±(s_± − 1)/2 · Γ_ℝ(s_±)`, `s_± = ½ + x ± it`.
-/

open ArithmeticFunction Complex

namespace RHTower

noncomputable section

/-- The arithmetic function `n ↦ n^{c}` with value `0` at `0`. -/
def twistPow (c : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ c, by simp⟩

theorem twistPow_apply {c : ℂ} {n : ℕ} (hn : n ≠ 0) : twistPow c n = (n : ℂ) ^ c := by
  simp [twistPow, hn]

/-- **Twisted zeta series.** `Σ n^{c} n^{−w} = ζ(w − c)` for `Re(w − c) > 1`. -/
theorem LSeriesHasSum_twistPow {c w : ℂ} (hw : 1 < (w - c).re) :
    LSeriesHasSum (fun n => twistPow c n) w (riemannZeta (w - c)) := by
  have hz := ArithmeticFunction.LSeriesHasSum_zeta hw
  unfold LSeriesHasSum at hz ⊢
  convert hz using 1
  funext n
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · rfl
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [twistPow_apply hn, zeta_apply_ne hn, Nat.cast_one,
      Complex.cpow_sub _ _ hn']
    have h1 : (n : ℂ) ^ c ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hn')
    have h2 : (n : ℂ) ^ w ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hn')
    field_simp

/-- The Eisenstein coefficients `a_τ(n) = Σ_{d ∣ n} d^{iτ}(n/d)^{−iτ}`. -/
def eisensteinCoeff (τ : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) ^ ((τ : ℂ) * I) * ((n / d : ℕ) : ℂ) ^ (-((τ : ℂ) * I))

theorem eisensteinCoeff_eq (τ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (twistPow ((τ : ℂ) * I) * twistPow (-((τ : ℂ) * I))) n = eisensteinCoeff τ n := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => twistPow ((τ : ℂ) * I) a
    * twistPow (-((τ : ℂ) * I)) b)]
  unfold eisensteinCoeff
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hq0 : n / d ≠ 0 := by
    have hdvd := Nat.dvd_of_mem_divisors hd
    exact Nat.div_ne_zero_iff_of_dvd hdvd |>.mpr ⟨hn, hd0⟩
  rw [twistPow_apply hd0, twistPow_apply hq0]

/-- **The slice's Dirichlet series is the Eisenstein L-series:**
`Σ a_τ(n) n^{−w} = ζ(w − iτ) ζ(w + iτ)` for `Re w > 1`. -/
theorem LSeries_eisensteinCoeff (τ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    LSeries (eisensteinCoeff τ) w = riemannZeta (w - τ * I) * riemannZeta (w + τ * I) := by
  have h1 : 1 < (w - (τ : ℂ) * I).re := by simpa using hw
  have h2 : 1 < (w - -((τ : ℂ) * I)).re := by simpa using hw
  have hmul := ArithmeticFunction.LSeriesHasSum_mul (LSeriesHasSum_twistPow h1)
    (LSeriesHasSum_twistPow h2)
  rw [sub_neg_eq_add] at hmul
  have hcongr : LSeriesHasSum (eisensteinCoeff τ) w
      (riemannZeta (w - τ * I) * riemannZeta (w + τ * I)) :=
    (LSeriesHasSum_congr w _ (fun hn => eisensteinCoeff_eq τ hn)).mp hmul
  exact hcongr.LSeries_eq


/-- **The slice is the completed Eisenstein L-function.**  For real `x > ½`,
`ξ(½+x+it) ξ(½−x+it) = G_t(x) · Σ_n a_t(n) n^{−(½+x)}`. -/
theorem xiSliceProduct_eq_gamma_mul_LSeries_eisenstein (t : ℝ) {x : ℝ} (hx : 1 / 2 < x) :
    xiSliceProduct t x =
      ((1 / 2 + x + t * I) * (1 / 2 + x + t * I - 1) / 2 * Gammaℝ (1 / 2 + x + t * I))
        * ((1 / 2 + x - t * I) * (1 / 2 + x - t * I - 1) / 2 * Gammaℝ (1 / 2 + x - t * I))
        * LSeries (eisensteinCoeff t) (1 / 2 + x) := by
  set s₁ : ℂ := 1 / 2 + x + t * I with hs₁
  set s₂ : ℂ := 1 / 2 + x - t * I with hs₂
  have hre₁ : s₁.re = 1 / 2 + x := by simp [hs₁]
  have hre₂ : s₂.re = 1 / 2 + x := by simp [hs₂]
  have hne : ∀ s : ℂ, s.re = 1 / 2 + x → s ≠ 0 ∧ s ≠ 1 := fun s hs => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, zero_re] at hs; linarith
    · rw [h, one_re] at hs; linarith
  have hcomp : ∀ s : ℂ, s.re = 1 / 2 + x → completedRiemannZeta s = Gammaℝ s * riemannZeta s :=
    fun s hs => by
      have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; linarith)
      rw [riemannZeta_def_of_ne_zero (hne s hs).1]
      field_simp
  unfold xiSliceProduct
  have hrefl : (1 / 2 - (x : ℂ) + t * I) = 1 - s₂ := by rw [hs₂]; ring
  rw [hrefl, xi_one_sub, show (1 / 2 + (x : ℂ) + t * I) = s₁ from rfl,
    xi_eq_mul_completedRiemannZeta (hne s₁ hre₁).1 (hne s₁ hre₁).2,
    xi_eq_mul_completedRiemannZeta (hne s₂ hre₂).1 (hne s₂ hre₂).2,
    hcomp s₁ hre₁, hcomp s₂ hre₂,
    LSeries_eisensteinCoeff t (w := 1 / 2 + x) (by simp; linarith)]
  have e₁ : (1 / 2 + (x : ℂ)) + t * I = s₁ := by rw [hs₁]
  have e₂ : (1 / 2 + (x : ℂ)) - t * I = s₂ := by rw [hs₂]
  rw [e₁, e₂]
  ring

end

end RHTower
