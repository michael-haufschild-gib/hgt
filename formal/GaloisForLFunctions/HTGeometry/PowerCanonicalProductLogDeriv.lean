import GaloisForLFunctions.HTGeometry.BarnesKernelMellin
import GaloisForLFunctions.HTGeometry.RationalPowerCyclicNorm
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The logarithmic derivative of a power canonical product

The Weierstrass factor of genus `g` has logarithmic derivative `-z^g/(1-z)`, so the Euler operator
applied to the canonical product `W_s(z) = ∏_{n ≥ 1} E_g(-z/n^s)` collapses on the positive axis to
a sum of model factors:

```text
x W_s'(x)/W_s(x) = ∑_{n ≥ 1} (-1)^g (x/n^s)^{g+1} / (1 + x/n^s) .
```

Every term decays like `n^{-s(g+1)}`, which is summable exactly because the genus
`g = ⌊1/s⌋` is admissible, and no factor vanishes on the positive axis because all the zeros of
`W_s` are negative.  This identifies the object of the Barnes expansion with the logarithmic
derivative of the canonical product itself.
-/

open Complex Filter Set

namespace HTGeometry

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The logarithmic derivative of a rescaled primary factor -/

/-- The derivative of a rescaled Weierstrass factor. -/
theorem hasDerivAt_primaryFactor_scaled (g : ℕ) (c z : ℂ) :
    HasDerivAt (fun w : ℂ => primaryFactor g (w / c))
      ((-(z / c) ^ g * Complex.exp (primaryExponent g (z / c))) * (1 / c)) z := by
  have hd1 : HasDerivAt (fun w : ℂ => w / c) (1 / c) z := by
    simpa using (hasDerivAt_id z).div_const c
  exact (primaryFactor_hasDerivAt g (z / c)).comp z hd1

/-- The logarithmic derivative of a rescaled Weierstrass factor. -/
theorem logDeriv_primaryFactor_scaled (g : ℕ) {c : ℂ} (hc : c ≠ 0) {z : ℂ} (hz : z / c ≠ 1) :
    logDeriv (fun w : ℂ => primaryFactor g (w / c)) z
      = -(z / c) ^ g / (c * (1 - z / c)) := by
  have hcomp := hasDerivAt_primaryFactor_scaled g c z
  have hval : primaryFactor g (z / c)
      = (1 - z / c) * Complex.exp (primaryExponent g (z / c)) := rfl
  have hexp : Complex.exp (primaryExponent g (z / c)) ≠ 0 := Complex.exp_ne_zero _
  have hsub : (1 : ℂ) - z / c ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [logDeriv_apply, hcomp.deriv, hval]
  field_simp

/-- Every rescaled primary factor is differentiable. -/
theorem differentiable_primaryFactor_scaled (g : ℕ) (c : ℂ) :
    Differentiable ℂ fun w : ℂ => primaryFactor g (w / c) := by
  intro w
  exact (hasDerivAt_primaryFactor_scaled g c w).differentiableAt

/-! ### The terms of the power canonical product on the positive axis -/

variable {s : ℝ}

/-- The `n`-th term of the logarithmic derivative of `W_s` on the positive axis, without its
parity sign. -/
def powerLogDerivTerm (s x : ℝ) (n : ℕ) : ℝ :=
  (x / ((n : ℝ) + 1) ^ s) ^ (powerGenus s)
    / (((n : ℝ) + 1) ^ s * (1 + x / ((n : ℝ) + 1) ^ s))

theorem powerScale_pos (s : ℝ) (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1) ^ s :=
  Real.rpow_pos_of_pos (by positivity) s

theorem powerZero_eq_neg (s : ℝ) (n : ℕ) :
    powerZero s n = -((((n : ℝ) + 1) ^ s : ℝ) : ℂ) := rfl

theorem ofReal_div_powerZero {x : ℝ} (s : ℝ) (n : ℕ) :
    ((x : ℝ) : ℂ) / powerZero s n = -(((x / ((n : ℝ) + 1) ^ s : ℝ)) : ℂ) := by
  rw [powerZero_eq_neg, div_neg, Complex.ofReal_div]

theorem div_powerZero_ne_one {x : ℝ} (hx : 0 < x) (s : ℝ) (n : ℕ) :
    ((x : ℝ) : ℂ) / powerZero s n ≠ 1 := by
  rw [ofReal_div_powerZero]
  intro hcon
  have hre := congrArg Complex.re hcon
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.one_re] at hre
  have hpos : (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := div_pos hx (powerScale_pos s n)
  linarith

/-- **The `n`-th logarithmic-derivative term on the positive axis**, in closed real form. -/
theorem logDeriv_powerFactor_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    logDeriv (fun w : ℂ => primaryFactor (powerGenus s) (w / powerZero s n)) ((x : ℝ) : ℂ)
      = ((-1) ^ (powerGenus s) : ℂ) * ((powerLogDerivTerm s x n : ℝ) : ℂ) := by
  have hA : (0 : ℝ) < ((n : ℝ) + 1) ^ s := powerScale_pos s n
  have ht : (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := div_pos hx hA
  have hAne : ((((n : ℝ) + 1) ^ s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hA)
  have hden : ((1 + x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith)
  rw [logDeriv_primaryFactor_scaled _ (powerZero_ne_zero s n) (div_powerZero_ne_one hx s n),
    ofReal_div_powerZero, powerZero_eq_neg, powerLogDerivTerm]
  push_cast
  rw [neg_pow]
  field_simp
  ring

theorem powerLogDerivTerm_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < powerLogDerivTerm s x n := by
  have hA : (0 : ℝ) < ((n : ℝ) + 1) ^ s := powerScale_pos s n
  have ht : (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := div_pos hx hA
  rw [powerLogDerivTerm]
  positivity

theorem powerLogDerivTerm_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    powerLogDerivTerm s x n
      ≤ x ^ (powerGenus s) * (1 / ‖powerZero s n‖ ^ (powerGenus s + 1)) := by
  have hA : (0 : ℝ) < ((n : ℝ) + 1) ^ s := powerScale_pos s n
  have ht : (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := div_pos hx hA
  have hnorm : ‖powerZero s n‖ = ((n : ℝ) + 1) ^ s := norm_powerZero s n
  rw [powerLogDerivTerm, hnorm]
  rw [div_pow, div_le_iff₀ (by positivity)]
  have hstep : x ^ (powerGenus s) / (((n : ℝ) + 1) ^ s) ^ (powerGenus s)
      ≤ x ^ (powerGenus s) / (((n : ℝ) + 1) ^ s) ^ (powerGenus s)
        * (1 + x / ((n : ℝ) + 1) ^ s) := by
    nlinarith [div_pos (pow_pos hx (powerGenus s)) (pow_pos hA (powerGenus s))]
  calc x ^ (powerGenus s) / (((n : ℝ) + 1) ^ s) ^ (powerGenus s)
      ≤ x ^ (powerGenus s) / (((n : ℝ) + 1) ^ s) ^ (powerGenus s)
          * (1 + x / ((n : ℝ) + 1) ^ s) := hstep
    _ = x ^ (powerGenus s) * (1 / (((n : ℝ) + 1) ^ s) ^ (powerGenus s + 1))
          * (((n : ℝ) + 1) ^ s * (1 + x / ((n : ℝ) + 1) ^ s)) := by
        field_simp
        ring

theorem summable_powerLogDerivTerm (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => powerLogDerivTerm s x n := by
  refine Summable.of_nonneg_of_le (fun n => le_of_lt (powerLogDerivTerm_pos hx n))
    (fun n => powerLogDerivTerm_le hx n) ?_
  exact (powerZero_summable hs).mul_left _

theorem summable_logDeriv_powerFactor (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      logDeriv (fun w : ℂ => primaryFactor (powerGenus s) (w / powerZero s n)) ((x : ℝ) : ℂ) := by
  have hcongr : (fun n : ℕ =>
      logDeriv (fun w : ℂ => primaryFactor (powerGenus s) (w / powerZero s n)) ((x : ℝ) : ℂ))
      = fun n : ℕ => ((-1) ^ (powerGenus s) : ℂ) * ((powerLogDerivTerm s x n : ℝ) : ℂ) :=
    funext fun n => logDeriv_powerFactor_eq hx n
  rw [hcongr]
  have hcast : Summable fun n : ℕ => ((powerLogDerivTerm s x n : ℝ) : ℂ) := by
    refine Summable.of_norm ?_
    refine (summable_powerLogDerivTerm hs hx).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (powerLogDerivTerm_pos hx n)]
  exact hcast.mul_left _

/-! ### Nonvanishing on the positive axis -/

theorem primaryFactor_div_powerZero_ne_zero {x : ℝ} (hx : 0 < x) (n : ℕ) :
    primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) ≠ 0 := by
  rw [primaryFactor]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact sub_ne_zero.mpr (Ne.symm (div_powerZero_ne_one hx s n))

/-- **The power canonical product does not vanish on the positive axis.** -/
theorem powerCanonicalProduct_ne_zero (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    powerCanonicalProduct s ((x : ℝ) : ℂ) ≠ 0 := by
  have hsum : Summable fun n : ℕ =>
      ‖primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) - 1‖ :=
    canonicalProduct_sub_one_norm_summable (powerGenus s) (powerZero s) (powerZero_ne_zero s)
      (powerZero_summable hs) ((x : ℝ) : ℂ)
  have hne : ∀ n : ℕ,
      1 + (primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) - 1) ≠ 0 := by
    intro n
    rw [show (1 : ℂ) + (primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) - 1)
      = primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) by ring]
    exact primaryFactor_div_powerZero_ne_zero hx n
  have hprod := tprod_one_add_ne_zero_of_summable hne hsum
  have hshape : (fun n : ℕ =>
      1 + (primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) - 1))
      = fun n : ℕ => primaryFactor (powerGenus s) (((x : ℝ) : ℂ) / powerZero s n) := by
    funext n
    ring
  rw [hshape] at hprod
  exact hprod

/-! ### The logarithmic derivative as a sum -/

/-- **The logarithmic derivative of `W_s` on the positive axis is the sum of the factor
logarithmic derivatives.** -/
theorem logDeriv_powerCanonicalProduct_eq_tsum (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    logDeriv (powerCanonicalProduct s) ((x : ℝ) : ℂ)
      = ∑' n : ℕ,
        logDeriv (fun w : ℂ => primaryFactor (powerGenus s) (w / powerZero s n))
          ((x : ℝ) : ℂ) := by
  have hmul : MultipliableLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) => primaryFactor (powerGenus s) (z / powerZero s n))
      (Set.univ : Set ℂ) :=
    (canonicalProduct_hasProdLocallyUniformlyOn (powerGenus s) (powerZero s)
      (powerZero_ne_zero s) (powerZero_summable hs)).multipliableLocallyUniformlyOn
  exact logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ ((x : ℝ) : ℂ))
    (fun n => primaryFactor_div_powerZero_ne_zero hx n)
    (fun n => (differentiable_primaryFactor_scaled (powerGenus s) (powerZero s n)).differentiableOn)
    (summable_logDeriv_powerFactor hs hx) hmul (powerCanonicalProduct_ne_zero hs hx)

/-- The Euler operator applied to the `n`-th term is the model factor with the genus sign. -/
theorem ofReal_mul_logDeriv_powerFactor {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((x : ℝ) : ℂ)
        * logDeriv (fun w : ℂ => primaryFactor (powerGenus s) (w / powerZero s n))
          ((x : ℝ) : ℂ)
      = ((-1) ^ (powerGenus s) : ℂ)
        * barnesModel (powerGenus s) (x / ((n : ℝ) + 1) ^ s) := by
  have hA : (0 : ℝ) < ((n : ℝ) + 1) ^ s := powerScale_pos s n
  have ht : (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := div_pos hx hA
  have hAne : ((n : ℝ) + 1) ^ s ≠ 0 := ne_of_gt hA
  have htne : 1 + x / ((n : ℝ) + 1) ^ s ≠ 0 := by positivity
  have hxeq : ((n : ℝ) + 1) ^ s * (x / ((n : ℝ) + 1) ^ s) = x := mul_div_cancel₀ x hAne
  have hkey : ∀ A t : ℝ, A ≠ 0 → 1 + t ≠ 0 →
      (A * t) * (t ^ (powerGenus s) / (A * (1 + t)))
        = t ^ (powerGenus s + 1) / (1 + t) := by
    intro A t hAne' hden'
    field_simp
    ring
  have hreal : x * powerLogDerivTerm s x n
      = (x / ((n : ℝ) + 1) ^ s) ^ (powerGenus s + 1) / (1 + x / ((n : ℝ) + 1) ^ s) := by
    rw [powerLogDerivTerm]
    calc x * ((x / ((n : ℝ) + 1) ^ s) ^ (powerGenus s)
            / (((n : ℝ) + 1) ^ s * (1 + x / ((n : ℝ) + 1) ^ s)))
        = (((n : ℝ) + 1) ^ s * (x / ((n : ℝ) + 1) ^ s))
            * ((x / ((n : ℝ) + 1) ^ s) ^ (powerGenus s)
              / (((n : ℝ) + 1) ^ s * (1 + x / ((n : ℝ) + 1) ^ s))) := by rw [hxeq]
      _ = (x / ((n : ℝ) + 1) ^ s) ^ (powerGenus s + 1) / (1 + x / ((n : ℝ) + 1) ^ s) :=
          hkey _ _ hAne htne
  rw [logDeriv_powerFactor_eq hx n, barnesModel]
  have hden : (1 : ℂ) + ((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) ≠ 0 := by
    have hcast : (1 : ℂ) + ((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ)
        = ((1 + x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hgoal : ((x : ℝ) : ℂ) * ((powerLogDerivTerm s x n : ℝ) : ℂ)
      = ((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) ^ (powerGenus s + 1)
        / (1 + ((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul, hreal]
    push_cast
    ring
  calc ((x : ℝ) : ℂ) * (((-1) ^ (powerGenus s) : ℂ) * ((powerLogDerivTerm s x n : ℝ) : ℂ))
      = ((-1) ^ (powerGenus s) : ℂ)
          * (((x : ℝ) : ℂ) * ((powerLogDerivTerm s x n : ℝ) : ℂ)) := by ring
    _ = ((-1) ^ (powerGenus s) : ℂ)
          * (((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) ^ (powerGenus s + 1)
            / (1 + ((x / ((n : ℝ) + 1) ^ s : ℝ) : ℂ))) := by rw [hgoal]

/-- **The Euler logarithmic derivative of the power canonical product.**  On the positive axis

`x W_s'(x)/W_s(x) = ∑_{n ≥ 1} (-1)^g (x/n^s)^{g+1}/(1 + x/n^s)`. -/
theorem ofReal_mul_logDeriv_powerCanonicalProduct (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ) * logDeriv (powerCanonicalProduct s) ((x : ℝ) : ℂ)
      = ∑' n : ℕ, ((-1) ^ (powerGenus s) : ℂ)
        * barnesModel (powerGenus s) (x / ((n : ℝ) + 1) ^ s) := by
  rw [logDeriv_powerCanonicalProduct_eq_tsum hs hx, ← tsum_mul_left]
  exact tsum_congr fun n => ofReal_mul_logDeriv_powerFactor hx n

end

end HTGeometry
