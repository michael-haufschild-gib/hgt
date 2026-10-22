import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticMobiusEndpoint
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusConnection
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The all-prime adiabatic Euler connection

For positive adiabatic parameter, the full Möbius series differentiates termwise under one
summable majorant `log n / n²`.  The resulting logarithmic Möbius series is exactly the physical
von Mangoldt connection.  The proof does not repeat the double-series convolution: the exact
gauge `M_a h(x) = x^a f_(exp(-a·)h)(x)` cancels `m^{-a}(mx)^a`, reducing the claim to the already
formalized critical connection `Λ * μ = -μ log`.
-/

namespace RHTower

open Filter Topology SchwartzMap ArithmeticFunction

noncomputable section

/-- A single term of the full adiabatic Möbius inverse. -/
def deningerAdiabaticMobiusTerm
    (h : DeningerMeyerSource) (x : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  (((((moebius n : ℤ) : ℝ) * deningerAdiabaticMobiusCoefficient a n : ℝ)) : ℂ) *
    deningerLogPull
      (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      ((n : ℝ) * x)

/-- The termwise parameter derivative `-μ(n) log(n)n^{-a}H(nx)`. -/
def deningerAdiabaticMobiusDerivativeTerm
    (h : DeningerMeyerSource) (x : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  (((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) *
      deningerAdiabaticMobiusCoefficient a n : ℝ)) : ℂ) *
    deningerLogPull
      (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      ((n : ℝ) * x)

/-- The full parameter derivative of the adiabatic inverse. -/
def deningerAdiabaticMobiusParameterDerivative
    (a : ℝ) (h : DeningerMeyerSource) (x : ℝ) : ℂ :=
  ∑' n : ℕ, deningerAdiabaticMobiusDerivativeTerm h x n a

theorem deningerAdiabaticMobiusTerm_hasDerivAt
    (h : DeningerMeyerSource) (x : ℝ) (n : ℕ) (a : ℝ) :
    HasDerivAt (deningerAdiabaticMobiusTerm h x n)
      (deningerAdiabaticMobiusDerivativeTerm h x n a) a := by
  have hlin : HasDerivAt (fun b : ℝ => -b * Real.log (n : ℝ))
      (-Real.log (n : ℝ)) a := by
    simpa using (hasDerivAt_id a).neg.mul_const (Real.log (n : ℝ))
  have hexp : HasDerivAt
      (fun b : ℝ => Real.exp (-b * Real.log (n : ℝ)))
      (-Real.log (n : ℝ) * Real.exp (-a * Real.log (n : ℝ))) a :=
    by
      have hraw := (Real.hasDerivAt_exp _).comp a hlin
      have hfun : (Real.exp ∘ fun b : ℝ => -b * Real.log (n : ℝ)) =ᶠ[𝓝 a]
          (fun b : ℝ => Real.exp (-b * Real.log (n : ℝ))) :=
        Eventually.of_forall fun _ => rfl
      exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hreal : HasDerivAt
      (fun b : ℝ => (((moebius n : ℤ) : ℝ) *
        Real.exp (-b * Real.log (n : ℝ))))
      (((moebius n : ℤ) : ℝ) *
        (-Real.log (n : ℝ) * Real.exp (-a * Real.log (n : ℝ)))) a :=
    by
      have hraw := (hasDerivAt_const a ((moebius n : ℤ) : ℝ)).mul hexp
      have hfun : ((fun _ : ℝ => ((moebius n : ℤ) : ℝ)) *
          fun b : ℝ => Real.exp (-b * Real.log (n : ℝ))) =ᶠ[𝓝 a]
          (fun b : ℝ => ((moebius n : ℤ) : ℝ) *
            Real.exp (-b * Real.log (n : ℝ))) :=
        Eventually.of_forall fun _ => rfl
      exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hcomplex := hreal.ofReal_comp.mul_const
    (deningerLogPull
      (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      ((n : ℝ) * x))
  change HasDerivAt
    (fun b : ℝ =>
      ((((moebius n : ℤ) : ℝ) * Real.exp (-b * Real.log (n : ℝ)) : ℝ) : ℂ) *
        deningerLogPull
          (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
          ((n : ℝ) * x))
    (((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) *
        Real.exp (-a * Real.log (n : ℝ)) : ℝ) : ℂ) *
      deningerLogPull
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
        ((n : ℝ) * x)) a
  have heq :
      (((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) *
          Real.exp (-a * Real.log (n : ℝ)) : ℝ)) : ℂ) *
          deningerLogPull
            (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
            ((n : ℝ) * x) =
        ((((moebius n : ℤ) : ℝ) *
          (-Real.log (n : ℝ) * Real.exp (-a * Real.log (n : ℝ))) : ℝ) : ℂ) *
          deningerLogPull
            (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
            ((n : ℝ) * x) := by
    congr 1
    norm_cast
    ring
  rw [heq]
  exact hcomplex

/-- The Möbius coefficients have norm at most one for positive parameter. -/
theorem deningerAdiabaticMobiusCoefficient_norm_le_one
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    |deningerAdiabaticMobiusCoefficient a n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deningerAdiabaticMobiusCoefficient]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [deningerAdiabaticMobiusCoefficient, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr ha.le) (Real.log_nonneg hn1))

theorem deningerAdiabaticMobiusTerm_summable
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => deningerAdiabaticMobiusTerm h x n a) := by
  obtain ⟨C, hC0, hC⟩ := deningerLogPull_norm_le_inv_sq
    (DeningerMeyerSource.toSource h).2
  have hs : Summable fun n : ℕ => (C / x ^ 2) * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded hs fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deningerAdiabaticMobiusTerm]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnR hx
    have hpull := (hC ((n : ℝ) * x) hnx).2
    have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rcases moebius_eq_or n with hm | hm | hm <;> rw [hm] <;> norm_num
    have hcoeff := deningerAdiabaticMobiusCoefficient_norm_le_one ha n
    rw [deningerAdiabaticMobiusTerm, norm_mul]
    have hscalar :
        ‖(((((moebius n : ℤ) : ℝ) *
          deningerAdiabaticMobiusCoefficient a n : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hmuR : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hmu
      nlinarith [abs_nonneg (((moebius n : ℤ) : ℝ)),
        abs_nonneg (deningerAdiabaticMobiusCoefficient a n)]
    refine le_trans (mul_le_mul hscalar hpull (norm_nonneg _) zero_le_one) (le_of_eq ?_)
    rw [mul_pow]
    field_simp

/-- Uniform derivative majorant on the whole positive parameter ray. -/
theorem deningerAdiabaticMobiusDerivativeTerm_norm_le
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x)
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖deningerAdiabaticMobiusDerivativeTerm h x n a‖ ≤
      (Classical.choose (deningerLogPull_norm_le_inv_sq
        (DeningerMeyerSource.toSource h).2) / x ^ 2) *
        (Real.log n / (n : ℝ) ^ 2) := by
  let C : ℝ := Classical.choose (deningerLogPull_norm_le_inv_sq
    (DeningerMeyerSource.toSource h).2)
  have hC := (Classical.choose_spec (deningerLogPull_norm_le_inv_sq
    (DeningerMeyerSource.toSource h).2)).2
  change ∀ y : ℝ, 0 < y →
    ‖deningerLogPull
      (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) y‖ ≤
        C * y ^ 2 ∧
      ‖deningerLogPull
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) y‖ ≤
        C / y ^ 2 at hC
  change _ ≤ (C / x ^ 2) * (Real.log n / (n : ℝ) ^ 2)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deningerAdiabaticMobiusDerivativeTerm]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnR hx
    have hpull := (hC ((n : ℝ) * x) hnx).2
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rcases moebius_eq_or n with hm | hm | hm <;> rw [hm] <;> norm_num
    have hcoeff := deningerAdiabaticMobiusCoefficient_norm_le_one ha n
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    simp only [deningerAdiabaticMobiusDerivativeTerm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hlog]
    have hscalar : |((moebius n : ℤ) : ℝ)| * Real.log (n : ℝ) *
        |deningerAdiabaticMobiusCoefficient a n| ≤ Real.log (n : ℝ) := by
      have hprod : |((moebius n : ℤ) : ℝ)| *
          |deningerAdiabaticMobiusCoefficient a n| ≤ 1 := by
        simpa using mul_le_mul hmu hcoeff
          (abs_nonneg (deningerAdiabaticMobiusCoefficient a n)) zero_le_one
      calc
        |((moebius n : ℤ) : ℝ)| * Real.log (n : ℝ) *
            |deningerAdiabaticMobiusCoefficient a n| =
          Real.log (n : ℝ) *
            (|((moebius n : ℤ) : ℝ)| *
              |deningerAdiabaticMobiusCoefficient a n|) := by ring
        _ ≤ Real.log (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hprod hlog
        _ = Real.log (n : ℝ) := mul_one _
    refine le_trans (mul_le_mul hscalar hpull (norm_nonneg _) hlog) (le_of_eq ?_)
    rw [mul_pow]
    field_simp

/-- **Termwise all-prime differentiation.** -/
theorem hasDerivAt_deningerAdiabaticMobiusPreimage
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => deningerAdiabaticMobiusPreimage b h x)
      (deningerAdiabaticMobiusParameterDerivative a h x) a := by
  let C : ℝ := Classical.choose (deningerLogPull_norm_le_inv_sq
    (DeningerMeyerSource.toSource h).2)
  let u : ℕ → ℝ := fun n => (C / x ^ 2) * (Real.log n / (n : ℝ) ^ 2)
  have hu : Summable u := Sieve.summable_log_div_sq.mul_left (C / x ^ 2)
  have hderiv : ∀ n : ℕ, ∀ b ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (deningerAdiabaticMobiusTerm h x n)
        (deningerAdiabaticMobiusDerivativeTerm h x n b) b :=
    fun n b _ => deningerAdiabaticMobiusTerm_hasDerivAt h x n b
  have hbound : ∀ n : ℕ, ∀ b ∈ Set.Ioi (0 : ℝ),
      ‖deningerAdiabaticMobiusDerivativeTerm h x n b‖ ≤ u n := by
    intro n b hb
    exact deningerAdiabaticMobiusDerivativeTerm_norm_le h hx hb n
  have hsum := deningerAdiabaticMobiusTerm_summable h hx ha
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi
    hderiv hbound ha hsum ha
  have hseries : ∀ b : ℝ,
      deningerAdiabaticMobiusPreimage b h x =
        ∑' n : ℕ, deningerAdiabaticMobiusTerm h x n b := by
    intro b
    simpa only [deningerAdiabaticMobiusTerm] using
      deningerAdiabaticMobiusPreimage_eq_tsum b h hx
  exact hmain.congr_of_eventuallyEq
    (Eventually.of_forall fun b => hseries b)

/-- The positive Euler/von-Mangoldt connection at adiabatic parameter `a`. -/
def deningerAdiabaticEulerPositive
    (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' m : ℕ, (((vonMangoldt m : ℝ) *
    deningerAdiabaticMobiusCoefficient a m : ℝ) : ℂ) * f ((m : ℝ) * x)

/-- The parameter derivative is the gauged critical Möbius derivative. -/
theorem deningerAdiabaticMobiusParameterDerivative_eq_gauge
    (a : ℝ) (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerAdiabaticMobiusParameterDerivative a h x =
      ((x ^ a : ℝ) : ℂ) * deningerMobiusDerivative
        (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
          DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x := by
  rw [deningerAdiabaticMobiusParameterDerivative, deningerMobiusDerivative,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deningerAdiabaticMobiusDerivativeTerm]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnR hx
    rw [deningerAdiabaticMobiusDerivativeTerm]
    have htilt :
        deningerLogPull
            (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
              DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) ((n : ℝ) * x) =
          ((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ) *
            deningerLogPull
              (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                𝓢(ℝ, ℂ))) ((n : ℝ) * x) := by
      simp only [deningerLogPull_apply]
      rw [deningerAdiabaticSource_apply, Real.log_mul hnR.ne' hx.ne']
    rw [htilt, deningerAdiabaticMobiusCoefficient, Real.rpow_def_of_pos hx]
    have hscalar :
        Real.exp (Real.log x * a) *
            Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) =
          Real.exp (-a * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hscalarC :
        ((Real.exp (Real.log x * a) : ℝ) : ℂ) *
            ((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ) =
          ((Real.exp (-a * Real.log (n : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hscalar]
    simp only [Complex.ofReal_mul]
    calc
      _ = ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
          (((Real.exp (-a * Real.log (n : ℝ)) : ℝ) : ℂ) *
            deningerLogPull
              (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                𝓢(ℝ, ℂ))) ((n : ℝ) * x)) := by ac_rfl
      _ = ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
          ((((Real.exp (Real.log x * a) : ℝ) : ℂ) *
            ((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ)) *
              deningerLogPull
                (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                  𝓢(ℝ, ℂ))) ((n : ℝ) * x)) := by rw [hscalarC]
      _ = _ := by ac_rfl

/-- **Euler parallel-inverse law** `∂ₐMₐ = Aₐ⁺Mₐ` on the positive ray. -/
theorem deningerAdiabaticEulerPositive_eq_parameterDerivative
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerAdiabaticEulerPositive a (deningerAdiabaticMobiusPreimage a h) x =
      deningerAdiabaticMobiusParameterDerivative a h x := by
  have hcritical := deningerMobius_connection
    (DeningerMeyerSource.toSource (deningerAdiabaticSource a h)).2 hx
  rw [deningerAdiabaticEulerPositive]
  calc
    (∑' m : ℕ, (((vonMangoldt m : ℝ) *
        deningerAdiabaticMobiusCoefficient a m : ℝ) : ℂ) *
          deningerAdiabaticMobiusPreimage a h ((m : ℝ) * x)) =
      ((x ^ a : ℝ) : ℂ) *
        ∑' m : ℕ, ((vonMangoldt m : ℝ) : ℂ) *
          deningerMobiusPreimage
            (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
              DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) ((m : ℝ) * x) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [deningerAdiabaticMobiusCoefficient]
      · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hmx : (0 : ℝ) < (m : ℝ) * x := mul_pos hmR hx
        rw [deningerAdiabaticMobiusPreimage]
        have hpow : ((m : ℝ) * x) ^ a = (m : ℝ) ^ a * x ^ a :=
          Real.mul_rpow hmR.le hx.le
        rw [hpow, deningerAdiabaticMobiusCoefficient,
          Real.rpow_def_of_pos hmR]
        have hcancel : Real.exp (-a * Real.log (m : ℝ)) *
            Real.exp (Real.log (m : ℝ) * a) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        have hcancelC :
            ((Real.exp (-a * Real.log (m : ℝ)) : ℝ) : ℂ) *
                ((Real.exp (Real.log (m : ℝ) * a) : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, hcancel]
          norm_num
        simp only [Complex.ofReal_mul]
        calc
          _ = (((Real.exp (-a * Real.log (m : ℝ)) : ℝ) : ℂ) *
              ((Real.exp (Real.log (m : ℝ) * a) : ℝ) : ℂ)) *
                (((vonMangoldt m : ℝ) : ℂ) *
                  (((x ^ a : ℝ) : ℂ) *
                    deningerMobiusPreimage
                      (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
                        DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) ((m : ℝ) * x))) := by ac_rfl
          _ = _ := by rw [hcancelC, one_mul]; ac_rfl
    _ = ((x ^ a : ℝ) : ℂ) * deningerMobiusDerivative
        (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
          DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x := by rw [hcritical]
    _ = deningerAdiabaticMobiusParameterDerivative a h x :=
      (deningerAdiabaticMobiusParameterDerivative_eq_gauge a h hx).symm

/-- Closed connection form of the parameter derivative. -/
theorem hasDerivAt_deningerAdiabaticMobiusPreimage_euler
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => deningerAdiabaticMobiusPreimage b h x)
      (deningerAdiabaticEulerPositive a (deningerAdiabaticMobiusPreimage a h) x) a := by
  rw [deningerAdiabaticEulerPositive_eq_parameterDerivative ha h hx]
  exact hasDerivAt_deningerAdiabaticMobiusPreimage h hx ha

end

end RHTower
