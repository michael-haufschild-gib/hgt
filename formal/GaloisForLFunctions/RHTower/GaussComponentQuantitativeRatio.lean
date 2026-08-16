import GaloisForLFunctions.RHTower.GaussComponentSampledRatio
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog

/-!
# Quantitative finite-shift laws for Gauss components

The qualitative sampled-ratio theorem is not strong enough to decide whether the
actual Gauss diagonal differs summably from its moving principal model.  This
module upgrades the vertical digamma asymptotic to explicit transport bounds.

For every component there is a constant `C` such that its exact logarithmic
derivative differs from the universal clock by `C/t`.  Integrating over a window
of length `h` and retaining the curvature of the logarithmic clock gives the
sharp structural envelope

`B_forward = (C h + h²) / t`.

The exact forward ratio differs from the frozen phase by at most `B_forward exp
B_forward`.  The backward law is frozen at the terminal height and has envelope

`B_backward = (C h + 2 h²) / (t-h)`.

Thus both signs of the Fourier lattice shift now carry quantitative control; the
quadratic term records the genuine moving-clock obstruction rather than a proof
artifact.
-/

namespace RHTower

open Complex Filter Topology MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem exists_gaussComponentVerticalLogDerivError_inv_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 * (m : ℝ) ≤ t →
      ‖gaussComponentVerticalLogDerivError k t‖ ≤ C / t := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 ≤ gaussComponentOffset k := by
    rw [gaussComponentOffset]
    positivity
  have hdelta : 0 ≤ gaussComponentDelta m := by
    rw [gaussComponentDelta]
    positivity
  set M : ℝ := gaussComponentOffset k + gaussComponentDelta m + 1 with hM
  have hMpos : 0 < M := by dsimp [M]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_digamma_sub_vertLog hMpos
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 2 * (m : ℝ)) ht
  set tau : ℝ := t / (2 * (m : ℝ)) with htau
  have htau1 : 1 ≤ tau := by
    rw [htau, le_div_iff₀ (by positivity)]
    simpa only [one_mul] using ht
  have htaupos : 0 < tau := lt_of_lt_of_le zero_lt_one htau1
  have haM : gaussComponentOffset k ≤ M := by dsimp [M]; linarith
  have halM : gaussComponentOffset k + gaussComponentDelta m ≤ M := by
    dsimp [M]
    linarith
  have hu := hbound (gaussComponentOffset k) tau ha haM htau1
  have hlpos := hbound (gaussComponentOffset k + gaussComponentDelta m) tau
    (add_nonneg ha hdelta) halM htau1
  have hconjVert : starRingEnd ℂ (vertLog tau) =
      ((Real.log tau : ℝ) : ℂ) - ((Real.pi : ℂ) / 2) * Complex.I := by
    have hpi : starRingEnd ℂ ((Real.pi : ℂ) / 2) =
        ((Real.pi : ℂ) / 2) := by
      rw [map_div₀, Complex.conj_ofReal, map_ofNat]
    rw [vertLog, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hpi]
    ring
  have hl :
      ‖Complex.digamma
          (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
            (tau : ℂ) * Complex.I) -
        (((Real.log tau : ℝ) : ℂ) - ((Real.pi : ℂ) / 2) * Complex.I)‖ ≤ C / tau := by
    have harg :
        (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
            (tau : ℂ) * Complex.I)
          = starRingEnd ℂ
              (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) +
                (tau : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [← hconjVert, harg, ReflectedDigammaAnomaly.digamma_conj, ← map_sub]
    change ‖starRingEnd ℂ
      (Complex.digamma
        (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) +
          (tau : ℂ) * Complex.I) - vertLog tau)‖ ≤ C / tau
    simpa only [Complex.norm_conj, Complex.ofReal_add] using hlpos
  have huarg : gaussComponentVerticalUpperArg k (t : ℂ) =
      (gaussComponentOffset k : ℂ) + (tau : ℂ) * Complex.I := by
    rw [gaussComponentVerticalUpperArg, htau]
    push_cast
    ring
  have hlarg : gaussComponentVerticalLowerArg k (t : ℂ) =
      ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
        (tau : ℂ) * Complex.I := by
    rw [gaussComponentVerticalLowerArg, htau]
    push_cast
    ring
  have hlogscale :
      Real.log tau - Real.log (Real.pi / (m : ℝ)) =
        Real.log (t / (2 * Real.pi)) := by
    rw [htau, ← Real.log_div
      (div_ne_zero htpos.ne' (by positivity : (2 * (m : ℝ)) ≠ 0))
      (div_ne_zero Real.pi_pos.ne' hmR.ne')]
    congr 1
    field_simp
  have hrepr :
      gaussComponentVerticalLogDerivError k t =
        Complex.I / (2 * (m : ℂ)) *
          ((Complex.digamma
                ((gaussComponentOffset k : ℂ) + (tau : ℂ) * Complex.I) - vertLog tau) +
            (Complex.digamma
                (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
                  (tau : ℂ) * Complex.I) -
                (((Real.log tau : ℝ) : ℂ) -
                  ((Real.pi : ℂ) / 2) * Complex.I))) := by
    rw [gaussComponentVerticalLogDerivError, gaussComponentVerticalLogDeriv,
      gaussComponentVerticalClock, huarg, hlarg, vertLog]
    push_cast
    rw [← hlogscale]
    push_cast
    ring
  rw [hrepr, norm_mul]
  have hcoef : ‖Complex.I / (2 * (m : ℂ))‖ = 1 / (2 * (m : ℝ)) := by
    rw [norm_div, norm_I, norm_mul]
    norm_num
  rw [hcoef]
  calc
    1 / (2 * (m : ℝ)) *
        ‖(Complex.digamma
              ((gaussComponentOffset k : ℂ) + (tau : ℂ) * Complex.I) - vertLog tau) +
          (Complex.digamma
              (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
                (tau : ℂ) * Complex.I) -
              (((Real.log tau : ℝ) : ℂ) -
                ((Real.pi : ℂ) / 2) * Complex.I))‖
      ≤ 1 / (2 * (m : ℝ)) * (C / tau + C / tau) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hu hl)
    _ = (2 * C) / t := by
      rw [htau]
      field_simp
      ring

/-- The exact logarithmic-derivative error accumulates at most linearly in the
window length and inversely in the base height. -/
theorem exists_gaussComponentVerticalAccumulatedError_inv_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 0 ≤ h → 2 * (m : ℝ) ≤ t →
      ‖gaussComponentVerticalAccumulatedError k t h‖ ≤ C * h / t := by
  obtain ⟨C, hC, hpoint⟩ := exists_gaussComponentVerticalLogDerivError_inv_bound hm k
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t h hh ht
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 2 * (m : ℝ)) ht
  have hle : t ≤ t + h := by linarith
  have hcoord : ∀ x ∈ Set.uIoc t (t + h),
      ‖gaussComponentVerticalLogDerivError k x‖ ≤ C / t := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have htx : t ≤ x := le_of_lt hx.1
    have hxpos : 0 < x := lt_of_lt_of_le htpos htx
    have hxbase : 2 * (m : ℝ) ≤ x := le_trans ht htx
    refine (hpoint x hxbase).trans ?_
    rw [div_le_div_iff₀ hxpos htpos]
    exact mul_le_mul_of_nonneg_left htx hC
  have hre :
      ‖∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re‖
        ≤ (C / t) * h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => (gaussComponentVerticalLogDerivError k x).re)
      (C := C / t) (a := t) (b := t + h) (fun x hx => ?_)
    · simpa [abs_of_nonneg hh] using hb
    · calc
        ‖(gaussComponentVerticalLogDerivError k x).re‖
            ≤ ‖gaussComponentVerticalLogDerivError k x‖ := by
              simpa [Real.norm_eq_abs] using
                Complex.abs_re_le_norm (gaussComponentVerticalLogDerivError k x)
        _ ≤ C / t := hcoord x hx
  have him :
      ‖∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im‖
        ≤ (C / t) * h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => (gaussComponentVerticalLogDerivError k x).im)
      (C := C / t) (a := t) (b := t + h) (fun x hx => ?_)
    · simpa [abs_of_nonneg hh] using hb
    · calc
        ‖(gaussComponentVerticalLogDerivError k x).im‖
            ≤ ‖gaussComponentVerticalLogDerivError k x‖ := by
              simpa [Real.norm_eq_abs] using
                Complex.abs_im_le_norm (gaussComponentVerticalLogDerivError k x)
        _ ≤ C / t := hcoord x hx
  rw [gaussComponentVerticalAccumulatedError]
  calc
    ‖((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re : ℝ) : ℂ) +
        ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im : ℝ) : ℂ) *
          Complex.I‖
      ≤ ‖((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re : ℝ) : ℂ)‖ +
          ‖((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
    _ = ‖∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re‖ +
          ‖∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im‖ := by
            rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real]
    _ ≤ (C / t) * h + (C / t) * h := add_le_add hre him
    _ = (2 * C) * h / t := by ring

/-- Curvature of the universal logarithmic clock over a forward window. -/
theorem norm_gaussComponentVerticalAccumulatedClock_sub_le
    {m : ℕ} (hm : 1 ≤ m) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    ‖gaussComponentVerticalAccumulatedClock m t h -
        (h : ℂ) * gaussComponentVerticalClock m t‖ ≤ h * (h / t) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set E : ℝ :=
    (∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
      h * Real.log (t / (2 * Real.pi)) with hE
  have hrepr :
      gaussComponentVerticalAccumulatedClock m t h -
          (h : ℂ) * gaussComponentVerticalClock m t =
        ((E / (m : ℝ) : ℝ) : ℂ) * Complex.I := by
    rw [gaussComponentVerticalAccumulatedClock_eq, gaussComponentVerticalClock_eq]
    rw [hE]
    push_cast
    ring
  have hEbound : |E| ≤ h * (h / t) := by
    rw [hE]
    exact abs_intervalIntegral_log_sub_le ht hh
  rw [hrepr, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hmR]
  calc
    |E| / (m : ℝ) ≤ |E| := by
      rw [div_le_iff₀ hmR]
      nlinarith [abs_nonneg E]
    _ ≤ h * (h / t) := hEbound

/-- The full transport exponent differs from the frozen phase clock by an explicit
`(linear + quadratic)/height` envelope. -/
theorem exists_gaussComponentVerticalTransportExponent_inv_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 0 ≤ h → 2 * (m : ℝ) ≤ t →
      ‖gaussComponentVerticalAccumulatedLogDeriv k t h -
          (h : ℂ) * gaussComponentVerticalClock m t‖ ≤
        (C * h + h * h) / t := by
  obtain ⟨C, hC, herr⟩ := exists_gaussComponentVerticalAccumulatedError_inv_bound hm k
  refine ⟨C, hC, ?_⟩
  intro t h hh ht
  have htpos : 0 < t := lt_of_lt_of_le (by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    positivity : 0 < 2 * (m : ℝ)) ht
  rw [gaussComponentVerticalAccumulatedLogDeriv_eq hm k htpos hh]
  calc
    ‖gaussComponentVerticalAccumulatedClock m t h +
          gaussComponentVerticalAccumulatedError k t h -
        (h : ℂ) * gaussComponentVerticalClock m t‖
      = ‖(gaussComponentVerticalAccumulatedClock m t h -
            (h : ℂ) * gaussComponentVerticalClock m t) +
          gaussComponentVerticalAccumulatedError k t h‖ := by abel_nf
    _ ≤ ‖gaussComponentVerticalAccumulatedClock m t h -
            (h : ℂ) * gaussComponentVerticalClock m t‖ +
          ‖gaussComponentVerticalAccumulatedError k t h‖ := norm_add_le _ _
    _ ≤ h * (h / t) + C * h / t :=
      add_le_add (norm_gaussComponentVerticalAccumulatedClock_sub_le hm htpos hh)
        (herr t h hh ht)
    _ = (C * h + h * h) / t := by ring

theorem norm_complex_exp_sub_one_le_norm_mul_exp (w : ℂ) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
  simpa [Finset.sum_range_succ, Nat.factorial] using hTaylor

/-- Quantitative finite-shift law.  The exact component ratio differs from the
frozen logarithmic rotation by the exponential envelope of the linear digamma
error plus the quadratic clock curvature. -/
theorem exists_gaussComponentVerticalValue_ratio_sub_clock_inv_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 0 ≤ h → 2 * (m : ℝ) ≤ t →
      let B := (C * h + h * h) / t
      ‖gaussComponentVerticalValue k (t + h) /
            gaussComponentVerticalValue k t -
          Complex.exp ((h : ℂ) * gaussComponentVerticalClock m t)‖ ≤
        B * Real.exp B := by
  obtain ⟨C, hC, hexponent⟩ :=
    exists_gaussComponentVerticalTransportExponent_inv_bound hm k
  refine ⟨C, hC, ?_⟩
  intro t h hh ht
  dsimp only
  have htpos : 0 < t := lt_of_lt_of_le (by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    positivity : 0 < 2 * (m : ℝ)) ht
  set A : ℂ := gaussComponentVerticalAccumulatedLogDeriv k t h with hA
  set H : ℂ := (h : ℂ) * gaussComponentVerticalClock m t with hH
  set B : ℝ := (C * h + h * h) / t with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have hE : ‖A - H‖ ≤ B := by
    rw [hA, hH, hB]
    exact hexponent t h hh ht
  have hratio : gaussComponentVerticalValue k (t + h) /
      gaussComponentVerticalValue k t = Complex.exp A := by
    rw [hA, gaussComponentVerticalAccumulatedLogDeriv,
      gaussComponentVerticalValue_add_div_eq_exp_integral_logDeriv hm k htpos hh]
  have hphase : ‖Complex.exp H‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : H.re = 0 := by
      rw [hH]
      simp [gaussComponentVerticalClock, Complex.mul_re]
    rw [hre]
    simp
  have hfactor : Complex.exp A - Complex.exp H =
      (Complex.exp (A - H) - 1) * Complex.exp H := by
    rw [sub_mul, one_mul, ← Complex.exp_add, sub_add_cancel]
  rw [hratio, hfactor, norm_mul, hphase, mul_one]
  calc
    ‖Complex.exp (A - H) - 1‖
        ≤ ‖A - H‖ * Real.exp ‖A - H‖ :=
          norm_complex_exp_sub_one_le_norm_mul_exp (A - H)
    _ ≤ B * Real.exp B := by
      exact mul_le_mul hE (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le hB0
    _ = (C * h + h * h) / t * Real.exp ((C * h + h * h) / t) := by rw [hB]

/-- Moving the frozen clock from the beginning to the end of a forward window
costs one further quadratic-curvature term. -/
theorem norm_gaussComponentVerticalClock_endpoint_sub_le
    {m : ℕ} (hm : 1 ≤ m) {s h : ℝ} (hs : 0 < s) (hh : 0 ≤ h) :
    ‖(h : ℂ) *
        (gaussComponentVerticalClock m (s + h) -
          gaussComponentVerticalClock m s)‖ ≤ h * (h / s) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set D : ℝ := Real.log ((s + h) / (2 * Real.pi)) -
    Real.log (s / (2 * Real.pi)) with hD
  have hx : s + h ∈ Set.uIcc s (s + h) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨by linarith, le_rfl⟩
  obtain ⟨hD0, hDle⟩ := log_div_self_bounds hs hh hx
  have hrepr :
      (h : ℂ) *
          (gaussComponentVerticalClock m (s + h) -
            gaussComponentVerticalClock m s) =
        (h : ℂ) * (((D / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [gaussComponentVerticalClock_eq, gaussComponentVerticalClock_eq, hD]
    push_cast
    ring
  rw [hrepr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh,
    norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hmR, abs_of_nonneg hD0]
  refine mul_le_mul_of_nonneg_left ?_ hh
  calc
    D / (m : ℝ) ≤ D := by
      rw [div_le_iff₀ hmR]
      nlinarith
    _ ≤ h / s := hDle

/-- Quantitative backward finite-shift law, frozen at the terminal height. -/
theorem exists_gaussComponentVerticalValue_sub_ratio_sub_clock_inv_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 0 ≤ h → 2 * (m : ℝ) ≤ t - h →
      let B := (C * h + 2 * h * h) / (t - h)
      ‖gaussComponentVerticalValue k (t - h) /
            gaussComponentVerticalValue k t -
          Complex.exp ((-h : ℂ) * gaussComponentVerticalClock m t)‖ ≤
        B * Real.exp B := by
  obtain ⟨C, hC, hforward⟩ :=
    exists_gaussComponentVerticalTransportExponent_inv_bound hm k
  refine ⟨C, hC, ?_⟩
  intro t h hh ht
  dsimp only
  set s : ℝ := t - h with hs
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hspos : 0 < s := lt_of_lt_of_le (by positivity : 0 < 2 * (m : ℝ)) (by simpa [s] using ht)
  have ht_eq : s + h = t := by rw [hs]; ring
  set A : ℂ := gaussComponentVerticalAccumulatedLogDeriv k s h with hA
  set H : ℂ := (-h : ℂ) * gaussComponentVerticalClock m t with hH
  set B : ℝ := (C * h + 2 * h * h) / s with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have hE : ‖-A - H‖ ≤ B := by
    have hmain := hforward s h hh (by simpa [s] using ht)
    have hend := norm_gaussComponentVerticalClock_endpoint_sub_le hm hspos hh
    rw [ht_eq] at hend
    have hsplit : -A - H =
        -(A - (h : ℂ) * gaussComponentVerticalClock m s) +
          (h : ℂ) *
            (gaussComponentVerticalClock m t - gaussComponentVerticalClock m s) := by
      rw [hH]
      ring
    rw [hsplit]
    calc
      ‖-(A - (h : ℂ) * gaussComponentVerticalClock m s) +
          (h : ℂ) *
            (gaussComponentVerticalClock m t - gaussComponentVerticalClock m s)‖
        ≤ ‖A - (h : ℂ) * gaussComponentVerticalClock m s‖ +
            ‖(h : ℂ) *
              (gaussComponentVerticalClock m t - gaussComponentVerticalClock m s)‖ := by
              simpa only [norm_neg] using norm_add_le
                (-(A - (h : ℂ) * gaussComponentVerticalClock m s))
                ((h : ℂ) *
                  (gaussComponentVerticalClock m t - gaussComponentVerticalClock m s))
      _ ≤ (C * h + h * h) / s + h * (h / s) := add_le_add (by
            rw [hA]
            exact hmain) hend
      _ = B := by rw [hB]; ring
  have hratio : gaussComponentVerticalValue k (t - h) /
      gaussComponentVerticalValue k t = Complex.exp (-A) := by
    have htransport : gaussComponentVerticalValue k (s + h) /
        gaussComponentVerticalValue k s = Complex.exp A := by
      rw [hA, gaussComponentVerticalAccumulatedLogDeriv,
        gaussComponentVerticalValue_add_div_eq_exp_integral_logDeriv hm k hspos hh]
    rw [ht_eq] at htransport
    rw [← inv_div, htransport, ← Complex.exp_neg]
  have hphase : ‖Complex.exp H‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : H.re = 0 := by
      rw [hH]
      simp [gaussComponentVerticalClock, Complex.mul_re]
    rw [hre]
    simp
  have hfactor : Complex.exp (-A) - Complex.exp H =
      (Complex.exp (-A - H) - 1) * Complex.exp H := by
    rw [sub_mul, one_mul, ← Complex.exp_add, sub_add_cancel]
  rw [hratio, hfactor, norm_mul, hphase, mul_one]
  calc
    ‖Complex.exp (-A - H) - 1‖
        ≤ ‖-A - H‖ * Real.exp ‖-A - H‖ :=
          norm_complex_exp_sub_one_le_norm_mul_exp (-A - H)
    _ ≤ B * Real.exp B := by
      exact mul_le_mul hE (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le hB0
    _ = (C * h + 2 * h * h) / (t - h) *
        Real.exp ((C * h + 2 * h * h) / (t - h)) := by rw [hB, hs]

end

end RHTower
