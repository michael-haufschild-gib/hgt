/-
# A nonvanishing entire function is a global exponential

Every zero-free holomorphic function on the whole plane admits a holomorphic logarithm: if
`f : ℂ → ℂ` is entire and `f z ≠ 0` everywhere, then `f = exp ∘ g` for some entire `g`.

The construction is constraint-side, not flow-side.  The logarithmic derivative
`logDeriv f = deriv f / f` is itself entire (the numerator is entire because the derivative of a
holomorphic function is holomorphic; the denominator is entire and never zero).  Because `ℂ` is a
plane, Morera's theorem supplies a global primitive `G` of `logDeriv f`, i.e. `G' = f'/f`
everywhere.  The auxiliary function `h z = f z · exp(−G z)` then has derivative
`f' · exp(−G) − f · (f'/f) · exp(−G) = 0` at every point, so it is constant.  Its constant value
`h 0 = f 0 · exp(−G 0)` is nonzero, hence equals `exp c` for `c = log (h 0)`, and
`f z = h 0 · exp(G z) = exp(c + G z)`.  The logarithm `g z = c + G z` is entire.
-/
import Mathlib

open Complex

namespace RHTower

/-- **A nonvanishing entire function is the exponential of an entire function.**
If `f : ℂ → ℂ` is holomorphic on all of `ℂ` and never zero, there is an entire `g` with
`f = exp ∘ g`.  The witness is `g z = log (f 0 · exp(−G 0)) + G z`, where `G` is a global
primitive of the (entire) logarithmic derivative `logDeriv f = deriv f / f`. -/
theorem entire_nonvanishing_has_log (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  -- `deriv f` is entire: the derivative of a holomorphic function on `ℂ` is holomorphic.
  have hf_an : AnalyticOnNhd ℂ f Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have hderiv : Differentiable ℂ (deriv f) :=
    analyticOnNhd_univ_iff_differentiable.mp hf_an.deriv
  -- Hence `logDeriv f = deriv f / f` is entire (denominator entire and nowhere zero).
  have hlog : Differentiable ℂ (logDeriv f) := by
    have hquot : Differentiable ℂ (fun z => deriv f z / f z) := hderiv.div hf h0
    simpa [logDeriv] using hquot
  -- Morera's theorem on the plane gives a global primitive `G` of `logDeriv f`.
  obtain ⟨G, hG0⟩ := hlog.isExactOn_univ
  have hG : ∀ z, HasDerivAt G (logDeriv f z) z := fun z => hG0 z (Set.mem_univ z)
  have hG_diff : Differentiable ℂ G := fun z => (hG z).differentiableAt
  -- `h z = f z · exp(−G z)` has vanishing derivative everywhere.
  set h : ℂ → ℂ := fun z => f z * Complex.exp (-G z) with hh_def
  have hHasDeriv : ∀ z, HasDerivAt h 0 z := by
    intro z
    have hexp : HasDerivAt (fun z => Complex.exp (-G z))
        (Complex.exp (-G z) * (-logDeriv f z)) z := ((hG z).neg).cexp
    have hmul := ((hf z).hasDerivAt).mul hexp
    have hv : deriv f z * Complex.exp (-G z)
        + f z * (Complex.exp (-G z) * (-logDeriv f z)) = 0 := by
      have hfz := h0 z
      rw [logDeriv_apply]
      field_simp
      ring
    rw [hv] at hmul
    exact hmul
  have hh_diff : Differentiable ℂ h := fun z => (hHasDeriv z).differentiableAt
  have hderiv0 : ∀ z, deriv h z = 0 := fun z => (hHasDeriv z).deriv
  have hconst : ∀ z, h z = h 0 := fun z => is_const_of_deriv_eq_zero hh_diff hderiv0 z 0
  -- The constant value `h 0` is nonzero, so it has a complex logarithm `c`.
  have h0ne : h 0 ≠ 0 := mul_ne_zero (h0 0) (Complex.exp_ne_zero _)
  set c : ℂ := Complex.log (h 0) with hc_def
  have hexpc : Complex.exp c = h 0 := Complex.exp_log h0ne
  refine ⟨fun z => c + G z, (differentiable_const c).add hG_diff, fun z => ?_⟩
  calc f z = f z * Complex.exp (-G z) * Complex.exp (G z) := by
          rw [mul_assoc, ← Complex.exp_add]; simp
    _ = h z * Complex.exp (G z) := by rw [hh_def]
    _ = h 0 * Complex.exp (G z) := by rw [hconst z]
    _ = Complex.exp c * Complex.exp (G z) := by rw [hexpc]
    _ = Complex.exp (c + G z) := (Complex.exp_add c (G z)).symm

end RHTower
