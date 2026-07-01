/-
# The `ρ_n`-loop as a concrete winding loop, and the reduction of `hodd`

The connected-case root gap `hodd` (`PeriodDoubling`) asks that the half-period loop
`rhoShiftLoop c hc n ht : s ↦ (ρ_n(t + 2ⁿ·2πi·s) − c)/(ρ_n(t) − c)` have **odd** winding: this is the
winding of the `ρ_n`-loop around the point `c`.

Here we realise the `ρ_n`-loop as an honest `Path` in `ℂ` (`rhoLoopC`) and prove `rhoShiftLoop` is its
normalisation around `c`. Because the loop's image lies in the exterior `escapeLevel c n`, and — for
`c ∈ mandelbrot` — both `0` and `c` lie in the *connected* sublevel set `C_n = (escapeLevel c n)ᶜ`
(`isPreconnected_escapeLevel_compl`) off the loop, the basepoint-constancy of winding
(`windPt_const_of_isPreconnected`) gives

    degZ⟦rhoShiftLoop⟧  =  windPt (ρ_n-loop) around `c`  =  windPt (ρ_n-loop) around `0`.

So `hodd` is **equivalent to the winding of the `ρ_n`-loop around `0` being odd** — a
basepoint-independent statement, no longer entangled with the location of `c` inside `K_c`. The
remaining atom is that winding around `0`, supplied by the `degZ` product recursion of the `ρ` tower.
-/
import GaloisForLFunctions.Bottcher.WindingBasepoint
import GaloisForLFunctions.Bottcher.PeriodDoubling
import GaloisForLFunctions.Bottcher.SublevelConnected
import GaloisForLFunctions.Bottcher.FilledJuliaConnected

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

noncomputable section

variable {c : ℂ}

/-- The level-`n` `ρ`-loop `s ↦ ρ_n(t + 2ⁿ·2πi·s)` as a `Path` in `ℂ`, based at `ρ_n(t)`. -/
def rhoLoopC (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c) :
    Path (rho c n t) (rho c n t) where
  toFun s := rho c n (t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ))
  continuous_toFun := by
    have hPsim : ∀ s : ℝ,
        ((((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)).re = 0 := by
      intro s
      rw [Complex.mul_re, vshift_re_zero n, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
    have harg : Continuous fun s : I =>
        t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ) := by fun_prop
    exact (rho_analytic c hc n).continuousOn.comp_continuous harg
      (fun s => exp_add_im_mem ht (hPsim (s : ℝ)))
  source' := by simp
  target' := by
    show rho c n (t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((1 : I) : ℂ))
        = rho c n t
    have h1 : ((1 : I) : ℂ) = 1 := by norm_num
    rw [h1, mul_one]
    exact rho_period hc n ht

/-- The `ρ`-loop stays in the exterior `escapeLevel c n`. -/
theorem rhoLoopC_mem (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c)
    (s : I) : (rhoLoopC hc n ht s : ℂ) ∈ escapeLevel c n := by
  have hPsim : ((((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((s : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re, vshift_re_zero n, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  exact rho_mem_escapeLevel c hc n (exp_add_im_mem ht hPsim)

/-- `rhoShiftLoop` is the normalisation of the `ρ`-loop around `c`. -/
theorem normLoop_rhoLoopC_eq (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c)
    (hcC : ∀ s : I, (rhoLoopC hc n ht s : ℂ) ≠ c) :
    normLoop (rhoLoopC hc n ht) c hcC = rhoShiftLoop c hc n ht := by
  ext s
  show ((rhoLoopC hc n ht s : ℂ) - c) / ((rhoLoopC hc n ht 0 : ℂ) - c)
      = (rho c n (t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)) - c)
        / (rho c n t - c)
  have h0 : (rhoLoopC hc n ht 0 : ℂ) = rho c n t := (rhoLoopC hc n ht).source
  rw [h0]
  rfl

/-- For `c ∈ mandelbrot`, the critical point `0` also never escapes at level `n`. -/
theorem zero_not_mem_escapeLevel_of_mem_mandelbrot (hcM : c ∈ mandelbrot) (n : ℕ) :
    (0 : ℂ) ∉ escapeLevel c n := by
  have h0 : (0 : ℂ) ∈ filledJulia c := hcM
  rw [filledJulia_eq_iInter_escapeLevel_compl] at h0
  exact Set.mem_iInter.mp h0 n

/-- **`hodd` reduces to the winding of the `ρ`-loop around `0`.** For a parameter whose critical value
never escapes, if additionally `0` does not escape at level `n` (automatic for `c ∈ mandelbrot`), then
the winding `degZ⟦rhoShiftLoop⟧` around `c` equals the winding of the `ρ_n`-loop around `0`: both `0`
and `c` lie in the connected sublevel set `(escapeLevel c n)ᶜ`, off the loop image, and winding is
constant across it (`windPt_const_of_isPreconnected`). -/
theorem degZ_rhoShiftLoop_eq_windPt_zero (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) (h0 : (0 : ℂ) ∉ escapeLevel c n)
    (h0ne : ∀ s : I, (rhoLoopC hc n ht s : ℂ) ≠ 0) :
    degZ ⟦rhoShiftLoop c hc n ht⟧ = windPt (rhoLoopC hc n ht) 0 h0ne := by
  have hSL : ∀ q ∈ (escapeLevel c n)ᶜ, ∀ s : I, (rhoLoopC hc n ht s : ℂ) ≠ q := by
    intro q hq s hcontra
    exact hq (hcontra ▸ rhoLoopC_mem hc n ht s)
  have hpre : IsPreconnected ((escapeLevel c n)ᶜ) := isPreconnected_escapeLevel_compl c hc n
  have hcC : c ∈ (escapeLevel c n)ᶜ := hc n
  have h0C : (0 : ℂ) ∈ (escapeLevel c n)ᶜ := h0
  have hconst := windPt_const_of_isPreconnected (rhoLoopC hc n ht) hpre hSL h0C hcC
  have hc_eq : windPt (rhoLoopC hc n ht) c (hSL c hcC) = degZ ⟦rhoShiftLoop c hc n ht⟧ := by
    unfold windPt
    rw [normLoop_rhoLoopC_eq hc n ht (hSL c hcC)]
  rw [← hc_eq]
  exact hconst.symm

/-- **The `hodd` input, packaged for `c ∈ mandelbrot`.** The odd-winding hypothesis of the connected
branch is equivalent to the `ρ_n`-loop winding oddly around `0`. -/
theorem hodd_iff_windPt_zero_odd (hcM : c ∈ mandelbrot) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c)
    (h0ne : ∀ s : I,
      (rhoLoopC (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht s : ℂ) ≠ 0) :
    (∃ k : ℤ, degZ ⟦rhoShiftLoop c
        (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht⟧ = 2 * k + 1)
      ↔ (∃ k : ℤ, windPt (rhoLoopC (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht)
          0 h0ne = 2 * k + 1) := by
  rw [degZ_rhoShiftLoop_eq_windPt_zero
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht
    (zero_not_mem_escapeLevel_of_mem_mandelbrot hcM n) h0ne]

end

end Bottcher
