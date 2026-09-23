/-
# Brick (a): the `ρ_n`-loop winds exactly once around `0`, discharging `hodd`

`RhoLoopWinding` reduced the connected-case root gap `hodd` to a *basepoint-independent* statement:
the winding of the level-`n` `ρ`-loop around `0`. Here that winding is computed to be `1`
(`windPt_rhoLoopC_zero_eq_one`), which closes `hodd` unconditionally for `c ∈ mandelbrot`.

The computation is an induction on `n` with **no large-modulus / intermediate-annulus hypothesis**:

* **Base** `n = 0`: `ρ_0 = exp`, so the normalised loop is literally the standard circle
  `s ↦ exp(2πi·s)` — winding `1` (`degZ_circleLoop`).
* **Step** `n → n+1`: squaring the normalised `ρ_{n+1}`-loop gives, via `ρ_{n+1}² = ρ_n − c`
  (`rho_succ_sq`), the normalised *doubled* `ρ_n`-loop taken around `c`
  (`sqLoop_normLoop_succ`). Its winding around `c` equals its winding around `0` because both `0`
  and `c` lie in the connected sublevel set `(escapeLevel c n)ᶜ` off the loop
  (`windPt_const_of_isPreconnected` — brick (b), applied a second time). The doubled loop is the
  self-concatenation `ρ_n-loop.trans ρ_n-loop`, whose winding is `2·W_n` (`degZ_trans`). Hence
  `2·W_{n+1} = 2·W_n`, so `W_{n+1} = W_n = 1`.

This route sidesteps the `f^[n]`-degree recursion entirely: there is no need for the intermediate
iterates to have large modulus, because the doubling comes from `Path.trans` and the basepoint move
from connectedness — both already formalised.
-/
import GaloisForLFunctions.Bottcher.RhoLoopWinding

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

noncomputable section

variable {c : ℂ}

/-- `sqLoop` squares the underlying `ℂ*`-value pointwise. -/
theorem sqLoop_coe (p : Path one_cs one_cs) (s : I) :
    ((sqLoop p s : Cs) : ℂ) = ((p s : Cs) : ℂ) ^ (2 : ℕ) := by
  rw [sqLoop, Path.cast_coe, Path.map_coe]
  rfl

/-- The self-concatenation of the `ρ`-loop traces `ρ_n` over the doubled period `2^(n+1)·2πi`. -/
theorem rhoLoopC_trans_apply (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) (s : I) :
    (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) s : ℂ)
      = rho c n (t + (((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)) := by
  rw [Path.trans_apply]
  split_ifs with h
  · show rho c n (t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        * ((((2 : ℝ) * (s : ℝ)) : ℝ) : ℂ)) = _
    congr 1
    push_cast [pow_succ]
    ring
  · set u : ℂ := t + (((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        * ((((2 : ℝ) * (s : ℝ) - 1) : ℝ) : ℂ) with hu
    have hure : ((((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        * ((((2 : ℝ) * (s : ℝ) - 1) : ℝ) : ℂ)).re = 0 := by
      rw [Complex.mul_re, vshift_re_zero n, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
    have humem : u ∈ coverPlane c := exp_add_im_mem ht hure
    show (rho c n u : ℂ) = _
    rw [← rho_period hc n humem]
    congr 1
    rw [hu]
    push_cast [pow_succ]
    ring

/-- The self-concatenation of the `ρ`-loop stays in the exterior `escapeLevel c n`. -/
theorem rhoLoopC_trans_mem (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) (s : I) :
    (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) s : ℂ) ∈ escapeLevel c n := by
  rw [rhoLoopC_trans_apply hc n ht s]
  have hre : ((((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)).re = 0 := by
    rw [Complex.mul_re, vshift_re_zero (n + 1), zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  exact rho_mem_escapeLevel c hc n (exp_add_im_mem ht hre)

/-- `normLoop` distributes over self-concatenation. -/
theorem normLoop_trans_self {a : ℂ} (p : Path a a) (q : ℂ)
    (hq : ∀ t : I, (p t : ℂ) ≠ q)
    (hqt : ∀ t : I, ((p.trans p) t : ℂ) ≠ q) :
    normLoop (p.trans p) q hqt = (normLoop p q hq).trans (normLoop p q hq) := by
  have h00 : ((p.trans p) 0 : ℂ) = (p 0 : ℂ) := (p.trans p).source.trans p.source.symm
  ext s
  show (((p.trans p) s : ℂ) - q) / (((p.trans p) 0 : ℂ) - q)
      = ↑(((normLoop p q hq).trans (normLoop p q hq)) s)
  rw [h00, Path.trans_apply, Path.trans_apply]
  split_ifs with h
  · rfl
  · rfl

/-- **Squaring the normalised `ρ_{n+1}`-loop yields the normalised doubled `ρ_n`-loop around `c`.**
Uses `ρ_{n+1}² = ρ_n − c` (`rho_succ_sq`) on numerator and denominator. -/
theorem sqLoop_normLoop_succ (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c)
    (h0 : ∀ s : I, (rhoLoopC hc (n + 1) ht s : ℂ) ≠ 0)
    (hcC : ∀ s : I, (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) s : ℂ) ≠ c) :
    sqLoop (normLoop (rhoLoopC hc (n + 1) ht) 0 h0)
      = normLoop ((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) c hcC := by
  ext s
  rw [sqLoop_coe]
  have hwmem : (t + (((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ))
      ∈ coverPlane c := by
    apply exp_add_im_mem ht
    rw [Complex.mul_re, vshift_re_zero (n + 1), zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  have e1 : (rhoLoopC hc (n + 1) ht 0 : ℂ) = rho c (n + 1) t := (rhoLoopC hc (n + 1) ht).source
  have e2 : (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) 0 : ℂ) = rho c n t :=
    ((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)).source
  have e3 : (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) s : ℂ)
      = rho c n (t + (((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)) :=
    rhoLoopC_trans_apply hc n ht s
  show (((rho c (n + 1) (t + (((2 ^ (n + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ))
        : ℂ) - 0) / ((rhoLoopC hc (n + 1) ht 0 : ℂ) - 0)) ^ (2 : ℕ)
      = (((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) s - c)
        / ((((rhoLoopC hc n ht).trans (rhoLoopC hc n ht)) 0 : ℂ) - c)
  rw [e1, e2, e3, sub_zero, sub_zero, div_pow, rho_succ_sq c hc n hwmem, rho_succ_sq c hc n ht]

/-- The `ρ`-loop never hits `0` when `c ∈ mandelbrot` (`0` never escapes). -/
theorem rhoLoopC_ne_zero (hcM : c ∈ mandelbrot) (n : ℕ) {t : ℂ} (ht : t ∈ coverPlane c) (s : I) :
    (rhoLoopC (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht s : ℂ) ≠ 0 := by
  intro heq
  exact zero_not_mem_escapeLevel_of_mem_mandelbrot hcM n
    (heq ▸ rhoLoopC_mem (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht s)

/-- **Brick (a): the `ρ_n`-loop winds exactly once around `0`.** By induction on `n`: the base loop
is the circle (`ρ_0 = exp`, winding `1`), and squaring the normalised `ρ_{n+1}`-loop equals the
normalised doubled `ρ_n`-loop around `c`, whose winding — by basepoint-constancy across the connected
sublevel set — equals its winding around `0`, i.e. `2·W_n`. So `2·W_{n+1} = 2·W_n`, giving
`W_{n+1} = W_n = 1`. -/
theorem windPt_rhoLoopC_zero_eq_one (hcM : c ∈ mandelbrot) (n : ℕ) {t : ℂ}
    (ht : t ∈ coverPlane c) :
    windPt (rhoLoopC (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht) 0
      (fun s => rhoLoopC_ne_zero hcM n ht s) = 1 := by
  set hc := criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM with hhc
  induction n with
  | zero =>
    have hcircle : normLoop (rhoLoopC hc 0 ht) 0 (fun s => rhoLoopC_ne_zero hcM 0 ht s)
        = circleLoop := by
      ext s
      have e0src : (rhoLoopC hc 0 ht 0 : ℂ) = Complex.exp t := (rhoLoopC hc 0 ht).source
      show ((Complex.exp (t + (((2 ^ (0 : ℕ) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ)) : ℂ)
            - 0) / ((rhoLoopC hc 0 ht 0 : ℂ) - 0) = ↑(circleLoop s)
      rw [e0src, sub_zero, sub_zero]
      show Complex.exp (t + (((2 ^ (0 : ℕ) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (s : ℂ))
            / Complex.exp t
          = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((s : ℝ) : ℂ))
      rw [← Complex.exp_sub]
      congr 1
      push_cast
      ring
    unfold windPt
    rw [hcircle, degZ_circleLoop]
  | succ k ih =>
    have h0 : ∀ s : I, (rhoLoopC hc (k + 1) ht s : ℂ) ≠ 0 :=
      fun s => rhoLoopC_ne_zero hcM (k + 1) ht s
    have h0p : ∀ s : I, (rhoLoopC hc k ht s : ℂ) ≠ 0 := fun s => rhoLoopC_ne_zero hcM k ht s
    have hmemtr : ∀ s : I, (((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) s : ℂ) ∈ escapeLevel c k :=
      rhoLoopC_trans_mem hc k ht
    have hcC : ∀ s : I, (((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) s : ℂ) ≠ c := by
      intro s hh
      have hm := hmemtr s
      rw [hh] at hm
      exact hc k hm
    have h0tr : ∀ s : I, (((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) s : ℂ) ≠ 0 := by
      intro s hh
      have hm := hmemtr s
      rw [hh] at hm
      exact zero_not_mem_escapeLevel_of_mem_mandelbrot hcM k hm
    have hpre : IsPreconnected ((escapeLevel c k)ᶜ) := isPreconnected_escapeLevel_compl c hc k
    have hSL : ∀ q ∈ (escapeLevel c k)ᶜ, ∀ s : I,
        (((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) s : ℂ) ≠ q := by
      intro q hq s hh
      have hm := hmemtr s
      rw [hh] at hm
      exact hq hm
    have hbrickb : windPt ((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) c hcC
        = windPt ((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) 0 h0tr :=
      windPt_const_of_isPreconnected ((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) hpre hSL
        (hc k) (zero_not_mem_escapeLevel_of_mem_mandelbrot hcM k)
    have hkeyII : windPt ((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) 0 h0tr
        = 2 * windPt (rhoLoopC hc k ht) 0 h0p := by
      unfold windPt
      rw [normLoop_trans_self (rhoLoopC hc k ht) 0 h0p h0tr,
        show (⟦(normLoop (rhoLoopC hc k ht) 0 h0p).trans (normLoop (rhoLoopC hc k ht) 0 h0p)⟧
            : Path.Homotopic.Quotient one_cs one_cs)
          = Path.Homotopic.Quotient.trans ⟦normLoop (rhoLoopC hc k ht) 0 h0p⟧
              ⟦normLoop (rhoLoopC hc k ht) 0 h0p⟧ from rfl, degZ_trans]
      ring
    have hkeyI : 2 * windPt (rhoLoopC hc (k + 1) ht) 0 h0
        = windPt ((rhoLoopC hc k ht).trans (rhoLoopC hc k ht)) c hcC := by
      unfold windPt
      rw [← degZ_sqLoop, sqLoop_normLoop_succ hc k ht h0 hcC]
    have hcomb : 2 * windPt (rhoLoopC hc (k + 1) ht) 0 h0 = 2 * 1 := by
      rw [hkeyI, hbrickb, hkeyII, ih]
    have hgoal : windPt (rhoLoopC hc (k + 1) ht) 0 h0 = 1 := by omega
    exact hgoal

/-- **`hodd`, unconditionally, for `c ∈ mandelbrot`.** The half-period `ρ`-loop `rhoShiftLoop` has
odd winding (`k = 0`, winding `1`) — the topological-degree input consumed by
`rho_antiperiod_of_odd_shift_winding_all` and the connected Böttcher branch. -/
theorem hodd_of_mem_mandelbrot (hcM : c ∈ mandelbrot) :
    ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ, degZ ⟦rhoShiftLoop c (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht⟧
        = 2 * k + 1 := by
  intro n t ht
  have hdeg : degZ ⟦rhoShiftLoop c (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) n ht⟧
      = 1 := by
    rw [degZ_rhoShiftLoop_eq_windPt_zero (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM)
      n ht (zero_not_mem_escapeLevel_of_mem_mandelbrot hcM n) (fun s => rhoLoopC_ne_zero hcM n ht s),
      windPt_rhoLoopC_zero_eq_one hcM n ht]
  exact ⟨0, hdeg.trans (by norm_num)⟩

end

end Bottcher
