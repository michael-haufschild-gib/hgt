import GaloisForLFunctions.RHTower.DirichletLEulerLogarithmRightOfTheOneLine
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The Euler logarithm of `ζ` on boxes right of the pole

Let `ℓ(w) = Σ_p −log(1 − p^{-w})` (`zetaEulerLog`, the Euler logarithm of the character mod `1`). On
`Re w > 1`, `e^{ℓ} = ζ`, `ℓ' = ζ'/ζ`, so `Re ℓ = log|ζ|`, and `ℓ` is real on the real axis.

**The argument stays bounded at the pole.** With `G = (w − 1)ζ(w)` (entire, zero-free on `Re w ≥ 1`)
one has `ζ'/ζ = G'/G − 1/(w − 1)`, so `h(s) = ℓ(1 + u + is) + log(u + is)` has `h' = i G'/G`. Hence
`|Im ℓ(1 + u + iτ)| ≤ π/2 + M_H |τ|` for `0 < u ≤ 1`, `|τ| ≤ H`, `M_H = max |G'/G|` on the box
(`exists_abs_im_zetaEulerLog_le`): the pole costs at most the angle `arg(u + iτ)`.
-/

noncomputable section
open Filter Topology Complex Set MeasureTheory

namespace RHTower

/-- The Euler logarithm of `ζ`: the Euler logarithm of the character mod `1`. -/
def zetaEulerLog (w : ℂ) : ℂ := eulerLog (1 : DirichletCharacter ℂ 1) w

theorem exp_zetaEulerLog {w : ℂ} (hw : 1 < w.re) : Complex.exp (zetaEulerLog w) = riemannZeta w := by
  rw [zetaEulerLog, exp_eulerLog _ hw, DirichletCharacter.LFunction_modOne_eq]

theorem re_zetaEulerLog {w : ℂ} (hw : 1 < w.re) :
    (zetaEulerLog w).re = Real.log ‖riemannZeta w‖ := by
  rw [← exp_zetaEulerLog hw, Complex.norm_exp, Real.log_exp]

theorem hasDerivAt_zetaEulerLog {w : ℂ} (hw : 1 < w.re) :
    HasDerivAt zetaEulerLog (deriv riemannZeta w / riemannZeta w) w := by
  have h := hasDerivAt_eulerLog (1 : DirichletCharacter ℂ 1) hw
  rwa [DirichletCharacter.LFunction_modOne_eq] at h

/-- The Euler logarithm is real on the real axis. -/
theorem im_zetaEulerLog_ofReal {x : ℝ} (hx : 1 < x) : (zetaEulerLog x).im = 0 := by
  have hterm : ∀ p : Nat.Primes, (-Complex.log (1 - (1 : DirichletCharacter ℂ 1) p *
      ((p : ℕ) : ℂ) ^ (-(x : ℂ)))).im = 0 := fun p => by
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have h1 : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
    have hpow : ((p : ℕ) : ℂ) ^ (-(x : ℂ)) = ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp0.le, Complex.ofReal_natCast, Complex.ofReal_neg]
    have hlt : ((p : ℕ) : ℝ) ^ (-x) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
    rw [h1, one_mul, hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log (by linarith), Complex.neg_im, Complex.ofReal_im, neg_zero]
  have hsum : Summable (fun p : Nat.Primes => -Complex.log (1 - (1 : DirichletCharacter ℂ 1) p *
      ((p : ℕ) : ℂ) ^ (-(x : ℂ)))) := by
    have hy : Summable (fun p : Nat.Primes => (1 : DirichletCharacter ℂ 1) p *
        ((p : ℕ) : ℂ) ^ (-(x : ℂ))) :=
      (Nat.Primes.summable_rpow.mpr (show -(x : ℂ).re < -1 by simp; linarith)).of_norm_bounded
        fun p => norm_char_prime_cpow_le _ p
    exact hy.clog_one_sub.neg
  rw [zetaEulerLog, eulerLog, Complex.im_tsum hsum]
  simp only [hterm, tsum_zero]

/-- **The argument of `ζ` on boxes right of the pole.** For every `H ≥ 0` there is `C` with
`|Im ℓ(1 + u + iτ)| ≤ C` for `0 < u ≤ 1`, `|τ| ≤ H`. -/
theorem exists_abs_im_zetaEulerLog_le (H : ℝ) :
    ∃ C : ℝ, ∀ u τ : ℝ, 0 < u → u ≤ 1 → |τ| ≤ H →
      |(zetaEulerLog (((1 + u : ℝ) : ℂ) + τ * I)).im| ≤ C := by
  set K : Set ℂ := (Icc (1 : ℝ) 2) ×ℂ (Icc (-H) H)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hGne : ∀ z ∈ K, zetaResidueUnit z ≠ 0 := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1, zetaResidueUnit_one]; exact one_ne_zero
    · have heq := (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds
      rw [heq]
      exact mul_ne_zero (sub_ne_zero.mpr hz1)
        (riemannZeta_ne_zero_of_one_le_re (Complex.mem_reProdIm.mp hz).1.1)
  have hcont : ContinuousOn (fun z => deriv zetaResidueUnit z / zetaResidueUnit z) K := fun z hz =>
    ((analyticAt_zetaResidueUnit z).deriv.continuousAt.div
      (analyticAt_zetaResidueUnit z).continuousAt (hGne z hz)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Real.pi / 2 + |M| * H, fun u τ hu hu1 hτ => ?_⟩
  have hH : 0 ≤ H := (abs_nonneg τ).trans hτ
  set w : ℝ → ℂ := fun s => ((1 + u : ℝ) : ℂ) + s * I
  have hwre : ∀ s : ℝ, (w s).re = 1 + u := fun s => by simp [w]
  have hwsub : ∀ s : ℝ, w s - 1 = (u : ℂ) + s * I := fun s => by simp only [w]; push_cast; ring
  have hslit : ∀ s : ℝ, (u : ℂ) + s * I ∈ Complex.slitPlane := fun s =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hu))
  -- `h(s) = ℓ(w s) + log(u + is)` has derivative `i G'/G (w s)`
  set h : ℝ → ℂ := fun s => zetaEulerLog (w s) + Complex.log ((u : ℂ) + s * I)
  have hderiv : ∀ s : ℝ, HasDerivAt h (I * (deriv zetaResidueUnit (w s) / zetaResidueUnit (w s))) s := by
    intro s
    have hw1 : 1 < (w s).re := by rw [hwre]; linarith
    have hne1 : w s ≠ 1 := by intro h1; have := congrArg Complex.re h1; rw [hwre] at this; simp at this; linarith
    have hpath : HasDerivAt w I s := by
      have := ((hasDerivAt_id (s : ℂ)).mul_const I).const_add (((1 + u : ℝ) : ℂ))
      simpa [w] using this.comp_ofReal
    have h1 := (hasDerivAt_zetaEulerLog hw1).comp s hpath
    have hpath2 : HasDerivAt (fun s : ℝ => (u : ℂ) + s * I) I s := by
      have := ((hasDerivAt_id (s : ℂ)).mul_const I).const_add (u : ℂ)
      simpa using this.comp_ofReal
    have h2 := (Complex.hasDerivAt_log (hslit s)).comp s hpath2
    have hGz : zetaResidueUnit (w s) ≠ 0 := by
      have heq := (zetaResidueUnit_eventuallyEq hne1).eq_of_nhds
      rw [heq]
      exact mul_ne_zero (sub_ne_zero.mpr hne1) (riemannZeta_ne_zero_of_one_le_re hw1.le)
    have hlog := logDeriv_zeta_eq hne1 hGz
    rw [logDeriv_apply, logDeriv_apply, hwsub] at hlog
    refine (h1.add h2).congr_deriv ?_
    rw [hlog]
    ring
  -- integrate along `[0, τ]`
  have hcontd : Continuous (fun s : ℝ => I * (deriv zetaResidueUnit (w s) / zetaResidueUnit (w s))) := by
    refine continuous_const.mul (continuous_iff_continuousAt.mpr fun s => ?_)
    have hpath : Continuous w := by
      simp only [w]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hne1 : w s ≠ 1 := by intro h1; have := congrArg Complex.re h1; rw [hwre] at this; simp at this; linarith
    have hGz : zetaResidueUnit (w s) ≠ 0 := by
      have heq := (zetaResidueUnit_eventuallyEq hne1).eq_of_nhds
      rw [heq]
      exact mul_ne_zero (sub_ne_zero.mpr hne1)
        (riemannZeta_ne_zero_of_one_le_re (by rw [hwre]; linarith))
    exact ((analyticAt_zetaResidueUnit (w s)).deriv.continuousAt.comp_of_eq hpath.continuousAt rfl).div
      ((analyticAt_zetaResidueUnit (w s)).continuousAt.comp_of_eq hpath.continuousAt rfl) hGz
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hcontd.intervalIntegrable 0 τ)
  have hbound : ‖h τ - h 0‖ ≤ |M| * |τ| := by
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_).trans
      (le_of_eq (by rw [sub_zero]))
    have hs' : |s| ≤ H := by
      rcases le_total 0 τ with h0 | h0
      · rw [uIoc_of_le h0] at hs
        rw [abs_of_pos hs.1]; exact hs.2.trans ((le_abs_self τ).trans hτ)
      · rw [uIoc_of_ge h0] at hs
        rw [abs_of_nonpos hs.2]; linarith [neg_abs_le τ, hs.1]
    have hmem : w s ∈ K := by
      rw [Complex.mem_reProdIm, hwre]
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have him : (w s).im = s := by simp [w]
      rw [him]; exact abs_le.mp hs'
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (hM _ hmem).trans (le_abs_self M)
  -- `Im h 0 = 0` and `|arg(u + iτ)| ≤ π/2`
  have hh0 : (h 0).im = 0 := by
    simp only [h, w, Complex.ofReal_zero, zero_mul, add_zero, Complex.add_im]
    rw [im_zetaEulerLog_ofReal (by linarith), ← Complex.ofReal_log hu.le, Complex.ofReal_im, add_zero]
  have harg : |(Complex.log ((u : ℂ) + τ * I)).im| ≤ Real.pi / 2 := by
    have hre : 0 ≤ ((u : ℂ) + τ * I).re := by simpa using hu.le
    rw [Complex.log_im]
    exact abs_le.mpr ⟨by linarith [Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl hre)],
      Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre)⟩
  have hτim : (zetaEulerLog (w τ)).im = (h τ).im - (Complex.log ((u : ℂ) + τ * I)).im := by
    simp only [h, Complex.add_im]; ring
  have him_diff : |(h τ).im| ≤ |M| * |τ| := by
    have := Complex.abs_im_le_norm (h τ - h 0)
    rw [Complex.sub_im, hh0, sub_zero] at this
    exact this.trans hbound
  show |(zetaEulerLog (w τ)).im| ≤ Real.pi / 2 + |M| * H
  rw [hτim]
  have := mul_le_mul_of_nonneg_left hτ (abs_nonneg M)
  calc |(h τ).im - (Complex.log ((u : ℂ) + τ * I)).im|
      ≤ |(h τ).im| + |(Complex.log ((u : ℂ) + τ * I)).im| := abs_sub _ _
    _ ≤ |M| * |τ| + Real.pi / 2 := add_le_add him_diff harg
    _ ≤ Real.pi / 2 + |M| * H := by linarith

/-- **`ℓ` at large heights**: `|ℓ(σ + it)| ≤ 9 log log|t| + C` for `1 < σ ≤ 2`, `|t| ≥ 9`. -/
theorem exists_norm_zetaEulerLog_le_large :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → 9 ≤ |t| →
      ‖zetaEulerLog (σ + t * I)‖ ≤ 9 * Real.log (Real.log |t|) + C :=
  exists_norm_eulerLog_le_large (1 : DirichletCharacter ℂ 1)

end RHTower
